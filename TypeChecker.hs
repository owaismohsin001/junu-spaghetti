{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
module TypeChecker where

import qualified Data.Map as Map
import Control.Monad
import Data.List
import Data.Either
import Data.Bifunctor
import Debug.Trace ( trace )
import Control.Monad.State
import Text.Megaparsec as P hiding (State)
import Text.Megaparsec.Pos (mkPos)
import Data.Functor
import qualified Data.Set as Set
import Data.Maybe
import Data.Tuple
import qualified Parser
import Nodes

insertAnnotation :: Lhs -> Finalizeable Annotation -> AnnotationState (Annotations (Finalizeable Annotation)) Annotation
insertAnnotation k v@(Finalizeable _ a) = do
    (a, ((i, Annotations b o), m)) <- get
    put (a, ((i, Annotations (Map.insert k v b) o), m))
    return a

getAnnotation :: Show a => Lhs -> Annotations a -> Result ErrorType a
getAnnotation k@(LhsIdentifer _ pos) (Annotations anns rest) =
    case Map.lookup k anns of
        Just v -> Right v
        Nothing -> 
            case rest of
                Just rs -> getAnnotation k rs
                Nothing -> Left $ NoDefinitionFound k pos
getAnnotation k a = error $ "Unexpected args " ++ show (k, a)

modifyAnnotation :: UserDefinedTypes -> Lhs -> Annotation -> Annotations (Finalizeable Annotation) -> Result ErrorType (Annotations (Finalizeable Annotation))
modifyAnnotation usts k@(LhsIdentifer _ pos) ann (Annotations anns rest) =
    case Map.lookup k anns of
        Just (Finalizeable False v) -> Right $ Annotations (Map.insert k (Finalizeable False ann) anns) rest
        Just (Finalizeable True v) -> 
            case sameTypesNoUnionSpec pos usts ann v of
                Right _ -> Right $ Annotations (Map.insert k (Finalizeable False ann) anns) rest
                Left err -> Left $ IrreconcilableAnnotatatedType k ann v pos
        Nothing -> 
            case rest of
                Just rs -> case modifyAnnotation usts k ann rs of
                    Right a -> Right $ Annotations anns (Just a)
                    Left err -> Left err
                Nothing -> Left $ NoDefinitionFound k pos
modifyAnnotation _ k ann as = error $ "Unexpected args " ++ show (k, ann, as)

modifyAnnotationState :: Lhs -> Annotation -> AnnotationState (Annotations (Finalizeable Annotation)) (Result ErrorType Annotation)
modifyAnnotationState k@(LhsIdentifer _ pos) v = do
    (a, ((i, anns), usts)) <- get
    case modifyAnnotation usts k v anns of
        Right x -> (Right <$> put (a, ((i, x), usts))) $> Right v
        Left err -> return $ Left err
modifyAnnotationState k v = error $ "Unexpected args " ++ show (k, v)

finalizeAnnotations :: Annotations (Finalizeable a) -> Annotations (Finalizeable a)
finalizeAnnotations (Annotations anns Nothing) = Annotations (Map.map finalize anns) Nothing
finalizeAnnotations (Annotations anns (Just rest)) = Annotations (Map.map finalize anns) (Just $ finalizeAnnotations rest)

finalizeAnnotationState :: AnnotationState (Annotations (Finalizeable a)) ()
finalizeAnnotationState = modify (\(a, ((i, anns), b)) -> (a, ((i, finalizeAnnotations anns), b)))

getAnnotationState :: Show a => Lhs -> AnnotationState (Annotations (Finalizeable a)) (Result ErrorType a)
getAnnotationState k = get >>= \(_, ((_, anns), _)) -> return (fromFinalizeable <$> getAnnotation k anns)

getAnnotationStateFinalizeable :: Show a => Lhs -> AnnotationState (Annotations a) (Result ErrorType a)
getAnnotationStateFinalizeable k = get >>= \(_, ((_, anns), _)) -> return (getAnnotation k anns)

rigidizeTypeConstraints :: UserDefinedTypes -> Constraint -> Constraint
rigidizeTypeConstraints usts (ConstraintHas lhs cs) = ConstraintHas lhs $ rigidizeTypeConstraints usts cs 
rigidizeTypeConstraints usts (AnnotationConstraint ann) = AnnotationConstraint $ rigidizeTypeVariables usts ann

rigidizeTypeVariables :: UserDefinedTypes -> Annotation -> Annotation
rigidizeTypeVariables usts fid@(GenericAnnotation id cns) = RigidAnnotation id $ map (rigidizeTypeConstraints usts) cns
rigidizeTypeVariables usts fid@RigidAnnotation{} = fid
rigidizeTypeVariables usts id@AnnotationLiteral{} = id
rigidizeTypeVariables usts fid@(Annotation id) = fromMaybe (error $ noTypeFound id sourcePos) (Map.lookup (LhsIdentifer id sourcePos) usts)
rigidizeTypeVariables usts (NewTypeAnnotation id anns annMap) = NewTypeAnnotation id (map (rigidizeTypeVariables usts) anns) (Map.map (rigidizeTypeVariables usts) annMap)
rigidizeTypeVariables usts (NewTypeInstanceAnnotation id anns) = NewTypeInstanceAnnotation id (map (rigidizeTypeVariables usts) anns)
rigidizeTypeVariables usts (FunctionAnnotation args ret) = FunctionAnnotation (map (rigidizeTypeVariables usts) args) (rigidizeTypeVariables usts ret)
rigidizeTypeVariables usts (StructAnnotation ms) = StructAnnotation $ Map.map (rigidizeTypeVariables usts) ms
rigidizeTypeVariables usts (TypeUnion ts) = TypeUnion $ Set.map (rigidizeTypeVariables usts) ts
rigidizeTypeVariables usts OpenFunctionAnnotation{} = error "Can't use rigidizeVariables with open functions"

unrigidizeTypeConstraints :: UserDefinedTypes -> Constraint -> Constraint
unrigidizeTypeConstraints usts (ConstraintHas lhs cs) = ConstraintHas lhs $ unrigidizeTypeConstraints usts cs 
unrigidizeTypeConstraints usts (AnnotationConstraint ann) = AnnotationConstraint $ unrigidizeTypeVariables usts ann

unrigidizeTypeVariables :: UserDefinedTypes -> Annotation -> Annotation
unrigidizeTypeVariables usts fid@(GenericAnnotation id cns) = fid
unrigidizeTypeVariables usts fid@(RigidAnnotation id cns) = GenericAnnotation id $ map (unrigidizeTypeConstraints usts) cns
unrigidizeTypeVariables usts id@AnnotationLiteral{} = id
unrigidizeTypeVariables usts fid@(Annotation id) = fromMaybe (error $ noTypeFound id sourcePos) (Map.lookup (LhsIdentifer id sourcePos) usts)
unrigidizeTypeVariables usts (NewTypeAnnotation id anns annMap) = NewTypeAnnotation id (map (unrigidizeTypeVariables usts) anns) (Map.map (unrigidizeTypeVariables usts) annMap)
unrigidizeTypeVariables usts (NewTypeInstanceAnnotation id anns) = NewTypeInstanceAnnotation id (map (unrigidizeTypeVariables usts) anns)
unrigidizeTypeVariables usts (FunctionAnnotation args ret) = FunctionAnnotation (map (unrigidizeTypeVariables usts) args) (unrigidizeTypeVariables usts ret)
unrigidizeTypeVariables usts (StructAnnotation ms) = StructAnnotation $ Map.map (unrigidizeTypeVariables usts) ms
unrigidizeTypeVariables usts (TypeUnion ts) = TypeUnion $ Set.map (unrigidizeTypeVariables usts) ts
unrigidizeTypeVariables usts OpenFunctionAnnotation{} = error "Can't use rigidizeVariables with open functions"

pushScope :: Show a => AnnotationState (Annotations a) ()
pushScope = (\(a, ((i, mp), b)) -> put (a, ((i, Annotations Map.empty $ Just mp), b))) =<< get

popScope :: Show a => AnnotationState (Annotations a) ()
popScope = (\(a, ((i, Annotations _ (Just mp)), b)) -> put (a, ((i, mp), b))) =<< get

mapRight :: Monad m => m (Either a t) -> (t -> m (Either a b)) -> m (Either a b)
mapRight f f1 = do
        a <- f
        case a of
            Right a -> f1 a
            Left err -> return $ Left err

makeFunAnnotation args = FunctionAnnotation (map snd args)

isCallable :: Annotation -> Bool
isCallable FunctionAnnotation{} = True
isCallable _ = False

mapLeft s f = case s of
        Left x -> f x
        Right a ->  Right a

toEither def (Just a) = Right a
toEither def Nothing = Left def

getTypeState :: Annotation -> P.SourcePos -> State (Annotation, (b, UserDefinedTypes)) (Either ErrorType Annotation)
getTypeState (Annotation id) pos = do
    (_, (_, types)) <- get
    case Map.lookup (LhsIdentifer id pos) types of
        Just st -> return $ Right st
        Nothing -> return . Left $ NoTypeFound id pos
getTypeState a _ = return $ Right a

getTypeStateFrom :: AnnotationState a (Either ErrorType Annotation) -> SourcePos -> AnnotationState a (Either ErrorType Annotation)
getTypeStateFrom f pos = do
    res <- f
    case res of
        Right res -> getTypeState res pos
        Left err -> return $ Left err

firstInferrableReturn :: P.SourcePos -> [Node] -> AnnotationState (Annotations (Finalizeable Annotation)) (Either ErrorType Node)
firstInferrableReturn pos [] = return . Left $ UnInferrableType Nothing pos
firstInferrableReturn pos (IfStmnt cond ts es _:xs) = do
    scope@(_, (_, mp)) <- get
    t <- firstInferrableReturn pos ts
    case t of
        Right a -> return $ Right a
        Left _ -> do
            put scope
            e <- firstInferrableReturn pos es
            case e of
                Right a -> return $ Right a
                Left err -> do
                    put scope
                    firstInferrableReturn pos xs
firstInferrableReturn pos (n@(DeclN (Decl _ rhs _ _)):xs) = do
    getAssumptionType n
    as <- firstInferrableReturn pos [rhs] 
    bs <- firstInferrableReturn pos xs
    return $ mapLeft as (const bs)
firstInferrableReturn pos (n@(DeclN (Assign _ rhs _)):xs) = do
    getAssumptionType n
    as <- firstInferrableReturn pos [rhs] 
    bs <- firstInferrableReturn pos xs
    return $ mapLeft as (const bs)
firstInferrableReturn _ ((Return a _):_) = return $ Right a
firstInferrableReturn pos (_:xs) = firstInferrableReturn pos xs

isGeneric :: P.SourcePos -> UserDefinedTypes -> Annotation -> Bool
isGeneric pos usts ann = evalState (go pos usts ann) Map.empty where
    go :: P.SourcePos -> UserDefinedTypes -> Annotation -> State (Map.Map Annotation Bool) Bool
    go pos mp GenericAnnotation{} = return True
    go pos mp (RigidAnnotation _ cns) = or <$> mapM goConstraints cns where
        goConstraints (ConstraintHas _ cn) = goConstraints cn
        goConstraints (AnnotationConstraint ann) = go pos mp ann
    go pos mp AnnotationLiteral{} = return False
    go pos mp wholeAnn@(Annotation ann) = do
        recordedAnns <- get
        case Map.lookup wholeAnn recordedAnns of
            Just b -> return b
            Nothing -> case Map.lookup (LhsIdentifer ann pos) mp of
                Just new_ann -> do
                    put $ Map.insert wholeAnn False recordedAnns
                    new_res <- go pos mp new_ann
                    put $ Map.insert wholeAnn new_res recordedAnns
                    return new_res
                Nothing -> return False
    go pos mp (FunctionAnnotation args ret) = or <$> mapM (go pos mp) (ret:args)
    go pos mp (StructAnnotation ms) = or <$> mapM (go pos mp) ms
    go pos mp (NewTypeAnnotation _ _ tmp) = or <$> mapM (go pos mp) tmp
    go pos mp (NewTypeInstanceAnnotation _ as) = or <$> mapM (go pos mp) as
    go pos mp (TypeUnion ts) = or <$> mapM (go pos mp) (Set.toList ts)
    go pos mp OpenFunctionAnnotation{} = return False

firstPreferablyDefinedRelation :: SourcePos
    -> Map.Map Lhs Annotation
    -> Set.Set Annotation
    -> TwoSets Annotation
    -> Map.Map Annotation a
    -> Map.Map Annotation (Set.Set Annotation)
    -> Annotation
    -> Either ErrorType Annotation
firstPreferablyDefinedRelation pos usts prevs defs mp rs k =
    case Map.lookup k rs of
        Just s -> 
            if notnull stf then Right . defResIfNull $ inDefs stf 
            else if notnull deftf then Right . defResIfNull $ inDefs deftf
            else if notnull prevs then Right . defResIfNull $ inDefs prevs
            else case defRes of
                    Right x -> Right x
                    Left _ -> Right $ Set.elemAt 0 $ if notnull $ inDefs s then inDefs s else s
            where 
                notnull = not . Set.null
                deftf = Set.filter (flip (isPrmaryDefMember usts) defs) s
                stf = Set.filter (\x -> isJust (Map.lookup x mp)) s

                defResIfNull s' = if notnull s' then Set.elemAt 0 s' else case defRes of
                    Right x -> x
                    Left _ -> Set.elemAt 0 s
        Nothing -> defRes
        where 
            inDefs s = Set.filter (flip (isPrmaryDefMember usts) defs) s
            inSecondaryDefs s = Set.filter (flip (isPrmaryDefMember usts) defs) s
            defRes = 
                case Map.elems $ Map.filter (\s -> isDefMember usts k s && not (Set.disjoint (primary defs) s)) $ Map.mapWithKey Set.insert rs of
                    [] -> case Map.elems $ Map.filter (\s -> isDefMember usts k s && not (Set.disjoint (secondary defs) s)) $ Map.mapWithKey Set.insert rs of
                        [] -> Left $ NoEstablishedRelationWith k pos
                        xs -> Right . Set.elemAt 0 . inSecondaryDefs $ head xs
                    xs -> Right . Set.elemAt 0 . inDefs $ head xs

isDefMember :: UserDefinedTypes -> Annotation -> Set.Set Annotation -> Bool
isDefMember usts a defs = rigidizeTypeVariables usts a `Set.member` defs || a `Set.member` defs

isPrmaryDefMember :: UserDefinedTypes -> Annotation -> TwoSets Annotation -> Bool
isPrmaryDefMember usts a defs = rigidizeTypeVariables usts a `primaryMember` defs || a `primaryMember` defs

isSecondaryDefMember :: UserDefinedTypes -> Annotation -> TwoSets Annotation -> Bool
isSecondaryDefMember usts a defs = rigidizeTypeVariables usts a `secondaryMember` defs || a `secondaryMember` defs

substituteVariablesOptFilter :: Bool
    -> SourcePos
    -> TwoSets Annotation
    -> Map.Map Annotation (Set.Set Annotation)
    -> Map.Map Annotation Annotation
    -> UserDefinedTypes
    -> Annotation
    -> Either ErrorType Annotation
substituteVariablesOptFilter pred pos defs rels mp usts n = evalState (go pred rels mp n) Set.empty where
    goConstraints :: Bool
        -> Map.Map Annotation (Set.Set Annotation)
        -> Map.Map Annotation Annotation
        -> Constraint
        -> State (Set.Set Annotation) (Either ErrorType Constraint)
    goConstraints pred rels mp (ConstraintHas lhs cs) = goConstraints pred rels mp cs >>= (\a -> return $ ConstraintHas lhs <$> a)
    goConstraints pred rels mp (AnnotationConstraint ann) = go pred rels mp ann >>= (\a -> return $ AnnotationConstraint <$> a)

    go :: Bool
        -> Map.Map Annotation (Set.Set Annotation)
        -> Map.Map Annotation Annotation
        -> Annotation
        -> State (Set.Set Annotation) (Either ErrorType Annotation)
    go pred rels mp fid@(GenericAnnotation id cns) =
        maybe g (\x -> if sameTypesBool pos usts fid x then g else return $ Right x) (Map.lookup fid mp) >>= \case
            Right retGen -> modify (retGen `Set.insert`) >> return (Right retGen)
            Left err -> return $ Left err
        where 
            f gs x = case firstPreferablyDefinedRelation pos usts gs defs mp rels x of
                Right a -> Right a
                Left _ -> Right x
            g = join <$> (mapM (goConstraints pred rels mp) cns >>= (\case
                Left err -> return $ Left err
                Right x -> get >>= \gs -> return $ Right $ (f gs . GenericAnnotation id) x) . sequence)
    go pred rels mp (RigidAnnotation id cns) = 
        go pred rels mp (GenericAnnotation id cns) >>= \case
            Right (GenericAnnotation id cns) -> return . Right $ RigidAnnotation id cns
            Right a -> return $ Right a
            Left err -> return $ Left err
    go pred rels mp id@AnnotationLiteral{} = return $ Right id
    go pred rels mp fid@(Annotation id) = return $ maybe (Left $ NoTypeFound id pos) Right (Map.lookup (LhsIdentifer id pos) usts)
    go pred rels mp (NewTypeAnnotation id anns annMap) = do
        anns' <- sequence <$> mapM (go pred rels mp) anns
        annMap' <- sequence <$> mapM (go pred rels mp) annMap
        return (NewTypeAnnotation id <$> anns' <*> annMap')
    go pred rels mp (NewTypeInstanceAnnotation id anns) =
        (\xanns -> return $ NewTypeInstanceAnnotation id <$> xanns) . sequence =<< mapM (go pred rels mp) anns
    go pred rels mp (FunctionAnnotation args ret) = mapM (go pred rels mp) args >>=
        (\args'
        -> go pred rels mp ret
                >>= \ ret' -> return $ FunctionAnnotation <$> args' <*> ret')
        . sequence
    go pred rels mp (StructAnnotation ms) = 
        (\ms' -> return $ StructAnnotation <$> ms') . sequence =<< mapM (go pred rels mp) ms
    go pred rels mp (TypeUnion ts) = 
        (\xs -> case (if pred then filter (\a -> not (isGeneric pos usts a) || (isGeneric pos usts a && annotationConsistsOf usts defs a)) else id) <$> xs of
            Left err -> return $ Left err
            Right [] -> return $ foldr1 (mergedTypeConcrete pos usts) <$> xs
            Right xs -> return . Right $ foldr1 (mergedTypeConcrete pos usts) xs) . sequence =<< mapM (go pred rels mp) (Set.toList ts)
    go pred rels mp OpenFunctionAnnotation{} = error "Can't use substituteVariables with open functions"

constraintsConsistsOf :: UserDefinedTypes -> TwoSets Annotation -> Constraint -> Bool
constraintsConsistsOf usts defs (ConstraintHas lhs cs) = constraintsConsistsOf usts defs cs 
constraintsConsistsOf usts defs (AnnotationConstraint ann) = annotationConsistsOf usts defs ann

annotationConsistsOf :: UserDefinedTypes -> TwoSets Annotation -> Annotation -> Bool
annotationConsistsOf usts defs fid@(GenericAnnotation id cns) = isSecondaryDefMember usts fid defs && all (constraintsConsistsOf usts defs) cns
annotationConsistsOf usts defs fid@(RigidAnnotation id cns) = isSecondaryDefMember usts fid defs && all (constraintsConsistsOf usts defs) cns
annotationConsistsOf usts defs AnnotationLiteral{} = False
annotationConsistsOf usts defs fid@(Annotation ident) = False
annotationConsistsOf usts defs (NewTypeAnnotation id anns annMap) = all (annotationConsistsOf usts defs) anns && and (Map.elems $ Map.map (annotationConsistsOf usts defs) annMap)
annotationConsistsOf usts defs (NewTypeInstanceAnnotation id anns) = all (annotationConsistsOf usts defs) anns
annotationConsistsOf usts defs (FunctionAnnotation args ret) = all (annotationConsistsOf usts defs) (ret:args)
annotationConsistsOf usts defs (StructAnnotation ms) = and . Map.elems $ Map.map (annotationConsistsOf usts defs) ms
annotationConsistsOf usts defs (TypeUnion ts) = all (annotationConsistsOf usts defs) ts
annotationConsistsOf usts defs (OpenFunctionAnnotation args ret ftr _) = all (annotationConsistsOf usts defs) (ftr:ret:args)

substituteVariables = substituteVariablesOptFilter True

collectGenericConstraintsOptionalHOF :: Bool -> Bool -> UserDefinedTypes -> Constraint -> Set.Set Annotation
collectGenericConstraintsOptionalHOF collectHOFs collectRigids usts (ConstraintHas lhs cs) = collectGenericConstraintsOptionalHOF collectHOFs collectRigids usts cs 
collectGenericConstraintsOptionalHOF collectHOFs collectRigids usts (AnnotationConstraint ann) = collectGenenricsOptionalHOF collectHOFs collectRigids usts ann

collectGenenricsOptionalHOF :: Bool -> Bool -> UserDefinedTypes -> Annotation -> Set.Set Annotation
collectGenenricsOptionalHOF collectHOFs collectRigids usts fid@(GenericAnnotation id cns) = Set.singleton fid `Set.union` Set.unions (map (collectGenericConstraintsOptionalHOF collectHOFs collectRigids usts) cns)
collectGenenricsOptionalHOF collectHOFs True usts fid@(RigidAnnotation id cns) = Set.singleton fid `Set.union` Set.unions (map (collectGenericConstraintsOptionalHOF collectHOFs True usts) cns)
collectGenenricsOptionalHOF collectHOFs False usts fid@(RigidAnnotation id cns) = Set.unions (map (collectGenericConstraintsOptionalHOF collectHOFs False usts) cns)
collectGenenricsOptionalHOF collectHOFs collectRigids usts AnnotationLiteral{} = Set.empty
collectGenenricsOptionalHOF collectHOFs collectRigids usts fid@(Annotation ident) = maybe (error "Run your passes in order. You should know that this doesn't exists by now") (const Set.empty) (Map.lookup (LhsIdentifer ident (SourcePos "" (mkPos 0) (mkPos 0))) usts)
collectGenenricsOptionalHOF collectHOFs collectRigids usts (NewTypeAnnotation id anns annMap) = Set.unions (Set.map (collectGenenricsOptionalHOF collectHOFs collectRigids usts) (Set.fromList anns)) `Set.union` foldl1 Set.union (map (collectGenenricsOptionalHOF collectHOFs collectRigids usts) (Map.elems annMap))
collectGenenricsOptionalHOF collectHOFs collectRigids usts (NewTypeInstanceAnnotation id anns) = Set.unions $ Set.map (collectGenenricsOptionalHOF collectHOFs collectRigids usts) (Set.fromList anns)
collectGenenricsOptionalHOF collectHOFs collectRigids usts (FunctionAnnotation args ret) = if collectHOFs then Set.unions $ Set.map (collectGenenricsOptionalHOF collectHOFs collectRigids usts) (Set.fromList $ args ++ [ret]) else Set.empty
collectGenenricsOptionalHOF collectHOFs collectRigids usts (StructAnnotation ms) = Set.unions $ Set.map (collectGenenricsOptionalHOF collectHOFs collectRigids usts) (Set.fromList $ Map.elems ms)
collectGenenricsOptionalHOF collectHOFs collectRigids usts (TypeUnion ts) = Set.unions $ Set.map (collectGenenricsOptionalHOF collectHOFs collectRigids usts) ts
collectGenenricsOptionalHOF collectHOFs collectRigids usts (OpenFunctionAnnotation args ret ftr _) = Set.unions $ Set.map (collectGenenricsOptionalHOF collectHOFs collectRigids usts) $ Set.fromList (args++[ret, ftr])

collectGenenrics = collectGenenricsOptionalHOF False True
collectGenenricsHOF = collectGenenricsOptionalHOF True True

getLookupTypeIfAvailable :: Annotation -> SubstituteState Annotation
getLookupTypeIfAvailable k = do
    (a, ((rs, mp), usts)) <- get
    case Map.lookup k mp of
        Just k -> getLookupTypeIfAvailable k
        Nothing -> return k

changeType :: P.SourcePos -> TwoSets Annotation -> Annotation -> Annotation -> SubstituteState (Either ErrorType ())
changeType pos defs k v = do
    (a, ((rel, mp), usts)) <- get
    case substituteVariables pos defs rel mp usts v of
        Right sub -> put (a, ((rel, Map.insert k sub mp), usts)) $> Right ()
        Left err -> return $ Left err

reshuffleTypes :: P.SourcePos -> TwoSets Annotation -> SubstituteState ()
reshuffleTypes pos defs = (\(_, ((_, mp), _)) -> sequence_ $ Map.mapWithKey (changeType pos defs) mp) =<< get

sameTypesNoUnionSpec = sameTypesGeneric (False, True, False, Map.empty)

addTypeVariable :: SourcePos
    -> (Annotation -> SourcePos -> UserDefinedTypes -> Annotation -> Annotation -> Either ErrorType Annotation)
    -> TwoSets Annotation
    -> Maybe (SubstituteState (Either ErrorType ()))
    -> Annotation
    -> Annotation
    -> SubstituteState (Either ErrorType Annotation)
addTypeVariable pos f defs stmnt k v = do
    (a, ((rs, mp), usts)) <- get
    case Map.lookup k mp of
        Nothing -> addToMap k v
        Just a -> if collectGenenricsNoRigids usts a == Set.empty && collectGenenricsNoRigids usts v == Set.empty then case f k pos usts a v of
                Right v -> addToMap k v
                Left err -> lastResort a rs mp usts (Left err)
            else specifyInternal pos stmnt f defs a v >>= \case
                Right v -> addToMap k v
                Left _ -> specifyInternal pos stmnt f defs v a >>= \case
                    Right v -> addToMap k v
                    Left err -> lastResort a rs mp usts (Left err)
    where
        collectGenenricsNoRigids = collectGenenricsOptionalHOF False False
        collectGenenricsNoRigidsHOF = collectGenenricsOptionalHOF True False

        addToMap k v = do
            (a, ((rs, mp), usts)) <- get
            if k `Set.member` collectGenenricsNoRigidsHOF usts v then 
                return . Left $ InfiniteTypeError k v pos 
            else do
                put (a, ((rs, Map.insert k v mp), usts))
                fromMaybe (updateRelations pos stmnt f defs) stmnt >>= \case
                    Right _ -> reshuffleTypes pos defs $> Right v
                    Left err -> return . Left $ UnificationError k err

        lastResort a rs mp usts x = if a == AnnotationLiteral "_" then addToMap k v else 
            case Map.lookup k rs of
                Just st -> if Set.member v st then addToMap k v else return x
                Nothing -> return x

-- This is written horribly, rewrite it
updateSingleRelation :: SourcePos
    -> p
    -> (Annotation
        -> SourcePos
        -> UserDefinedTypes
        -> Annotation
        -> Annotation
        -> Either ErrorType Annotation)
    -> TwoSets Annotation
    -> Annotation
    -> SubstituteState (Either ErrorType ())
updateSingleRelation pos stmnt fa defs r = do
    (a, ((rs, mp), usts)) <- get
    case Map.lookup r rs of
        Just rl -> do
            (\case 
                Right _ -> do
                    put (a, ((Map.insert r (getAllRelationsInvolving r rs) rs, mp), usts))
                    maybe (return $ Right ()) (fmap ($> ()) . specifyInternal pos (Just . return $ Right ()) fa defs r) fnv
                Left err -> return $ Left err) . sequence =<< mapM (uncurry f) mls'
            where 
            m = Map.filterWithKey (\k _ -> k `Set.member` rl) mp
            mls = Map.toList m
            fnv = firstNonUnderscore mls
            mls' = case fnv of 
                Just a -> map (\(k, _) -> (k, a)) mls
                Nothing -> []
            f = addTypeVariable pos fa defs (Just . return $ Right ())
            firstNonUnderscore [] = Nothing 
            firstNonUnderscore ((_, AnnotationLiteral "_"):xs) = firstNonUnderscore xs
            firstNonUnderscore ((_, ann):xs) = Just ann

            getAllRelationsInvolving r rs = Set.unions $ Map.elems $ Map.filter (Set.member r) $ Map.mapWithKey Set.insert rs
        Nothing -> return . Left $ NoEstablishedRelationWith r pos

updateRelations :: P.SourcePos
    -> Maybe (SubstituteState (Either ErrorType ()))
    -> (Annotation -> P.SourcePos -> UserDefinedTypes -> Annotation -> Annotation -> Either ErrorType Annotation) 
    -> TwoSets Annotation
    -> SubstituteState (Either ErrorType ())
updateRelations pos f stmnt defs = do
    (a, ((rs, mp), usts)) <- get
    x <- mapM (updateSingleRelation pos f stmnt defs) $ Map.keys rs
    case sequence x of
        Right _ -> return $ Right ()
        Left err -> return $ Left err

addRelation :: SourcePos
    -> Maybe (SubstituteState (Either ErrorType ()))
    -> (Annotation -> SourcePos -> UserDefinedTypes -> Annotation -> Annotation -> Either ErrorType Annotation)
    -> TwoSets Annotation
    -> Annotation
    -> Annotation
    -> SubstituteState (Either a ())
addRelation pos stmnt f defs r nv = do
    (a, ((rs, mp), usts)) <- get
    case Map.lookup r rs of
        Just rl -> do
            let nrs = Map.insert r (rl `Set.union` Set.singleton nv) rs
            put (a, ((nrs, mp), usts))
            Right () <$ updateSingleRelation pos stmnt f defs r
        Nothing -> do
            let nrs = Map.insert r (Set.singleton nv) rs
            put (a, ((nrs, mp), usts))
            Right () <$ updateSingleRelation pos stmnt f defs r

applyConstraintState :: SourcePos
    -> Maybe (SubstituteState (Either ErrorType ()))
    -> (Annotation -> SourcePos -> UserDefinedTypes -> Annotation -> Annotation -> Either ErrorType Annotation) 
    -> TwoSets Annotation -> Annotation -> Constraint -> SubstituteState (Either ErrorType Annotation)
applyConstraintState pos stmnt f defs ann (ConstraintHas lhs cn) = 
    do 
        mp <- getTypeMap
        case ann of
            StructAnnotation mp -> 
                case lhs `Map.lookup` mp of
                    Just ann -> applyConstraintState pos stmnt f defs ann cn
                    Nothing -> return . Left $ FieldNotFound lhs ann pos
            Annotation id ->
                case LhsIdentifer id pos `Map.lookup` mp of
                    Just ann -> applyConstraintState pos stmnt f defs ann cn
                    Nothing -> return . Left $ NoTypeFound id pos
            NewTypeInstanceAnnotation id args -> 
                        accessNewType args
                        (\(NewTypeAnnotation _ _ ps) -> 
                            case Map.lookup lhs ps of
                                Just ann -> applyConstraintState pos stmnt f defs ann cn
                                Nothing -> return . Left $ FieldNotFound lhs ann pos
                            ) 
                        (LhsIdentifer id pos)
            g@(GenericAnnotation id cns) -> case genericHas pos g lhs cns of
                Right ann -> applyConstraintState pos stmnt f defs ann cn
                Left err -> return $ Left err
            g@(RigidAnnotation id cns) -> case genericHas pos g lhs cns of
                Right ann -> applyConstraintState pos stmnt f defs ann cn
                Left err -> return $ Left err
            t@TypeUnion{} -> typeUnionHas pos stmnt f defs t cn >>= \case
                Right ann -> applyConstraintState pos stmnt f defs ann cn
                Left err -> return $ Left err
            a -> return . Left $ UnsearchableType lhs a pos
applyConstraintState pos stmnt f defs ann2 (AnnotationConstraint ann1) = do
    a <- if isGenericAnnotation ann2 && isGenericAnnotation ann1 then addRelation pos stmnt f defs ann2 ann1 *> addRelation pos stmnt f defs ann1 ann2 $> Right ann1 else addTypeVariable pos f defs stmnt ann1 ann2
    case a of
        Right _ -> specifyInternal pos stmnt f defs ann1 ann2
        Left err -> return $ Left err

typeUnionHas pos stmnt f defs (TypeUnion st) cn = (\case
                Left err -> return $ Left err
                Right stl -> do
                    a <- sequence <$> mapM (flip (applyConstraintState pos stmnt f defs) cn) stl
                    case a of
                        Right (x:_) -> return $ Right x
                        Left err -> return $ Left err
                ) . sequence =<< mapM (flip (applyConstraintState pos stmnt f defs) cn) stl where stl = Set.toList st
typeUnionHas _ _ _ _ t _ = error $ "typeUnionHas can only be called with type union, not " ++ show t

isValidNewTypeInstance = undefined

isGeneralizedInstance pos ann@(NewTypeInstanceAnnotation id1 anns1) = do
    a <- fullAnotationFromInstance pos ann
    case a of
        Right (NewTypeAnnotation id2 anns2 _) -> return $ id1 == id2 && length anns1 < length anns2
        Right _ -> return False
        Left err -> return False
isGeneralizedInstance a b = error $ "Unexpected argments for isGeneralizedInstance [" ++ show a ++ ", " ++ show b ++ "]"

isGeneralizedInstanceFree :: SourcePos -> Annotation -> Map.Map Lhs Annotation -> Bool
isGeneralizedInstanceFree pos ann@(NewTypeInstanceAnnotation id1 anns1) mp =
    case fullAnotationFromInstanceFree pos mp ann of
        Right (NewTypeAnnotation id2 anns2 _) -> id1 == id2 && length anns1 < length anns2
        Right _ -> False
        Left err -> False
isGeneralizedInstanceFree a b c = error $ "Unexpected argments for isGeneralizedInstance [" ++ show a ++ ", " ++ show b ++ ", " ++ show c ++ "]"

specifyInternal :: SourcePos
    -> Maybe (SubstituteState (Either ErrorType ()))
    -> (Annotation -> SourcePos -> UserDefinedTypes -> Annotation -> Annotation -> Either ErrorType Annotation)
    -> TwoSets Annotation
    -> Annotation
    -> Annotation
    -> SubstituteState (Either ErrorType Annotation)
specifyInternal pos stmnt f defs a@AnnotationLiteral{} b@AnnotationLiteral{} = (\mp -> return $ sameTypes pos mp a b *> Right a) =<< gets (snd . snd)
specifyInternal pos stmnt f defs a@(RigidAnnotation id1 cns1) b@(RigidAnnotation id2 cns2) 
    | id1 == id2 = (b <$) <$> (sequence <$> mapM (applyConstraintState pos stmnt f defs b) cns1)
    | otherwise = return . Left $ UnmatchedType a b pos
specifyInternal pos stmnt f defs a@(GenericAnnotation id cns) b@(AnnotationLiteral ann) = do
    mp <- getTypeMap
    ann <- addTypeVariable pos f defs stmnt a b
    case ann of
        Right ann ->
            (\case
                Right _ -> return $ Right b
                Left err -> return $ Left err) . sequence =<< mapM (applyConstraintState pos stmnt f defs ann) cns
        Left err -> return $ Left err
specifyInternal pos stmnt f defs a@(GenericAnnotation id cns) b@(Annotation ann) = do
    anno <- getTypeState b pos
    case anno of
        Right ann -> specifyInternal pos stmnt f defs a ann
        Left err -> return $ Left err
specifyInternal pos stmnt f defs a@(Annotation id1) b@(Annotation id2) 
    | id1 == id2 = return $ Right b
    | otherwise = (\mp -> case Map.lookup (LhsIdentifer id1 pos) mp of 
        Just a' -> case Map.lookup (LhsIdentifer id2 pos) mp of
            Just b' -> specifyInternal pos stmnt f defs a' b'
            Nothing -> return . Left $ NoTypeFound id2 pos
        Nothing -> return . Left $ NoTypeFound id1 pos) =<< getTypeMap
specifyInternal pos stmnt f defs a@(Annotation id) b = (\mp -> case Map.lookup (LhsIdentifer id pos) mp of 
    Just a' -> specifyInternal pos stmnt f defs a' b
    Nothing -> return . Left $ NoTypeFound id pos) =<< getTypeMap
specifyInternal pos stmnt f defs a b@(Annotation id) = (\mp -> case Map.lookup (LhsIdentifer id pos) mp of 
    Just b' -> specifyInternal pos stmnt f defs a b'
    Nothing -> return . Left $ NoTypeFound id pos) =<< getTypeMap
specifyInternal pos stmnt f defs a@(GenericAnnotation id1 cns1) b@(GenericAnnotation id2 cns2) = do
    (\case
        Right _ -> addRelation pos stmnt f defs b a *> addRelation pos stmnt f defs a b $> Right b
        Left err -> return $ Left err
        ) . sequence =<< mapM (applyConstraintState pos stmnt f defs b) cns1
specifyInternal pos stmnt f defs a@(GenericAnnotation id cns) b@(TypeUnion st) = (\case
    Right _ -> do
        a <- addTypeVariable pos f defs stmnt a b
        case a of
            Right _ -> return $ Right b
            Left err -> return $ Left err
    Left err -> return $ Left err) . sequence =<< mapM (applyConstraintState pos stmnt f defs b) cns
specifyInternal pos stmnt f defs a@(StructAnnotation ms1) b@(StructAnnotation ms2)
    | Map.size ms1 /= Map.size ms2 = return . Left $ UnmatchedType a b pos
    | Map.null ms1 && Map.null ms2 = return $ Right b
    | Set.fromList (Map.keys ms1) == Set.fromList (Map.keys ms2) = (\case
        Right _ -> return $ Right b
        Left err -> return $ Left err) . sequence =<< zipWithM (specifyInternal pos stmnt f defs) (Map.elems ms1) (Map.elems ms2)
specifyInternal pos stmnt f defs a@(OpenFunctionAnnotation oargs oret _ _) b@(FunctionAnnotation args ret) 
    | length args /= length oargs = return . Left $ CallError oargs args pos
    | otherwise = (\case
        Right _ -> return $ Right b
        Left err -> return $ Left err
        ) . sequence =<< zipWithM (specifyInternal pos stmnt f defs) (oargs ++ [oret]) (args ++ [ret])
specifyInternal pos stmnt f defs a@(FunctionAnnotation oargs oret) b@(FunctionAnnotation args ret)
    | length args /= length oargs = return . Left $ CallError oargs args pos
    | otherwise = (\case
        Right _ -> return $ Right b
        Left err -> return $ Left err
        ) . sequence =<< zipWithM (specifyInternal pos stmnt f defs) (oargs ++ [oret]) (args ++ [ret])
specifyInternal pos stmnt f defs a@(NewTypeAnnotation id1 anns1 _) b@(NewTypeInstanceAnnotation id2 anns2) 
    | id1 /= id2 = return . Left $ UnmatchedType a b pos
    | otherwise = do
        (_, ((_, mp), usts)) <- get
        specifyInternal pos stmnt (const mergedTypeConcreteEither) defs (NewTypeInstanceAnnotation id1 anns1) b
        where 
            fx rels = do
                mapM_ sequence_ <$> sequence (Map.map sequence <$> Map.mapWithKey (\k v -> map (\a -> 
                    addRelation pos stmnt f defs k a >>= \case
                        Right _ -> addRelation pos stmnt f defs a k
                        Left err -> return $ Left err) v) $ Map.map Set.toList rels)
specifyInternal pos stmnt f defs a@(NewTypeInstanceAnnotation id1 anns1) b@(NewTypeInstanceAnnotation id2 anns2) 
    | id1 /= id2 = (\mp -> return $ sameTypes pos mp a b) =<< getTypeMap
    | otherwise  = do
        pred <- isGeneralizedInstance pos a
        if pred then do
            x <- fullAnotationFromInstance pos a
            case x of
                Right ntp@(NewTypeAnnotation id anns mp) -> specifyInternal pos stmnt f defs ntp b
                Right _ -> return . Left $ NoTypeFound id1 pos
                Left err -> return $ Left err
        else (\case
                Right _ -> return $ Right b
                Left err -> return $ Left err
                ) . sequence =<< zipWithM (specifyInternal pos stmnt f defs) anns1 anns2
specifyInternal pos stmnt fa defs a@(TypeUnion _as) b@(TypeUnion _bs) = do
    mp <- getTypeMap
    case (foldr1 (mergedTypeConcrete pos mp) _as, foldr1 (mergedTypeConcrete pos mp) _bs) of
        (TypeUnion as, TypeUnion bs) -> do
            xs <- sequence <$> mapM (f mp $ Set.toList _as) (Set.toList _bs)
            case xs of
                Right _ -> return $ Right b
                Left _ -> do
                    xs <- sequence <$> mapM (f mp $ Set.toList as) (Set.toList bs)
                    case xs of
                        Right _ -> return $ Right b
                        Left err -> if Set.size as == Set.size bs && Set.null (collectGenenrics mp a) then return $ Left err 
                                else distinctUnion mp err (Set.toList $ collectGenenrics mp a)
        (a, b) -> specifyInternal pos stmnt fa defs a b
    where
        f mp ps2 v1 = getFirst a b pos $ map (\x -> specifyInternal pos stmnt (const sameTypes) defs x v1) ps2
        typeUnionList (TypeUnion xs) action = action $ Set.toList xs
        typeUnionList a action = specifyInternal pos stmnt (const sameTypes) defs a b
        g mp ps2 v1 = map (\x -> (specifyInternal pos stmnt (const sameTypes) defs x v1, x)) ps2
        isRightLifted s = isRight <$> s
        distinctUnion _ err [] = return $ Left err
        distinctUnion mp _ xs = do
            let as' = match ++ left where (match, left) = partition (isGeneric pos mp) (Set.toList _as)
            let bs' = match ++ left where (match, left) = partition (isGeneric pos mp) (Set.toList _bs)
            usts <- getTypeMap
            c1 <- specifyInternal pos stmnt (const sameTypes) defs (head xs) (foldr1 (mergedTypeConcrete pos usts) $ take (length xs) as')
            c2 <- sequence <$> zipWithM (flip (specifyInternal pos stmnt (const sameTypes) defs)) (tail xs) (drop (length xs) as')
            case (c1, c2) of
                (Right _, Right _) -> return $ Right $ mergedTypeConcrete pos usts b b
                (Left err, _) -> return $ Left err
                (_, Left err) -> return $ Left err
specifyInternal pos stmnt f defs a b@(TypeUnion st) = do
    x <- sequence <$> mapM (flip (specifyInternal pos stmnt f defs) a) stl
    case x of
        Right a -> return . Right $ head a
        Left err -> return $ Left err
    where stl = Set.toList st
specifyInternal pos stmnt f defs a@(TypeUnion st) b = getFirst a b pos $ map (flip (specifyInternal pos stmnt f defs) b) $ Set.toList st
specifyInternal pos stmnt f defs a@(GenericAnnotation id cns) b = 
    (\case
        Right _ -> do
            a <- addTypeVariable pos f defs stmnt a b
            case a of
                Right _ -> return $ Right b
                Left err -> return $ Left err
        Left err -> return $ Left err) . sequence =<< mapM (applyConstraintState pos stmnt f defs b) cns
specifyInternal pos _ _ _ a b = (\mp -> return $ sameTypes pos mp a b) =<< getTypeMap

getFirst a b pos [] = return . Left $ UnmatchedType a b pos
getFirst a b pos (x:xs) = x >>= \case
    Right a -> return $ Right a
    Left _ -> getFirst a b pos xs

basicSpecifyFunction :: Annotation -> SourcePos -> UserDefinedTypes -> Annotation -> Annotation -> Either ErrorType Annotation
basicSpecifyFunction _ pos usts a b = sameTypesGeneric (False, True, True, Map.empty) pos usts a b $> b

-- specify :: SourcePos -> Set.Set Annotation -> Map.Map Annotation Annotation -> UserDefinedTypes -> Annotation -> Annotation -> Either String (Annotation, TypeRelations)
specifyGeneralized pos f defs base mp a b = (,rel) <$> ann where (ann, (ann1, ((rel, nmp), usts))) = runState (specifyInternal pos Nothing f defs a b) (a, ((Map.empty, base), mp))

specify :: SourcePos -> TwoSets Annotation -> Map.Map Annotation Annotation -> Map.Map Lhs Annotation -> Annotation -> Annotation -> Either ErrorType (Annotation, TypeRelations)
specify pos = specifyGeneralized pos basicSpecifyFunction

getPartialSpecificationRules :: SourcePos -> TwoSets Annotation -> Map.Map Annotation Annotation -> UserDefinedTypes -> Annotation -> Annotation -> (Map.Map Annotation Annotation, TypeRelations)
getPartialSpecificationRules pos defs base mp a b = (nmp, rel) where (ann, (ann1, ((rel, nmp), usts))) = runState (specifyInternal pos Nothing basicSpecifyFunction defs a b) (a, ((Map.empty, base), mp))

getPartialNoUnderScoreSpecificationRules :: SourcePos -> TwoSets Annotation -> Map.Map Annotation Annotation -> UserDefinedTypes -> Annotation -> Annotation -> (Map.Map Annotation Annotation, TypeRelations)
getPartialNoUnderScoreSpecificationRules pos defs base mp a b = 
    (Map.mapWithKey (\k a -> if a == AnnotationLiteral "_" then k else a) nmp, rel) where (nmp, rel) = getPartialSpecificationRules pos defs base mp a b

getSpecificationRulesGeneralized :: SourcePos
    -> (Annotation -> SourcePos -> UserDefinedTypes -> Annotation -> Annotation -> Either ErrorType Annotation)
    -> TwoSets Annotation
    -> Map.Map Annotation Annotation
    -> Map.Map Lhs Annotation
    -> Annotation
    -> Annotation
    -> Either ErrorType (Annotation, Map.Map Annotation Annotation, TypeRelations)
getSpecificationRulesGeneralized pos f defs base mp a b = case fst st of
    Right r -> Right (r, nmp, rel)
    Left err -> Left err 
    where st@(ann, (ann1, ((rel, nmp), usts))) = runState (specifyInternal pos Nothing f defs a b) (a, ((Map.empty, base), mp))

getSpecificationRules :: SourcePos -> TwoSets Annotation -> Map.Map Annotation Annotation -> Map.Map Lhs Annotation -> Annotation-> Annotation -> Either ErrorType (Annotation, Map.Map Annotation Annotation, TypeRelations)
getSpecificationRules pos = getSpecificationRulesGeneralized pos basicSpecifyFunction

sameTypesGenericBool gs crt pos mp a b = case sameTypesGeneric gs pos mp a b of
    Right _ -> True
    Left _ -> False

sameTypesBool pos mp a b = case sameTypes pos mp a b of
    Right _ -> True
    Left _ -> False

specifyTypesBool pos defs base usts a b = case specify pos defs base usts a b of
    Right _ -> True
    Left _ -> False                                     

isGenericAnnotation a = case a of 
    a@GenericAnnotation{} -> True
    _ -> False

expectedUnion pos lhs ann = ExpectedSomething "union" (AnnotationLiteral $ show lhs) pos

fNode f x = head $ f [x]

earlyReturnToElse :: [Node] -> [Node]
earlyReturnToElse [] = []
earlyReturnToElse (IfStmnt c ts [] pos:xs) = 
    if isReturn $ last ts then [IfStmnt c (earlyReturnToElse ts) (earlyReturnToElse xs) pos]
    else IfStmnt c (earlyReturnToElse ts) [] pos : earlyReturnToElse xs
    where 
        isReturn a@Return{} = True
        isReturn _ = False
earlyReturnToElse (IfStmnt c ts es pos:xs) = IfStmnt c (earlyReturnToElse ts) (earlyReturnToElse es) pos : earlyReturnToElse xs
earlyReturnToElse (FunctionDef args ret ns pos:xs) = FunctionDef args ret (earlyReturnToElse ns) pos : earlyReturnToElse xs
earlyReturnToElse (DeclN (Decl lhs n ann pos):xs) = DeclN (Decl lhs (fNode earlyReturnToElse n) ann pos) : earlyReturnToElse xs
earlyReturnToElse (DeclN (Assign lhs n pos):xs) = DeclN (Assign lhs (fNode earlyReturnToElse n) pos) : earlyReturnToElse xs
earlyReturnToElse (x:xs) = x : earlyReturnToElse xs

freshDecl :: P.SourcePos -> Node -> TraversableNodeState Decl
freshDecl pos node = do
    (i, xs) <- get
    let id = LhsIdentifer ("__new_lifted_lambda_" ++ show i) pos
    put (i+1, xs ++ [Decl id node Nothing pos])
    return $ Decl id node Nothing pos

getDecls :: TraversableNodeState [Decl]
getDecls = get >>= \(_, xs) -> return xs

putDecls :: TraversableNodeState a -> TraversableNodeState a
putDecls action = do
    modify $ \(a, _) -> (a, [])
    action

inNewScope :: TraversableNodeState a -> TraversableNodeState a
inNewScope action = do
    (a, xs) <- get
    put (a+1, [])
    res <- action
    put (a, xs)
    return res

lastRegisteredId :: TraversableNodeState String
lastRegisteredId = do
    (i, _) <- get
    return ("__new_lifted_lambda_" ++ show (i-1))

registerNode :: Node -> TraversableNodeState Node
registerNode n@(FunctionDef args ret body pos) = do 
    mbody <- inNewScope $ liftLambda body
    decl <- freshDecl pos $ FunctionDef args ret mbody pos
    id <- lastRegisteredId
    return $ Identifier id pos
registerNode (IfStmnt c ts es pos) = putDecls $ do
    cx <- registerNode c
    tsx <- inNewScope $ liftLambda ts
    esx <- inNewScope $ liftLambda es
    return $ IfStmnt cx tsx esx pos
registerNode (Call e args pos) = Call <$> registerNode e <*> mapM registerNode args <*> return pos
registerNode (Return n pos) = flip Return pos <$> registerNode n
registerNode (StructN (Struct mp pos)) = StructN . flip Struct pos <$> mapM registerNode mp
registerNode (IfExpr c t e pos) = IfExpr <$> registerNode c <*> registerNode t <*> registerNode e <*> return pos
registerNode (Access n lhs pos) = flip Access lhs <$> registerNode n <*> return pos
registerNode (CreateNewType lhs args pos) = CreateNewType lhs <$> mapM registerNode args <*> return pos
registerNode a = return a

getRegister :: Node -> TraversableNodeState (Node, [Decl])
getRegister n = (,) <$> registerNode n <*> getDecls

liftLambda :: [Node] -> TraversableNodeState [Node]
liftLambda [] = return []
liftLambda (DeclN (ImplOpenFunction lhs args ret body ftr pos):xs) = putDecls $ do
    rest <- liftLambda xs
    (\mbody -> DeclN (ImplOpenFunction lhs args ret mbody ftr pos) : rest) <$> liftLambda body
liftLambda (DeclN opf@OpenFunctionDecl{}:xs) = (DeclN opf : ) <$> liftLambda xs
liftLambda (DeclN (Decl lhs (FunctionDef args ret body fpos) ann pos):xs) =  putDecls $ do
    mbody <- inNewScope $ liftLambda body
    rest <- liftLambda xs
    return $ DeclN (Decl lhs (FunctionDef args ret mbody fpos) ann pos) : rest
liftLambda (DeclN (Decl lhs n ann pos):xs) = putDecls $ do
    getRegister n >>= \(x, ds) -> (map DeclN ds ++) . (DeclN (Decl lhs x ann pos) :) <$> liftLambda xs
liftLambda (DeclN (Assign lhs (FunctionDef args ret body fpos) pos):xs) = putDecls $ do
    mbody <- inNewScope $ liftLambda body
    rest <- liftLambda xs
    return $ DeclN (Assign lhs (FunctionDef args ret mbody fpos) pos) : rest
liftLambda (DeclN (Assign lhs n pos):xs) =
    putDecls $ getRegister n >>= \(x, ds) -> (map DeclN ds ++) . (DeclN (Assign lhs x pos) :) <$> liftLambda xs
liftLambda (DeclN (Expr n):xs) = 
    putDecls $ getRegister n >>= \(x, ds) -> (map DeclN ds ++) . (DeclN (Expr x) :) <$> liftLambda xs
liftLambda (n:ns) = putDecls $ getRegister n >>= \(x, ds) -> (map DeclN ds ++) . (x :) <$> liftLambda ns

definitivelyReturns :: [Node] -> Bool
definitivelyReturns [] = False
definitivelyReturns (IfStmnt _ ts es _:ns) = 
    (definitivelyReturns ts && definitivelyReturns es) || definitivelyReturns ns
definitivelyReturns (Return{}:_) = True
definitivelyReturns (_:ns) = definitivelyReturns ns

initIdentLhs :: Lhs -> Lhs
initIdentLhs (LhsAccess acc p pos) = LhsIdentifer id pos where (Identifier id pos) = initIdent $ Access acc p pos
initIdentLhs n = error $ "Only call initIdent with " ++ show n

initIdent (Access id@Identifier{} _ _) = id
initIdent (Access x _ _) = initIdent x
initIdent n = error $ "Only call initIdent with " ++ show n

trimAccess (Access (Access id p pos) _ _) = Access id p pos
trimAccess n = error $ "Only call initIdent with " ++ show n

makeUnionIfNotSame pos a clhs lhs = do
    case a of
        Right a -> join $ (\b m -> 
            case b of
                Left err -> return $ Left err
                Right (AnnotationLiteral "_") -> modifyAnnotationState lhs a
                Right b ->
                    do 
                        x <- getTypeState a pos 
                        case x of 
                            Right a -> 
                                case sameTypesImpl a pos m b a of
                                    Left _ -> f a m (Right b)
                                    Right _ -> return $ Right a
                            Left err -> return $ Left err
            ) <$> clhs <*> getTypeMap 
        Left err -> return $ Left err
    where
        f a m = \case
                Right b -> modifyAnnotationState lhs $ mergedTypeConcrete pos m a b
                Left err -> return $ Left err

modifyWhole :: [Lhs] -> Annotation -> Annotation -> AnnotationState a Annotation
modifyWhole (p:xs) whole@(StructAnnotation ps) given = case Map.lookup p ps of
    Just a -> modifyWhole xs a given >>= \x -> return . StructAnnotation $ Map.insert p x ps
    Nothing -> error $ "You should already know that " ++ show p ++  " is in " ++ show ps ++ " before comming here"
modifyWhole [] _ given = return given

listAccess n = reverse $ go n where
    go (Access n lhs _) = lhs : listAccess n
    go Identifier{} = []

makeImpl a b TypeUnion{} = a
makeImpl a b (NewTypeInstanceAnnotation _ xs) = 
    if isJust $ find isTypeUnion xs then a else b where
    isTypeUnion TypeUnion{} = True
    isTypeUnion _ = False
makeImpl a b _ = b

sameTypesImpl :: Annotation -> SourcePos -> UserDefinedTypes -> Annotation -> Annotation -> Either ErrorType Annotation
sameTypesImpl = makeImpl sameTypesNoUnionSpec sameTypes

matchingUserDefinedType :: P.SourcePos -> TwoSets Annotation -> UserDefinedTypes -> Annotation -> Maybe Annotation
matchingUserDefinedType pos defs usts t = (\(LhsIdentifer id _, _) -> Just $ Annotation id) =<< find (isRight . snd) (Map.mapWithKey (,) $ Map.map (flip (specify pos defs Map.empty usts) t) usts)

evaluateTExpr :: P.SourcePos -> UserDefinedTypes -> TypeDeductionExpr -> State Annotation (Either ErrorType Annotation)
evaluateTExpr pos usts (IsType _ ann) = do
    typ <- get 
    case filterUnion pos usts (\a b -> not $ excludeSameTypes pos usts a b) ann typ of
        Right typ' -> put typ' $> Right typ'
        Left err -> return $ Left err
evaluateTExpr pos usts (NotIsType _ ann) = do
    typ <- get 
    case filterUnion pos usts (excludeSameTypes pos usts) ann typ of
        Right typ' -> put typ' $> Right typ'
        Left err -> return $ Left err
evaluateTExpr pos usts (NegateTypeDeduction tExpr) = do
    typ <- get 
    evaluateTExpr pos usts $ negateDeduction tExpr

evaluateTExprTotal :: P.SourcePos -> UserDefinedTypes -> TypeDeductionExpr -> Annotation -> Either ErrorType Annotation
evaluateTExprTotal pos usts tExpr typLhs = res $> st where (res, st) = runState (evaluateTExpr pos usts tExpr) typLhs

getAssumptionType :: Node -> AnnotationState (Annotations (Finalizeable Annotation)) (Result ErrorType Annotation)
getAssumptionType (DeclN (Decl lhs n a _)) = case a of 
    Just a -> Right <$> insertAnnotation lhs (Finalizeable True a)
    Nothing -> mapRight (getAssumptionType n) (fmap Right . insertAnnotation lhs . Finalizeable False)
getAssumptionType (DeclN (Assign lhs@(LhsAccess access p accPos) expr pos)) = 
    do
        expcd <- getAssumptionType (Access access p accPos)
        rhs <- getTypeStateFrom (getAssumptionType expr) pos
        full <- getTypeStateFrom (getAnnotationState $ initIdentLhs lhs) pos
        mp <- getTypeMap
        case (full, expcd, rhs) of
            (Right whole, Right expcd, Right rhs) ->
                case sameTypesImpl rhs pos mp expcd rhs of
                    Right a -> return $ Right a
                    Left _ -> do
                        x <- modifyAccess mp pos (Access access p accPos) whole expcd rhs p access accPos getAssumptionType
                        case x of
                            Right x -> modifyAnnotationState (initIdentLhs lhs) x
                            Left err -> return $ Left err
            (Left err, _, _) -> return $ Left err
            (_, Left err, _) -> return $ Left err
            (_, _, Left err) -> return $ Left err
getAssumptionType (DeclN (Assign lhs n pos)) = getAssumptionType n >>= \x -> makeUnionIfNotSame pos x (getAnnotationState lhs) lhs
getAssumptionType (DeclN (FunctionDecl lhs ann _)) = Right <$> insertAnnotation lhs (Finalizeable False ann)
getAssumptionType (CreateNewType lhs args pos) = do
    mp <- getTypeMap
    argsn <- sequence <$> mapM getAssumptionType args
    case argsn of
        Right as -> case Map.lookup lhs mp of
            Just ntp@(NewTypeAnnotation id anns _) -> 
                if length anns == length args then 
                    case join $ specify pos <$> Right (fromUnionLists (map (collectGenenrics mp) as, map (collectGenenricsHOF mp) as)) <*> Right Map.empty <*> Right mp <*> Right ntp <*> (NewTypeInstanceAnnotation id <$> argsn) of
                        Right as -> return $ NewTypeInstanceAnnotation id <$> argsn
                        Left err -> return $ Left err
                else return . Left $ CallError anns as pos
            Just a -> return . Left $ UninstantiableType a pos
            Nothing -> return . Left $ NoTypeFound (show lhs) pos
        Left err -> return $ Left err
getAssumptionType (DeclN (OpenFunctionDecl lhs ann _)) = Right <$> insertAnnotation lhs (Finalizeable False ann)
getAssumptionType (DeclN impl@(ImplOpenFunction lhs args (Just ret) ns implft pos)) = do
    a <- getAnnotationState lhs
    mp <- getTypeMap
    case a of
        Left err -> return $ Left err
        Right a@(OpenFunctionAnnotation anns ret' ft impls) -> do
            let b = makeFunAnnotation args ret
            case getSpecificationRules pos (TwoSets (collectGenenrics mp implft) (collectGenenricsHOF mp implft)) Map.empty mp ft implft of
                Right (_, base, _) -> 
                    case getSpecificationRules pos (fromUnionLists (map (collectGenenrics mp) (ret:map snd args), map (collectGenenricsHOF mp) (ret:map snd args))) base mp a b of
                        Left err -> return $ Left err
                        Right (_, res, _) -> 
                                    let 
                                        aeq = Set.fromList $ Map.keys $ Map.filterWithKey (\a b -> isGenericAnnotation a && not (sameTypesBool pos mp a b)) res
                                        beq = Set.fromList $ Map.keys $ Map.filterWithKey (\a b -> isGenericAnnotation a && not (sameTypesBool pos mp a b)) base
                                    in
                                    if Set.size aeq >= Set.size beq then 
                                        modifyAnnotationState lhs (OpenFunctionAnnotation anns ret' ft $ implft:impls)
                                    else return . Left $ UnspecifiableTypeSpecified pos
                Left err -> return $ Left err
        Right a -> return . Left $ UnExtendableType a pos
getAssumptionType (DeclN (ImplOpenFunction lhs args Nothing ns implft pos)) = do
    a <- getAnnotationState lhs
    mp <- getTypeMap
    case a of
        Left err -> return $ Left err
        Right fun@(OpenFunctionAnnotation anns ret' ft impls) -> 
            case getSpecificationRules pos (TwoSets (collectGenenrics mp implft) (collectGenenricsHOF mp implft)) Map.empty mp ft implft of
                Right (_, base, _) -> do
                    let defsNoRet = fromUnionLists (map (collectGenenrics mp . snd) args, map (collectGenenricsHOF mp . snd) args)
                    let (specificationRules, rels) = getPartialNoUnderScoreSpecificationRules pos defsNoRet Map.empty mp fun (FunctionAnnotation (map snd args) (AnnotationLiteral "_"))
                    case substituteVariables pos defsNoRet rels specificationRules mp ret' of
                        Left a -> return . Left $ UnInferrableType (Just a) pos
                        Right inferredRetType ->
                            let spfun = makeFunAnnotation args inferredRetType in
                            case getSpecificationRules pos (fromUnionLists (map (collectGenenrics mp) (inferredRetType:map snd args), map (collectGenenricsHOF mp) (inferredRetType:map snd args))) base mp fun spfun of
                                Left err -> return $ Left err
                                Right (_, res, _) -> 
                                    let 
                                        a = Set.fromList $ Map.keys $ Map.filterWithKey (\a b -> isGenericAnnotation a && not (sameTypesBool pos mp a b)) res
                                        b = Set.fromList $ Map.keys $ Map.filterWithKey (\a b -> isGenericAnnotation a && not (sameTypesBool pos mp a b)) base
                                    in
                                    if Set.size a >= Set.size b then 
                                        modifyAnnotationState lhs (OpenFunctionAnnotation anns ret' ft $ implft:impls)
                                    else return . Left $ UnspecifiableTypeSpecified pos
                Left err -> return $ Left err
        Right a -> return . Left $ UnExtendableType a pos
getAssumptionType (DeclN (Expr n)) = getAssumptionType n
getAssumptionType (Return n pos) = getAssumptionType n >>= \x -> makeUnionIfNotSame pos x (getAnnotationState lhs) lhs
    where lhs = LhsIdentifer "return" pos
getAssumptionType (IfStmnt (TypeDeductionNode lhs tExpr _) ts es pos) = do
    mp <- getTypeMap
    typLhs <- getAnnotationState lhs
    pushScope
    case evaluateTExprTotal pos mp tExpr =<< typLhs of
        Right ann -> do
            insertAnnotation lhs (Finalizeable False ann)
            t <- sequence <$> mapM getAssumptionType ts
            popScope
            pushScope
            case es of
                [] -> return ann
                _ -> do
                    case evaluateTExprTotal pos mp (negateDeduction tExpr) =<< typLhs of
                        Right remAnn -> insertAnnotation lhs $ Finalizeable False remAnn
                        Left _ -> return ann
            e <- sequence <$> mapM getAssumptionType es
            popScope
            let res = case (t, e) of
                    (Right b, Right c) -> Right $ AnnotationLiteral "_"
                    (Left a, _) -> Left a
                    (_, Left a) -> Left a
            return res
        Left err -> return $ Left err
getAssumptionType (IfStmnt cond ts es pos) = do
    (_, (_, mp)) <- get
    c <- consistentTypes cond
    case sameTypes pos mp (AnnotationLiteral "Bool") <$> c of
        Right _ -> do
            pushScope
            t <- sequence <$> mapM getAssumptionType ts
            popScope
            pushScope
            e <- sequence <$> mapM getAssumptionType es
            popScope
            let res = case (c, t, e) of
                    (Right a, Right b, Right c) -> Right $ AnnotationLiteral "_"
                    (Left a, _, _) -> Left a
                    (_, Left a, _) -> Left a
                    (_, _, Left a) -> Left a
            return res
        Left err -> return $ Left err
getAssumptionType (IfExpr c t e pos) =
    (\tx ex mp -> mergedTypeConcrete pos mp <$> tx <*> ex) <$> getAssumptionType t <*> getAssumptionType e <*> getTypeMap
getAssumptionType (FunctionDef args ret body pos) = 
    case ret of
        Just ret -> return . Right $ makeFunAnnotation args ret
        Nothing -> do
            whole_old_ans@(a, ((i, old_ans), mp)) <- get
            let program = Program body
            let ans = (a, ((i, assumeProgramMapping program i (Annotations (Map.fromList $ (LhsIdentifer "return" pos, Finalizeable False $ AnnotationLiteral "_"):map (second (Finalizeable True . rigidizeTypeVariables mp)) args) (Just old_ans)) mp), mp))
            put ans
            mapM_ getAssumptionType body
            (new_ans, _) <- gets snd
            x <- firstInferrableReturn pos body
            case x of
                Right ret -> do
                    typ <- getAnnotationState $ LhsIdentifer "return" pos
                    let ntyp = typ >>= (\c -> 
                            if c then maybe typ Right . matchingUserDefinedType pos emptyTwoSets (Map.filter isStructOrUnionOrFunction mp) =<< typ 
                            else typ
                            ) . isSearchable
                    put whole_old_ans
                    return (makeFunAnnotation args . unrigidizeTypeVariables mp <$> ntyp)
                Left err -> return . Left $ err
    where
        isSearchable Annotation{} = False
        isSearchable AnnotationLiteral{} = False
        isSearchable NewTypeInstanceAnnotation{} = False
        isSearchable NewTypeAnnotation{} = False
        isSearchable OpenFunctionAnnotation{} = False
        isSearchable GenericAnnotation{} = False
        isSearchable _ = True

        isStructOrUnionOrFunction TypeUnion{} = True
        isStructOrUnionOrFunction StructAnnotation{} = True
        isStructOrUnionOrFunction FunctionAnnotation{} = True
        isStructOrUnionOrFunction _ = False
getAssumptionType (Call e args pos) = (\case
                    Right fann@(FunctionAnnotation fargs ret) -> do
                        mp <- getTypeMap
                        anns <- sequence <$> mapM consistentTypes args
                        case anns of
                            Right anns -> let 
                                defs = fromUnionLists (map (collectGenenrics mp) anns, map (collectGenenricsHOF mp) anns)
                                (spec, rel) = getPartialNoUnderScoreSpecificationRules pos defs Map.empty mp fann (FunctionAnnotation anns (AnnotationLiteral "_")) in
                                case substituteVariables pos defs rel spec mp ret of
                                    Right ret' -> case specify pos defs Map.empty mp fann (FunctionAnnotation anns ret') of
                                        Right _ -> return $ Right ret'
                                        Left err -> return $ Left err
                                    Left err -> return $ Left err
                            Left err -> return $ Left err
                    Right opf@(OpenFunctionAnnotation oanns oret ft impls) -> do
                        mp <- getTypeMap
                        anns <- sequence <$> mapM consistentTypes args
                        case anns of
                            Right anns -> let
                                defs = fromUnionLists (map (collectGenenrics mp) anns, map (collectGenenricsHOF mp) anns)
                                (spec, rel) = getPartialNoUnderScoreSpecificationRules pos defs Map.empty mp (FunctionAnnotation oanns oret) (FunctionAnnotation anns (AnnotationLiteral "_")) in
                                case substituteVariables pos defs rel spec mp oret of
                                    Right ret' -> case getSpecificationRules pos defs Map.empty mp (FunctionAnnotation oanns oret) (FunctionAnnotation anns ret') of
                                        Right (_, base, _) -> case Map.lookup ft base of
                                            Just a -> maybe 
                                                    (return . Left $ NoInstanceFound opf a pos) 
                                                    (const . return $ Right ret')
                                                    (find (\b -> specifyTypesBool pos defs base mp b a) impls)
                                            Nothing -> return . Left $ NotOccuringTypeOpenFunction ft pos
                                        Left err -> return $ Left err
                                    Left err -> return $ Left err
                            Left err -> return $ Left err
                    Right ann -> return . Left $ UnCallableType ann pos
                    Left err -> return $ Left err) =<< getTypeStateFrom (getAssumptionType e) pos
getAssumptionType (StructN (Struct ns _)) = 
        (\xs -> mapRight 
            (return . Right $ AnnotationLiteral "_") 
            (const . return $ StructAnnotation <$> sequence xs)) =<< mapM getAssumptionType ns
getAssumptionType (Access st p pos) = do
    mp <- getTypeMap
    f mp =<< getTypeStateFrom (consistentTypes st) pos where 

    f :: UserDefinedTypes -> Either ErrorType Annotation -> AnnotationState (Annotations (Finalizeable Annotation)) (Either ErrorType Annotation)
    f mp = \case
            Right g@(GenericAnnotation _ cns) -> return $ genericHas pos g p cns
            Right g@(RigidAnnotation _ cns) -> return $ genericHas pos g p cns
            Right (TypeUnion st) -> ((\x -> head <$> mapM (sameTypes pos mp (head x)) x) =<<) <$> x where 
                x = sequence <$> mapM (\x -> f mp =<< getTypeState x pos) stl
                stl = Set.toList st
            Right (NewTypeInstanceAnnotation id anns) -> 
                accessNewType anns
                (\(NewTypeAnnotation _ _ ps) -> return $ toEither (FieldNotFound p (AnnotationLiteral $ show ps) pos) (Map.lookup p ps)) 
                (LhsIdentifer id pos)
            Right (StructAnnotation ps) -> return $ toEither (FieldNotFound p (AnnotationLiteral $ show ps) pos) (Map.lookup p ps)
            Right a -> return . Left $ FieldNotFound p a pos
            Left err -> return $ Left err
getAssumptionType (Lit (LitInt _ _)) = return . Right $ AnnotationLiteral "Int"
getAssumptionType (Lit (LitBool _ _)) = return . Right $ AnnotationLiteral "Bool"
getAssumptionType (Lit (LitString _ _)) = return . Right $ AnnotationLiteral "String"
getAssumptionType (Identifier x pos) = do
    ann <- getAnnotationState (LhsIdentifer x pos)
    case ann of
        Right a -> return $ Right a
        Left err  -> return $ Left err
getAssumptionType n = error $ "No arument of the follwoing type expected " ++ show n

genericHas :: SourcePos -> Annotation -> Lhs -> [Constraint] -> Either ErrorType Annotation
genericHas pos g givenLhs [] = Left $ FieldNotFound givenLhs g pos 
genericHas pos g givenLhs ((ConstraintHas lhs (AnnotationConstraint ann)):xs) = if lhs == givenLhs then Right ann else genericHas pos g givenLhs xs

makeAssumptions :: State (Annotation, b) a -> b -> b
makeAssumptions s m = snd $ execState s (AnnotationLiteral "_", m)

assumeProgramMapping :: Program -> Int -> Annotations (Finalizeable Annotation) -> UserDefinedTypes -> Annotations (Finalizeable Annotation)
assumeProgramMapping (Program xs) i anns mp = snd . fst $ makeAssumptions (mapM getAssumptionType $ filter nonDecls xs) ((i, anns), mp)

nonDecls (DeclN Decl{}) = True
nonDecls (DeclN FunctionDecl{}) = True
nonDecls (DeclN Assign{}) = True
nonDecls _ = False

sourcePos = SourcePos "core" (mkPos 0) (mkPos 0)

baseMapping = Map.fromList $ map (second (Finalizeable True)) [
    (LhsIdentifer "add" sourcePos, OpenFunctionAnnotation [GenericAnnotation "a" [], GenericAnnotation "a" []] (GenericAnnotation "a" []) (GenericAnnotation "a" []) [AnnotationLiteral "Int", AnnotationLiteral "String"]),
    (LhsIdentifer "println" sourcePos, FunctionAnnotation [GenericAnnotation "a" []] (GenericAnnotation "a" [])),
    (LhsIdentifer "duplicate" sourcePos, FunctionAnnotation [GenericAnnotation "a" []] (GenericAnnotation "a" [])),
    (LhsIdentifer "write" sourcePos, FunctionAnnotation [GenericAnnotation "a" []] (StructAnnotation Map.empty)),
    (LhsIdentifer "concat" sourcePos, FunctionAnnotation [TypeUnion (Set.fromList [Annotation "Nil",NewTypeInstanceAnnotation "Array" [GenericAnnotation "a" []]]),TypeUnion (Set.fromList [Annotation "Nil",NewTypeInstanceAnnotation "Array" [GenericAnnotation "b" []]])] (TypeUnion (Set.fromList [Annotation "Nil",NewTypeInstanceAnnotation "Array" [TypeUnion (Set.fromList [GenericAnnotation "a" [],GenericAnnotation "b" []])]]))),
    (LhsIdentifer "index" sourcePos, FunctionAnnotation [NewTypeInstanceAnnotation "Array" [GenericAnnotation "a" []],AnnotationLiteral "Int"] (TypeUnion $ Set.fromList [Annotation "Nil", GenericAnnotation "a" []])),
    (LhsIdentifer "sub" sourcePos, OpenFunctionAnnotation [GenericAnnotation "a" [], GenericAnnotation "a" []] (GenericAnnotation "a" []) (GenericAnnotation "a" []) [AnnotationLiteral "Int"]),
    (LhsIdentifer "mod" sourcePos, OpenFunctionAnnotation [GenericAnnotation "a" [], GenericAnnotation "a" []] (GenericAnnotation "a" []) (GenericAnnotation "a" []) [AnnotationLiteral "Int"]),
    (LhsIdentifer "mul" sourcePos, OpenFunctionAnnotation [GenericAnnotation "a" [], GenericAnnotation "a" []] (GenericAnnotation "a" []) (GenericAnnotation "a" []) [AnnotationLiteral "Int"]),
    (LhsIdentifer "div" sourcePos, OpenFunctionAnnotation [GenericAnnotation "a" [], GenericAnnotation "a" []] (GenericAnnotation "a" []) (GenericAnnotation "a" []) [AnnotationLiteral "Int"]),
    (LhsIdentifer "gt" sourcePos, OpenFunctionAnnotation [GenericAnnotation "a" [], GenericAnnotation "a" []] (AnnotationLiteral "Bool") (GenericAnnotation "a" []) [AnnotationLiteral "Int", AnnotationLiteral "String"]),
    (LhsIdentifer "gte" sourcePos, OpenFunctionAnnotation [GenericAnnotation "a" [], GenericAnnotation "a" []] (AnnotationLiteral "Bool") (GenericAnnotation "a" []) [AnnotationLiteral "Int", AnnotationLiteral "String"]),
    (LhsIdentifer "lt" sourcePos, OpenFunctionAnnotation [GenericAnnotation "a" [], GenericAnnotation "a" []] (AnnotationLiteral "Bool") (GenericAnnotation "a" []) [AnnotationLiteral "Int", AnnotationLiteral "String"]),
    (LhsIdentifer "lte" sourcePos, OpenFunctionAnnotation [GenericAnnotation "a" [], GenericAnnotation "a" []] (AnnotationLiteral "Bool") (GenericAnnotation "a" []) [AnnotationLiteral "Int", AnnotationLiteral "String"]),
    (LhsIdentifer "eq" sourcePos, OpenFunctionAnnotation [GenericAnnotation "a" [], GenericAnnotation "a" []] (AnnotationLiteral "Bool") (GenericAnnotation "a" []) [AnnotationLiteral "Int", AnnotationLiteral "Bool", AnnotationLiteral "String"]),
    (LhsIdentifer "neq" sourcePos, OpenFunctionAnnotation [GenericAnnotation "a" [], GenericAnnotation "a" []] (AnnotationLiteral "Bool") (GenericAnnotation "a" []) [AnnotationLiteral "Int", AnnotationLiteral "Bool", AnnotationLiteral "String"]),
    (LhsIdentifer "anded" sourcePos, OpenFunctionAnnotation [GenericAnnotation "a" [], GenericAnnotation "a" []] (AnnotationLiteral "Bool") (GenericAnnotation "a" []) [AnnotationLiteral "Bool"]),
    (LhsIdentifer "ored" sourcePos, OpenFunctionAnnotation [GenericAnnotation "a" [], GenericAnnotation "a" []] (AnnotationLiteral "Bool") (GenericAnnotation "a" []) [AnnotationLiteral "Bool"]),
    (LhsIdentifer "not" sourcePos, FunctionAnnotation [AnnotationLiteral "Bool"] (AnnotationLiteral "Bool")),
    (LhsIdentifer "neg" sourcePos, FunctionAnnotation [AnnotationLiteral "Int"] (AnnotationLiteral "Int"))
    ]

assumeProgram prog i = assumeProgramMapping prog i (Annotations Map.empty (Just $ Annotations baseMapping Nothing))

noTypeFound expected pos = "No type named " ++ expected ++ " found\n" ++ showPos pos
unmatchedType a b pos = "Can't match expected type " ++ show a ++ " with given type " ++ show b ++ "\n" ++ showPos pos

unionFrom :: Annotation -> Annotation -> Either a b -> Annotation
unionFrom a b x = 
    case x of
        Right _ -> b
        Left err -> createUnion a b

mergedTypeConcrete = mergedType (True, False, False, Map.empty) comparisionEither
mergedTypeConcreteEither pos mp a b = Right $ mergedTypeConcrete pos mp a b

mergedType :: (Bool, Bool, Bool, Map.Map String [Constraint]) -> ComparisionReturns ErrorType Annotation -> SourcePos -> UserDefinedTypes -> Annotation -> Annotation -> Annotation
mergedType gs crt pos mp a b = simplify $ go gs crt pos mp a b where

    simplify :: Annotation -> Annotation
    simplify (TypeUnion ts) = TypeUnion . Set.fromList . map (foldr1 (mergedType gs crt pos mp)) . groupBy2 $ Set.toList ts where
        groupBy2 :: [Annotation] -> [[Annotation]]
        groupBy2 = go [] where
            go acc [] = acc
            go acc (h:t) =
                let (hs, nohs) = partition (hasSameFunctor h) t
                in go ((h:hs):acc) nohs
        hasSameFunctor (NewTypeInstanceAnnotation id1 _) (NewTypeInstanceAnnotation id2 _) = id1 == id2
        hasSameFunctor a b = sameTypesBool pos mp a b
    simplify a = a

    go :: (Bool, Bool, Bool, Map.Map String [Constraint]) -> ComparisionReturns ErrorType Annotation -> SourcePos -> UserDefinedTypes -> Annotation -> Annotation -> Annotation
    go _ crt pos _ a@AnnotationLiteral{} b@AnnotationLiteral{} = 
        if a == b then a else createUnion a b
    go gs crt pos mp a@(FunctionAnnotation as ret1) b@(FunctionAnnotation bs ret2) = 
        if length as == length bs then FunctionAnnotation (init ls) (last ls)
        else createUnion a b
        where ls = zipWith (mergedType gs crt pos mp) (as ++ [ret1]) (bs ++ [ret2])
    go gs crt pos mp a@(NewTypeAnnotation id1 anns1 _) b@(NewTypeInstanceAnnotation id2 anns2) 
        | id1 /= id2 = createUnion a b
        | otherwise = mergedType gs crt pos mp (NewTypeInstanceAnnotation id1 anns1) b
    go gs crt pos mp a@(NewTypeInstanceAnnotation e1 as1) b@(NewTypeInstanceAnnotation e2 as2)
        | e1 == e2 && length as1 == length as2 = NewTypeInstanceAnnotation e1 ls
        | e1 == e2 && length as1 < length as2 = case flip (mergedType gs crt pos mp) b <$> fullAnotationFromInstanceFree pos mp a of
            Right a -> a
            Left  _ -> createUnion a b
        | otherwise = createUnion a b
        where ls = zipWith (mergedType gs crt pos mp) as1 as2
    go gs crt pos mp a@(StructAnnotation ps1) b@(StructAnnotation ps2)
        | Map.empty == ps1 || Map.empty == ps2 = if ps1 == ps2 then a else createUnion a b
        | Map.size ps1 /= Map.size ps2 = createUnion a b
        | isJust $ sequence ls = maybe (createUnion a b) StructAnnotation (sequence ls)
        | otherwise = createUnion a b
        where
            ls = Map.mapWithKey (f ps1) ps2
            f ps2 k v1 = 
                case Map.lookup k ps2 of
                    Just v2
                        -> case sameTypesGenericCrt gs crt pos mp v1 v2 of
                            Right a -> Just a
                            Left err -> Nothing
                    Nothing -> Nothing
    go gs crt pos mp a@(TypeUnion as) b@(TypeUnion bs) = do
        case mapM_ (f mp $ Set.toList as) (Set.toList bs) of
            Right () -> foldr1 (mergedType gs crt pos mp) (Set.toList bs)
            Left _ -> case createUnion a b of
                TypeUnion xs -> foldr1 (mergedType gs crt pos mp) $ Set.toList $ Set.map (mergeUnions xs) xs
                a -> a
        where
            mergeUnions xs a = foldr1 (mergedType gs crt pos mp) $ filter (predicate a) nxs where nxs = Set.toList xs
            predicate a b = isRight (sameTypesGenericCrt gs crt pos mp a b) || isRight (sameTypesGenericCrt gs crt pos mp b a)
            f mp ps2 v1 = join $ getFirst a b pos $ map (\x -> success crt <$> sameTypesGenericCrt gs crt pos mp x v1) ps2
    go gs crt pos mp a@(TypeUnion st) b = 
        case fromJust $ getFirst a b pos $ map (\x -> Just $ sameTypesGenericCrt gs crt pos mp x b) $ Set.toList st of
            Right _ -> a
            Left _ -> createUnion a b
    go gs crt pos mp a b@(TypeUnion st) = mergedType gs crt pos mp b a
    go gs crt pos mp (Annotation id1) b@(Annotation id2)
        | id1 == id2 = b
        | otherwise = case Map.lookup (LhsIdentifer id1 pos) mp of
            Just a -> case Map.lookup (LhsIdentifer id2 pos) mp of
                Just b -> unionFrom a b $ sameTypesGenericCrt gs crt pos mp a b
    go gs crt pos mp (Annotation id) b = 
        case Map.lookup (LhsIdentifer id pos) mp of
            Just a -> unionFrom a b $ sameTypesGenericCrt gs crt pos mp a b
    go gs crt pos mp b (Annotation id) = 
        case Map.lookup (LhsIdentifer id pos) mp of
            Just a -> unionFrom a b $ sameTypesGenericCrt gs crt pos mp a b
    go tgs@(_, sensitive, _, gs) crt pos mp a@(GenericAnnotation id1 cs1) b@(GenericAnnotation id2 cs2)
        | sensitive && id1 `Map.member` gs && id2 `Map.member` gs && id1 /= id2 = createUnion a b
        | otherwise = if id1 == id2 then unionFrom a b $ zipWithM (matchConstraint tgs crt pos mp) cs1 cs2 *> success crt a else createUnion a b
    go tgs@(_, sensitive, _, gs) crt pos mp a@(GenericAnnotation _ acs) b = 
        if sensitive then 
            unionFrom a b $ mapM (matchConstraint tgs crt pos mp (AnnotationConstraint b)) acs
        else createUnion a b
    go tgs@(_, sensitive, _, gs) crt pos mp b a@(GenericAnnotation _ acs) = 
        if sensitive then 
            unionFrom a b $ mapM (matchConstraint tgs crt pos mp (AnnotationConstraint b)) acs *> success crt a
        else createUnion a b
    go (considerUnions, sensitive, leftGeneral, gs) crt pos mp ft@(OpenFunctionAnnotation anns1 ret1 forType impls) (OpenFunctionAnnotation anns2 ret2 _ _) =
        OpenFunctionAnnotation (init ls) (last ls) forType impls where 
            ls = zipWith (mergedType (considerUnions, sensitive, leftGeneral, gs') crt pos mp) (anns1 ++ [ret1]) (anns2 ++ [ret2])
            gs' = genericsFromList (anns1 ++ [ret1]) `Map.union` gs 
    go (considerUnions, sensitive, leftGeneral, gs) crt pos mp a@(OpenFunctionAnnotation anns1 ret1 _ _) (FunctionAnnotation args ret2) = 
        FunctionAnnotation (init ls) (last ls) where
            ls = zipWith (mergedType (considerUnions, sensitive, leftGeneral, gs') crt pos mp) (anns1 ++ [ret1]) (args ++ [ret2])
            gs' = genericsFromList (anns1 ++ [ret1]) `Map.union` gs
    go gs crt pos mp a@(RigidAnnotation id1 _) b@(RigidAnnotation id2 _) 
        | id1 == id2 = a
        | otherwise = createUnion a b
    go _ crt pos _ a b = createUnion a b

sameTypesGenericCrt :: (Bool, Bool, Bool, Map.Map String [Constraint]) -> ComparisionReturns ErrorType Annotation -> P.SourcePos -> UserDefinedTypes -> Annotation -> Annotation -> Either ErrorType Annotation
sameTypesGenericCrt _ crt pos _ a@AnnotationLiteral{} b@AnnotationLiteral{} = 
    if a == b then success crt a else failout crt a b pos
sameTypesGenericCrt gs crt pos mp a@(FunctionAnnotation as ret1) b@(FunctionAnnotation bs ret2) = 
    if length as == length bs then (\xs -> FunctionAnnotation (init xs) (last xs)) <$> ls
    else failout crt a b pos
    where ls = zipWithM (sameTypesGenericCrt gs crt pos mp) (as ++ [ret1]) (bs ++ [ret2])
sameTypesGenericCrt (_, gs, leftGeneral, cns) crt pos mp a@(NewTypeAnnotation id1 anns1 _) b@(NewTypeInstanceAnnotation id2 anns2) 
    | id1 /= id2 = Left $ UnmatchedType a b pos
    | otherwise = sameTypesGenericCrt (True, gs, leftGeneral, cns) crt pos mp (NewTypeInstanceAnnotation id1 anns1) b
sameTypesGenericCrt (_, gs, leftGeneral, cns) crt pos mp a@(NewTypeInstanceAnnotation id1 anns1) b@(NewTypeAnnotation id2 anns2 _)
    | id1 /= id2 = Left $ UnmatchedType a b pos
    | leftGeneral = sameTypesGenericCrt (True, gs, leftGeneral, cns) crt pos mp b (NewTypeInstanceAnnotation id1 anns1)
    | otherwise = Left $ UnmatchedType a b pos
sameTypesGenericCrt gs@(_, _, leftGeneral, _) crt pos mp a@(NewTypeInstanceAnnotation e1 as1) b@(NewTypeInstanceAnnotation e2 as2)
    | e1 == e2 && length as1 == length as2 = NewTypeInstanceAnnotation e1 <$> ls
    | e1 == e2 && length as1 < length as2 && isGeneralizedInstanceFree pos a mp = flip (sameTypesGenericCrt gs crt pos mp) b =<< fullAnotationFromInstanceFree pos mp a
    | e1 == e2 && length as1 > length as2 && isGeneralizedInstanceFree pos b mp && leftGeneral = sameTypesGenericCrt gs crt pos mp a =<< fullAnotationFromInstanceFree pos mp b
    | otherwise = failout crt a b pos 
    where ls = zipWithM (sameTypesGenericCrt gs crt pos mp) as1 as2
sameTypesGenericCrt gs crt pos mp a@(StructAnnotation ps1) b@(StructAnnotation ps2)
    | Map.empty == ps1 || Map.empty == ps2 = if ps1 == ps2 then success crt a else failout crt a b pos
    | Map.size ps1 /= Map.size ps2 = failout crt a b pos
    | isJust $ sequence ls = maybe (failout crt a b pos) (success crt) (StructAnnotation <$> sequence ls)
    | otherwise = failout crt a b pos
    where
        ls = Map.mapWithKey (f ps1) ps2
        f ps2 k v1 = 
            case Map.lookup k ps2 of
                Just v2
                    -> case sameTypesGenericCrt gs crt pos mp v1 v2 of
                        Right a -> Just a
                        Left err -> Nothing
                Nothing -> Nothing
sameTypesGenericCrt gs crt pos mp a@(TypeUnion as) b@(TypeUnion bs) = do
    case mapM (f mp $ Set.toList as) (Set.toList bs) of
        Right s -> success crt $ TypeUnion $ Set.fromList s
        Left err -> failiure crt err
    where
        f mp ps2 v1 = fromJust $ getFirst a b pos $ map (\x -> Just $ sameTypesGenericCrt gs crt pos mp x v1) ps2
sameTypesGenericCrt tgs@(considerUnions, _, _, _) crt pos mp a@(TypeUnion st) b
    | considerUnions =
        fromJust $ getFirst a b pos $ map (\x -> Just $ sameTypesGenericCrt tgs crt pos mp x b) $ Set.toList st
    | otherwise = Left $ UnmatchedType a b pos
sameTypesGenericCrt tgs@(considerUnions, _, _, _) crt pos mp b a@(TypeUnion st) = Left $ UnmatchedType a b pos
sameTypesGenericCrt gs crt pos mp (Annotation id1) b@(Annotation id2)
    | id1 == id2 = success crt b
    | otherwise = case Map.lookup (LhsIdentifer id1 pos) mp of
        Just a -> case Map.lookup (LhsIdentifer id2 pos) mp of
            Just b -> sameTypesGenericCrt gs crt pos mp a b
            Nothing -> failiure crt $ NoTypeFound id2 pos
        Nothing -> failiure crt $ NoTypeFound id1 pos
sameTypesGenericCrt gs crt pos mp (Annotation id) b = 
    case Map.lookup (LhsIdentifer id pos) mp of
        Just a -> sameTypesGenericCrt gs crt pos mp a b
        Nothing -> failiure crt $ NoTypeFound id pos
sameTypesGenericCrt gs crt pos mp b (Annotation id) = 
    case Map.lookup (LhsIdentifer id pos) mp of
        Just a -> sameTypesGenericCrt gs crt pos mp a b
        Nothing -> failiure crt $ NoTypeFound id pos
sameTypesGenericCrt tgs@(_, sensitive, _, gs) crt pos mp a@(GenericAnnotation id1 cs1) b@(GenericAnnotation id2 cs2)
    | sensitive && id1 `Map.member` gs && id2 `Map.member` gs && id1 /= id2 = Left $ UnmatchedType a b pos
    | otherwise = if id1 == id2 then zipWithM (matchConstraint tgs crt pos mp) cs1 cs2 *> success crt a else failout crt a b pos
sameTypesGenericCrt gs crt pos mp a@(GenericAnnotation id1 cs1) b@(RigidAnnotation id2 cs2) = sameTypesGenericCrt gs crt pos mp (RigidAnnotation id1 cs1) (RigidAnnotation id2 cs2) $> b
sameTypesGenericCrt gs crt pos mp a@(RigidAnnotation id1 cs1) b@(GenericAnnotation id2 cs2) = sameTypesGenericCrt gs crt pos mp (RigidAnnotation id1 cs1) (RigidAnnotation id2 cs2) $> b
sameTypesGenericCrt tgs@(_, sensitive, _, gs) crt pos mp a@(RigidAnnotation id1 cs1) b@(RigidAnnotation id2 cs2)
    | id1 == id2 = zipWithM (matchConstraint tgs crt pos mp) cs1 cs2 *> success crt a 
    | otherwise = failout crt a b pos
sameTypesGenericCrt tgs@(_, sensitive, _, gs) crt pos mp a@(GenericAnnotation _ acs) b = 
    if sensitive then 
        mapM (matchConstraint tgs crt pos mp (AnnotationConstraint b)) acs *> success crt b
    else Left $ UnmatchedType a b pos
sameTypesGenericCrt tgs@(_, sensitive, _, gs) crt pos mp b a@(GenericAnnotation _ acs) = 
    if sensitive then 
        mapM (matchConstraint tgs crt pos mp (AnnotationConstraint b)) acs *> success crt a
    else Left $ UnmatchedType a b pos
sameTypesGenericCrt (considerUnions, sensitive, leftGeneral, gs) crt pos mp ft@(OpenFunctionAnnotation anns1 ret1 forType impls) (OpenFunctionAnnotation anns2 ret2 _ _) =
    (\xs -> OpenFunctionAnnotation (init xs) (last xs) forType impls) <$> ls where 
        ls = zipWithM (sameTypesGenericCrt (considerUnions, sensitive, leftGeneral, gs') crt pos mp) (anns1 ++ [ret1]) (anns2 ++ [ret2])
        gs' = genericsFromList (anns1 ++ [ret1]) `Map.union` gs 
sameTypesGenericCrt (considerUnions, sensitive, leftGeneral, gs) crt pos mp a@(OpenFunctionAnnotation anns1 ret1 _ _) (FunctionAnnotation args ret2) = 
    (\xs -> FunctionAnnotation (init xs) (last xs)) <$> ls where
        ls = zipWithM (sameTypesGenericCrt (considerUnions, sensitive, leftGeneral, gs') crt pos mp) (anns1 ++ [ret1]) (args ++ [ret2])
        gs' = genericsFromList (anns1 ++ [ret1]) `Map.union` gs
sameTypesGenericCrt _ crt pos _ a b = failout crt a b pos

genericsFromList :: [Annotation] -> Map.Map String [Constraint]
genericsFromList anns = foldr1 Map.union (map getGenerics anns)

matchConstraint :: (Bool, Bool, Bool, Map.Map String [Constraint]) -> ComparisionReturns ErrorType Annotation -> SourcePos -> UserDefinedTypes -> Constraint -> Constraint -> Either ErrorType Constraint
matchConstraint gs crt pos mp c@(AnnotationConstraint a) (AnnotationConstraint b) = c <$ sameTypesGenericCrt gs crt pos mp a b
matchConstraint gs crt pos mp a@(ConstraintHas lhs cns) b@(AnnotationConstraint ann) = 
    case ann of
        StructAnnotation ds -> 
            if lhs `Map.member` ds then Right b
            else Left $ UnmatchedConstraint a b pos
        _ -> Left $ UnmatchedConstraint a b pos
matchConstraint gs crt pos mp c@(ConstraintHas a c1) d@(ConstraintHas b c2) = 
    if a /= b then Left $ UnmatchedConstraint c d pos
    else c <$ matchConstraint gs crt pos mp c1 c2
matchConstraint gs crt pos mp a@(AnnotationConstraint ann) b@(ConstraintHas lhs cns) = matchConstraint gs crt pos mp b a

getGenerics :: Annotation -> Map.Map String [Constraint]
getGenerics (GenericAnnotation id cons) = Map.singleton id cons
getGenerics (OpenFunctionAnnotation anns ret _ _) = foldr1 Map.union (map getGenerics $ ret:anns)
getGenerics _ = Map.empty

comparisionEither :: ComparisionReturns ErrorType Annotation
comparisionEither = ComparisionReturns {
    success = Right,
    failiure = Left,
    failout = \a b pos -> Left $ UnmatchedType a b pos
}

unionEither :: ComparisionReturns String Annotation
unionEither = ComparisionReturns {
    success = Right,
    failiure = Left,
    failout = \a b _ -> Right $ createUnion a b
}

createUnion a b = go a b where
    go (TypeUnion s1) (TypeUnion s2) = TypeUnion $ s1 `Set.union` s2
    go (TypeUnion s1) a = TypeUnion $ a `Set.insert` s1
    go a (TypeUnion s1) = TypeUnion $ a `Set.insert` s1
    go a b = TypeUnion $ Set.fromList [a, b]

sameTypesGeneric a = sameTypesGenericCrt a comparisionEither

sameTypes :: SourcePos -> UserDefinedTypes -> Annotation -> Annotation -> Either ErrorType Annotation
sameTypes = sameTypesGeneric (True, False, False, Map.empty)

getTypeMap :: State (a, (b, c)) c
getTypeMap = gets (snd . snd)

findFromUserDefinedTypes pos id usts = case Map.lookup (LhsIdentifer id pos) usts of
    Just x -> Right x
    Nothing -> Left $ NoTypeFound id pos

filterUnion :: SourcePos
    -> UserDefinedTypes
    -> (Annotation -> Annotation -> Bool)
    -> Annotation
    -> Annotation
    -> Either ErrorType Annotation
filterUnion pos usts f _a _b = 
    let 
        a = case _a of
            Annotation id -> case findFromUserDefinedTypes pos id usts of 
                Right x -> x
                Left _ -> _a
            _ -> _a
        b = case _b of
            Annotation id -> case findFromUserDefinedTypes pos id usts of 
                Right x -> x
                Left _ -> _b
            _ -> _b
    in case b of
        TypeUnion{} -> go pos usts f a b 
        NewTypeInstanceAnnotation{} -> go pos usts f a b
        _ -> if f a b then Left $ UnmatchedType a b pos else Right a
    where
        go :: SourcePos -> UserDefinedTypes -> (Annotation -> Annotation -> Bool) -> Annotation -> Annotation -> Either ErrorType Annotation
        go pos usts f a (TypeUnion ts) =
            if Set.size ts == 1 then go pos usts f a $ Set.elemAt 0 ts else do
                let
                    (unions, simples) = partition isUnion . Set.toList . Set.map snd . Set.filter pred $ Set.map (\b -> (f a b, b)) ts 
                    unions' = map snd $ filter (isLeft . fst) $ map (\x -> (go pos usts f a x, x)) unions in
                    let xs = Set.fromList $ unions' ++ simples in
                    if Set.null xs then 
                        Left $ UnmatchablePredicates a pos
                    else Right $ foldr1 (mergedTypeConcrete pos usts) xs
            where 
                pred (b, v) = (isUnion v && b) || not b
                isUnion = makeImpl True False
        go pos usts f a@(NewTypeInstanceAnnotation id1 anns1) b@(NewTypeInstanceAnnotation id2 anns2)
            | id1 /= id2 = Left $ expectedUnion pos a b
            | otherwise =
                case zipWithM (go pos usts f) anns1 anns2 of
                    Right xs -> Right $ NewTypeInstanceAnnotation id1 xs
                    Left err -> Left err
        go pos usts f a b = if f a b then Right a else Left $ UnmatchedType a b pos

excludeSameTypes pos usts a b = any isRight xs where
    xs = [sameTypes pos usts b a $> b, sameTypes pos usts a b $> b, (fst <$> specify pos (TwoSets (collectGenenrics usts a) (collectGenenrics usts a)) Map.empty usts a b) $> b]

accessNewType givenArgs f fid@(LhsIdentifer id pos) =
    (\case
        Right x -> f x
        Left err -> return . Left $ err) =<< getFullAnnotation fid givenArgs
accessNewType _ _ _ = error "Only unions allowed"

fullAnotationFromInstance pos (NewTypeInstanceAnnotation id args) = getFullAnnotation (LhsIdentifer id pos) args
fullAnotationFromInstance a b = error $ "Unexpected argments for isGeneralizedInstance [" ++ show a ++ ", " ++ show b ++ "]"

fullAnotationFromInstanceFree pos mp (NewTypeInstanceAnnotation id givenArgs) = 
    case Map.lookup fid mp of
        Just x@(NewTypeAnnotation id args map) -> 
            substituteVariablesOptFilter False pos (f mp) Map.empty (Map.fromList $ zip args givenArgs) mp x
        Just a -> Left $ NoTypeFound id pos
        Nothing -> Left $ NoTypeFound id pos
    where 
        f mp = fromUnionLists (map (collectGenenrics mp) givenArgs, map (collectGenenricsHOF mp) givenArgs)
        fid = LhsIdentifer id pos
fullAnotationFromInstanceFree a b c = error $ "Unexpected argments for isGeneralizedInstance [" ++ show a ++ ", " ++ show b ++ ", " ++ show c ++ "]"

getFullAnnotation fid@(LhsIdentifer id pos) givenArgs = do
    mp <- getTypeMap
    case Map.lookup fid mp of
        Just x@(NewTypeAnnotation id args map) -> 
            return $ substituteVariablesOptFilter False pos (f mp) Map.empty (Map.fromList $ zip args givenArgs) mp x
        Just a -> return . Left $ NoTypeFound id pos
        Nothing -> return . Left $ NoTypeFound id pos
    where f mp = fromUnionLists (map (collectGenenrics mp) givenArgs, map (collectGenenricsHOF mp) givenArgs)
getFullAnnotation a b = error $ "Unexpected argments for getFullAnnotation [" ++ show a ++ ", " ++ show b ++ "]"

modifyAccess mp pos acc whole expected given prop access accPos f = case whole of
    g@(GenericAnnotation _ cns) -> return $ genericHas pos g prop cns
    g@(RigidAnnotation _ cns) -> return $ genericHas pos g prop cns
    TypeUnion{} -> f (Access access prop accPos) >>= \res -> return $ sameTypes pos mp given =<< res
    NewTypeInstanceAnnotation{} -> f (Access access prop accPos) >>= \res -> return $ sameTypes pos mp given =<< res
    StructAnnotation ps -> case sameTypesImpl given pos mp expected given of 
        Right a -> return $ Right a
        Left err -> Right <$> modifyWhole (listAccess acc) whole (mergedTypeConcrete pos mp expected given)
    a -> return . Left $ FieldNotFound prop a pos 

consistentTypesPass :: ConsistencyPass -> Node -> AnnotationState (Annotations (Finalizeable Annotation)) (Either ErrorType Annotation)
consistentTypesPass VerifyAssumptions (DeclN (Decl lhs rhs _ pos)) = (\a b m -> mergedTypeConcrete pos m <$> a <*> b)
    <$> getAnnotationState lhs <*> consistentTypesPass VerifyAssumptions rhs <*> getTypeMap
consistentTypesPass RefineAssumtpions (DeclN (Decl lhs rhs _ pos)) = consistentTypesPass RefineAssumtpions rhs >>= \x -> makeUnionIfNotSame pos x (getAnnotationState lhs) lhs
consistentTypesPass VerifyAssumptions (DeclN (Assign (LhsAccess access prop accPos) rhs pos)) = (\a b m -> join $ sameTypes pos m <$> a <*> b)
    <$> getAssumptionType (Access access prop accPos) <*> consistentTypesPass VerifyAssumptions rhs <*> getTypeMap
consistentTypesPass RefineAssumtpions (DeclN (Assign lhs@(LhsAccess access prop accPos) rhs pos)) =
    do
        expcd <- consistentTypesPass RefineAssumtpions (Access access prop accPos)
        rhs <- getTypeStateFrom (consistentTypesPass RefineAssumtpions rhs) pos
        full <- getTypeStateFrom (getAnnotationState $ initIdentLhs lhs) pos
        mp <- getTypeMap
        case (full, expcd, rhs) of
            (Right whole, Right expcd, Right rhs) ->
                case sameTypesImpl rhs pos mp expcd rhs of
                    Right a -> return $ Right a
                    Left _ -> do
                        x <- modifyAccess mp pos (Access access prop accPos) whole expcd rhs prop access accPos (consistentTypesPass RefineAssumtpions)
                        case x of
                            Right x -> modifyAnnotationState (initIdentLhs lhs) x
                            Left err -> return $ Left err
            (Left err, _, _) -> return $ Left err
            (_, Left err, _) -> return $ Left err
            (_, _, Left err) -> return $ Left err
consistentTypesPass VerifyAssumptions (DeclN (Assign lhs rhs pos)) = (\a b m -> mergedTypeConcrete pos m <$> a <*> b) 
    <$> getAnnotationState lhs <*> consistentTypesPass VerifyAssumptions rhs <*> getTypeMap
consistentTypesPass RefineAssumtpions (DeclN (Assign lhs rhs pos)) = getAssumptionType rhs >>= \x -> makeUnionIfNotSame pos x (getAnnotationState lhs) lhs
consistentTypesPass p (DeclN (FunctionDecl lhs ann pos)) = do
    m <- getTypeMap
    l <- getAnnotationState lhs
    case l of
        Right l -> if p == VerifyAssumptions then return $ sameTypes pos m ann l else makeUnionIfNotSame pos (Right ann) (getAnnotationState lhs) lhs
        Left err -> return $ Left err
consistentTypesPass p (DeclN (ImplOpenFunction lhs args (Just ret) exprs _ pos)) = consistentTypesPass p $ FunctionDef args (Just ret) exprs pos
consistentTypesPass p (DeclN (ImplOpenFunction lhs args Nothing exprs implft pos)) = do
    a <- getAnnotationState lhs
    mp <- getTypeMap
    case a of
        Left err -> return $ Left err
        Right fun@(OpenFunctionAnnotation anns ret' ft impls) -> do
            let defs = fromUnionLists (map (collectGenenrics mp . snd) args, map (collectGenenricsHOF mp . snd) args)
            let (specificationRules, rels) = getPartialNoUnderScoreSpecificationRules pos defs Map.empty mp fun (FunctionAnnotation (map snd args) (AnnotationLiteral "_"))
            case substituteVariables pos defs rels specificationRules mp ret' of
                Left err -> return . Left $ UnInferrableType (Just err) pos
                Right inferredRetType ->
                    case specify pos defs Map.empty mp fun (makeFunAnnotation args inferredRetType) of
                        Left err -> return $ Left err
                        Right (ann, defs) -> consistentTypesPass p $ FunctionDef args (Just inferredRetType) exprs pos
        Right a -> return . Left $ UnExtendableType a pos
consistentTypesPass p (DeclN (OpenFunctionDecl lhs ann pos)) =  do
    m <- getTypeMap
    l <- getAnnotationState lhs
    case l of
        Right l -> if p == VerifyAssumptions then return $ sameTypes pos m ann l else makeUnionIfNotSame pos (Right ann) (getAnnotationState lhs) lhs
        Left err -> return $ Left err
consistentTypesPass p (IfExpr cond t e pos) = do
    m <- getTypeMap
    c <- consistentTypesPass p cond
    case c >>= \x -> sameTypes pos m x (AnnotationLiteral "Bool") of
        Right _ -> (\a b -> mergedTypeConcrete pos m <$> a <*> b) <$> consistentTypesPass p t <*> consistentTypesPass p e
        Left err -> return $ Left err
consistentTypesPass p (CreateNewType lhs@(LhsIdentifer id _) args pos) = do
    mp <- getTypeMap
    argsn <- sequence <$> mapM (consistentTypesPass p) args
    case argsn of
        Right as -> case Map.lookup lhs mp of
            Just ntp@(NewTypeAnnotation id anns _) -> 
                if length args == length anns then
                case specify pos <$> Right (fromUnionLists (map (collectGenenrics mp) as, map (collectGenenricsHOF mp) as)) <*> Right Map.empty <*> Right mp <*> Right ntp <*> (NewTypeInstanceAnnotation id <$> argsn) of
                    Right _ -> return $ NewTypeInstanceAnnotation id <$> argsn
                    Left err -> return $ Left err
                else return . Left $ CallError anns as pos
            Just a -> return . Left $ UninstantiableType a pos
            Nothing -> return . Left $ NoTypeFound id pos
        Left err -> return $ Left err
consistentTypesPass p (DeclN (Expr n)) = consistentTypesPass p n
consistentTypesPass p (IfStmnt (TypeDeductionNode lhs tExpr _) ts es pos) = do
    (_, (_, mp)) <- get
    pushScope
    typLhs <- getAnnotationState lhs
    case typLhs of
        Right t -> res t
        _ -> return . Left $ expectedUnion pos lhs typLhs
    where res t = do
            usts <- getTypeMap
            case evaluateTExprTotal pos usts tExpr t of
                Left err -> return $ Left err
                Right ann' -> do
                    insertAnnotation lhs $ Finalizeable False ann'
                    mapM_ getAssumptionType ts
                    t' <- if p == RefineAssumtpions then return . Right $ [AnnotationLiteral "_"] else sequence <$> mapM (consistentTypesPass RefineAssumtpions) ts
                    ts' <- sequence <$> mapM (consistentTypesPass p) ts
                    popScope
                    pushScope
                    case es of
                        [] -> popScope $> (ts' *> Right (AnnotationLiteral "_"))
                        _ -> 
                            case evaluateTExprTotal pos usts (negateDeduction tExpr) t of
                                Right ann' -> do
                                    insertAnnotation lhs $ Finalizeable False ann'
                                    mapM_ getAssumptionType es
                                    e' <- if p == RefineAssumtpions then return . Right $ [AnnotationLiteral "_"] else sequence <$> mapM (consistentTypesPass RefineAssumtpions) es
                                    e <- sequence <$> mapM (consistentTypesPass p) es
                                    popScope
                                    let res = case (ts', t', e, e') of
                                            (Right _, Right _, Right _, Right _) -> Right $ AnnotationLiteral "_"
                                            (Left a, _, _, _) -> Left a
                                            (_, Left a, _, _) -> Left a
                                            (_, _, Left a, _) -> Left a
                                            (_, _, _, Left a) -> Left a
                                    return res
                                Left err -> return $ Left err
consistentTypesPass p (IfStmnt cond ts es pos) = do
    (_, (_, mp)) <- get
    c <- consistentTypesPass p cond
    case sameTypes pos mp (AnnotationLiteral "Bool") <$> c of
        Right _ -> do
            c <- consistentTypesPass p cond
            pushScope
            mapM_ getAssumptionType ts
            t' <- if p == RefineAssumtpions then return . Right $ [AnnotationLiteral "_"] else sequence <$> mapM (consistentTypesPass RefineAssumtpions) ts
            t <- sequence <$> mapM (consistentTypesPass p) ts
            popScope
            pushScope
            mapM_ getAssumptionType es
            e' <- if p == RefineAssumtpions then return . Right $ [AnnotationLiteral "_"] else sequence <$> mapM (consistentTypesPass RefineAssumtpions) es
            e <- sequence <$> mapM (consistentTypesPass p) es
            popScope
            let res = case (c, t, e, e', t') of
                    (Right a, Right b, Right c, Right e', Right t') -> Right $ AnnotationLiteral "_"
                    (Left a, _, _, _, _) -> Left a
                    (_, Left a, _, _, _) -> Left a
                    (_, _, Left a, _, _) -> Left a
                    (_, _, _, Left a, _) -> Left a
                    (_, _, _, _, Left a) -> Left a
            return res
        Left err -> return $ Left err
consistentTypesPass p (StructN (Struct ns _)) = (\case
    Right a -> return . Right $ StructAnnotation a
    Left err -> return $ Left err) . sequence =<< mapM (consistentTypesPass p) ns
consistentTypesPass pass (Access st p pos) = do
    mp <- getTypeMap
    f mp =<< getTypeStateFrom (consistentTypesPass pass st) pos where 

    f :: UserDefinedTypes -> Either ErrorType Annotation -> AnnotationState (Annotations (Finalizeable Annotation)) (Either ErrorType Annotation)
    f mp = \case
            Right g@(GenericAnnotation _ cns) -> return $ genericHas pos g p cns
            Right g@(RigidAnnotation _ cns) -> return $ genericHas pos g p cns
            Right (TypeUnion st) -> ((\x -> head <$> mapM (sameTypes pos mp (head x)) x) =<<) <$> x where 
                x = sequence <$> mapM (\x -> f mp =<< getTypeState x pos) stl
                stl = Set.toList st
            Right (NewTypeInstanceAnnotation id anns) -> 
                accessNewType anns
                (\(NewTypeAnnotation _ _ ps) -> return $ toEither (FieldNotFound p (AnnotationLiteral $ show ps) pos) (Map.lookup p ps))  
                (LhsIdentifer id pos)
            Right (StructAnnotation ps) -> return $ toEither (FieldNotFound p (AnnotationLiteral $ show ps) pos) (Map.lookup p ps)
            Right a -> return . Left $ UnsearchableType p a pos
            Left err -> return $ Left err
consistentTypesPass p (FunctionDef args ret body pos) = 
    if definitivelyReturns body then
        case ret of
            Just ret -> do
                scope <- get
                finalizeAnnotationState
                (a, ((i, ans), mp)) <- get
                mp <- getTypeMap
                let program = Program body
                let ans' = (a, ((i, assumeProgramMapping program i (Annotations (Map.fromList $ (LhsIdentifer "return" pos, Finalizeable True $ rigidizeTypeVariables mp ret):map (second (Finalizeable True . rigidizeTypeVariables mp)) args) (Just ans)) mp), mp))
                put ans'
                xs <- sequence <$> mapM (consistentTypesPass p) body
                s <- getAnnotationState (LhsIdentifer "return" pos)
                put scope
                case s of
                    Right ret' -> case xs of
                        Right _ -> return (sameTypes pos mp (makeFunAnnotation args $ unrigidizeTypeVariables mp ret) (makeFunAnnotation args $ unrigidizeTypeVariables mp ret'))
                        Left err -> return . Left $ err
                    Left err -> return $ Left err
            Nothing -> do
                scope <- get
                finalizeAnnotationState
                (a, ((i, old_ans), mp)) <- get
                let program = Program body
                let ans = (a, ((i, assumeProgramMapping program i (Annotations (Map.fromList $ (LhsIdentifer "return" pos, Finalizeable False $ AnnotationLiteral "_"):map (second (Finalizeable True . rigidizeTypeVariables mp)) args) (Just old_ans)) mp), mp))
                put ans
                xs <- sequence <$> mapM (consistentTypesPass p) body
                (_, ((i, new_ans), _)) <- get
                case xs of
                    Right _ ->
                        (\case
                            Right ret -> case getAnnotation (LhsIdentifer "return" pos) new_ans of
                                Right (Finalizeable _ ret') -> do
                                    typ <- consistentTypesPass p ret
                                    put scope
                                    return $ Right $ makeFunAnnotation args $ unrigidizeTypeVariables mp ret'
                                Left err -> return $ Left err
                            Left err -> return $ Left err) =<< firstInferrableReturn pos body
                    Left err -> return $ Left err
    else return . Left $ InDefinitiveReturn Nothing pos
consistentTypesPass p (Return n pos) = consistentTypesPass p n >>= \x -> makeUnionIfNotSame pos x (getAnnotationState lhs) lhs
    where lhs = LhsIdentifer "return" pos
consistentTypesPass p (Call e args pos) =  (\case 
                    Right fann@(FunctionAnnotation fargs ret) -> do
                        mp <- getTypeMap
                        anns <- sequence <$> mapM (consistentTypesPass p) args
                        case anns of
                            Right anns -> let 
                                (spec, rels) = getPartialNoUnderScoreSpecificationRules pos defs Map.empty mp fann (FunctionAnnotation anns (AnnotationLiteral "_")) 
                                defs = fromUnionLists (map (collectGenenrics mp) anns, map (collectGenenricsHOF mp) anns) in
                                case substituteVariables pos defs rels spec mp ret of
                                    Right ret' -> case specify pos defs Map.empty mp fann (FunctionAnnotation anns ret') of
                                        Right r -> return $ Right ret'
                                        Left err -> return $ Left err
                                    Left err -> return $ Left err
                            Left err -> return $ Left err                    
                    Right opf@(OpenFunctionAnnotation oanns oret ft impls) -> do
                        mp <- getTypeMap
                        anns <- sequence <$> mapM (consistentTypesPass p) args
                        case anns of
                            Right anns -> let 
                                defs = fromUnionLists (map (collectGenenrics mp) anns, map (collectGenenricsHOF mp) anns)
                                (spec, rel) = getPartialNoUnderScoreSpecificationRules pos defs Map.empty mp (FunctionAnnotation oanns oret) (FunctionAnnotation anns (AnnotationLiteral "_")) in
                                case substituteVariables pos defs rel spec mp oret of
                                    Right ret' -> case getSpecificationRules pos defs Map.empty mp (FunctionAnnotation oanns oret) (FunctionAnnotation anns ret') of
                                        Right (_, base, _) -> case Map.lookup ft base of
                                            Just a -> maybe 
                                                    (return . Left $ NoInstanceFound opf a pos) 
                                                    (const . return $ Right ret')
                                                    (find (\b -> specifyTypesBool pos defs base mp b a) impls)
                                            Nothing -> return . Left $ NotOccuringTypeOpenFunction ft pos
                                        Left err -> return $ Left err
                                    Left err -> return $ Left err
                            Left err -> return $ Left err       
                    Right ann -> return . Left $ UnCallableType ann pos
                    Left err -> return $ Left err) =<< getTypeStateFrom (getAssumptionType e) pos
consistentTypesPass p (Identifier x pos) = getAnnotationState (LhsIdentifer x pos)
consistentTypesPass p (Lit (LitInt _ _)) = return . Right $ AnnotationLiteral "Int"
consistentTypesPass p (Lit (LitBool _ _)) = return . Right $ AnnotationLiteral "Bool"
consistentTypesPass p (Lit (LitString _ _)) = return . Right $ AnnotationLiteral "String"
consistentTypesPass p a = error $ show a

consistentTypes n = consistentTypesPass RefineAssumtpions n >>= \case
    Right _ -> consistentTypesPass VerifyAssumptions n
    Left err -> return $ Left err

onlyTypeDecls :: Node -> Bool
onlyTypeDecls (DeclN StructDef{}) = True
onlyTypeDecls (DeclN NewTypeDecl{}) = True
onlyTypeDecls _ = False

typeNodes :: [Node] -> ([Node], [Node])
typeNodes = partition onlyTypeDecls

typeMap :: [Node] -> Map.Map Lhs (Annotation, P.SourcePos)
typeMap xs = Map.fromList (map makeTup xs) where
    makeTup (DeclN (StructDef lhs rhs pos)) = (lhs, (rhs, pos))
    makeTup (DeclN (NewTypeDecl lhs rhs pos)) = (lhs, (rhs, pos))

allExists :: Map.Map Lhs (Annotation, P.SourcePos) -> Either ErrorType ()
allExists mp = mapM_ (exists mp) mp where
    exists :: Map.Map Lhs (Annotation, P.SourcePos) -> (Annotation, P.SourcePos) -> Either ErrorType ()
    exists mp (NewTypeAnnotation{}, pos) = Right ()
    exists mp (NewTypeInstanceAnnotation id anns1, pos) = case Map.lookup (LhsIdentifer id pos) mp of
        Just (NewTypeAnnotation id anns2 _, pos) -> if length anns1 == length anns2 then Right () else Left $ UnequalArguments anns1 anns2 pos
        Just a -> Left $ UninstantiableType (fst a) pos
        Nothing -> Left $ NoTypeFound id pos
    exists mp (Annotation id, pos) = 
        case Map.lookup (LhsIdentifer id pos) mp of
            Just _ -> Right ()
            Nothing -> Left $ NoTypeFound id pos
    exists mp (AnnotationLiteral lit, pos) = Right ()
    exists mp (FunctionAnnotation as ret, pos) = mapM_ (exists mp . (, pos)) as >> exists mp (ret, pos)
    exists mp (TypeUnion s, pos) = mapM_ (exists mp . (, pos)) (Set.toList s)
    exists mp (OpenFunctionAnnotation anns ret ftr _, pos) = mapM_ (exists mp . (, pos)) $ [ftr, ret] ++ anns
    exists mp (StructAnnotation xs, pos) = mapM_ (exists mp . (, pos)) (Map.elems xs)
    exists mp (GenericAnnotation _ cns, pos) = mapM_ (constraintExists mp . (, pos)) cns where 
        constraintExists mp (ConstraintHas _ cn, pos) = constraintExists mp (cn, pos)
        constraintExists mp (AnnotationConstraint ann, pos) = exists mp (ann, pos)

newTypeName :: P.SourcePos -> DefineTypesState Annotation Lhs
newTypeName pos = do
    s <- get
    (a, ((i, b), c)) <- get
    put (a, ((i+1, b), c))
    return $ LhsIdentifer ("auto_generated_type_" ++ show i) pos

defineSingleType :: P.SourcePos -> Annotation -> DefineTypesState Annotation Annotation
defineSingleType pos (FunctionAnnotation anns ret) = FunctionAnnotation <$> mapM (defineSingleType pos) anns <*> defineSingleType pos ret
defineSingleType pos g@GenericAnnotation{} = return g
defineSingleType pos lit@AnnotationLiteral{} = return lit
defineSingleType pos (OpenFunctionAnnotation anns ret ftr impls) = OpenFunctionAnnotation <$> mapM (defineSingleType pos) anns <*> defineSingleType pos ret <*> defineSingleType pos ftr <*> mapM (defineSingleType pos) impls
defineSingleType pos (NewTypeInstanceAnnotation id anns) = NewTypeInstanceAnnotation id <$> mapM (defineSingleType pos) anns
defineSingleType pos (TypeUnion st) = TypeUnion <$> (Set.fromList <$> mapM (defineSingleType pos) (Set.toList st))
defineSingleType pos ann = do
    mp <- getTypeMap
    case find (isRight . fst) $ Map.mapWithKey (\ann2 v -> (sameTypes pos (invertUserDefinedTypes mp) ann ann2, v)) mp of
        Just (Right ann, lhs@(LhsIdentifer id _)) -> modifyAnnotations lhs (Annotation id) $> Annotation id
        Just a -> error $ "Unexpected " ++ show a ++ " from defineSingleType"
        Nothing -> do
            tn <- newTypeName pos
            addToMap tn ann
            modifyAnnotations tn ann
            defineSingleType pos ann
            modifyAnnotations tn (Annotation $ show tn) $> ann
    where 
        addToMap :: Lhs -> Annotation -> DefineTypesState Annotation ()
        addToMap tn ann = do
            (a, ((i, b), mp)) <- get
            let new_mp = Map.insert ann tn mp
            put (a, ((i, b), new_mp))

        modifyAnnotations :: Lhs -> Annotation -> DefineTypesState Annotation ()
        modifyAnnotations tn ann = do
            (a, ((i, anns), mp)) <- get
            new_anns <- f (invertUserDefinedTypes mp) anns
            put (a, ((i, new_anns), mp))
            where 
                f mp (Annotations anns rest) = Annotations <$> sequence (
                    Map.map (\ann2 -> if isRight $ sameTypesImpl ann2 pos mp ann ann2 then return . Annotation $ show tn else defineSingleType pos ann2) anns
                    ) <*> sequence (f mp <$> rest)

defineTypesState :: Annotations Annotation -> DefineTypesState Annotation (Annotations Annotation)
defineTypesState (Annotations anns rest) = Annotations
  <$> sequence (Map.mapWithKey (\(LhsIdentifer _ pos) v -> defineSingleType pos v) anns)
  <*> sequence (defineTypesState <$> rest)

defineAllTypes :: UserDefinedTypes -> Annotations Annotation -> (UserDefinedTypes, Annotations Annotation)
defineAllTypes usts anns = (invertUserDefinedTypes $ snd $ snd st, snd . fst . snd $ st) where 
    st = execState (defineTypesState anns) (AnnotationLiteral "_", ((0, anns), invertUserDefinedTypes usts))

removeFinalization :: Annotations (Finalizeable a) -> Annotations a
removeFinalization (Annotations anns Nothing) = Annotations (Map.map fromFinalizeable anns) Nothing
removeFinalization (Annotations anns rest) = Annotations (Map.map fromFinalizeable anns) (removeFinalization <$> rest)

addFinalization :: Annotations a -> Annotations (Finalizeable a)
addFinalization (Annotations anns Nothing) = Annotations (Map.map (Finalizeable True) anns) Nothing
addFinalization (Annotations anns rest) = Annotations (Map.map (Finalizeable True) anns) (addFinalization <$> rest)

invertUserDefinedTypes :: Ord k => Map.Map a k -> Map.Map k a
invertUserDefinedTypes usts = Map.fromList $ Map.elems $ Map.mapWithKey (curry swap) usts

predefinedTypeNodes :: [Node]
predefinedTypeNodes = map DeclN [
    StructDef (LhsIdentifer "Nil" sourcePos) (StructAnnotation Map.empty) sourcePos,
    NewTypeDecl (LhsIdentifer "Array" sourcePos) (NewTypeAnnotation "Array" [GenericAnnotation "x" []] $ Map.singleton (LhsIdentifer "_value" sourcePos) $ GenericAnnotation "x" []) sourcePos
    ]

typeCheckedScope :: [Node] -> Either ErrorType ([Node], [Node], (UserDefinedTypes, Annotations Annotation))
typeCheckedScope program = 
    do
        allExists typesPos
        case runState (mapM getAssumptionType earlyReturns) (AnnotationLiteral "_", ((0, assumeProgram (Program $ earlyReturnToElse lifted) 0 types), types)) of
            (res, (a, map@(_, usts))) -> case sequence_ res of
                Left err -> Left err 
                Right () -> res >> Right (metProgram, earlyReturns, (usts, removeFinalization as)) where
                    res = sequence f
                    (_, ((_, as), _)) = s
                    (f, s) = runState (mapM consistentTypes (earlyReturnToElse lifted)) (a, map)
    where 
        earlyReturns = earlyReturnToElse lifted
        lifted = evalState (liftLambda restProgram) (0, [])
        (_metProgram, restProgram) = typeNodes program
        metProgram = _metProgram ++ predefinedTypeNodes
        typesPos = typeMap metProgram
        types = Map.map fst typesPos
