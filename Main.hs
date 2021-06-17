{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
module Main where

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

insertAnnotation :: Lhs -> Finalizeable Annotation -> AnnotationState Annotation
insertAnnotation k v@(Finalizeable _ a) = modify (\(a, (Annotations b o, m)) -> (a, (Annotations (Map.insert k v b) o, m))) >> return a

getAnnotation :: Lhs -> Annotations -> Result String (Finalizeable Annotation)
getAnnotation k@(LhsIdentifer _ pos) (Annotations anns rest) =
    case Map.lookup k anns of
        Just v -> Right v
        Nothing -> 
            case rest of
                Just rs -> getAnnotation k rs
                Nothing -> Left $ show k ++ " not found in this scope\n" ++ showPos pos
getAnnotation k a = error $ "Unexpected args " ++ show (k, a)

modifyAnnotation :: Lhs -> Annotation -> Annotations -> Result String Annotations
modifyAnnotation k@(LhsIdentifer _ pos) ann (Annotations anns rest) =
    case Map.lookup k anns of
        Just (Finalizeable False v) -> Right $ Annotations (Map.insert k (Finalizeable False ann) anns) rest
        Just (Finalizeable True v) -> Left $ "Can not reconcile annotated " ++ show v ++ " with " ++ show ann ++ "\n" ++ showPos pos
        Nothing -> 
            case rest of
                Just rs -> case modifyAnnotation k ann rs of
                    Right a -> Right $ Annotations anns (Just a)
                    Left err -> Left err
                Nothing -> Left $ show k ++ " not found in this scope\n" ++ showPos pos
modifyAnnotation k ann as = error $ "Unexpected args " ++ show (k, ann, as)

modifyAnnotationState :: Lhs -> Annotation -> AnnotationState (Result String Annotation)
modifyAnnotationState k v = do
    (a, (anns, b)) <- get
    case modifyAnnotation k v anns of
        Right x -> (Right <$> put (a, (x, b))) $> Right v
        Left err -> return $ Left err

finalizeAnnotations :: Annotations -> Annotations
finalizeAnnotations (Annotations anns Nothing) = Annotations (Map.map finalize anns) Nothing
finalizeAnnotations (Annotations anns (Just rest)) = Annotations (Map.map finalize anns) (Just $ finalizeAnnotations rest)

finalizeAnnotationState :: AnnotationState ()
finalizeAnnotationState = modify (\(a, (anns, b)) -> (a, (finalizeAnnotations anns, b)))

getAnnotationState :: Lhs -> AnnotationState (Result String Annotation)
getAnnotationState k = get >>= \(_, (anns, _)) -> return (fromFinalizeable <$> getAnnotation k anns)

getAnnotationStateFinalizeable :: Lhs -> AnnotationState (Result String (Finalizeable Annotation))
getAnnotationStateFinalizeable k = get >>= \(_, (anns, _)) -> return (getAnnotation k anns)

pushScope :: AnnotationState ()
pushScope = (\(a, (mp, b)) -> put (a, (Annotations Map.empty $ Just mp, b))) =<< get

popScope :: AnnotationState ()
popScope = (\(a, (Annotations _ (Just mp), b)) -> put (a, (mp, b))) =<< get

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

callError :: [Annotation] -> [Annotation] -> Either [Char] Annotation
callError fargs args = Left $ "Expected " ++ show fargs ++ " arguments but got " ++ show args ++ " args"

mapLeft s f = case s of
        Left x -> f x
        Right a ->  Right a

toEither def (Just a) = Right a
toEither def Nothing = Left def

getTypeState :: Annotation -> P.SourcePos -> State (Annotation, (b, UserDefinedTypes)) (Either String Annotation)
getTypeState (Annotation id) pos = do
    (_, (_, types)) <- get
    case Map.lookup (LhsIdentifer id pos) types of
        Just st -> return $ Right st
        Nothing -> return . Left $ "No type named " ++ id ++ " found\n" ++ showPos pos 
getTypeState a _ = return $ Right a

getTypeStateFrom :: AnnotationState (Either String Annotation) -> SourcePos -> AnnotationState (Either String Annotation)
getTypeStateFrom f pos = do
    res <- f
    case res of
        Right res -> getTypeState res pos
        Left err -> return $ Left err

firstInferrableReturn :: P.SourcePos -> [Node] -> AnnotationState (Either String Node)
firstInferrableReturn pos [] = return . Left $ "Could not infer the type of function at \n" ++ showPos pos
firstInferrableReturn pos (IfStmnt cond ts es _:xs) = do
    scope@(_, (_, mp)) <- get
    c <- getAssumptionType cond
    case sameTypes pos mp (AnnotationLiteral "Bool") <$> c of
        Right _ -> do
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
                            return $ Left err
        Left err -> return $ Left err
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
firstInferrableReturn pos ((Return a _):_) = return $ Right a
firstInferrableReturn pos (_:xs) = firstInferrableReturn pos xs

isGeneric :: P.SourcePos -> UserDefinedTypes -> Annotation -> Bool
isGeneric pos mp GenericAnnotation{} = True
isGeneric pos mp AnnotationLiteral{} = False
isGeneric pos mp (Annotation ann) = maybe False (isGeneric pos mp) (Map.lookup (LhsIdentifer ann pos) mp)
isGeneric pos mp (FunctionAnnotation args ret) = any (isGeneric pos mp) (ret:args)
isGeneric pos mp (StructAnnotation ms) = any (isGeneric pos mp) ms
isGeneric pos mp (NewTypeAnnotation _ _ tmp) = any (isGeneric pos mp) tmp
isGeneric pos mp (NewTypeInstanceAnnotation _ as) = any (isGeneric pos mp) as
isGeneric pos mp (TypeUnion ts) = any (isGeneric pos mp) ts
isGeneric pos mp OpenFunctionAnnotation{} = False

firstPreferablyDefinedRelation pos defs mp rs k =
    case Map.lookup k rs of
        Just s -> 
            if notnull stf then Right $ Set.elemAt 0 stf 
            else if notnull deftf then Right $ Set.elemAt 0 deftf  
            else case defRes of
                    Right x -> Right x
                    Left _ -> Right $ Set.elemAt 0 s 
            where 
                notnull = not . Set.null
                deftf = Set.filter (`Set.member` defs) s
                stf = Set.filter (\x -> isJust (Map.lookup x mp)) s
        Nothing -> defRes
        where 
            defRes = 
                case Map.elems $ Map.filter (\s -> Set.member k s && not (Set.disjoint defs s)) $ Map.mapWithKey Set.insert rs of
                    [] -> Left $ "No relation of generic " ++ show k ++ " found\n" ++ showPos pos
                    xs -> Right $ Set.elemAt 0 $ head xs

substituteConstraints :: SourcePos -> Set.Set Annotation -> TypeRelations -> Map.Map Annotation Annotation -> UserDefinedTypes -> Constraint -> Either String  Constraint
substituteConstraints pos defs rels mp usts (ConstraintHas lhs cs) = ConstraintHas lhs <$> substituteConstraints pos defs rels mp usts cs 
substituteConstraints pos defs rels mp usts (AnnotationConstraint ann) = AnnotationConstraint <$> substituteVariables pos defs rels mp usts ann

substituteVariables :: SourcePos -> Set.Set Annotation -> TypeRelations -> Map.Map Annotation Annotation -> UserDefinedTypes -> Annotation -> Either String Annotation
substituteVariables pos defs rels mp usts fid@(GenericAnnotation id cns) = 
    maybe g (\x -> if sameTypesBool pos usts fid x then g else Right x) (Map.lookup fid mp)
    where 
        f x = case firstPreferablyDefinedRelation pos defs mp rels x of
            Right a -> Right a
            Left _ -> Right x
        g = mapM (substituteConstraints pos defs rels mp usts) cns >>= f . GenericAnnotation id
substituteVariables pos defs rels mp usts id@AnnotationLiteral{} = Right id
substituteVariables pos defs rels mp usts fid@(Annotation id) = maybe (Left $ noTypeFound id pos) Right (Map.lookup (LhsIdentifer id pos) usts)
substituteVariables pos defs rels mp usts (NewTypeAnnotation id anns annMap) = NewTypeAnnotation id <$> mapM (substituteVariables pos defs rels mp usts) anns <*> mapM (substituteVariables pos defs rels mp usts) annMap
substituteVariables pos defs rels mp usts (NewTypeInstanceAnnotation id anns) =  NewTypeInstanceAnnotation id <$> mapM (substituteVariables pos defs rels mp usts) anns
substituteVariables pos defs rels mp usts (FunctionAnnotation args ret) = FunctionAnnotation <$> mapM (substituteVariables pos defs rels mp usts) args <*> substituteVariables pos defs rels mp usts ret
substituteVariables pos defs rels mp usts (StructAnnotation ms) = StructAnnotation <$> mapM (substituteVariables pos defs rels mp usts) ms
substituteVariables pos defs rels mp usts (TypeUnion ts) = TypeUnion . Set.fromList <$> mapM (substituteVariables pos defs rels mp usts) (Set.toList ts)
substituteVariables pos defs rels mp usts OpenFunctionAnnotation{} = error "Can't use substituteVariables with open functions"

collectGenericConstraints :: UserDefinedTypes -> Constraint -> Set.Set Annotation
collectGenericConstraints usts (ConstraintHas lhs cs) = collectGenericConstraints usts cs 
collectGenericConstraints usts (AnnotationConstraint ann) = collectGenenrics usts ann

collectGenenrics :: UserDefinedTypes -> Annotation -> Set.Set Annotation
collectGenenrics usts fid@(GenericAnnotation id cns) = Set.singleton fid `Set.union` Set.unions (map (collectGenericConstraints usts) cns)
collectGenenrics usts AnnotationLiteral{} = Set.empty
collectGenenrics usts fid@(Annotation ident) = maybe (error "Run your passes in order. You should know that this doesn't exists by now") (collectGenenrics usts) (Map.lookup (LhsIdentifer ident (SourcePos "" (mkPos 0) (mkPos 0))) usts)
collectGenenrics usts (NewTypeAnnotation id anns annMap) = Set.unions (Set.map (collectGenenrics usts) (Set.fromList anns)) `Set.union` foldl1 Set.union (map (collectGenenrics usts) (Map.elems annMap))
collectGenenrics usts (NewTypeInstanceAnnotation id anns) = Set.unions $ Set.map (collectGenenrics usts) (Set.fromList anns)
collectGenenrics usts (FunctionAnnotation args ret) = Set.empty
collectGenenrics usts (StructAnnotation ms) = Set.unions $ Set.map (collectGenenrics usts) (Set.fromList $ Map.elems ms)
collectGenenrics usts (TypeUnion ts) = Set.unions $ Set.map (collectGenenrics usts) ts
collectGenenrics usts (OpenFunctionAnnotation args ret ftr _) = Set.unions $ Set.map (collectGenenrics usts) $ Set.fromList (args++[ret, ftr])

getLookupTypeIfAvailable :: Annotation -> SubstituteState Annotation
getLookupTypeIfAvailable k = do
    (a, ((rs, mp), usts)) <- get
    case Map.lookup k mp of
        Just k -> getLookupTypeIfAvailable k
        Nothing -> return k

changeType :: P.SourcePos -> Annotation -> Annotation -> SubstituteState (Either String ())
changeType pos k v = do
    (a, ((rel, mp), usts)) <- get
    case substituteVariables pos Set.empty rel mp usts v of
        Right sub -> put (a, ((rel, Map.insert k sub mp), usts)) $> Right ()
        Left err -> return $ Left err

reshuffleTypes :: P.SourcePos -> SubstituteState ()
reshuffleTypes pos = (\(_, ((_, mp), _)) -> sequence_ $ Map.mapWithKey (changeType pos) mp) =<< get

sameTypesNoUnionSpec = sameTypesGeneric (False, True, Map.empty)

addTypeVariableGeneralized n pos stmnt k v = do
        (a, ((rs, mp), usts)) <- get
        case Map.lookup k mp of
            Nothing -> addToMap a rs mp usts k v
            Just a -> do
                case sameTypesNoUnionSpec pos usts a v of
                    Left err -> if a == AnnotationLiteral "_" then addToMap a rs mp usts k v else 
                        case Map.lookup k rs of
                            Just st -> if Set.member v st then addToMap a rs mp usts k v else return $ Left err
                            Nothing -> 
                                if n > 0 then do
                                    reshuffleTypes pos
                                    addTypeVariableGeneralized (n-1) pos stmnt k v
                                    else return $ Left err
                    Right a -> addToMap a rs mp usts k v
    where
        addToMap a rs mp usts k v = do
            put (a, ((rs, Map.insert k v mp), usts))
            stmnt
            reshuffleTypes pos
            return $ Right v

addTypeVariable :: SourcePos -> Annotation -> Annotation -> SubstituteState (Either String Annotation)
addTypeVariable pos = addTypeVariableGeneralized 5 pos (updateRelations pos)

-- This is written horribly, rewrite it
updateSingleRelation pos r = do
    (a, ((rs, mp), usts)) <- get
    case Map.lookup r rs of
        Just rl -> do
            (\case 
                Right _ -> maybe (return $ Right ()) (\a -> f r a $> Right ()) fnv
                Left err -> return $ Left err) . sequence =<< mapM (uncurry f) mls'
            where 
            m = Map.filterWithKey (\k _ -> k `Set.member` rl) mp
            mls = Map.toList m
            fnv = firstNonUnderscore mls
            mls' = case fnv of 
                Just a -> map (\(k, _) -> (k, a)) mls
                Nothing -> []
            f = addTypeVariableGeneralized 5 pos (return $ Right ())

            firstNonUnderscore [] = Nothing 
            firstNonUnderscore ((_, AnnotationLiteral "_"):xs) = firstNonUnderscore xs
            firstNonUnderscore ((_, ann):xs) = Just ann
        Nothing -> return . Left $ "No relation on " ++ show r ++ " has been established"

updateRelations :: P.SourcePos -> SubstituteState (Either String ())
updateRelations pos = do
    (a, ((rs, mp), usts)) <- get
    x <- mapM (updateSingleRelation pos) $ Map.keys rs
    case sequence x of
        Right _ -> return $ Right ()
        Left err -> return $ Left err

addRelation :: P.SourcePos -> Annotation -> Annotation -> SubstituteState (Either String ())
addRelation pos r nv = do
    (a, ((rs, mp), usts)) <- get
    case Map.lookup r rs of
        Just rl -> do
            let nrs = Map.insert r (rl `Set.union` Set.singleton nv) rs
            put (a, ((nrs, mp), usts))
            Right () <$ updateSingleRelation pos r
        Nothing -> do
            let nrs = Map.insert r (Set.singleton nv) rs
            put (a, ((nrs, mp), usts))
            Right () <$ updateSingleRelation pos r

applyConstraintState :: SourcePos -> Annotation -> Constraint -> SubstituteState (Either String Annotation)
applyConstraintState pos ann (ConstraintHas lhs cn) = 
    do 
        mp <- getTypeMap
        case ann of
            StructAnnotation mp -> 
                case lhs `Map.lookup` mp of
                    Just ann -> applyConstraintState pos ann cn
                    Nothing -> return . Left $ "No field named " ++ show lhs ++ " found in " ++ show ann ++ "\n" ++ showPos pos
            Annotation id ->
                case LhsIdentifer id pos `Map.lookup` mp of
                    Just ann -> applyConstraintState pos ann cn
                    Nothing -> return . Left $ "No type named " ++ id ++ " found\n" ++ showPos pos
            NewTypeInstanceAnnotation id args -> 
                        accessNewType args
                        (\(NewTypeAnnotation _ _ ps) -> 
                            case Map.lookup lhs ps of
                                Just ann -> applyConstraintState pos ann cn
                                Nothing -> return . Left $ "Could not find " ++ show lhs ++ " in " ++ show ps ++ "\n" ++ showPos pos
                            ) 
                        (\a -> return . Left $ "Cannot get " ++ show lhs ++ " from type " ++ show a ++ "\n" ++ showPos pos)
                        (LhsIdentifer id pos)
            g@(GenericAnnotation id cns) -> return $ genericHas pos mp lhs cns
            t@TypeUnion{} -> typeUnionHas pos t cn
            a -> return . Left $ "Can't search for field " ++ show lhs ++ " in " ++ show a ++ "\n" ++ showPos pos
applyConstraintState pos ann2 (AnnotationConstraint ann1) = do
    a <- if isGenericAnnotation ann2 && isGenericAnnotation ann1 then addRelation pos ann2 ann1 *> addRelation pos ann1 ann2 $> Right ann1 else addTypeVariable pos ann1 ann2
    case a of
        Right _ -> specifyInternal pos ann1 ann2
        Left err -> return $ Left err

typeUnionHas pos (TypeUnion st) cn = (\case
                Left err -> return $ Left err
                Right stl -> do
                    a <- sequence <$> mapM (flip (applyConstraintState pos) cn) stl
                    case a of
                        Right (x:_) -> return $ Right x
                        Left err -> return $ Left err
                ) . sequence =<< mapM (flip (applyConstraintState pos) cn) stl where stl = Set.toList st
typeUnionHas _ t _ = error $ "typeUnionHas can only be called with type union, not " ++ show t

specifyInternal :: SourcePos
    -> Annotation
    -> Annotation
    -> SubstituteState (Either String Annotation)
specifyInternal pos a@AnnotationLiteral{} b@AnnotationLiteral{} = (\mp -> return $ sameTypes pos mp a b *> Right a) =<< gets (snd . snd)
specifyInternal pos a@(GenericAnnotation id cns) b@(AnnotationLiteral ann) = do
    mp <- getTypeMap
    ann <- addTypeVariable pos a b
    case ann of
        Right ann ->
            (\case
                Right _ -> return $ Right b
                Left err -> return $ Left err) . sequence =<< mapM (applyConstraintState pos ann) cns
        Left err -> return $ Left err
specifyInternal pos a@(GenericAnnotation id cns) b@(Annotation ann) = do
    anno <- getTypeState b pos
    case anno of
        Right ann -> specifyInternal pos a ann
        Left err -> return $ Left err
specifyInternal pos a@(Annotation id1) b@(Annotation id2) 
    | id1 == id2 = return $ Right b
    | otherwise = (\mp -> case Map.lookup (LhsIdentifer id1 pos) mp of 
        Just a' -> case Map.lookup (LhsIdentifer id2 pos) mp of
            Just b' -> specifyInternal pos a' b'
            Nothing -> undefined
        Nothing -> return $ Left $ noTypeFound id1 pos) =<< getTypeMap
specifyInternal pos a@(Annotation id) b = (\mp -> case Map.lookup (LhsIdentifer id pos) mp of 
        Just a' -> specifyInternal pos a' b
        Nothing -> return $ Left $ noTypeFound id pos) =<< getTypeMap
specifyInternal pos a b@(Annotation id) = (\mp -> case Map.lookup (LhsIdentifer id pos) mp of 
    Just b' -> specifyInternal pos a b'
    Nothing -> return $ Left $ noTypeFound id pos) =<< getTypeMap
specifyInternal pos a@(GenericAnnotation id1 cns1) b@(GenericAnnotation id2 cns2) = do
    (\case
        Right _ -> addRelation pos b a *> addRelation pos a b $> Right b
        Left err -> return $ Left err
        ) . sequence =<< mapM (applyConstraintState pos b) cns1
specifyInternal pos a@(GenericAnnotation id cns) b@(TypeUnion st) = (\case
        Right _ -> do
            a <- addTypeVariable pos a b
            case a of
                Right _ -> return $ Right b
                Left err -> return $ Left err
        Left err -> return $ Left err) . sequence =<< mapM (applyConstraintState pos b) cns
specifyInternal pos a@(StructAnnotation ms1) b@(StructAnnotation ms2)
    | Map.size ms1 /= Map.size ms2 = return . Left $ unmatchedType a b pos
    | Set.fromList (Map.keys ms1) == Set.fromList (Map.keys ms2) = (\case
        Right _ -> return $ Right b
        Left err -> return $ Left err) . sequence =<< zipWithM (specifyInternal pos) (Map.elems ms1) (Map.elems ms2)
specifyInternal pos a@(OpenFunctionAnnotation oargs oret _ _) b@(FunctionAnnotation args ret) 
    | length args /= length oargs = return $ callError oargs args
    | otherwise = (\case
        Right _ -> return $ Right b
        Left err -> return $ Left err
        ) . sequence =<< zipWithM (specifyInternal pos) (oargs ++ [oret]) (args ++ [ret])
specifyInternal pos a@(FunctionAnnotation oargs oret) b@(FunctionAnnotation args ret)
    | length args /= length oargs = return $ callError oargs args
    | otherwise = (\case
        Right _ -> return $ Right b
        Left err -> return $ Left err
        ) . sequence =<< zipWithM (specifyInternal pos) (oargs ++ [oret]) (args ++ [ret])
specifyInternal pos a@(NewTypeInstanceAnnotation id1 anns1) b@(NewTypeInstanceAnnotation id2 anns2)
    | length anns1 /= length anns2 = return $ callError anns1 anns2
    | otherwise = (\case
        Right _ -> return $ Right b
        Left err -> return $ Left err
        ) . sequence =<< zipWithM (specifyInternal pos) anns1 anns2
specifyInternal pos a@(TypeUnion as) b@(TypeUnion bs) = do
    mp <- getTypeMap
    xs <- sequence <$> mapM (f mp $ Set.toList as) (Set.toList bs)
    case xs of
        Right _ -> return $ Right b
        Left err -> return $ Left err
    where
        f mp ps2 v1 = getFirst a b pos $ map (\x -> specifyInternal pos x v1) ps2
specifyInternal pos a b@(TypeUnion st) = do
    x <- sequence <$> mapM (flip (specifyInternal pos) a) stl
    case x of
        Right a -> return . Right $ head a
        Left err -> return $ Left err
    where stl = Set.toList st
specifyInternal pos a@(TypeUnion st) b = getFirst a b pos $ map (flip (specifyInternal pos) b) stl where stl = Set.toList st
specifyInternal pos a@(GenericAnnotation id cns) b = 
    (\case
        Right _ -> do
            a <- addTypeVariable pos a b
            case a of
                Right _ -> return $ Right b
                Left err -> return $ Left err
        Left err -> return $ Left err) . sequence =<< mapM (applyConstraintState pos b) cns
specifyInternal pos a b = (\mp -> return $ sameTypes pos mp a b) =<< getTypeMap

getFirst a b pos [] = return . Left $ unmatchedType a b pos
getFirst a b pos (x:xs) = x >>= \case
    Right a -> return $ Right a
    Left _ -> getFirst a b pos xs

specify :: SourcePos -> Map.Map Annotation Annotation -> UserDefinedTypes -> Annotation -> Annotation -> Either String (Annotation, TypeRelations)
specify pos base mp a b = (,rel) <$> ann where (ann, (ann1, ((rel, nmp), usts))) = runState (specifyInternal pos a b) (a, ((Map.empty, base), mp))

getPartialSpecificationRules :: SourcePos -> Map.Map Annotation Annotation -> UserDefinedTypes -> Annotation -> Annotation -> (Map.Map Annotation Annotation, TypeRelations)
getPartialSpecificationRules pos base mp a b = (nmp, rel) where (ann, (ann1, ((rel, nmp), usts))) = runState (specifyInternal pos a b) (a, ((Map.empty, base), mp))

getPartialNoUnderScoreSpecificationRules :: SourcePos -> Map.Map Annotation Annotation -> UserDefinedTypes -> Annotation -> Annotation -> (Map.Map Annotation Annotation, TypeRelations)
getPartialNoUnderScoreSpecificationRules pos base mp a b = 
    (Map.mapWithKey (\k a -> if a == AnnotationLiteral "_" then k else a) nmp, rel) where (nmp, rel) = getPartialSpecificationRules pos base mp a b

getSpecificationRules :: SourcePos -> Map.Map Annotation Annotation -> UserDefinedTypes  -> Annotation -> Annotation -> Either String (Map.Map Annotation Annotation)
getSpecificationRules pos base mp a b = case fst st of
    Right _ -> Right (snd $ fst $ snd $ snd st)
    Left err -> Left err 
    where st = runState (specifyInternal pos a b) (a, ((Map.empty, base), mp))


sameTypesGenericBool gs crt pos mp a b = case sameTypesGeneric gs pos mp a b of
                        Right _ -> True
                        Left _ -> False

sameTypesBool pos mp a b = case sameTypes pos mp a b of
                        Right _ -> True
                        Left _ -> False

specifyTypesBool pos base usts a b = case specify pos base usts a b of
                        Right _ -> True
                        Left _ -> False                                     

isGenericAnnotation a = case a of 
    a@GenericAnnotation{} -> True
    _ -> False

expectedUnion pos lhs ann = "Expected a type union, got type " ++ show ann ++ " from " ++ show lhs ++ "\n" ++ showPos pos

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

modifyWhole :: [Lhs] -> Annotation -> Annotation -> AnnotationState Annotation
modifyWhole (p:xs) whole@(StructAnnotation ps) given = case Map.lookup p ps of
    Just a -> modifyWhole xs a given >>= \x -> return . StructAnnotation $ Map.insert p x ps
    Nothing -> error $ "You should already know that " ++ show p ++  " is in " ++ show ps ++ " before comming here"
modifyWhole [] _ given = return given

listAccess n = reverse $ go n where
    go (Access n lhs _) = lhs : listAccess n
    go Identifier{} = []

sameTypesImpl :: Annotation -> SourcePos -> UserDefinedTypes -> Annotation -> Annotation -> Either String Annotation
sameTypesImpl TypeUnion{} = sameTypesNoUnionSpec
sameTypesImpl _ = sameTypes

matchingUserDefinedType :: P.SourcePos -> UserDefinedTypes -> Annotation -> Maybe Annotation
matchingUserDefinedType pos usts t = (\(LhsIdentifer id _, _) -> Just $ Annotation id) =<< find (isRight . snd) (Map.mapWithKey (,) $ Map.map (flip (specify pos Map.empty usts) t) usts)

getAssumptionType :: Node -> AnnotationState (Result String Annotation)
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
                        x <- f mp pos (Access access p accPos) whole expcd rhs
                        case x of
                            Right x -> modifyAnnotationState (initIdentLhs lhs) x
                            Left err -> return $ Left err
            (Left err, _, _) -> return $ Left err
            (_, Left err, _) -> return $ Left err
            (_, _, Left err) -> return $ Left err
    where

    f :: UserDefinedTypes -> P.SourcePos -> Node -> Annotation -> Annotation -> Annotation -> AnnotationState (Either String Annotation)
    f mp pos acc whole expected given = case whole of
            g@(GenericAnnotation _ cns) -> return $ genericHas pos g p cns
            TypeUnion{} -> getAssumptionType (Access access p accPos) >>= \res -> return $ sameTypes pos mp given =<< res
            NewTypeInstanceAnnotation{} -> getAssumptionType (Access access p accPos) >>= \res -> return $ sameTypes pos mp given =<< res
            StructAnnotation ps -> case sameTypesImpl given pos mp expected given of 
                Right a -> return $ Right a
                Left err -> Right <$> modifyWhole (listAccess acc) whole (mergedTypeConcrete pos mp expected given)
            a -> return . Left $ "Cannot get " ++ show p ++ " from type " ++ show a ++ "\n" ++ showPos pos
getAssumptionType (DeclN (Assign lhs n pos)) = getAssumptionType n >>= \x -> makeUnionIfNotSame pos x (getAnnotationState lhs) lhs
getAssumptionType (DeclN (FunctionDecl lhs ann _)) = Right <$> insertAnnotation lhs (Finalizeable False ann)
getAssumptionType (CreateNewType lhs args pos) = do
    mp <- getTypeMap
    argsn <- sequence <$> mapM getAssumptionType args
    case argsn of
        Right as -> return $ case Map.lookup lhs mp of
            Just (NewTypeAnnotation id anns _) -> 
                if length anns == length args then NewTypeInstanceAnnotation id <$> argsn
                else Left $ "Can't match arguments " ++ show as ++ " with " ++ show anns
            Just a -> error (show a)
            Nothing -> Left $ noTypeFound (show lhs) pos
        Left err -> return $ Left err
getAssumptionType (DeclN (OpenFunctionDecl lhs ann _)) = Right <$> insertAnnotation lhs (Finalizeable False ann)
getAssumptionType (DeclN impl@(ImplOpenFunction lhs args (Just ret) ns implft pos)) = do
    a <- getAnnotationState lhs
    mp <- getTypeMap
    case a of
        Left err -> return $ Left err
        Right a@(OpenFunctionAnnotation anns ret' ft impls) -> do
            let b = makeFunAnnotation args ret
            case getSpecificationRules pos Map.empty mp ft implft of
                Right base -> 
                    case getSpecificationRules pos base mp a b of
                        Left err -> return $ Left err
                        Right res -> 
                                    let 
                                        aeq = Set.fromList $ Map.keys $ Map.filterWithKey (\a b -> isGenericAnnotation a && not (sameTypesBool pos mp a b)) res
                                        beq = Set.fromList $ Map.keys $ Map.filterWithKey (\a b -> isGenericAnnotation a && not (sameTypesBool pos mp a b)) base
                                    in
                                    if aeq == beq then 
                                        Right <$> insertAnnotation lhs (Finalizeable True (OpenFunctionAnnotation anns ret' ft $ implft:impls))
                                    else return . Left $ "Forbidden to specify specified type variables\n" ++ showPos pos
                Left err -> return $ Left err
        Right a -> return . Left $ "Cannot extend function " ++ show a ++ "\n" ++ showPos pos
getAssumptionType (DeclN (ImplOpenFunction lhs args Nothing ns implft pos)) = do
    a <- getAnnotationState lhs
    mp <- getTypeMap
    case a of
        Left err -> return $ Left err
        Right fun@(OpenFunctionAnnotation anns ret' ft impls) -> 
            case getSpecificationRules pos Map.empty mp ft implft of
                Right base -> do
                    let (specificationRules, rels) = getPartialNoUnderScoreSpecificationRules pos Map.empty mp fun (FunctionAnnotation (map snd args) (AnnotationLiteral "_"))
                    case substituteVariables pos (Set.unions $ map (collectGenenrics mp . snd) args) rels specificationRules mp ret' of
                        Left a -> return . Left $ "Could not infer the return type: " ++ a ++ "\n" ++ showPos pos
                        Right inferredRetType ->
                            let spfun = makeFunAnnotation args inferredRetType in
                            case getSpecificationRules pos base mp fun spfun of
                                Left err -> return $ Left err
                                Right res -> 
                                    let 
                                        a = Set.fromList (Map.keys (Map.filterWithKey (\a b -> isGenericAnnotation a && not (sameTypesBool pos mp a b)) res))
                                        b = Set.fromList (Map.keys (Map.filterWithKey (\a b -> isGenericAnnotation a && not (sameTypesBool pos mp a b)) base))
                                    in
                                    if a == b then 
                                        Right <$> insertAnnotation lhs (Finalizeable True (OpenFunctionAnnotation anns ret' ft $ implft:impls))
                                    else return . Left $ "Forbidden to specify specified type variables\n" ++ showPos pos
                Left err -> return $ Left err
        Right a -> return . Left $ "Cannot extend function " ++ show a ++ "\n" ++ showPos pos
getAssumptionType (CastNode lhs ann _) = Right <$> (insertAnnotation lhs (Finalizeable False ann) $> AnnotationLiteral "Bool")
getAssumptionType (RemoveFromUnionNode lhs ann pos) =
    (\case
        Right a@TypeUnion{} -> (return . Right $ AnnotationLiteral "Bool") <$ (\x -> insertAnnotation lhs . Finalizeable False) =<< excludeFromUnion pos ann a
        Right a -> return . Left $ expectedUnion pos lhs ann
        Left err -> return $ Left err) =<< getAnnotationState lhs
getAssumptionType (DeclN (Expr n)) = getAssumptionType n
getAssumptionType (Return n pos) = getAssumptionType n >>= \x -> makeUnionIfNotSame pos x (getAnnotationState lhs) lhs
    where lhs = LhsIdentifer "return" pos
getAssumptionType (IfStmnt (RemoveFromUnionNode lhs ann _) ts es pos) = do
    (_, (_, mp)) <- get
    pushScope
    typLhs <- getAnnotationState lhs
    case typLhs of
        Right union@TypeUnion{} ->  do
            insertAnnotation lhs . Finalizeable False =<< excludeFromUnion pos ann union
            t <- sequence <$> mapM getAssumptionType ts
            popScope
            pushScope
            insertAnnotation lhs (Finalizeable False ann)
            e <- sequence <$> mapM getAssumptionType es
            popScope
            let res = case (t, e) of
                    (Right b, Right c) -> Right $ AnnotationLiteral "_"
                    (Left a, _) -> Left a
                    (_, Left a) -> Left a
            return res
        _ -> return . Left $ expectedUnion pos lhs typLhs
getAssumptionType (IfStmnt (CastNode lhs ann _) ts es pos) = do
    mp <- getTypeMap
    pushScope
    insertAnnotation lhs (Finalizeable False ann)
    t <- sequence <$> mapM getAssumptionType ts
    popScope
    pushScope
    typLhs <- getAnnotationState lhs
    case typLhs of
        Right ts@TypeUnion{} -> insertAnnotation lhs . Finalizeable False =<< excludeFromUnion pos ann ts
        _ -> return ann
    e <- sequence <$> mapM getAssumptionType es
    popScope
    let res = case (t, e) of
            (Right b, Right c) -> Right $ AnnotationLiteral "_"
            (Left a, _) -> Left a
            (_, Left a) -> Left a
    return res
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
            whole_old_ans@(a, (old_ans, mp)) <- get
            let program = Program body
            let ans = (a, (assumeProgramMapping program (Annotations (Map.fromList $ (LhsIdentifer "return" pos, Finalizeable False $ AnnotationLiteral "_"):map (second (Finalizeable True)) args) (Just old_ans)) mp, mp))
            put ans
            mapM_ getAssumptionType body
            (new_ans, _) <- gets snd
            x <- firstInferrableReturn pos body
            case x of
                Right ret -> do
                    typ <- getAnnotationState $ LhsIdentifer "return" pos
                    let ntyp = typ >>= (\c -> 
                            if c then maybe typ Right . matchingUserDefinedType pos (Map.filter isStructOrUnionOrFunction mp) =<< typ 
                            else typ
                            ) . isSearchable
                    put whole_old_ans
                    return (makeFunAnnotation args <$> ntyp)
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
                                (spec, rel) = getPartialNoUnderScoreSpecificationRules pos Map.empty mp fann (FunctionAnnotation anns (AnnotationLiteral "_")) 
                                defs = Set.unions $ map (collectGenenrics mp) anns in
                                case substituteVariables pos defs rel spec mp ret of
                                    Right ret' -> case specify pos Map.empty mp fann (FunctionAnnotation anns ret') of
                                        Right _ -> return $ Right ret'
                                        Left err -> return $ Left err
                                    Left err -> return $ Left err
                            Left err -> return $ Left err
                    Right opf@(OpenFunctionAnnotation oanns oret ft impls) -> do
                        mp <- getTypeMap
                        anns <- sequence <$> mapM consistentTypes args
                        case anns of
                            Right anns -> let 
                                (spec, rel) = getPartialNoUnderScoreSpecificationRules pos Map.empty mp (FunctionAnnotation oanns oret) (FunctionAnnotation anns (AnnotationLiteral "_")) in
                                case substituteVariables pos (Set.unions $ map (collectGenenrics mp) anns) rel spec mp oret of
                                    Right ret' -> case getSpecificationRules pos Map.empty mp (FunctionAnnotation oanns oret) (FunctionAnnotation anns ret') of
                                        Right base -> case Map.lookup ft base of
                                            Just a -> maybe 
                                                    (return . Left $ "Could find instance " ++ show opf ++ " for " ++ show a ++ "\n" ++ showPos pos) 
                                                    (const . return $ Right ret')
                                                    (find (\b -> specifyTypesBool pos base mp b a) impls)
                                            Nothing -> return . Left $ "The argument does not even once occur in the whole method\n" ++ showPos pos
                                        Left err -> return $ Left err
                                    Left err -> return $ Left err
                            Left err -> return $ Left err       
                    Right ann -> return . Left $ "Can't call a value of type " ++ show ann ++ "\n" ++ showPos pos
                    Left err -> return $ Left err) =<< getTypeStateFrom (getAssumptionType e) pos
getAssumptionType (StructN (Struct ns _)) = 
        (\xs -> mapRight 
            (return . Right $ AnnotationLiteral "_") 
            (const . return $ StructAnnotation <$> sequence xs)) =<< mapM getAssumptionType ns
getAssumptionType (Access st p pos) = do
    mp <- getTypeMap
    f mp =<< getTypeStateFrom (consistentTypes st) pos where 

    f :: UserDefinedTypes -> Either String Annotation -> AnnotationState (Either String Annotation)
    f mp = \case
            Right g@(GenericAnnotation _ cns) -> return $ genericHas pos g p cns
            Right (TypeUnion st) -> ((\x -> head <$> mapM (sameTypes pos mp (head x)) x) =<<) <$> x where 
                x = sequence <$> mapM (\x -> f mp =<< getTypeState x pos) stl
                stl = Set.toList st
            Right (NewTypeInstanceAnnotation id anns) -> 
                accessNewType anns
                (\(NewTypeAnnotation _ _ ps) -> return $ toEither ("Could not find " ++ show p ++ " in " ++ show ps ++ "\n" ++ showPos pos) (Map.lookup p ps)) 
                (\a -> return . Left $ "Cannot get " ++ show p ++ " from type " ++ show a ++ "\n" ++ showPos pos)
                (LhsIdentifer id pos)
            Right (StructAnnotation ps) -> return $ toEither ("Could not find " ++ show p ++ " in " ++ show ps ++ "\n" ++ showPos pos) (Map.lookup p ps)
            Right a -> return . Left $ "Cannot get " ++ show p ++ " from type " ++ show a ++ "\n" ++ showPos pos
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

genericHas pos g givenLhs [] = Left $ "Could not find " ++ show givenLhs ++ " in " ++ show g ++ "\n" ++ showPos pos
genericHas pos g givenLhs ((ConstraintHas lhs (AnnotationConstraint ann)):xs) = if lhs == givenLhs then Right ann else genericHas pos g givenLhs xs

makeAssumptions :: State (Annotation, b) a -> b -> b
makeAssumptions s m = snd $ execState s (AnnotationLiteral "_", m)

assumeProgramMapping :: Program -> Annotations -> UserDefinedTypes -> Annotations
assumeProgramMapping (Program xs) anns mp = fst $ makeAssumptions (mapM getAssumptionType $ filter nonDecls xs) (anns, mp)

nonDecls (DeclN Decl{}) = True
nonDecls (DeclN FunctionDecl{}) = True
nonDecls (DeclN Assign{}) = True
nonDecls _ = False

sourcePos = SourcePos "core" (mkPos 0) (mkPos 0)

baseMapping = Map.fromList $ map (second (Finalizeable True)) [
    (LhsIdentifer "add" sourcePos, OpenFunctionAnnotation [GenericAnnotation "a" [], GenericAnnotation "a" []] (GenericAnnotation "a" []) (GenericAnnotation "a" []) [AnnotationLiteral "Int", AnnotationLiteral "String"]),
    (LhsIdentifer "sub" sourcePos, OpenFunctionAnnotation [GenericAnnotation "a" [], GenericAnnotation "a" []] (GenericAnnotation "a" []) (GenericAnnotation "a" []) [AnnotationLiteral "Int"]),
    (LhsIdentifer "mul" sourcePos, OpenFunctionAnnotation [GenericAnnotation "a" [], GenericAnnotation "a" []] (GenericAnnotation "a" []) (GenericAnnotation "a" []) [AnnotationLiteral "Int"]),
    (LhsIdentifer "div" sourcePos, OpenFunctionAnnotation [GenericAnnotation "a" [], GenericAnnotation "a" []] (GenericAnnotation "a" []) (GenericAnnotation "a" []) [AnnotationLiteral "Int"]),
    (LhsIdentifer "gt" sourcePos, OpenFunctionAnnotation [GenericAnnotation "a" [], GenericAnnotation "a" []] (AnnotationLiteral "Bool") (GenericAnnotation "a" []) [AnnotationLiteral "Int"]),
    (LhsIdentifer "gte" sourcePos, OpenFunctionAnnotation [GenericAnnotation "a" [], GenericAnnotation "a" []] (AnnotationLiteral "Bool") (GenericAnnotation "a" []) [AnnotationLiteral "Int"]),
    (LhsIdentifer "lt" sourcePos, OpenFunctionAnnotation [GenericAnnotation "a" [], GenericAnnotation "a" []] (AnnotationLiteral "Bool") (GenericAnnotation "a" []) [AnnotationLiteral "Int"]),
    (LhsIdentifer "lte" sourcePos, OpenFunctionAnnotation [GenericAnnotation "a" [], GenericAnnotation "a" []] (AnnotationLiteral "Bool") (GenericAnnotation "a" []) [AnnotationLiteral "Int"]),
    (LhsIdentifer "eq" sourcePos, OpenFunctionAnnotation [GenericAnnotation "a" [], GenericAnnotation "a" []] (AnnotationLiteral "Bool") (GenericAnnotation "a" []) [AnnotationLiteral "Int", AnnotationLiteral "Bool", AnnotationLiteral "String"]),
    (LhsIdentifer "neq" sourcePos, OpenFunctionAnnotation [GenericAnnotation "a" [], GenericAnnotation "a" []] (AnnotationLiteral "Bool") (GenericAnnotation "a" []) [AnnotationLiteral "Int", AnnotationLiteral "Bool", AnnotationLiteral "String"]),
    (LhsIdentifer "and" sourcePos, OpenFunctionAnnotation [GenericAnnotation "a" [], GenericAnnotation "a" []] (AnnotationLiteral "Bool") (GenericAnnotation "a" []) [AnnotationLiteral "Bool"]),
    (LhsIdentifer "or" sourcePos, OpenFunctionAnnotation [GenericAnnotation "a" [], GenericAnnotation "a" []] (AnnotationLiteral "Bool") (GenericAnnotation "a" []) [AnnotationLiteral "Bool"]),
    (LhsIdentifer "not" sourcePos, FunctionAnnotation [AnnotationLiteral "Bool"] (AnnotationLiteral "Bool")),
    (LhsIdentifer "neg" sourcePos, FunctionAnnotation [AnnotationLiteral "Int"] (AnnotationLiteral "Int"))
    ]

assumeProgram prog = assumeProgramMapping prog (Annotations Map.empty (Just $ Annotations baseMapping Nothing))

showPos :: SourcePos -> String
showPos (P.SourcePos s ln cn) = 
    "In file: " ++ s ++ ", at line: " ++ tail (dropWhile (/= ' ') (show ln)) ++ ", at colounm: " ++ tail (dropWhile (/= ' ') (show cn))

noTypeFound expected pos = "No type named " ++ expected ++ " found\n" ++ showPos pos
unmatchedType a b pos = "Can't match expected type " ++ show a ++ " with given type " ++ show b ++ "\n" ++ showPos pos

unionFrom :: Annotation -> Annotation -> Either a b -> Annotation
unionFrom a b x = 
    case x of
        Right _ -> b
        Left err -> createUnion a b

mergedTypeConcrete = mergedType (True, False, Map.empty) comparisionEither

mergedType :: (Bool, Bool, Map.Map String [Constraint]) -> ComparisionReturns String Annotation -> P.SourcePos -> UserDefinedTypes -> Annotation -> Annotation -> Annotation
mergedType _ crt pos _ a@AnnotationLiteral{} b@AnnotationLiteral{} = 
    if a == b then a else createUnion a b
mergedType gs crt pos mp a@(FunctionAnnotation as ret1) b@(FunctionAnnotation bs ret2) = 
    if length as == length bs then FunctionAnnotation (init ls) (last ls)
    else createUnion a b
    where ls = zipWith (mergedType gs crt pos mp) (as ++ [ret1]) (bs ++ [ret2])
mergedType gs crt pos mp a@(NewTypeInstanceAnnotation e1 as1) b@(NewTypeInstanceAnnotation e2 as2)
    | e1 == e2 && length as1 == length as2 = NewTypeInstanceAnnotation e1 ls
    | otherwise = createUnion a b
    where ls = zipWith (mergedType gs crt pos mp) as1 as2
mergedType gs crt pos mp a@(StructAnnotation ps1) b@(StructAnnotation ps2)
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
mergedType gs crt pos mp a@(TypeUnion as) b@(TypeUnion bs) = do
    case mapM_ (f mp $ Set.toList as) (Set.toList bs) of
        Right () -> b
        Left err -> createUnion a b
    where
        f mp ps2 v1 = join $ getFirst a b pos $ map (\x -> success crt <$> sameTypesGenericCrt gs crt pos mp x v1) ps2
mergedType gs crt pos mp a@(TypeUnion st) b = 
    case fromJust $ getFirst a b pos $ map (\x -> Just $ sameTypesGenericCrt gs crt pos mp x b) $ Set.toList st of
        Right _ -> a
        Left _ -> createUnion a b
mergedType gs crt pos mp a b@(TypeUnion st) = mergedType gs crt pos mp b a
mergedType gs crt pos mp (Annotation id1) b@(Annotation id2)
    | id1 == id2 = b
    | otherwise = case Map.lookup (LhsIdentifer id1 pos) mp of
        Just a -> case Map.lookup (LhsIdentifer id2 pos) mp of
            Just b -> unionFrom a b $ sameTypesGenericCrt gs crt pos mp a b
mergedType gs crt pos mp (Annotation id) b = 
    case Map.lookup (LhsIdentifer id pos) mp of
        Just a -> unionFrom a b $ sameTypesGenericCrt gs crt pos mp a b
mergedType gs crt pos mp b (Annotation id) = 
    case Map.lookup (LhsIdentifer id pos) mp of
        Just a -> unionFrom a b $ sameTypesGenericCrt gs crt pos mp a b
mergedType tgs@(_, sensitive, gs) crt pos mp a@(GenericAnnotation id1 cs1) b@(GenericAnnotation id2 cs2)
    | sensitive && id1 `Map.member` gs && id2 `Map.member` gs && id1 /= id2 = createUnion a b
    | otherwise = if id1 == id2 then unionFrom a b $ zipWithM (matchConstraint tgs crt pos mp) cs1 cs2 *> success crt a else createUnion a b
mergedType tgs@(_, sensitive, gs) crt pos mp a@(GenericAnnotation _ acs) b = 
    if sensitive then 
        unionFrom a b $ mapM (matchConstraint tgs crt pos mp (AnnotationConstraint b)) acs
    else createUnion a b
mergedType tgs@(_, sensitive, gs) crt pos mp b a@(GenericAnnotation _ acs) = 
    if sensitive then 
        unionFrom a b $ mapM (matchConstraint tgs crt pos mp (AnnotationConstraint b)) acs *> success crt a
    else createUnion a b
mergedType (considerUnions, sensitive, gs) crt pos mp ft@(OpenFunctionAnnotation anns1 ret1 forType impls) (OpenFunctionAnnotation anns2 ret2 _ _) =
    OpenFunctionAnnotation (init ls) (last ls) forType impls where 
        ls = zipWith (mergedType (considerUnions, sensitive, gs') crt pos mp) (anns1 ++ [ret1]) (anns2 ++ [ret2])
        gs' = genericsFromList (anns1 ++ [ret1]) `Map.union` gs 
mergedType (considerUnions, sensitive, gs) crt pos mp a@(OpenFunctionAnnotation anns1 ret1 _ _) (FunctionAnnotation args ret2) = 
    FunctionAnnotation (init ls) (last ls) where
        ls = zipWith (mergedType (considerUnions, sensitive, gs') crt pos mp) (anns1 ++ [ret1]) (args ++ [ret2])
        gs' = genericsFromList (anns1 ++ [ret1]) `Map.union` gs
mergedType _ crt pos _ a b = createUnion a b

sameTypesGenericCrt :: (Bool, Bool, Map.Map String [Constraint]) -> ComparisionReturns String Annotation -> P.SourcePos -> UserDefinedTypes -> Annotation -> Annotation -> Either String Annotation
sameTypesGenericCrt _ crt pos _ a@AnnotationLiteral{} b@AnnotationLiteral{} = 
    if a == b then success crt a else failout crt a b pos
sameTypesGenericCrt gs crt pos mp a@(FunctionAnnotation as ret1) b@(FunctionAnnotation bs ret2) = 
    if length as == length bs then (\xs -> FunctionAnnotation (init xs) (last xs)) <$> ls
    else failout crt a b pos
    where ls = zipWithM (sameTypesGenericCrt gs crt pos mp) (as ++ [ret1]) (bs ++ [ret2])
sameTypesGenericCrt gs crt pos mp a@(NewTypeInstanceAnnotation e1 as1) b@(NewTypeInstanceAnnotation e2 as2)
    | e1 == e2 && length as1 == length as2 = NewTypeInstanceAnnotation e1 <$> ls
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
sameTypesGenericCrt tgs@(considerUnions, _, _) crt pos mp a@(TypeUnion st) b
    | considerUnions =
        fromJust $ getFirst a b pos $ map (\x -> Just $ sameTypesGenericCrt tgs crt pos mp x b) $ Set.toList st
    | otherwise = Left $ unmatchedType a b pos
sameTypesGenericCrt tgs@(considerUnions, _, _) crt pos mp b a@(TypeUnion st) 
    | considerUnions =
        fromJust $ getFirst a b pos $ map (\x -> Just $ sameTypesGenericCrt tgs crt pos mp x b) $ Set.toList st
    | otherwise = Left $ unmatchedType a b pos
sameTypesGenericCrt gs crt pos mp (Annotation id1) b@(Annotation id2)
    | id1 == id2 = success crt b
    | otherwise = case Map.lookup (LhsIdentifer id1 pos) mp of
        Just a -> case Map.lookup (LhsIdentifer id2 pos) mp of
            Just b -> sameTypesGenericCrt gs crt pos mp a b
            Nothing -> failiure crt $ noTypeFound id2 pos
        Nothing -> failiure crt $ noTypeFound id1 pos
sameTypesGenericCrt gs crt pos mp (Annotation id) b = 
    case Map.lookup (LhsIdentifer id pos) mp of
        Just a -> sameTypesGenericCrt gs crt pos mp a b
        Nothing -> failiure crt $ noTypeFound id pos
sameTypesGenericCrt gs crt pos mp b (Annotation id) = 
    case Map.lookup (LhsIdentifer id pos) mp of
        Just a -> sameTypesGenericCrt gs crt pos mp a b
        Nothing -> failiure crt $ noTypeFound id pos
sameTypesGenericCrt tgs@(_, sensitive, gs) crt pos mp a@(GenericAnnotation id1 cs1) b@(GenericAnnotation id2 cs2)
    | sensitive && id1 `Map.member` gs && id2 `Map.member` gs && id1 /= id2 = Left $ "Expected " ++ show a ++ " but got " ++ show b
    | otherwise = if id1 == id2 then zipWithM (matchConstraint tgs crt pos mp) cs1 cs2 *> success crt a else failout crt a b pos
sameTypesGenericCrt tgs@(_, sensitive, gs) crt pos mp a@(GenericAnnotation _ acs) b = 
    if sensitive then 
        mapM (matchConstraint tgs crt pos mp (AnnotationConstraint b)) acs *> success crt b
    else Left $ unmatchedType a b pos
sameTypesGenericCrt tgs@(_, sensitive, gs) crt pos mp b a@(GenericAnnotation _ acs) = 
    if sensitive then 
        mapM (matchConstraint tgs crt pos mp (AnnotationConstraint b)) acs *> success crt a
    else Left $ unmatchedType a b pos
sameTypesGenericCrt (considerUnions, sensitive, gs) crt pos mp ft@(OpenFunctionAnnotation anns1 ret1 forType impls) (OpenFunctionAnnotation anns2 ret2 _ _) =
    (\xs -> OpenFunctionAnnotation (init xs) (last xs) forType impls) <$> ls where 
        ls = zipWithM (sameTypesGenericCrt (considerUnions, sensitive, gs') crt pos mp) (anns1 ++ [ret1]) (anns2 ++ [ret2])
        gs' = genericsFromList (anns1 ++ [ret1]) `Map.union` gs 
sameTypesGenericCrt (considerUnions, sensitive, gs) crt pos mp a@(OpenFunctionAnnotation anns1 ret1 _ _) (FunctionAnnotation args ret2) = 
    (\xs -> FunctionAnnotation (init xs) (last xs)) <$> ls where
        ls = zipWithM (sameTypesGenericCrt (considerUnions, sensitive, gs') crt pos mp) (anns1 ++ [ret1]) (args ++ [ret2])
        gs' = genericsFromList (anns1 ++ [ret1]) `Map.union` gs
sameTypesGenericCrt _ crt pos _ a b = failout crt a b pos

genericsFromList :: [Annotation] -> Map.Map String [Constraint]
genericsFromList anns = foldr1 Map.union (map getGenerics anns)

matchConstraint :: (Bool, Bool, Map.Map String [Constraint]) -> ComparisionReturns String Annotation -> SourcePos -> UserDefinedTypes -> Constraint -> Constraint -> Either String Constraint
matchConstraint gs crt pos mp c@(AnnotationConstraint a) (AnnotationConstraint b) = c <$ sameTypesGenericCrt gs crt pos mp a b
matchConstraint gs crt pos mp a@(ConstraintHas lhs cns) b@(AnnotationConstraint ann) = 
    case ann of
        StructAnnotation ds -> 
            if lhs `Map.member` ds then Right b
            else Left $ "Can't match " ++ show a ++ " with " ++ show b
        _ -> Left $ "Can't match " ++ show a ++ " with " ++ show b
matchConstraint gs crt pos mp c@(ConstraintHas a c1) (ConstraintHas b c2) = 
    if a /= b then Left $ "Can't match constraint " ++ show a ++ " with constraint " ++ show b ++ "\n" ++ showPos pos
    else c <$ matchConstraint gs crt pos mp c1 c2
matchConstraint gs crt pos mp a@(AnnotationConstraint ann) b@(ConstraintHas lhs cns) = matchConstraint gs crt pos mp b a

getGenerics :: Annotation -> Map.Map String [Constraint]
getGenerics (GenericAnnotation id cons) = Map.singleton id cons
getGenerics (OpenFunctionAnnotation anns ret _ _) = foldr1 Map.union (map getGenerics $ ret:anns)
getGenerics _ = Map.empty

comparisionEither :: ComparisionReturns String Annotation
comparisionEither = ComparisionReturns {
    success = Right,
    failiure = Left,
    failout = \a b pos -> Left $ unmatchedType a b pos
}

unionEither :: ComparisionReturns String Annotation
unionEither = ComparisionReturns {
    success = Right,
    failiure = Left,
    failout = \a b _ -> Right $ createUnion a b
}

createUnion (TypeUnion s1) (TypeUnion s2) = TypeUnion $ s1 `Set.union` s2
createUnion (TypeUnion s1) a = TypeUnion $ a `Set.insert` s1
createUnion a (TypeUnion s1) = TypeUnion $ a `Set.insert` s1
createUnion a b = TypeUnion $ Set.fromList [a, b]

sameTypesGeneric a = sameTypesGenericCrt a comparisionEither

sameTypes :: SourcePos -> UserDefinedTypes -> Annotation -> Annotation -> Either String Annotation
sameTypes = sameTypesGeneric (True, False, Map.empty)

getTypeMap :: State (a, (b, c)) c
getTypeMap = gets (snd . snd)

excludeFromUnion :: P.SourcePos -> Annotation -> Annotation -> AnnotationState Annotation
excludeFromUnion pos a (TypeUnion ts) = do
    (_, (_, usts)) <- get
    return . TypeUnion . Set.fromList . remove . Set.toList $ Set.map (\b -> (sameTypes pos usts a b, b)) ts where
    remove [] = []
    remove ((Right a, _):xs) = remove xs
    remove ((Left _, a):xs) = a : remove xs

accessNewType givenArgs f g fid@(LhsIdentifer id pos) = do
            mp <- getTypeMap
            case Map.lookup fid mp of
                Just x@(NewTypeAnnotation id args map) -> 
                    case substituteVariables pos (collectGenenrics mp x) Map.empty (Map.fromList $ zip args givenArgs) mp x of
                        Right x -> f x
                        Left err -> return . Left $ err
                Just a -> g a
                Nothing -> return . Left $ noTypeFound id pos

consistentTypes ::  Node -> AnnotationState (Either String Annotation)
consistentTypes (DeclN (Decl lhs rhs _ pos)) = (\a b m -> join $ sameTypes pos m <$> a <*> b)
    <$> getAnnotationState lhs <*> consistentTypes rhs <*> getTypeMap
consistentTypes (DeclN (Assign (LhsAccess access prop accPos) rhs pos)) = (\a b m -> join $ sameTypes pos m <$> a <*> b)
    <$> getAssumptionType (Access access prop accPos) <*> consistentTypes rhs <*> getTypeMap
consistentTypes (DeclN (Assign lhs rhs pos)) = (\a b m -> join $ sameTypes pos m <$> a <*> b) 
    <$> getAnnotationState lhs <*> consistentTypes rhs <*> getTypeMap
consistentTypes (DeclN (FunctionDecl lhs ann pos)) = do
    m <- getTypeMap
    l <- getAnnotationState lhs
    case l of
        Right l -> return $ sameTypes pos m ann l 
        Left err -> return $ Left err
consistentTypes (DeclN (ImplOpenFunction lhs args (Just ret) exprs _ pos)) = consistentTypes $ FunctionDef args (Just ret) exprs pos
consistentTypes (DeclN (ImplOpenFunction lhs args Nothing exprs implft pos)) = do
    a <- getAnnotationState lhs
    mp <- getTypeMap
    case a of
        Left err -> return $ Left err
        Right fun@(OpenFunctionAnnotation anns ret' ft impls) -> do
            let (specificationRules, rels) = getPartialNoUnderScoreSpecificationRules pos Map.empty mp fun (FunctionAnnotation (map snd args) (AnnotationLiteral "_"))
            case substituteVariables pos (Set.unions $ map (collectGenenrics mp . snd) args) rels specificationRules mp ret' of
                Left err -> return . Left $ "Could not infer the return type: " ++ err ++ "\n" ++ showPos pos
                Right inferredRetType ->
                    case specify pos Map.empty mp fun (makeFunAnnotation args inferredRetType) of
                        Left err -> return $ Left err
                        Right ann -> consistentTypes $ FunctionDef args (Just inferredRetType) exprs pos
        Right a -> return . Left $ "Cannot extend function " ++ show a ++ "\n" ++ showPos pos
consistentTypes (DeclN (OpenFunctionDecl lhs ann pos)) =  do
    m <- getTypeMap
    l <- getAnnotationState lhs
    case l of
        Right l -> return $ sameTypes pos m ann l 
        Left err -> return $ Left err
consistentTypes (IfExpr cond t e pos) = do
    m <- getTypeMap
    c <- consistentTypes cond
    case c >>= \x -> sameTypes pos m x (AnnotationLiteral "Bool") of
        Right _ -> (\a b -> mergedTypeConcrete pos m <$> a <*> b) <$> consistentTypes t <*> consistentTypes e
        Left err -> return $ Left err
consistentTypes (CreateNewType lhs@(LhsIdentifer id _) args pos) = do
    mp <- getTypeMap
    argsn <- sequence <$> mapM consistentTypes args
    case argsn of
        Right as -> return $ case Map.lookup lhs mp of
            Just (NewTypeAnnotation id anns _) -> 
                if length anns == length args then NewTypeInstanceAnnotation id <$> argsn
                else Left $ "Can't match arguments " ++ show as ++ " with " ++ show anns ++ "\n" ++ showPos pos
            Just a -> Left $ show a ++ " is not an instantiable type" ++ showPos pos
            Nothing -> Left $ noTypeFound id pos
        Left err -> return $ Left err
consistentTypes (DeclN (Expr n)) = consistentTypes n
consistentTypes (IfStmnt (RemoveFromUnionNode lhs ann _) ts es pos) = do
    (_, (_, mp)) <- get
    pushScope
    typLhs <- getAnnotationState lhs
    case typLhs of
        Right union@TypeUnion{} ->  do
            insertAnnotation lhs . Finalizeable False =<< excludeFromUnion pos ann union
            mapM_ getAssumptionType ts
            t <- sequence <$> mapM consistentTypes ts
            popScope
            pushScope
            insertAnnotation lhs (Finalizeable False ann)
            mapM_ getAssumptionType es
            e <- sequence <$> mapM consistentTypes es
            popScope
            let res = case (t, e) of
                    (Right b, Right c) -> Right $ AnnotationLiteral "_"
                    (Left a, _) -> Left a
                    (_, Left a) -> Left a
            return res
        _ -> return . Left $ expectedUnion pos lhs typLhs
consistentTypes (IfStmnt (CastNode lhs ann _) ts es pos) = do
    (_, (_, mp)) <- get
    pushScope
    insertAnnotation lhs (Finalizeable False ann)
    mapM_ getAssumptionType ts
    t <- sequence <$> mapM consistentTypes ts
    popScope
    pushScope
    typLhs <- getAnnotationState lhs
    case typLhs of
        Right ts@TypeUnion{} -> insertAnnotation lhs . Finalizeable False =<< excludeFromUnion pos ann ts
        _ -> return ann
    mapM_ getAssumptionType es
    e <- sequence <$> mapM consistentTypes es
    popScope
    let res = case (t, e) of
            (Right b, Right c) -> Right $ AnnotationLiteral "_"
            (Left a, _) -> Left a
            (_, Left a) -> Left a
    return res
consistentTypes (IfStmnt cond ts es pos) = do
    (_, (_, mp)) <- get
    c <- consistentTypes cond
    case sameTypes pos mp (AnnotationLiteral "Bool") <$> c of
        Right _ -> do
            c <- consistentTypes cond
            pushScope
            mapM_ getAssumptionType ts
            t <- sequence <$> mapM consistentTypes ts
            popScope
            pushScope
            mapM_ getAssumptionType es
            e <- sequence <$> mapM consistentTypes es
            popScope
            let res = case (c, t, e) of
                    (Right a, Right b, Right c) -> Right $ AnnotationLiteral "_"
                    (Left a, _, _) -> Left a
                    (_, Left a, _) -> Left a
                    (_, _, Left a) -> Left a
            return res
        Left err -> return $ Left err
consistentTypes (StructN (Struct ns _)) = (\case
    Right a -> return . Right $ StructAnnotation a
    Left err -> return $ Left err) . sequence =<< mapM consistentTypes ns
consistentTypes (Access st p pos) = do
    mp <- getTypeMap
    f mp =<< getTypeStateFrom (consistentTypes st) pos where 
    
    f :: UserDefinedTypes -> Either String Annotation -> AnnotationState (Either String Annotation)
    f mp = \case
            Right g@(GenericAnnotation _ cns) -> return $ genericHas pos g p cns
            Right (TypeUnion st) -> ((\x -> head <$> mapM (sameTypes pos mp (head x)) x) =<<) <$> x where 
                x = sequence <$> mapM (\x -> f mp =<< getTypeState x pos) stl
                stl = Set.toList st
            Right (NewTypeInstanceAnnotation id anns) -> 
                accessNewType anns
                (\(NewTypeAnnotation _ _ ps) -> return $ toEither ("Could not find " ++ show p ++ " in " ++ show ps ++ "\n" ++ showPos pos) (Map.lookup p ps)) 
                (\a -> return . Left $ "Cannot get " ++ show p ++ " from type " ++ show a ++ "\n" ++ showPos pos)
                (LhsIdentifer id pos)
            Right (StructAnnotation ps) -> return $ toEither ("Could not find " ++ show p ++ " in " ++ show ps ++ "\n" ++ showPos pos) (Map.lookup p ps)
            Right a -> return . Left $ "Cannot get " ++ show p ++ " from type " ++ show a ++ "\n" ++ showPos pos
            Left err -> return $ Left err
consistentTypes (FunctionDef args ret body pos) = 
    case ret of
        Just ret -> do
            scope <- get
            finalizeAnnotationState
            (a, (ans, mp)) <- get
            mp <- getTypeMap
            let program = Program body
            let ans' = (a, (assumeProgramMapping program (Annotations (Map.fromList $ (LhsIdentifer "return" pos, Finalizeable True ret):map (second (Finalizeable True)) args) (Just ans)) mp, mp))
            put ans'
            xs <- sequence <$> mapM consistentTypes body
            s <- getAnnotationState (LhsIdentifer "return" pos)
            put scope
            case s of
                Right ret' -> case xs of
                    Right _ -> return (sameTypes pos mp (makeFunAnnotation args ret) (makeFunAnnotation args ret'))
                    Left err -> return . Left $ err
                Left err -> return $ Left err
        Nothing -> do
            scope <- get
            finalizeAnnotationState
            (a, (old_ans, mp)) <- get
            let program = Program body
            let ans = (a, (assumeProgramMapping program (Annotations (Map.fromList $ (LhsIdentifer "return" pos, Finalizeable False $ AnnotationLiteral "_"):map (second (Finalizeable True)) args) (Just old_ans)) mp, mp))
            put ans
            xs <- sequence <$> mapM consistentTypes body
            (_, (new_ans, _)) <- get
            case xs of
                Right _ ->
                    (\case
                        Right ret -> case getAnnotation (LhsIdentifer "return" pos) new_ans of
                            Right (Finalizeable _ ret') -> do
                                typ <- consistentTypes ret
                                put scope
                                return $ Right $ makeFunAnnotation args ret'
                            Left err -> return $ Left err
                        Left err -> return $ Left err) =<< firstInferrableReturn pos body
                Left err -> return $ Left err
consistentTypes (Return n pos) = consistentTypes n >>= \x -> makeUnionIfNotSame pos x (getAnnotationState lhs) lhs
    where lhs = LhsIdentifer "return" pos
consistentTypes (Call e args pos) =  (\case 
                    Right fann@(FunctionAnnotation fargs ret) -> do
                        mp <- getTypeMap
                        anns <- sequence <$> mapM consistentTypes args
                        case anns of
                            Right anns -> let 
                                (spec, rels) = getPartialNoUnderScoreSpecificationRules pos Map.empty mp fann (FunctionAnnotation anns (AnnotationLiteral "_")) in
                                case substituteVariables pos (Set.unions $ map (collectGenenrics mp) anns) rels spec mp ret of
                                    Right ret' -> case specify pos Map.empty mp fann (FunctionAnnotation anns ret') of
                                        Right r -> return $ Right ret'
                                        Left err -> return $ Left err
                                    Left err -> return $ Left err
                            Left err -> return $ Left err                    
                    Right opf@(OpenFunctionAnnotation oanns oret ft impls) -> do
                        mp <- getTypeMap
                        anns <- sequence <$> mapM consistentTypes args
                        case anns of
                            Right anns -> let 
                                (spec, rel) = getPartialNoUnderScoreSpecificationRules pos Map.empty mp (FunctionAnnotation oanns oret) (FunctionAnnotation anns (AnnotationLiteral "_")) in
                                case substituteVariables pos (Set.unions $ map (collectGenenrics mp) anns) rel spec mp oret of
                                    Right ret' -> case getSpecificationRules pos Map.empty mp (FunctionAnnotation oanns oret) (FunctionAnnotation anns ret') of
                                        Right base -> case Map.lookup ft base of
                                            Just a -> maybe 
                                                    (return . Left $ "Could find instance " ++ show opf ++ " for " ++ show a ++ "\n" ++ showPos pos) 
                                                    (const . return $ Right ret')
                                                    (find (\b -> specifyTypesBool pos base mp b a) impls)
                                            Nothing -> return . Left $ "The argument does not even once occur in the whole method\n" ++ showPos pos
                                        Left err -> return $ Left err
                                    Left err -> return $ Left err
                            Left err -> return $ Left err       
                    Right ann -> return . Left $ "Can't call a value of type " ++ show ann ++ "\n" ++ showPos pos
                    Left err -> return $ Left err) =<< getTypeStateFrom (getAssumptionType e) pos
consistentTypes (Identifier x pos) = getAnnotationState (LhsIdentifer x pos)
consistentTypes (Lit (LitInt _ _)) = return . Right $ AnnotationLiteral "Int"
consistentTypes (Lit (LitBool _ _)) = return . Right $ AnnotationLiteral "Bool"
consistentTypes (Lit (LitString _ _)) = return . Right $ AnnotationLiteral "String"
consistentTypes a = error $ show a

onlyTypeDecls :: Node -> Bool
onlyTypeDecls (DeclN StructDef{}) = True
onlyTypeDecls (DeclN NewTypeDecl{}) = True
onlyTypeDecls _ = False

typeNodes :: [Node] -> ([Node], [Node])
typeNodes = partition onlyTypeDecls

typeMap :: [Node] -> Map.Map Lhs (Annotation, P.SourcePos)
typeMap xs = Map.fromList $ map makeTup xs where
    makeTup (DeclN (StructDef lhs rhs pos)) = (lhs, (rhs, pos))
    makeTup (DeclN (NewTypeDecl lhs rhs pos)) = (lhs, (rhs, pos))

allExists :: Map.Map Lhs (Annotation, P.SourcePos) -> Either String ()
allExists mp = mapM_ (exists mp) mp where
    exists :: Map.Map Lhs (Annotation, P.SourcePos) -> (Annotation, P.SourcePos) -> Either String ()
    exists mp (NewTypeAnnotation{}, pos) = Right ()
    exists mp (NewTypeInstanceAnnotation id anns1, pos) = case Map.lookup (LhsIdentifer id pos) mp of
        Just (NewTypeAnnotation id anns2 _, pos) -> if length anns1 == length anns2 then Right () else Left $ "Unequal arguments " ++ show anns1 ++ " can't be matched with " ++ show anns2
        Just a -> Left $ "Cannot instantiate " ++ show a ++ "\n" ++ showPos pos
        Nothing -> Left $ noTypeFound id pos
    exists mp (Annotation id, pos) = 
        case Map.lookup (LhsIdentifer id pos) mp of
            Just _ -> Right ()
            Nothing -> Left $ noTypeFound id pos
    exists mp (AnnotationLiteral lit, pos) = Right ()
    exists mp (FunctionAnnotation as ret, pos) = mapM_ (exists mp . (, pos)) as >> exists mp (ret, pos)
    exists mp (TypeUnion s, pos) = mapM_ (exists mp . (, pos)) (Set.toList s)
    exists mp (OpenFunctionAnnotation anns ret ftr _, pos) = mapM_ (exists mp . (, pos)) $ [ftr, ret] ++ anns
    exists mp (StructAnnotation xs, pos) = mapM_ (exists mp . (, pos)) (Map.elems xs)
    exists mp (GenericAnnotation _ cns, pos) = mapM_ (constraintExists mp . (, pos)) cns where 
        constraintExists mp (ConstraintHas _ cn, pos) = constraintExists mp (cn, pos)
        constraintExists mp (AnnotationConstraint ann, pos) = exists mp (ann, pos)

newTypeName :: P.SourcePos -> DefineTypesState Lhs
newTypeName pos = do
    s <- get
    (a, ((i, b), c)) <- get
    put (a, ((i+1, b), c))
    return $ LhsIdentifer ("auto_generated_type_" ++ show i) pos

defineSingleType :: P.SourcePos -> Annotation -> DefineTypesState Annotation
defineSingleType pos f@FunctionAnnotation{} = return f
defineSingleType pos lit@AnnotationLiteral{} = return lit
defineSingleType pos f@OpenFunctionAnnotation{} = return f
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
        addToMap :: Lhs -> Annotation -> DefineTypesState ()
        addToMap tn ann = do
            (a, ((i, b), mp)) <- get
            let new_mp = Map.insert ann tn mp
            put (a, ((i, b), new_mp))

        modifyAnnotations :: Lhs -> Annotation -> DefineTypesState ()
        modifyAnnotations tn ann = do
            (a, ((i, anns), mp)) <- get
            new_anns <- f (invertUserDefinedTypes mp) anns
            put (a, ((i, new_anns), mp))
            where 
                f mp (CompleteAnnotations anns rest) = CompleteAnnotations <$> sequence (
                    Map.map (\ann2 -> if isRight $ sameTypesImpl ann2 pos mp ann ann2 then return . Annotation $ show tn else defineSingleType pos ann2) anns
                    ) <*> sequence (f mp <$> rest)

defineTypesState :: CompleteAnnotations -> DefineTypesState CompleteAnnotations
defineTypesState (CompleteAnnotations anns rest) = CompleteAnnotations
  <$> sequence (Map.mapWithKey (\(LhsIdentifer _ pos) v -> defineSingleType pos v) anns)
  <*> sequence (defineTypesState <$> rest)

defineAllTypes :: UserDefinedTypes -> CompleteAnnotations -> (UserDefinedTypes, CompleteAnnotations)
defineAllTypes usts anns = (invertUserDefinedTypes $ snd $ snd st, snd . fst . snd $ st) where 
    st = execState (defineTypesState anns) (AnnotationLiteral "_", ((0, anns), invertUserDefinedTypes usts))

removeFinalization :: Annotations -> CompleteAnnotations
removeFinalization (Annotations anns Nothing) = CompleteAnnotations (Map.map fromFinalizeable anns) Nothing
removeFinalization (Annotations anns rest) = CompleteAnnotations (Map.map fromFinalizeable anns) (removeFinalization <$> rest)

invertUserDefinedTypes :: Ord k => Map.Map a k -> Map.Map k a
invertUserDefinedTypes usts = Map.fromList $ Map.elems $ Map.mapWithKey (curry swap) usts

typeCheckedScope :: [Node] -> Either String (UserDefinedTypes, CompleteAnnotations)
typeCheckedScope program = 
    do
        allExists typesPos
        case runState (mapM getAssumptionType (earlyReturnToElse lifted)) (AnnotationLiteral "_", (assumeProgram (Program $ earlyReturnToElse lifted) types, types)) of
            (res, (a, map@(_, usts))) -> case sequence_ res of
                Left err -> Left err 
                Right () -> res >> Right (defineAllTypes usts (removeFinalization as)) where
                    res = sequence f
                    (_, (as, _)) = s
                    (f, s) = runState (mapM consistentTypes (earlyReturnToElse lifted)) (a, map)
    where 
        lifted = evalState (liftLambda restProgram) (0, [])
        (metProgram, restProgram) = typeNodes program
        typesPos = typeMap metProgram
        types = Map.map fst typesPos

parseFile :: String -> [Char] -> Either String (UserDefinedTypes, CompleteAnnotations)
parseFile fn text = 
    case P.runParser Parser.wholeProgramParser fn (filter (/= '\t') text) of
        Right ns -> typeCheckedScope ns
        Left e -> Left $ P.errorBundlePretty e

main :: IO ()
main = do
    text <- readFile "test.junu"
    case parseFile "test.junu" text of
        Right (usts, as) -> printUsts usts *> print (f as)
        Left a -> putStrLn a
    where 
        p (LhsIdentifer k _) _
            | null $ tail k = True
            | head k == '_' && head (tail k) == '_' = False
            | otherwise = True
        p a _ = error $ "Unexpected pattern " ++ show a
        f (CompleteAnnotations mp r) = CompleteAnnotations (Map.filterWithKey p mp) r

        printUsts :: UserDefinedTypes -> IO ()
        printUsts usts = sequence_ $ Map.mapWithKey (\k v -> putStrLn $ show k ++ " = " ++ show v) usts