{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
module Main where

import qualified Data.Map as Map
import Control.Monad
import Data.List
import Debug.Trace ( trace )
import Control.Monad.State
import Text.Megaparsec as P hiding (State)
import Text.Megaparsec.Pos (mkPos)
import Data.Functor
import qualified Data.Set as Set
import Data.Maybe
import qualified Parser
import Nodes

insertAnnotation :: Lhs -> Annotation -> AnnotationState Annotation
insertAnnotation k v = modify (\(a, (Annotations b o, m)) -> (a, (Annotations (Map.insert k v b) o, m))) >> return v

getAnnotation :: Lhs -> Annotations -> Result String Annotation
getAnnotation k@(LhsIdentifer _ pos) (Annotations anns rest) = do
    case Map.lookup k anns of
        Just v -> Right v
        Nothing -> 
            case rest of
                Just rs -> getAnnotation k rs
                Nothing -> Left $ show k ++ " not found in this scope\n" ++ showPos pos

getAnnotationState :: Lhs -> AnnotationState (Result String Annotation)
getAnnotationState k = get >>= \(_, (anns, _)) -> return $ getAnnotation k anns

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
isGeneric pos mp (FunctionAnnotation args ret) = all (isGeneric pos mp) (ret:args)
isGeneric pos mp (StructAnnotation ms) = all (isGeneric pos mp) ms
isGeneric pos mp OpenFunctionAnnotation{} = False

substituteConstraints :: SourcePos -> TypeRelations -> Map.Map Annotation Annotation -> UserDefinedTypes -> Constraint -> Either String  Constraint
substituteConstraints pos rels mp usts (ConstraintHas lhs cs) = ConstraintHas lhs <$> substituteConstraints pos rels mp usts cs 
substituteConstraints pos rels mp usts (AnnotationConstraint ann) = AnnotationConstraint <$> substituteVariables pos rels mp usts ann

substituteVariables :: SourcePos -> TypeRelations -> Map.Map Annotation Annotation -> UserDefinedTypes -> Annotation -> Either String Annotation
substituteVariables pos rels mp usts fid@(GenericAnnotation id cns) = 
    maybe (GenericAnnotation id <$> mapM (substituteConstraints pos rels mp usts) cns) (
        \x -> case firstPreferablyDefinedRelation pos mp rels x of
            Right a -> Right a
            Left _ -> Right x
    ) (Map.lookup fid mp)
substituteVariables pos rels mp usts id@AnnotationLiteral{} = Right id
substituteVariables pos rels mp usts fid@(Annotation id) = maybe (Left $ noTypeFound id pos) Right (Map.lookup (LhsIdentifer id pos) usts)
substituteVariables pos rels mp usts (NewTypeAnnotation id anns annMap) = NewTypeAnnotation id <$> mapM (substituteVariables pos rels mp usts) anns <*> mapM (substituteVariables pos rels mp usts) annMap
substituteVariables pos rels mp usts (NewTypeInstanceAnnotation id anns) = NewTypeInstanceAnnotation id <$> mapM (substituteVariables pos rels mp usts) anns
substituteVariables pos rels mp usts (FunctionAnnotation args ret) = FunctionAnnotation <$> mapM (substituteVariables pos rels mp usts) args <*> substituteVariables pos rels mp usts ret
substituteVariables pos rels mp usts (StructAnnotation ms) = StructAnnotation <$> mapM (substituteVariables pos rels mp usts) ms
substituteVariables pos rels mp usts (TypeUnion ts) = TypeUnion . Set.fromList <$> mapM (substituteVariables pos rels mp usts) (Set.toList ts)
substituteVariables pos rels mp usts OpenFunctionAnnotation{} = error "Can't use substituteVariables with open functions"

getLookupTypeIfAvailable :: Annotation -> SubstituteState Annotation
getLookupTypeIfAvailable k = do
    (a, ((rs, mp), usts)) <- get
    case Map.lookup k mp of
        Just k -> getLookupTypeIfAvailable k
        Nothing -> return k

changeType :: P.SourcePos -> Annotation -> Annotation -> SubstituteState (Either String ())
changeType pos k v = do
    (a, ((rel, mp), usts)) <- get
    case substituteVariables pos rel mp usts v of
        Right sub -> put (a, ((rel, Map.insert k sub mp), usts)) $> Right ()
        Left err -> return $ Left err

reshuffleTypes :: P.SourcePos -> SubstituteState ()
reshuffleTypes pos = (\(_, ((_, mp), _)) -> sequence_ $ Map.mapWithKey (changeType pos) mp) =<< get

firstPreferablyDefinedRelation pos mp rs k =
    case Map.lookup k rs of
        Just s -> if Set.null stf then Right $ Set.elemAt 0 s else Right $ Set.elemAt 0 stf where stf = Set.filter (\x -> isJust (Map.lookup x mp)) s
        Nothing -> Left $ "No relation of generic " ++ show k ++ " found\n" ++ showPos pos

addTypeVariableGeneralized pos stmnt k v =  do
    (a, ((rs, mp), usts)) <- get
    case Map.lookup k mp of
        Nothing -> addToMap a rs mp usts k v
        Just a -> do
            case sameTypes pos usts a v of
                Left err -> if a == AnnotationLiteral "_" then addToMap a rs mp usts k v else 
                    case Map.lookup k rs of
                        Just st -> if Set.member v st then addToMap a rs mp usts k v else return $ Left err
                        Nothing -> return $ Left err
                Right a -> addToMap a rs mp usts k v
        where 
            addToMap a rs mp usts k v = do
                put (a, ((rs, Map.insert k v mp), usts))
                stmnt
                reshuffleTypes pos
                return $ Right v

addTypeVariable :: SourcePos -> Annotation -> Annotation -> SubstituteState (Either String Annotation)
addTypeVariable pos = addTypeVariableGeneralized pos (updateRelations pos)

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
            f = addTypeVariableGeneralized pos (return $ Right ())

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
specifyInternal pos a@(GenericAnnotation id1 cns1) b@(GenericAnnotation id2 cns2) = 
    if and $ zipWith (==) cns1 cns2 then
        addRelation pos b a *> addRelation pos a b $> Right b
    else undefined
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


sameTypesGenericBool gs pos mp a b = case sameTypesGeneric gs pos mp a b of
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

getAssumptionType :: Node -> AnnotationState (Result String Annotation)
getAssumptionType (DeclN (Decl lhs n a _)) = case a of 
    Just a -> Right <$> insertAnnotation lhs a
    Nothing -> mapRight (getAssumptionType n) (fmap Right . insertAnnotation lhs)
getAssumptionType (DeclN (FunctionDecl lhs ann _)) = Right <$> insertAnnotation lhs ann
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
getAssumptionType (DeclN (OpenFunctionDecl lhs ann _)) = Right <$> insertAnnotation lhs ann
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
                                        Right <$> insertAnnotation lhs (OpenFunctionAnnotation anns ret' ft $ implft:impls)
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
                    case substituteVariables pos rels specificationRules mp ret' of
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
                                        Right <$> insertAnnotation lhs (OpenFunctionAnnotation anns ret' ft $ implft:impls)
                                    else return . Left $ "Forbidden to specify specified type variables\n" ++ showPos pos
                Left err -> return $ Left err
        Right a -> return . Left $ "Cannot extend function " ++ show a ++ "\n" ++ showPos pos
getAssumptionType (DeclN (Assign (LhsAccess access prop accPos) expr pos)) = 
    getTypeStateFrom (getAssumptionType (Access access prop accPos)) pos
getAssumptionType (DeclN (Assign lhs n _)) = mapRight (getAssumptionType n) (fmap Right . insertAnnotation lhs)
getAssumptionType (CastNode lhs ann _) = Right <$> (insertAnnotation lhs ann $> AnnotationLiteral "Bool")
getAssumptionType (RemoveFromUnionNode lhs ann pos) =
    (\case
        Right a@TypeUnion{} -> (return . Right $ AnnotationLiteral "Bool") <$ insertAnnotation lhs =<< excludeFromUnion pos ann a
        Right a -> return . Left $ expectedUnion pos lhs ann
        Left err -> return $ Left err) =<< getAnnotationState lhs
getAssumptionType (DeclN (Expr n)) = getAssumptionType n
getAssumptionType (Return n pos) = getAssumptionType n
getAssumptionType (IfStmnt cond ts es pos) = return . Right $ AnnotationLiteral "_"
getAssumptionType (IfExpr c t e _) = getAssumptionType t
getAssumptionType (FunctionDef args ret body pos) = 
    case ret of
        Just ret -> return . Right $ makeFunAnnotation args ret
        Nothing -> do
            whole_old_ans@(a, (old_ans, mp)) <- get
            let program = Program body
            let ans = (a, (assumeProgramMapping program (Annotations (Map.fromList args) (Just old_ans)) mp, mp))
            put ans
            mapM_ getAssumptionType body
            (new_ans, _) <- gets snd
            x <- firstInferrableReturn pos body
            case x of
                Right ret -> do
                    typ <- getAssumptionType ret
                    put whole_old_ans
                    return (makeFunAnnotation args <$> typ)
                Left err -> return . Left $ err
getAssumptionType (Call e args pos) = (\case
                    Right fann@(FunctionAnnotation fargs ret) -> do
                        mp <- getTypeMap
                        anns <- sequence <$> mapM consistentTypes args
                        case anns of
                            Right anns -> let 
                                (spec, rel) = getPartialNoUnderScoreSpecificationRules pos Map.empty mp fann (FunctionAnnotation anns (AnnotationLiteral "_")) in
                                case substituteVariables pos rel spec mp ret of
                                    Right ret' -> case specify pos Map.empty mp fann (FunctionAnnotation anns ret') of
                                        Right _ -> return $ Right ret'
                                        Left err -> return $ Left err
                                    Left err -> return $ Left err
                            Left err -> return $ Left err
                    Right opf@(OpenFunctionAnnotation oanns oret ft impls) -> 
                        do
                            mp <- getTypeMap
                            anns <- sequence <$> mapM consistentTypes args
                            case anns of
                                Right anns -> do
                                    let f = FunctionAnnotation anns (AnnotationLiteral "_")
                                    let (spec, rels) = getPartialNoUnderScoreSpecificationRules pos Map.empty mp opf f
                                    case Map.lookup oret spec of
                                        Just ret' -> 
                                            case getSpecificationRules pos Map.empty mp opf $ FunctionAnnotation anns ret' of
                                                Right base -> case Map.lookup ft base of
                                                    Just a -> maybe 
                                                        (return . Left $ "Could find instance " ++ show opf ++ " for " ++ show a ++ "\n" ++ showPos pos) 
                                                        (const $ return $ Right ret')
                                                        (find (\b -> specifyTypesBool pos base mp b a) impls)
                                                    Nothing -> return . Left $ "The argument does not even once occur in the whole method\n" ++ showPos pos
                                                Left err -> return $ Left err
                                        Nothing -> case substituteVariables pos rels spec mp oret of
                                            Right ret -> return $ Right ret
                                            Left err -> if isGeneric pos mp oret then return . Left $ "Can't call " ++ show opf ++ " with arguments " ++ show anns ++ "\n" ++ showPos pos else return $ Right oret
                                Left err -> return $ Left err
                    Right ann -> return . Left $ "Can't call a value of type " ++ show ann ++ "\n" ++ showPos pos
                    Left err -> return $ Left err) =<< getTypeStateFrom (getAssumptionType e) pos
getAssumptionType (StructN (Struct ns _)) = 
    (\xs -> 
        mapRight 
            (return . Right $ AnnotationLiteral "_") 
            (const . return . Right . StructAnnotation $ Map.map (\(Right a) -> a) xs)) =<< mapM getAssumptionType ns
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

genericHas pos g givenLhs [] = Left $ "Could not find " ++ show givenLhs ++ " in " ++ show g ++ "\n" ++ showPos pos
genericHas pos g givenLhs ((ConstraintHas lhs (AnnotationConstraint ann)):xs) = if lhs == givenLhs then Right ann else genericHas pos g givenLhs xs

makeAssumptions :: State (Annotation, b) a -> b -> b
makeAssumptions s m = snd $ execState s (AnnotationLiteral "_", m)

assumeProgramMapping :: Program -> Annotations -> UserDefinedTypes -> Annotations
assumeProgramMapping (Program xs) anns mp = fst $ makeAssumptions (mapM getAssumptionType $ filter nonDecls xs) (anns, mp)

nonDecls (DeclN Decl{}) = True
nonDecls (DeclN FunctionDecl{}) = True
nonDecls _ = False

sourcePos = SourcePos "core" (mkPos 0) (mkPos 0)

baseMapping = Map.fromList [
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

assumeProgram prog = assumeProgramMapping prog (Annotations baseMapping Nothing)

showPos :: SourcePos -> String
showPos (P.SourcePos s ln cn) = 
    "In file: " ++ s ++ ", at line: " ++ tail (dropWhile (/= ' ') (show ln)) ++ ", at colounm: " ++ tail (dropWhile (/= ' ') (show cn))

noTypeFound expected pos = "No type named " ++ expected ++ " found\n" ++ showPos pos
unmatchedType a b pos = "Can't match expected type " ++ show a ++ " with given type " ++ show b ++ "\n" ++ showPos pos

sameTypesGeneric :: (Bool, Map.Map String [Constraint]) -> P.SourcePos -> UserDefinedTypes -> Annotation -> Annotation -> Either String Annotation
-- sameTypesGeneric _ pos _ (AnnotationLiteral "_") (AnnotationLiteral "_") = error $ "Unexpected case\n" ++ showPos pos
-- sameTypesGeneric _ pos _ (AnnotationLiteral "_") b = Right b
-- sameTypesGeneric _ pos _ a (AnnotationLiteral "_") = Right a
sameTypesGeneric _ pos _ a@AnnotationLiteral{} b@AnnotationLiteral{} = 
    if a == b then Right a else Left $ unmatchedType a b pos
sameTypesGeneric gs pos mp a@(FunctionAnnotation as ret1) b@(FunctionAnnotation bs ret2) = 
    if length as == length bs then (\xs -> FunctionAnnotation (init xs) (last xs)) <$> ls
    else Left $ unmatchedType a b pos
    where ls = zipWithM (sameTypesGeneric gs pos mp) (as ++ [ret1]) (bs ++ [ret2])
sameTypesGeneric gs pos mp a@(NewTypeInstanceAnnotation e1 as1) b@(NewTypeInstanceAnnotation e2 as2)
    | e1 == e2 && length as1 == length as2 = NewTypeInstanceAnnotation e1 <$> ls
    | otherwise = Left $ unmatchedType a b pos 
    where ls = zipWithM (sameTypesGeneric gs pos mp) as1 as2
sameTypesGeneric gs pos mp a@(TypeUnion as) b@(TypeUnion bs)
    | Set.size as /= Set.size bs = Left $ unmatchedType a b pos
    | isJust ls = maybe (Left $ unmatchedType a b pos) Right (TypeUnion . Set.fromList <$> ls)
    where
        ls = mapM (f as) (Set.toList bs)
        f ps2 v1 = find (sameTypesGenericBool gs pos mp v1) ps2
sameTypesGeneric gs pos mp a@(StructAnnotation ps1) b@(StructAnnotation ps2)
    | Map.empty == ps1 || Map.empty == ps2 = if ps1 == ps2 then Right a else Left $ unmatchedType a b pos
    | Map.size ps1 /= Map.size ps2 = Left $ unmatchedType a b pos
    | isJust $ sequence ls = maybe (Left $ unmatchedType a b pos) Right (StructAnnotation <$> (sequence ls))
    | otherwise = Left $ unmatchedType a b pos
    where
        ls = Map.mapWithKey (f ps1) ps2
        f ps2 k v1 = 
            case Map.lookup k ps2 of
                Just v2
                    -> case sameTypesGeneric gs pos mp v1 v2 of
                        Right a -> Just a
                        Left err -> Nothing
                Nothing -> Nothing
sameTypesGeneric gs pos mp a@(TypeUnion as) b@(TypeUnion bs) = do
    case mapM (f mp $ Set.toList as) (Set.toList bs) of
        Right s -> Right $ TypeUnion $ Set.fromList s
        Left err -> Left err
    where
        f mp ps2 v1 = join $ getFirst a b pos $ map (\x -> Right <$> sameTypesGeneric gs pos mp x v1) ps2
sameTypesGeneric gs pos mp a@(TypeUnion st) b = 
    fromJust $ getFirst a b pos $ map (\x -> Just $ sameTypesGeneric gs pos mp x b) $ Set.toList st
sameTypesGeneric gs pos mp b a@(TypeUnion st) = 
    fromJust $ getFirst a b pos $ map (\x -> Just $ sameTypesGeneric gs pos mp x b) $ Set.toList st
sameTypesGeneric gs pos mp (Annotation id1) b@(Annotation id2)
    | id1 == id2 = Right b
    | otherwise = case Map.lookup (LhsIdentifer id1 pos) mp of
        Just a -> case Map.lookup (LhsIdentifer id2 pos) mp of
            Just b -> sameTypesGeneric gs pos mp a b
            Nothing -> Left $ noTypeFound id2 pos
        Nothing -> Left $ noTypeFound id1 pos
sameTypesGeneric gs pos mp (Annotation id) b = 
    case Map.lookup (LhsIdentifer id pos) mp of
        Just a -> sameTypesGeneric gs pos mp a b
        Nothing -> Left $ noTypeFound id pos
sameTypesGeneric gs pos mp b (Annotation id) = 
    case Map.lookup (LhsIdentifer id pos) mp of
        Just a -> sameTypesGeneric gs pos mp a b
        Nothing -> Left $ noTypeFound id pos
sameTypesGeneric tgs@(sensitive, gs) pos mp a@(GenericAnnotation id1 cs1) b@(GenericAnnotation id2 cs2)
    | sensitive && id1 `Map.member` gs && id2 `Map.member` gs && id1 /= id2 = Left $ "Expected " ++ show a ++ " but got " ++ show b
    | otherwise = if id1 == id2 then zipWithM (matchConstraint tgs pos mp) cs1 cs2 *> Right a else Left $ unmatchedType a b pos
sameTypesGeneric tgs@(sensitive, gs) pos mp a@(GenericAnnotation _ acs) b = 
    if sensitive then 
        mapM (matchConstraint tgs pos mp (AnnotationConstraint b)) acs *> Right b
    else Left $ unmatchedType a b pos
sameTypesGeneric tgs@(sensitive, gs) pos mp b a@(GenericAnnotation _ acs) = 
    if sensitive then 
        mapM (matchConstraint tgs pos mp (AnnotationConstraint b)) acs *> Right a
    else Left $ unmatchedType a b pos
sameTypesGeneric (sensitive, gs) pos mp ft@(OpenFunctionAnnotation anns1 ret1 forType impls) (OpenFunctionAnnotation anns2 ret2 _ _) =
    (\xs -> OpenFunctionAnnotation (init xs) (last xs) forType impls) <$> ls where 
        ls = zipWithM (sameTypesGeneric (sensitive, gs') pos mp) (anns1 ++ [ret1]) (anns2 ++ [ret2])
        gs' = genericsFromList (anns1 ++ [ret1]) `Map.union` gs 
sameTypesGeneric (sensitive, gs) pos mp a@(OpenFunctionAnnotation anns1 ret1 _ _) (FunctionAnnotation args ret2) = 
    (\xs -> FunctionAnnotation (init xs) (last xs)) <$> ls where
        ls = zipWithM (sameTypesGeneric (sensitive, gs') pos mp) (anns1 ++ [ret1]) (args ++ [ret2])
        gs' = genericsFromList (anns1 ++ [ret1]) `Map.union` gs
sameTypesGeneric _ pos _ a b = Left $ unmatchedType a b pos

genericsFromList :: [Annotation] -> Map.Map String [Constraint]
genericsFromList anns = foldr1 Map.union (map getGenerics anns)

matchConstraint :: (Bool, Map.Map String [Constraint]) -> SourcePos -> UserDefinedTypes -> Constraint -> Constraint -> Either String Constraint
matchConstraint gs pos mp c@(AnnotationConstraint a) (AnnotationConstraint b) = c <$ sameTypesGeneric gs pos mp a b
matchConstraint gs pos mp a@(ConstraintHas lhs cns) b@(AnnotationConstraint ann) = 
    case ann of
        StructAnnotation ds -> 
            if lhs `Map.member` ds then Right b
            else Left $ "Can't match " ++ show a ++ " with " ++ show b
        _ -> Left $ "Can't match " ++ show a ++ " with " ++ show b
matchConstraint gs pos mp c@(ConstraintHas a c1) (ConstraintHas b c2) = 
    if a /= b then Left $ "Can't match constraint " ++ show a ++ " with constraint " ++ show b ++ "\n" ++ showPos pos
    else c <$ matchConstraint gs pos mp c1 c2
matchConstraint gs pos mp a@(AnnotationConstraint ann) b@(ConstraintHas lhs cns) = matchConstraint gs pos mp b a

getGenerics :: Annotation -> Map.Map String [Constraint]
getGenerics (GenericAnnotation id cons) = Map.singleton id cons
getGenerics (OpenFunctionAnnotation anns ret _ _) = foldr1 Map.union (map getGenerics $ ret:anns)
getGenerics _ = Map.empty

sameTypes :: SourcePos -> UserDefinedTypes -> Annotation -> Annotation -> Either String Annotation
sameTypes = sameTypesGeneric (False, Map.empty)

getTypeMap :: State (a, (b, UserDefinedTypes)) (Map.Map Lhs Annotation)
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
                    case substituteVariables pos Map.empty (Map.fromList $ zip args givenArgs) mp x of
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
            case substituteVariables pos rels specificationRules mp ret' of
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
        Right _ -> (\a b -> join $ sameTypes pos m <$> a <*> b) <$> consistentTypes t <*> consistentTypes e
        Left err -> return $ Left err
consistentTypes (CreateNewType lhs args pos) = do
    mp <- getTypeMap
    argsn <- sequence <$> mapM consistentTypes args
    case argsn of
        Right as -> return $ case Map.lookup lhs mp of
            Just (NewTypeAnnotation id anns _) -> 
                if length anns == length args then NewTypeInstanceAnnotation id <$> argsn
                else Left $ "Can't match arguments " ++ show as ++ " with " ++ show anns
        Left err -> return $ Left err
consistentTypes (DeclN (Expr n)) = consistentTypes n
consistentTypes (IfStmnt (RemoveFromUnionNode lhs ann _) ts es pos) = do
    scope@(_, (_, mp)) <- get
    typLhs <- getAnnotationState lhs
    case typLhs of
        Right union@TypeUnion{} ->  do
            insertAnnotation lhs =<< excludeFromUnion pos ann union
            mapM_ getAssumptionType ts
            t <- sequence <$> mapM consistentTypes ts
            annRet <- getAnnotationState (LhsIdentifer "return" pos)
            put scope
            case annRet of
                Right annRet -> insertAnnotation (LhsIdentifer "return" pos) annRet
                Left _ -> return $ AnnotationLiteral "_"
            insertAnnotation lhs ann
            mapM_ getAssumptionType es
            e <- sequence <$> mapM consistentTypes es
            annRet <- getAnnotationState (LhsIdentifer "return" pos)
            put scope
            case annRet of
                Right annRet -> insertAnnotation (LhsIdentifer "return" pos) annRet
                Left _ -> return $ AnnotationLiteral "_"
            let res = case (t, e) of
                    (Right b, Right c) -> Right $ AnnotationLiteral "_"
                    (Left a, _) -> Left a
                    (_, Left a) -> Left a
            put scope
            return res
        _ -> return . Left $ expectedUnion pos lhs typLhs

consistentTypes (IfStmnt (CastNode lhs ann _) ts es pos) = do
    scope@(_, (_, mp)) <- get
    insertAnnotation lhs ann
    mapM_ getAssumptionType ts
    t <- sequence <$> mapM consistentTypes ts
    annRet <- getAnnotationState (LhsIdentifer "return" pos)
    put scope
    case annRet of
        Right annRet -> insertAnnotation (LhsIdentifer "return" pos) annRet
        Left _ -> return $ AnnotationLiteral "_"
    typLhs <- getAnnotationState lhs
    case typLhs of
        Right ts@TypeUnion{} -> insertAnnotation lhs =<< excludeFromUnion pos ann ts
        _ -> return ann
    mapM_ getAssumptionType es
    e <- sequence <$> mapM consistentTypes es
    annRet <- getAnnotationState (LhsIdentifer "return" pos)
    put scope
    case annRet of
        Right annRet -> insertAnnotation (LhsIdentifer "return" pos) annRet
        Left _ -> return $ AnnotationLiteral "_"
    let res = case (t, e) of
            (Right b, Right c) -> Right $ AnnotationLiteral "_"
            (Left a, _) -> Left a
            (_, Left a) -> Left a
    put scope
    return res
consistentTypes (IfStmnt cond ts es pos) = do
    scope@(_, (_, mp)) <- get
    c <- consistentTypes cond
    case sameTypes pos mp (AnnotationLiteral "Bool") <$> c of
        Right _ -> do
            c <- consistentTypes cond
            mapM_ getAssumptionType ts
            t <- sequence <$> mapM consistentTypes ts
            annRet <- getAnnotationState (LhsIdentifer "return" pos)
            put scope
            case annRet of
                Right annRet -> insertAnnotation (LhsIdentifer "return" pos) annRet
                Left _ -> return $ AnnotationLiteral "_"
            mapM_ getAssumptionType es
            e <- sequence <$> mapM consistentTypes es
            annRet <- getAnnotationState (LhsIdentifer "return" pos)
            put scope
            case annRet of
                Right annRet -> insertAnnotation (LhsIdentifer "return" pos) annRet
                Left _ -> return $ AnnotationLiteral "_"
            let res = case (c, t, e) of
                    (Right a, Right b, Right c) -> Right $ AnnotationLiteral "_"
                    (Left a, _, _) -> Left a
                    (_, Left a, _) -> Left a
                    (_, _, Left a) -> Left a
            put scope
            return res
        Left err -> return $ Left err
consistentTypes (StructN (Struct ns _)) = 
    (\xs -> 
        mapRight 
            (return . Right $ AnnotationLiteral "_") 
            (const . return . Right . StructAnnotation $ Map.map (\(Right a) -> a) xs)) =<< mapM consistentTypes ns
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
            whole_old@(a, (ans, mp)) <- get
            map <- getTypeMap
            let program = Program body
            let ans' = (assumeProgramMapping program (Annotations (Map.fromList $ args ++ [(LhsIdentifer "return" pos, ret)]) (Just ans)) mp, mp)
            let (rest, res) = runState (mapM consistentTypes body) (AnnotationLiteral "_", ans')
            put whole_old
            case getAnnotation (LhsIdentifer "return" pos) (fst $ snd res) of
                Right ret' -> case sequence rest of
                    Right _ -> return $ sameTypes pos map (makeFunAnnotation args ret) (makeFunAnnotation args ret')
                    Left err -> return . Left $ err
                Left err -> return $ Left err
        Nothing -> do
            whole_old_ans@(a, (old_ans, mp)) <- get
            let program = Program body
            let ans = (a, (assumeProgramMapping program (Annotations (Map.fromList $ (LhsIdentifer "return" pos, AnnotationLiteral "_"):args) (Just old_ans)) mp, mp))
            put ans
            xs <- sequence <$> mapM consistentTypes body
            new_ans <- gets $ fst . snd
            case xs of
                Right _ ->
                    (\case
                        Right ret -> case getAnnotation (LhsIdentifer "return" pos) new_ans of
                            Right ret' -> do
                                typ <- consistentTypes ret
                                let ntyp = if ret' == AnnotationLiteral "_" then typ else sameTypes pos mp ret' =<< typ
                                put whole_old_ans
                                return $ makeFunAnnotation args <$> ntyp
                            Left err -> return $ Left err
                        Left err -> return $ Left err) =<< firstInferrableReturn pos body
                Left err -> return $ Left err
consistentTypes (Return n pos) = getAnnotationState (LhsIdentifer "return" pos) >>= \case
    Left _ -> mapRight (consistentTypes n) (fmap Right . insertAnnotation (LhsIdentifer "return" pos))
    Right (AnnotationLiteral "_") -> mapRight (consistentTypes n) (fmap Right . insertAnnotation (LhsIdentifer "return" pos))
    Right a -> (\b mp -> sameTypes pos mp a =<< b) <$> consistentTypes n <*> getTypeMap
consistentTypes (Call e args pos) =  (\case 
                    Right fann@(FunctionAnnotation fargs ret) -> do
                        mp <- getTypeMap
                        anns <- sequence <$> mapM consistentTypes args
                        case anns of
                            Right anns -> let 
                                (spec, rels) = getPartialNoUnderScoreSpecificationRules pos Map.empty mp fann (FunctionAnnotation anns (AnnotationLiteral "_")) in
                                case substituteVariables pos rels spec mp ret of
                                    Right ret' -> case specify pos Map.empty mp fann (FunctionAnnotation anns ret') of
                                        Right r -> return $ Right ret'
                                        Left err -> return $ Left err
                                    Left err -> return $ Left err
                            Left err -> return $ Left err                    
                    Right opf@(OpenFunctionAnnotation oanns oret ft impls) -> 
                        do
                            mp <- getTypeMap
                            anns <- sequence <$> mapM consistentTypes args
                            case anns of
                                Right anns -> do
                                    let f = FunctionAnnotation anns (AnnotationLiteral "_")
                                    let (spec, rels) = getPartialNoUnderScoreSpecificationRules pos Map.empty mp opf f
                                    case Map.lookup oret spec of
                                        Just ret' -> 
                                            case getSpecificationRules pos Map.empty mp opf $ FunctionAnnotation anns ret' of
                                                Right base -> case Map.lookup ft base of
                                                    Just a -> maybe 
                                                        (return . Left $ "Could find instance " ++ show opf ++ " for " ++ show a ++ "\n" ++ showPos pos) 
                                                        (const $ return $ Right ret')
                                                        (find (\b -> specifyTypesBool pos base mp b a) impls)
                                                    Nothing -> return . Left $ "The argument does not even once occur in the whole method\n" ++ showPos pos
                                                Left err -> return $ Left err
                                        Nothing -> case substituteVariables pos rels spec mp oret of
                                            Right ret -> return $ Right ret
                                            Left err -> if isGeneric pos mp oret then return . Left $ "Can't call " ++ show opf ++ " with arguments " ++ show anns ++ "\n" ++ showPos pos else return $ Right oret
                                Left err -> return $ Left err
                    Right ann -> return . Left $ "Can't call a value of type " ++ show ann ++ "\n" ++ showPos pos
                    Left err -> return $ Left err) =<< getTypeStateFrom (consistentTypes e) pos
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
    exists mp (TypeUnion s, pos) = mapM_ (\x -> exists mp (x, pos)) (Set.toList s)
    exists mp (StructAnnotation xs, pos) = mapM_ (exists mp . (, pos)) (Map.elems xs)
    exists mp (GenericAnnotation _ cns, pos) = mapM_ (constraintExists mp . (, pos)) cns where 
        constraintExists mp (ConstraintHas _ cn, pos) = constraintExists mp (cn, pos)
        constraintExists mp (AnnotationConstraint ann, pos) = exists mp (ann, pos)

tests program = 
    do
        allExists typesPos
        case runState (mapM getAssumptionType restProgram) (AnnotationLiteral "_", (assumeProgram (Program restProgram) types, types)) of
            (res, (a, map)) -> case sequence_ res of
                Left err -> Left err 
                Right err -> sequence (evalState (mapM consistentTypes (earlyReturnToElse restProgram)) (a, map))
    where 
        (metProgram, restProgram) = typeNodes program
        typesPos = typeMap metProgram
        types = Map.map fst typesPos

parseFile :: String -> [Char] -> Either String [Annotation]
parseFile fn text = 
    case P.runParser Parser.wholeProgramParser fn (filter (/= '\t') text) of
        Right ns -> tests ns
        Left e -> Left $ P.errorBundlePretty e

main :: IO ()
main = do
    text <- readFile "test.junu"
    case parseFile "test.junu" text of
        Right as -> mapM_ print as
        Left a -> putStrLn a