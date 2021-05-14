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

firstInferrableReturn :: P.SourcePos -> Annotations -> [Node] -> Either String Node
firstInferrableReturn pos ans [] = Left $ "Could not infer the type of function at \n" ++ showPos pos
firstInferrableReturn pos ans (IfStmnt c ts es _:xs) = 
    mapLeft (firstInferrableReturn pos ans [c]) (\_ -> 
            mapLeft (firstInferrableReturn pos ans ts) (\_ -> 
                mapLeft (firstInferrableReturn pos ans es) (const $ firstInferrableReturn pos ans xs)
                )
        )
firstInferrableReturn pos ans ((DeclN (Decl _ rhs _ _)):xs) = 
    mapLeft (firstInferrableReturn pos ans [rhs]) (const $ firstInferrableReturn pos ans xs)
firstInferrableReturn pos ans ((DeclN (Assign _ rhs _)):xs) = 
    mapLeft (firstInferrableReturn pos ans [rhs]) (const $ firstInferrableReturn pos ans xs)
firstInferrableReturn pos ans ((Return a _):_) = Right a
firstInferrableReturn pos ans (_:xs) = firstInferrableReturn pos ans xs

isGeneric :: P.SourcePos -> UserDefinedTypes -> Annotation -> Bool
isGeneric pos mp GenericAnnotation{} = True
isGeneric pos mp AnnotationLiteral{} = False
isGeneric pos mp (Annotation ann) = maybe False (isGeneric pos mp) (Map.lookup (LhsIdentifer ann pos) mp)
isGeneric pos mp (FunctionAnnotation args ret) = all (isGeneric pos mp) (ret:args)
isGeneric pos mp (StructAnnotation ms) = all (isGeneric pos mp) ms
isGeneric pos mp OpenFunctionAnnotation{} = False

substituteConstraints :: SourcePos -> Map.Map Annotation Annotation -> UserDefinedTypes -> Constraint -> Either String  Constraint
substituteConstraints pos mp usts (ConstraintHas lhs cs) = ConstraintHas lhs <$> substituteConstraints pos mp usts cs 
substituteConstraints pos mp usts (AnnotationConstraint ann) = AnnotationConstraint <$> substituteVariables pos mp usts ann

substituteVariables :: SourcePos -> Map.Map Annotation Annotation -> UserDefinedTypes -> Annotation -> Either String Annotation
substituteVariables pos mp usts fid@(GenericAnnotation id cns) = maybe (GenericAnnotation id <$> mapM (substituteConstraints pos mp usts) cns) Right (Map.lookup fid mp)
substituteVariables pos mp usts id@AnnotationLiteral{} = Right id
substituteVariables pos mp usts (Annotation id) = maybe (Left $ noTypeFound id pos) Right (Map.lookup (LhsIdentifer id pos) usts)
substituteVariables pos mp usts (FunctionAnnotation args ret) = FunctionAnnotation <$> mapM (substituteVariables pos mp usts) args <*> substituteVariables pos mp usts ret
substituteVariables pos mp usts (StructAnnotation ms) = StructAnnotation <$> mapM (substituteVariables pos mp usts) ms
substituteVariables pos mp usts OpenFunctionAnnotation{} = error "Can't use substituteVariables with open functions"

addTypeVariable :: P.SourcePos -> Annotation -> Annotation -> SubstituteState (Either String Annotation)
addTypeVariable pos k v =  do
    (a, (mp, usts)) <- get
    case Map.lookup k mp of
        Nothing -> addToMap a mp usts
        Just a -> case sameTypes pos usts a v of
            Left err -> if a == AnnotationLiteral "_" then addToMap a mp usts else return $ Left err
            Right a -> addToMap a mp usts
        where 
            addToMap :: Annotation -> Map.Map Annotation Annotation -> UserDefinedTypes -> SubstituteState (Either String Annotation)
            addToMap a mp usts = do
                put (a, (Map.insert k v mp, usts))
                return $ Right v

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
            a -> return . Left $ "Can't search for field " ++ show lhs ++ " in " ++ show a ++ "\n" ++ showPos pos
applyConstraintState pos ann2 (AnnotationConstraint ann1) = do
    a <- addTypeVariable pos ann1 ann2
    case a of
        Right _ -> specifyInternal pos ann1 ann2
        Left err -> return $ Left err

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
specifyInternal pos a@(GenericAnnotation id cns) b = 
    (\case
        Right _ -> do
            a <- addTypeVariable pos a b
            case a of
                Right _ -> return $ Right b
                Left err -> return $ Left err
        Left err -> return $ Left err) . sequence =<< mapM (applyConstraintState pos b) cns
specifyInternal pos a b = (\mp -> return $ sameTypes pos mp a b) =<< getTypeMap

specify :: SourcePos -> Map.Map Annotation Annotation -> UserDefinedTypes -> Annotation -> Annotation -> Either String Annotation
specify pos base mp a b = evalState (specifyInternal pos a b) (a, (base, mp))

getPartialSpecificationRules :: SourcePos -> Map.Map Annotation Annotation -> UserDefinedTypes -> Annotation -> Annotation -> Map.Map Annotation Annotation
getPartialSpecificationRules pos base mp a b = (fst . snd) (execState (specifyInternal pos a b) (a, (base, mp)))

getPartialNoUnderScoreSpecificationRules :: SourcePos -> Map.Map Annotation Annotation -> UserDefinedTypes -> Annotation -> Annotation -> Map.Map Annotation Annotation
getPartialNoUnderScoreSpecificationRules pos base mp a b = 
    Map.mapWithKey (\k a -> if a == AnnotationLiteral "_" then k else a) $ getPartialSpecificationRules pos base mp a b

-- Map.mapWithKey (\k a -> if a == AnnotationLiteral "_" then k else a) $ getPartialSpecificationRules pos Map.empty mp fann (FunctionAnnotation anns (AnnotationLiteral "_"))

getSpecificationRules :: SourcePos -> Map.Map Annotation Annotation -> UserDefinedTypes  -> Annotation -> Annotation -> Either String (Map.Map Annotation Annotation)
getSpecificationRules pos base mp a b = case fst st of
    Right _ -> Right (fst $ snd $ snd st)
    Left err -> Left err 
    where st = runState (specifyInternal pos a b) (a, (base, mp))



sameTypesBool pos mp a b = case sameTypes pos mp a b of
                        Right _ -> True
                        Left _ -> False
                                            

isGenericAnnotation a = case a of 
    a@GenericAnnotation{} -> True
    _ -> False

getAssumptionType :: Node -> AnnotationState (Result String Annotation)
getAssumptionType (DeclN (Decl lhs n a _)) = case a of 
    Just a -> Right <$> insertAnnotation lhs a
    Nothing -> mapRight (getAssumptionType n) (fmap Right . insertAnnotation lhs)
getAssumptionType (DeclN (FunctionDecl lhs ann _)) = Right <$> insertAnnotation lhs ann
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
                    let specificationRules = getPartialNoUnderScoreSpecificationRules pos Map.empty mp fun (FunctionAnnotation (map snd args) (AnnotationLiteral "_"))
                    case substituteVariables pos specificationRules mp ret' of
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
getAssumptionType (DeclN (Expr n)) = getAssumptionType n
getAssumptionType (Return n _) = getAssumptionType n
getAssumptionType IfStmnt{} = return . Right $ AnnotationLiteral "_"
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
            case firstInferrableReturn pos new_ans body of
                Right st -> do
                    ret <- getAssumptionType st
                    modify (const whole_old_ans)
                    return $ makeFunAnnotation args <$> ret
                Left err -> return . Left $ err
getAssumptionType (Call e args pos) = (\case
                    Right fann@(FunctionAnnotation fargs ret) -> do
                        mp <- getTypeMap
                        anns <- sequence <$> mapM consistentTypes args
                        case anns of
                            Right anns -> let 
                                spec = getPartialNoUnderScoreSpecificationRules pos Map.empty mp fann (FunctionAnnotation anns (AnnotationLiteral "_")) in
                                case substituteVariables pos spec mp ret of
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
                                    let spec = getPartialNoUnderScoreSpecificationRules pos Map.empty mp opf f
                                    case Map.lookup oret spec of
                                        Just ret' -> 
                                            case getSpecificationRules pos Map.empty mp opf $ FunctionAnnotation anns ret' of
                                                Right base -> case Map.lookup ft base of
                                                    Just a -> maybe 
                                                        (return . Left $ "Could find instance " ++ show opf ++ " for " ++ show a ++ "\n" ++ showPos pos) 
                                                        (const $ return $ Right ret')
                                                        (find (sameTypesBool pos mp a) impls)
                                                    Nothing -> return . Left $ "The argument does not even once occur in the whole method\n" ++ showPos pos
                                                Left err -> return $ Left err
                                        Nothing -> case substituteVariables pos spec mp oret of
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
getAssumptionType (Access st p pos) = (\case
                    Right (GenericAnnotation g cns) -> return $ genericHas pos g p cns
                    Right (StructAnnotation ps) -> return $ toEither ("Could not find " ++ show p ++ " in " ++ show ps ++ "\n" ++ showPos pos) (Map.lookup p ps)
                    Right a -> return . Left $ "Cannot get " ++ show p ++ " from type " ++ show a ++ "\n" ++ showPos pos
                    Left err -> return $ Left err
                    ) =<< getTypeStateFrom (consistentTypes st) pos
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
    if length as == length bs then a <$ zipWithM (sameTypesGeneric gs pos mp) (as ++ [ret1]) (bs ++ [ret2])
    else Left $ unmatchedType a b pos
sameTypesGeneric gs pos mp a@(StructAnnotation ps1) b@(StructAnnotation ps2)
    | Map.empty == ps1 || Map.empty == ps2 = if ps1 == ps2 then Right a else Left $ unmatchedType a b pos
    | Map.size ps1 /= Map.size ps2 = Left $ unmatchedType a b pos
    | Map.foldr (&&) True (Map.mapWithKey (f ps1) ps2) = Right a
    | otherwise = Left $ unmatchedType a b pos
    where
        f ps2 k v1 = 
            case Map.lookup k ps2 of
                Just v2
                    -> case sameTypesGeneric gs pos mp v1 v2 of
                        Right _ -> True
                        Left err -> False
                Nothing -> False
sameTypesGeneric gs pos mp (Annotation id1) (Annotation id2) = 
    case Map.lookup (LhsIdentifer id1 pos) mp of
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
sameTypesGeneric (sensitive, gs) pos mp ft@(OpenFunctionAnnotation anns1 ret1 _ _) (OpenFunctionAnnotation anns2 ret2 _ _) =
    zipWithM (sameTypesGeneric (sensitive, gs') pos mp) (anns1 ++ [ret1]) (anns2 ++ [ret2]) *> Right ft where 
        gs' = genericsFromList (anns1 ++ [ret1]) `Map.union` gs
sameTypesGeneric (sensitive, gs) pos mp a@(OpenFunctionAnnotation anns1 ret1 _ _) (FunctionAnnotation args ret2) = 
    zipWithM (sameTypesGeneric (sensitive, gs') pos mp) (anns1 ++ [ret1]) (args ++ [ret2]) *> Right a where
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
            let specificationRules = getPartialNoUnderScoreSpecificationRules pos Map.empty mp fun (FunctionAnnotation (map snd args) (AnnotationLiteral "_"))
            case substituteVariables pos specificationRules mp ret' of
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
consistentTypes (DeclN (Expr n)) = consistentTypes n
consistentTypes (IfStmnt cond ts es pos) = do
    scope@(_, (_, mp)) <- get
    c <- consistentTypes cond
    case sameTypes pos mp (AnnotationLiteral "Bool") <$> c of
        Right _ -> do
            c <- consistentTypes cond
            mapM_ getAssumptionType ts
            t <- sequence <$> mapM consistentTypes ts
            put scope
            mapM_ getAssumptionType es
            e <- sequence <$> mapM consistentTypes es
            put scope
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
consistentTypes (Access st p pos) = (\case
                    Right (GenericAnnotation g cns) -> return $ genericHas pos g p cns
                    Right (StructAnnotation ps) -> return $ toEither ("Could not find " ++ show p ++ " in " ++ show ps ++ "\n" ++ showPos pos) (Map.lookup p ps)
                    Right a -> return . Left $ "Cannot get " ++ show p ++ " from type " ++ show a ++ "\n" ++ showPos pos
                    Left err -> return $ Left err) =<< getTypeStateFrom (consistentTypes st) pos
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
                    case firstInferrableReturn pos new_ans body of
                        Right st -> do
                            ret <- getAssumptionType st
                            put whole_old_ans
                            return (makeFunAnnotation args <$> ret)
                        Left err -> return . Left $ err
                Left err -> return $ Left err
consistentTypes (Return n pos) =  getAnnotationState (LhsIdentifer "return" pos) >>= \case
    Left _ -> mapRight (consistentTypes n) (fmap Right . insertAnnotation (LhsIdentifer "return" pos))
    Right (AnnotationLiteral "_") -> mapRight (consistentTypes n) (fmap Right . insertAnnotation (LhsIdentifer "return" pos))
    Right a -> (\b mp -> sameTypes pos mp a =<< b) <$> consistentTypes n <*> getTypeMap
consistentTypes (Call e args pos) =  (\case 
                    Right fann@(FunctionAnnotation fargs ret) -> do
                        mp <- getTypeMap
                        anns <- sequence <$> mapM consistentTypes args
                        case anns of
                            Right anns -> let 
                                spec = getPartialNoUnderScoreSpecificationRules pos Map.empty mp fann (FunctionAnnotation anns (AnnotationLiteral "_")) in
                                case substituteVariables pos spec mp ret of
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
                                    let spec = getPartialNoUnderScoreSpecificationRules pos Map.empty mp opf f
                                    case Map.lookup oret spec of
                                        Just ret' -> 
                                            case getSpecificationRules pos Map.empty mp opf $ FunctionAnnotation anns ret' of
                                                Right base -> case Map.lookup ft base of
                                                    Just a -> maybe 
                                                        (return . Left $ "Could find instance " ++ show opf ++ " for " ++ show a ++ "\n" ++ showPos pos) 
                                                        (const $ return $ Right ret')
                                                        (find (sameTypesBool pos mp a) impls)
                                                    Nothing -> return . Left $ "The argument does not even once occur in the whole method\n" ++ showPos pos
                                                Left err -> return $ Left err
                                        Nothing -> case substituteVariables pos spec mp oret of
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
onlyTypeDecls _ = False

typeNodes :: [Node] -> ([Node], [Node])
typeNodes = partition onlyTypeDecls

typeMap :: [Node] -> Map.Map Lhs (Annotation, P.SourcePos)
typeMap xs = Map.fromList $ map makeTup xs where
    makeTup (DeclN (StructDef lhs rhs pos)) = (lhs, (rhs, pos))

allExists :: Map.Map Lhs (Annotation, P.SourcePos) -> Either String ()
allExists mp = mapM_ (exists mp) mp where
    exists :: Map.Map Lhs (Annotation, P.SourcePos) -> (Annotation, P.SourcePos) -> Either String ()
    exists mp (Annotation id, pos) = 
        case Map.lookup (LhsIdentifer id pos) mp of
            Just _ -> Right ()
            Nothing -> Left $ noTypeFound id pos
    exists mp (AnnotationLiteral lit, pos) = Right ()
    exists mp (FunctionAnnotation as ret, pos) = mapM_ (exists mp . (, pos)) as >> exists mp (ret, pos)
    exists mp (StructAnnotation xs, pos) = mapM_ (exists mp . (, pos)) (Map.elems xs)

tests program = 
    do
        allExists typesPos
        case runState (mapM getAssumptionType restProgram) (AnnotationLiteral "_", (assumeProgram (Program restProgram) types, types)) of
            (res, (a, map)) -> case sequence_ res of
                Left err -> Left err 
                Right err -> sequence (evalState (mapM consistentTypes restProgram) (a, map))
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