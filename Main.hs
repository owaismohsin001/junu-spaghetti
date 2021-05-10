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

getTypeState :: Annotation -> P.SourcePos -> AnnotationState (Either String Annotation)
getTypeState (Annotation id) pos = do
    (_, (_, types)) <- get
    case Map.lookup (LhsIdentifer id pos) types of
        Just st -> return $ Right st
        Nothing -> return . Left $ "No type named " ++ id ++ " found"
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

getAssumptionType :: Node -> AnnotationState (Result String Annotation)
getAssumptionType (DeclN (Decl lhs n a _)) = case a of 
    Just a -> Right <$> insertAnnotation lhs a
    Nothing -> mapRight (getAssumptionType n) (fmap Right . insertAnnotation lhs)
getAssumptionType (DeclN (FunctionDecl lhs ann _)) = Right <$> insertAnnotation lhs ann
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
                    Right (FunctionAnnotation fargs ret) -> do
                        mp <- gets (snd . snd)
                        anns <- sequence <$> mapM consistentTypes args
                        case anns of
                            Right anns -> return $ ret <$ zipWithM (sameTypes pos mp) fargs anns
                            Left err -> return $ Left err
                    Right ann -> return . Left $ "Can't call a value of type " ++ show ann ++ "\n" ++ showPos pos
                    Left err -> return $ Left err) =<< getTypeStateFrom (getAssumptionType e) pos
getAssumptionType (StructN (Struct ns _)) = 
    (\xs -> 
        mapRight 
            (return . Right $ AnnotationLiteral "_") 
            (const . return . Right . StructAnnotation $ Map.map (\(Right a) -> a) xs)) =<< mapM getAssumptionType ns
getAssumptionType (Access st p pos) = (\case
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

makeAssumptions :: State (Annotation, b) a -> b -> b
makeAssumptions s m = snd $ execState s (AnnotationLiteral "_", m)

assumeProgramMapping :: Program -> Annotations -> UserDefinedTypes -> Annotations
assumeProgramMapping (Program xs) anns mp = fst $ makeAssumptions (mapM getAssumptionType $ filter nonDecls xs) (anns, mp)

nonDecls (DeclN Decl{}) = True
nonDecls (DeclN FunctionDecl{}) = True
nonDecls _ = False

sourcePos = SourcePos "core" (mkPos 0) (mkPos 0)

baseMapping = Map.fromList [
    (LhsIdentifer "add" sourcePos, FunctionAnnotation [AnnotationLiteral "Int", AnnotationLiteral "Int"] (AnnotationLiteral "Int")),
    (LhsIdentifer "sub" sourcePos, FunctionAnnotation [AnnotationLiteral "Int", AnnotationLiteral "Int"] (AnnotationLiteral "Int")),
    (LhsIdentifer "mul" sourcePos, FunctionAnnotation [AnnotationLiteral "Int", AnnotationLiteral "Int"] (AnnotationLiteral "Int")),
    (LhsIdentifer "div" sourcePos, FunctionAnnotation [AnnotationLiteral "Int", AnnotationLiteral "Int"] (AnnotationLiteral "Int")),
    (LhsIdentifer "gt" sourcePos, FunctionAnnotation [AnnotationLiteral "Int", AnnotationLiteral "Int"] (AnnotationLiteral "Bool")),
    (LhsIdentifer "gte" sourcePos, FunctionAnnotation [AnnotationLiteral "Int", AnnotationLiteral "Int"] (AnnotationLiteral "Bool")),
    (LhsIdentifer "lt" sourcePos, FunctionAnnotation [AnnotationLiteral "Int", AnnotationLiteral "Int"] (AnnotationLiteral "Bool")),
    (LhsIdentifer "lte" sourcePos, FunctionAnnotation [AnnotationLiteral "Int", AnnotationLiteral "Int"] (AnnotationLiteral "Bool")),
    (LhsIdentifer "eq" sourcePos, FunctionAnnotation [AnnotationLiteral "Int", AnnotationLiteral "Int"] (AnnotationLiteral "Bool")),
    (LhsIdentifer "neq" sourcePos, FunctionAnnotation [AnnotationLiteral "Int", AnnotationLiteral "Int"] (AnnotationLiteral "Bool")),
    (LhsIdentifer "and" sourcePos, FunctionAnnotation [AnnotationLiteral "Bool", AnnotationLiteral "Bool"] (AnnotationLiteral "Bool")),
    (LhsIdentifer "or" sourcePos, FunctionAnnotation [AnnotationLiteral "Bool", AnnotationLiteral "Bool"] (AnnotationLiteral "Bool")),
    (LhsIdentifer "not" sourcePos, FunctionAnnotation [AnnotationLiteral "Bool"] (AnnotationLiteral "Bool")),
    (LhsIdentifer "neg" sourcePos, FunctionAnnotation [AnnotationLiteral "Int"] (AnnotationLiteral "Int"))
    ]

assumeProgram prog = assumeProgramMapping prog (Annotations baseMapping Nothing)

showPos :: SourcePos -> String
showPos (P.SourcePos s ln cn) = 
    "In file: " ++ s ++ ", at line: " ++ tail (dropWhile (/= ' ') (show ln)) ++ ", at colounm: " ++ tail (dropWhile (/= ' ') (show cn))

noTypeFound expected pos = "No type named " ++ expected ++ " found\n" ++ showPos pos
unmatchedType a b pos = "Can't match expected type " ++ show a ++ " with given type " ++ show b ++ "\n" ++ showPos pos

sameTypes :: P.SourcePos -> UserDefinedTypes -> Annotation -> Annotation -> Either String Annotation
sameTypes pos _ a@AnnotationLiteral{} b@AnnotationLiteral{} = 
    if a == b then Right a else Left $ unmatchedType a b pos
sameTypes pos mp a@(FunctionAnnotation as ret1) b@(FunctionAnnotation bs ret2) = 
    if length as == length bs then a <$ zipWithM (sameTypes pos mp) (as ++ [ret1]) (bs ++ [ret2])
    else Left $ unmatchedType a b pos
sameTypes pos mp a@(StructAnnotation ps1) b@(StructAnnotation ps2)
    | Map.empty == ps1 || Map.empty == ps2 = if ps1 == ps2 then Right a else Left $ unmatchedType a b pos
    | Map.foldr (&&) True (Map.mapWithKey (f ps1) ps2) = Right a
    | otherwise = Left $ unmatchedType a b pos
    where
        f ps2 k v1 = 
            case Map.lookup k ps2 of
                Just v2
                    -> case sameTypes pos mp v1 v2 of
                        Right _ -> True
                        Left err -> False
                Nothing -> False
sameTypes pos mp (Annotation id1) (Annotation id2) = 
    case Map.lookup (LhsIdentifer id1 pos) mp of
        Just a -> case Map.lookup (LhsIdentifer id2 pos) mp of
            Just b -> sameTypes pos mp a b
            Nothing -> Left $ noTypeFound id2 pos
        Nothing -> Left $ noTypeFound id1 pos
sameTypes pos mp (Annotation id) b = 
    case Map.lookup (LhsIdentifer id pos) mp of
        Just a -> sameTypes pos mp a b
        Nothing -> Left $ noTypeFound id pos
sameTypes pos mp b (Annotation id) = 
    case Map.lookup (LhsIdentifer id pos) mp of
        Just a -> sameTypes pos mp a b
        Nothing -> Left $ noTypeFound id pos
sameTypes pos _ a b = Left $ unmatchedType a b pos

-- getReturns :: [Node] -> [[Node]]
-- getReturns [] = []
-- getReturns (DeclN (Decl _ rhs _ _):xs) = getReturns [rhs] ++ getReturns xs
-- getReturns (DeclN (Assign _ rhs _):xs) = getReturns [rhs] ++ getReturns xs
-- getReturns ((FunctionDef args ret body _):xs) = getReturns body ++ getReturns xs
-- getReturns (rt@(Return x pos):xs) = [rt] : getReturns xs
-- getReturns ((Call e as pos):xs) = join $ getReturns [e] : map (getReturns . (:[])) as
-- getReturns (Lit{}:xs) = getReturns xs
-- getReturns (Identifier{}:xs) = getReturns xs



consistentTypes ::  Node -> AnnotationState (Either String Annotation)
consistentTypes (DeclN (Decl lhs rhs _ pos)) = (\a b m -> join $ sameTypes pos m <$> a <*> b)
    <$> getAnnotationState lhs <*> consistentTypes rhs <*> gets (snd . snd)
consistentTypes (DeclN (Assign (LhsAccess access prop accPos) rhs pos)) = (\a b m -> join $ sameTypes pos m <$> a <*> b)
    <$> getAssumptionType (Access access prop accPos) <*> consistentTypes rhs <*> gets (snd . snd)
consistentTypes (DeclN (Assign lhs rhs pos)) = (\a b m -> join $ sameTypes pos m <$> a <*> b) 
    <$> getAnnotationState lhs <*> consistentTypes rhs <*> gets (snd . snd)
consistentTypes (DeclN (FunctionDecl lhs ann pos)) = do
    m <- gets (snd . snd)
    l <- getAnnotationState lhs
    case l of
        Right l -> return $ sameTypes pos m ann l 
        Left err -> return $ Left err
consistentTypes (IfExpr cond t e pos) = do
    m <- gets (snd . snd)
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
                    Right (StructAnnotation ps) -> return $ toEither ("Could not find " ++ show p ++ " in " ++ show ps ++ "\n" ++ showPos pos) (Map.lookup p ps)
                    Right a -> return . Left $ "Cannot get " ++ show p ++ " from type " ++ show a ++ "\n" ++ showPos pos
                    Left err -> return $ Left err) =<< getTypeStateFrom (consistentTypes st) pos
consistentTypes (FunctionDef args ret body pos) = 
    case ret of
        Just ret -> do
            whole_old@(a, (ans, mp)) <- get
            map <- gets (snd . snd)
            let program = Program body
            let ans' = (assumeProgramMapping program (Annotations (Map.fromList $ args ++ [(LhsIdentifer "return" pos, ret)]) (Just ans)) mp, mp)
            let (rest, res) = runState (mapM consistentTypes body) (AnnotationLiteral "_", ans')
            case getAnnotation (LhsIdentifer "return" pos) (fst $ snd res) of
                Right ret' -> case sequence rest of
                    Right _ -> return $ sameTypes pos map (makeFunAnnotation args ret) (makeFunAnnotation args ret')
                    Left err -> return . Left $ err
                Left err -> return $ Left err
        Nothing -> do
            whole_old_ans@(a, (old_ans, mp)) <- get
            let program = Program body
            let ans = (a, (assumeProgramMapping program (Annotations (Map.fromList args) (Just old_ans)) mp, mp))
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
    Right a -> (\b mp -> sameTypes pos mp a =<< b) <$> consistentTypes n <*> gets (snd . snd)
    Left _ -> mapRight (consistentTypes n) (fmap Right . insertAnnotation (LhsIdentifer "return" pos))
consistentTypes (Call e args pos) =  (\case 
                    Right (FunctionAnnotation fargs ret) -> do
                        mp <- gets (snd . snd)
                        anns <- sequence <$> mapM consistentTypes args
                        case anns of
                            Right anns -> return $ ret <$ zipWithM (sameTypes pos mp) fargs anns
                            Left err -> return $ Left err
                    Right ann -> return . Left $ "Can't call a value of type " ++ show ann ++ "\n" ++ showPos pos
                    Left err -> return $ Left err) =<< getTypeStateFrom (consistentTypes e) pos
consistentTypes (Identifier x pos) = getAnnotationState (LhsIdentifer x pos)
consistentTypes (Lit (LitInt _ _)) = return . Right $ AnnotationLiteral "Int"
consistentTypes (Lit (LitBool _ _)) = return . Right $ AnnotationLiteral "Bool"
consistentTypes (Lit (LitString _ _)) = return . Right $ AnnotationLiteral "String"

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