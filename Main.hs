{-# LANGUAGE LambdaCase #-}
module Main where

import qualified Data.Map as Map
import Control.Monad
import Debug.Trace ( trace )
import Control.Monad.State
import Text.Megaparsec as P hiding (State)
import Text.Megaparsec.Pos (mkPos)
import qualified Parser
import Nodes

insertAnnotation :: Lhs -> Annotation -> AnnotationState Annotation
insertAnnotation k v = modify (\(a, Annotations b o) -> (a, Annotations (Map.insert k v b) o)) >> return v

getAnnotation :: Lhs -> Annotations -> Result String Annotation
getAnnotation k (Annotations anns rest) = do
    case Map.lookup k anns of
        Just v -> Right v
        Nothing -> 
            case rest of
                Just rs -> getAnnotation k rs
                Nothing -> Left $ show k ++ " not found in this scope"

getAnnotationState :: Lhs -> AnnotationState (Result String Annotation)
getAnnotationState k = get >>= \(_, anns) -> return $ getAnnotation k anns

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

firstInferrableReturn :: P.SourcePos -> Annotations -> [Node] -> Either String Node
firstInferrableReturn pos ans [] = Left $ "Could not infer the type of function at \n" ++ showPos pos
firstInferrableReturn pos ans ((DeclN (Decl _ rhs _ _)):xs) = 
    mapLeft (firstInferrableReturn pos ans [rhs]) (const $ firstInferrableReturn pos ans xs)
firstInferrableReturn pos ans ((DeclN (Assign _ rhs _)):xs) = 
    mapLeft (firstInferrableReturn pos ans [rhs]) (const $ firstInferrableReturn pos ans xs)
firstInferrableReturn pos ans ((DeclN (FunctionDecl _ rhs _)):xs) = firstInferrableReturn pos ans xs
firstInferrableReturn pos ans ((Identifier s _):xs) = firstInferrableReturn pos ans xs
firstInferrableReturn pos ans (Lit{}:xs) = firstInferrableReturn pos ans xs
firstInferrableReturn pos ans (FunctionDef{}:xs) = firstInferrableReturn pos ans xs
firstInferrableReturn pos ans ((Return a _):_) = Right a
firstInferrableReturn pos ans (Call{}:xs) = firstInferrableReturn pos ans xs

getAssumptionType :: Node -> AnnotationState (Result String Annotation)
getAssumptionType (DeclN (Decl lhs n a _)) = case a of 
    Just a -> Right <$> insertAnnotation lhs a
    Nothing -> mapRight (getAssumptionType n) (fmap Right . insertAnnotation lhs)
getAssumptionType (DeclN (FunctionDecl lhs ann _)) = Right <$> insertAnnotation lhs ann
getAssumptionType (DeclN (Assign lhs n _)) = mapRight (getAssumptionType n) (fmap Right . insertAnnotation lhs)
getAssumptionType (DeclN (Expr n)) = getAssumptionType n
getAssumptionType (Return n _) = getAssumptionType n
getAssumptionType (FunctionDef args ret body pos) = 
    case ret of
        Just ret -> return . Right $ makeFunAnnotation args ret
        Nothing -> do
            whole_old_ans@(a, old_ans) <- get
            let program = Program body
            let ans = (a, assumeProgramMapping program (Annotations (Map.fromList args) (Just old_ans)))
            modify (const ans)
            mapM_ getAssumptionType body
            new_ans <- gets snd
            case firstInferrableReturn pos new_ans body of
                Right st -> do
                    ret <- getAssumptionType st
                    modify (const whole_old_ans)
                    return (makeFunAnnotation args <$> ret)
                Left err -> return . Left $ err
getAssumptionType (Call e args pos) = do
    funAnn <- getAssumptionType e
    case funAnn of
        Right (FunctionAnnotation fargs ret) -> (\case 
                Right args' -> 
                    if length args' == length fargs then zipWithM_ (sameTypes pos) fargs args' >> return ret 
                    else callError fargs args'
                Left err -> Left err
            ) <$> (sequence <$> mapM getAssumptionType args)
        Right _ -> return . Left $ "Can't call " ++ show e
        Left err -> return $ Left err
getAssumptionType (Lit (LitInt _ _)) = return . Right $ Annotation "Int"
getAssumptionType (Lit (LitBool _ _)) = return . Right $ Annotation "Bool"
getAssumptionType (Lit (LitString _ _)) = return . Right $ Annotation "String"
getAssumptionType (Identifier x pos) = do
    ann <- getAnnotationState (LhsIdentifer x pos)
    case ann of
        Right a -> return $ Right a
        Left err  -> return $ Left err

makeAssumptions :: State (Annotation, b) a -> b -> b
makeAssumptions s m = snd $ execState s (Annotation "_", m)

assumeProgramMapping :: Program -> Annotations -> Annotations
assumeProgramMapping (Program xs) = makeAssumptions (mapM getAssumptionType $ filter nonDecls xs)

nonDecls (DeclN Decl{}) = True
nonDecls (DeclN FunctionDecl{}) = True
nonDecls _ = False

sourcePos = SourcePos "core" (mkPos 0) (mkPos 0)

baseMapping = Map.fromList [
    (LhsIdentifer "add" sourcePos, FunctionAnnotation [Annotation "Int", Annotation "Int"] (Annotation "Int")),
    (LhsIdentifer "sub" sourcePos, FunctionAnnotation [Annotation "Int", Annotation "Int"] (Annotation "Int")),
    (LhsIdentifer "mul" sourcePos, FunctionAnnotation [Annotation "Int", Annotation "Int"] (Annotation "Int")),
    (LhsIdentifer "div" sourcePos, FunctionAnnotation [Annotation "Int", Annotation "Int"] (Annotation "Int")),
    (LhsIdentifer "gt" sourcePos, FunctionAnnotation [Annotation "Int", Annotation "Int"] (Annotation "Int")),
    (LhsIdentifer "gte" sourcePos, FunctionAnnotation [Annotation "Int", Annotation "Int"] (Annotation "Int")),
    (LhsIdentifer "lt" sourcePos, FunctionAnnotation [Annotation "Int", Annotation "Int"] (Annotation "Int")),
    (LhsIdentifer "lte" sourcePos, FunctionAnnotation [Annotation "Int", Annotation "Int"] (Annotation "Int")),
    (LhsIdentifer "eq" sourcePos, FunctionAnnotation [Annotation "Int", Annotation "Int"] (Annotation "Int")),
    (LhsIdentifer "neq" sourcePos, FunctionAnnotation [Annotation "Int", Annotation "Int"] (Annotation "Int")),
    (LhsIdentifer "and" sourcePos, FunctionAnnotation [Annotation "Bool", Annotation "Bool"] (Annotation "Bool")),
    (LhsIdentifer "or" sourcePos, FunctionAnnotation [Annotation "Bool", Annotation "Bool"] (Annotation "Bool")),
    (LhsIdentifer "not" sourcePos, FunctionAnnotation [Annotation "Bool"] (Annotation "Bool")),
    (LhsIdentifer "neg" sourcePos, FunctionAnnotation [Annotation "Int"] (Annotation "Int"))
    ]

assumeProgram :: Map.Map Lhs Annotation -> Program -> Annotations
assumeProgram base = flip assumeProgramMapping (Annotations base Nothing)

showPos (P.SourcePos s ln cn) = 
    "In file: " ++ s ++ ", at line: " ++ tail (dropWhile (/= ' ') (show ln)) ++ ", at colounm: " ++ tail (dropWhile (/= ' ') (show cn))

sameTypes :: P.SourcePos -> Annotation -> Annotation -> Either String Annotation
sameTypes pos a@Annotation{} b@Annotation{} = 
    if a == b then Right a else Left $ "Can't match expected type " ++ show a ++ " with given type " ++ show b ++ "\n" ++ showPos pos
sameTypes pos a@FunctionAnnotation{} b@FunctionAnnotation{} = 
    if a == b then Right a else Left $ "Can't match expected type " ++ show a ++ " with given type " ++ show b ++ "\n" ++ showPos pos
sameTypes pos a b = Left $ "Can't match expected type " ++ show a ++ " with given type " ++ show b ++ "\n" ++ showPos pos

getReturns :: [Node] -> [[Node]]
getReturns [] = []
getReturns (DeclN (Decl _ rhs _ _):xs) = getReturns [rhs] ++ getReturns xs
getReturns (DeclN (Assign _ rhs _):xs) = getReturns [rhs] ++ getReturns xs
getReturns ((FunctionDef args ret body _):xs) = getReturns body ++ getReturns xs
getReturns (rt@(Return x pos):xs) = [rt] : getReturns xs
getReturns ((Call e as pos):xs) = join $ getReturns [e] : map (getReturns . (:[])) as
getReturns (Lit{}:xs) = getReturns xs
getReturns (Identifier{}:xs) = getReturns xs


consistentTypes ::  Node -> AnnotationState (Either String Annotation)
consistentTypes (DeclN (Decl lhs rhs _ pos)) = (\a b -> join $ sameTypes pos <$> a <*> b)
    <$> getAnnotationState lhs <*> consistentTypes rhs
consistentTypes (DeclN (Assign lhs rhs pos)) = (\a b -> join $ sameTypes pos <$> a <*> b) 
    <$> getAnnotationState lhs <*> consistentTypes rhs
consistentTypes (DeclN (FunctionDecl lhs ann pos)) = (sameTypes pos ann =<<) <$> getAnnotationState lhs
consistentTypes (DeclN (Expr n)) = consistentTypes n
consistentTypes (FunctionDef args ret body pos) = 
    case ret of
        Just ret -> do
            whole_old@(a, ans) <- get
            let program = Program body
            let ans' = assumeProgramMapping program (Annotations (Map.fromList $ args ++ [(LhsIdentifer "return" pos, ret)]) (Just ans))
            let (rest, res) = runState (mapM consistentTypes body) (Annotation "_", ans')
            case getAnnotation (LhsIdentifer "return" pos) (snd res) of
                Right ret' -> case sequence rest of
                    Right _ -> return $ sameTypes pos (makeFunAnnotation args ret) (makeFunAnnotation args ret')
                    Left err -> return . Left $ err
                Left err -> return $ Left err
        Nothing -> do
            whole_old_ans@(a, old_ans) <- get
            let program = Program body
            let ans = (a, assumeProgramMapping program (Annotations (Map.fromList args) (Just old_ans)))
            put ans
            xs <- sequence <$> mapM consistentTypes body
            new_ans <- gets snd
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
    Right a -> (sameTypes pos a =<<) <$> consistentTypes n
    Left _ -> mapRight (consistentTypes n) (fmap Right . insertAnnotation (LhsIdentifer "return" pos))
consistentTypes (Call e args pos) =  
    consistentTypes e >>= \case
        Right (FunctionAnnotation fargs ret) -> anns >>= \anns ->
            if lenA == lenB then return (ret <$ (zipWithM (sameTypes pos) fargs =<< anns))
            else return (callError fargs =<< anns)
            where 
                (lenA, lenB) = (length args, length fargs)
                anns = sequence <$> mapM consistentTypes args
        Right ann -> return . Left $ "Can't call a value of type " ++ show ann ++ "\n" ++ showPos pos
        Left err -> return . Left $ err
consistentTypes (Identifier x pos) = getAnnotationState (LhsIdentifer x pos)
consistentTypes (Lit (LitInt _ _)) = return . Right $ Annotation "Int"
consistentTypes (Lit (LitBool _ _)) = return . Right $ Annotation "Bool"
consistentTypes (Lit (LitString _ _)) = return . Right $ Annotation "String"

tests :: [Node] -> [Either String Annotation]
tests program = fst $ runState (mapM consistentTypes program) (Annotation "_", assumeProgram baseMapping $ Program program)

parseFile fn text = 
    case P.runParser Parser.wholeProgramParser fn (filter (/= '\t') text) of
        Right ns -> sequence $ tests ns
        Left e -> Left $ P.errorBundlePretty e

main :: IO ()
main = do
    text <- readFile "test.junu"
    case parseFile "test.junu" text of
        Right as -> mapM_ print as
        Left a -> putStrLn a