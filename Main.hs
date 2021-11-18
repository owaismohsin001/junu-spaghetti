{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
module Main where

import qualified Data.Map as Map
import Debug.Trace ( trace )
import Text.Megaparsec as P hiding (State)
import qualified Data.Set as Set
import qualified Parser
import Data.List
import Nodes
import System.Environment   
import Data.Char
import Data.Either
import TypeChecker
import Data.Maybe
import Control.Monad.State
import System.Process

safeName = ("v"++)

processIdentifier :: ([Char] -> t -> a) -> Set.Set String -> String -> t -> State (Map.Map String Int, Int) a
processIdentifier f nds id pos     
    | id `Set.member` nds = return $ f id pos 
    | otherwise = do
        (appliedTo, n) <- get
        case id `Map.lookup` appliedTo of
            Just i -> return $ f (safeName $ show i) pos
            Nothing -> do
                modify (\(a, b) -> (Map.insert id (b+1) a, b+1))
                (_, n) <- get
                return $ f (safeName $ show n) pos

changeNamesLhs :: Set.Set String -> Lhs -> State (Map.Map String Int, Int) Lhs
changeNamesLhs nds fid@(LhsIdentifer id pos) = processIdentifier LhsIdentifer nds id pos 
changeNamesLhs nds access@LhsAccess{} = revampLhsId nds access

revampLhsId nds (LhsAccess id@Identifier{} lhs pos) = LhsAccess <$> changeNames nds id <*> return lhs <*> return pos
revampLhsId nds (LhsAccess x lhs pos) = LhsAccess <$> revampId nds x <*> return lhs <*> return pos
revampLhsId _ n = error $ "Only call revampLhsId with " ++ show n

changeNamesDecl :: Set.Set String -> Decl -> State (Map.Map String Int, Int) Decl 
changeNamesDecl nds (Decl lhs rhs ann pos) = Decl <$> changeNamesLhs nds lhs <*> changeNames nds rhs <*> return ann <*> return pos
changeNamesDecl nds (Assign lhs rhs pos) = Assign <$> changeNamesLhs nds lhs <*> changeNames nds rhs <*> return pos
changeNamesDecl nds (FunctionDecl lhs ann pos) = FunctionDecl <$> changeNamesLhs nds lhs <*> return ann <*> return pos
changeNamesDecl nds (StructDef lhs ann pos) = StructDef <$> changeNamesLhs nds lhs <*> return ann <*> return pos
changeNamesDecl nds (OpenFunctionDecl lhs ann pos) = OpenFunctionDecl <$> changeNamesLhs nds lhs <*> return ann <*> return pos
changeNamesDecl nds (ImplOpenFunction lhs args ann ds ftr pos) = 
    ImplOpenFunction <$> changeNamesLhs nds lhs <*> mapM (\(lhs, ann) -> (, ann) <$> changeNamesLhs nds lhs) args <*> return ann <*> mapM (changeNames nds) ds <*> return ftr <*> return pos
changeNamesDecl nds (NewTypeDecl lhs ann pos) = NewTypeDecl <$> changeNamesLhs nds lhs <*> return ann <*> return pos
changeNamesDecl nds (Expr e) = Expr <$> changeNames nds e

changeNames :: Set.Set String -> Node -> State (Map.Map String Int, Int) Node
changeNames nds (Identifier id pos) = processIdentifier Identifier nds id pos 
changeNames nds (FunctionDef args ret ns pos) = 
    FunctionDef <$> mapM (\(lhs, ann) -> (, ann) <$> changeNamesLhs nds lhs) args <*> return ret <*> mapM (changeNames nds) ns <*> return pos
changeNames nds (Return n pos) = flip Return pos <$> changeNames nds n
changeNames nds (Call n as pos) = Call <$> changeNames nds n <*> mapM (changeNames nds) as <*> return pos
changeNames nds access@Access{} = revampId nds access
changeNames nds (IfStmnt c ts es pos) = IfStmnt <$> changeNames nds c <*> mapM (changeNames nds) ts <*> mapM (changeNames nds) es <*> return pos
changeNames nds (IfExpr c t e pos) = IfExpr <$> changeNames nds c <*> changeNames nds t <*> changeNames nds e <*> return pos
changeNames nds (CreateNewType lhs as pos) = flip (CreateNewType lhs) pos <$> mapM (changeNames nds) as
changeNames nds (TypeDeductionNode lhs tExpr pos) = TypeDeductionNode <$> changeNamesLhs nds lhs <*> changeNamesTExpr nds tExpr <*> return pos
changeNames nds (Lit lit) = return $ Lit lit
changeNames nds (DeclN decl) = DeclN <$> changeNamesDecl nds decl
changeNames nds (StructN (Struct map pos)) = StructN <$> (Struct <$> mapM (changeNames nds) map <*> return pos)

changeNamesTExpr nds (NegateTypeDeduction tExpr) = NegateTypeDeduction <$> changeNamesTExpr nds tExpr
changeNamesTExpr nds (IsType lhs ann) = flip IsType ann <$> changeNamesLhs nds lhs
changeNamesTExpr nds (NotIsType lhs ann) = flip NotIsType ann <$> changeNamesLhs nds lhs

revampId nds (Access id@Identifier{} lhs pos) = Access <$> changeNames nds id <*> return lhs <*> return pos
revampId nds (Access x lhs pos) = Access <$> revampId nds x <*> return lhs <*> return pos
revampId _ n = error $ "Only call revampId with " ++ show n

generateLhsLua :: UserDefinedTypes -> Lhs -> String
generateLhsLua _ (LhsIdentifer id _) = id
generateLhsLua usts (LhsAccess accNode lhs _) = generateLua usts accNode ++ "." ++ show lhs

generateLuaDecl :: UserDefinedTypes -> Decl -> [Char]
generateLuaDecl usts (Decl lhs rhs _ _) = generateLhsLua usts lhs ++ " = " ++ generateLua usts rhs
generateLuaDecl usts (Assign lhs rhs _) = generateLhsLua usts lhs ++ " = " ++ generateLua usts rhs
generateLuaDecl usts (FunctionDecl lhs _ _) = "local " ++ generateLhsLua usts lhs
generateLuaDecl usts (StructDef lhs ann _) = "Is" ++ generateLhsLua usts lhs ++ " = " ++ generateLuaTypes usts ann
generateLuaDecl usts (OpenFunctionDecl lhs _ _) = generateLhsLua usts lhs ++ " = newOpenFunction()"
generateLuaDecl usts (ImplOpenFunction lhs args _ body _ pos) = 
    "newOpenInstance(" ++ show lhs ++ 
    ", function(" ++ intercalate ", " (map (show . fst) args) ++ ") return " ++
    intercalate " and " (map (\(lhs, ann) -> generateLua usts $ TypeDeductionNode lhs (IsType lhs ann) pos) args) ++ 
    " end, function(" ++ intercalate ", " (map (show . fst) args) ++ ")\n" ++ 
    indent (intercalate "\n" $ map (generateLua usts) body) ++ "\nend)"
generateLuaDecl usts (NewTypeDecl lhs (NewTypeAnnotation id args mp) _) = 
    "function " ++ id ++ "(" ++ intercalate ", " genArgs ++ ") return { _type = \"" ++ id ++ "\", _args = {" ++ intercalate ", " genArgs ++ "}, " ++ intercalate ", " (zipWith (\k v -> show k ++ " = " ++ v) (map fst (Map.toList mp)) genArgs) ++ "} end" where 
        genArgs = map (("x" ++) . show) [1 .. length args]
generateLuaDecl usts (NewTypeDecl lhs ann _) = error $ "The parser should only put NewTypeAnnotation here, not " ++ show ann
generateLuaDecl usts (Expr e) = generateLua usts e

generateLuaLit :: Lit -> String
generateLuaLit (LitInt i _) = show i
generateLuaLit (LitString s _) = show s
generateLuaLit (LitBool b _) = map toLower $ show b

generateLuaConstraints :: UserDefinedTypes -> Constraint -> String
generateLuaConstraints usts (ConstraintHas lhs cn) = generateLhsLua usts lhs ++ " = " ++ generateLuaConstraints usts cn
generateLuaConstraints usts (AnnotationConstraint ann) = generateLuaTypes usts ann

generateLuaTypes :: UserDefinedTypes -> Annotation -> String
generateLuaTypes usts (Annotation id) = "function(a) return Is" ++ id ++ "(a) end"
generateLuaTypes usts (AnnotationLiteral id) = "function(a) return Is" ++ id ++ "(a) end"
generateLuaTypes usts (FunctionAnnotation args ret) = "function(a) return IsFunction" ++ "(" ++ show (length args) ++ ")(a) end"
generateLuaTypes usts (StructAnnotation mp) = "function(a) return IsStruct({structSpec = {"++ intercalate ", " (map (\ (k, v) -> generateLhsLua usts k ++ " = " ++ generateLuaTypes usts v) $ Map.toList mp) ++ "}})(a) end"
generateLuaTypes usts (GenericAnnotation _ cns) = "function(a) return AnyMatching({constraintSpec = {" ++ intercalate ", " (map (generateLuaConstraints usts) cns) ++ "}})(a) end"
generateLuaTypes usts t@(NewTypeInstanceAnnotation id args) = "function(a) return IsNamedType({namedTypeSpec = {name = " ++ show id ++ ", args = {" ++ intercalate ", " (map (generateLuaTypes usts) args) ++ "}}})(a) end"
generateLuaTypes usts (TypeUnion ts) = "function(a) return Choice({" ++ intercalate ", " (Set.toList $ Set.map (generateLuaTypes usts) ts) ++ "})(a) end"
generateLuaTypes usts a = error $ "Cannot reach type annotation " ++ show a 

generateLua :: UserDefinedTypes ->  Node -> String
generateLua usts (DeclN decl) = generateLuaDecl usts  decl
generateLua usts (Identifier id _) = id
generateLua usts (Lit lit) = generateLuaLit lit
generateLua usts (FunctionDef args _ body _) = "function(" ++ intercalate ", " (map (generateLhsLua usts . fst) args) ++ ")\n" ++ indent (intercalate "\n" (map (forwardDeclareWholeLua usts) body ++ map (generateLua usts) body)) ++ "\nend"
generateLua usts (Return (Return n _) _) = "return " ++ generateLua usts n
generateLua usts (Return n _) = "return " ++ generateLua usts n
generateLua usts (Call e as _) = generateLua usts e ++ "(" ++ intercalate ", " (map (generateLua usts) as) ++ ")"
generateLua usts (StructN (Struct mp _)) = "{" ++ intercalate ", " (Map.elems $ Map.mapWithKey (\k v -> generateLhsLua usts k ++ " = " ++ generateLua usts v) mp) ++ "}"
generateLua usts (Access n lhs _) = generateLua usts n ++ "." ++ show lhs
generateLua usts (IfStmnt c ts es _) = "if " ++ generateLua usts c ++ " then\n" ++ indent (intercalate "\n" (map (forwardDeclareWholeLua usts) ts ++ map (generateLua usts) ts)) ++ "\nelse\n" ++ indent (intercalate "\n" (map (forwardDeclareWholeLua usts) es ++ map (generateLua usts) es)) ++ "\nend"
generateLua usts (IfExpr c t e _) = generateLua usts c ++ " and " ++ generateLua usts t ++ " or " ++ generateLua usts e
generateLua usts (CreateNewType lhs args _) = generateLhsLua usts lhs ++ "(" ++ intercalate ", " (map (generateLua usts) args) ++ ")"
generateLua usts (TypeDeductionNode _ tExpr _) = generateTypeDeductionLua usts tExpr 

generateTypeDeductionLua :: UserDefinedTypes -> TypeDeductionExpr -> [Char]
generateTypeDeductionLua usts (IsType lhs ann) = "IsType(" ++ generateLhsLua usts lhs ++ ", " ++ generateLuaTypes usts ann ++ ")"
generateTypeDeductionLua usts (NotIsType lhs ann) = "not IsType(" ++ generateLhsLua usts lhs ++ ", " ++ generateLuaTypes usts ann ++ ")"
generateTypeDeductionLua usts (NegateTypeDeduction typ) = "not " ++ generateTypeDeductionLua usts typ

forwardDeclareLua :: UserDefinedTypes -> Node -> Set.Set String
forwardDeclareLua usts (DeclN (StructDef lhs ann _)) = Set.fromList ["Is" ++ generateLhsLua usts lhs, generateLhsLua usts lhs]
forwardDeclareLua usts (DeclN (FunctionDecl lhs _ _)) = Set.singleton $ generateLhsLua usts lhs
forwardDeclareLua usts (DeclN (Decl lhs@LhsIdentifer{} _ _ _)) = Set.singleton $ generateLhsLua usts lhs
forwardDeclareLua usts (DeclN (OpenFunctionDecl lhs _ _)) = Set.singleton $ generateLhsLua usts lhs
forwardDeclareLua usts (DeclN (NewTypeDecl lhs ann _)) = Set.fromList ["Is" ++ generateLhsLua usts lhs, generateLhsLua usts lhs]
forwardDeclareLua _ _ = Set.empty

forwardDeclareWholeLua usts n = intercalate "\n" $ Set.toList $ Set.map (\x -> "local " ++ x ++ "\n") $ forwardDeclareLua usts n

class CodeGen a where
    generate :: a -> UserDefinedTypes -> Node -> String
    forwardDeclare :: a -> UserDefinedTypes -> Node -> String
    invoke :: a -> FilePath -> IO ()

data Lua = Lua

instance CodeGen Lua where
    generate = const generateLua
    forwardDeclare = const forwardDeclareWholeLua
    invoke Lua fn = callCommand $ "luajit " ++ fn

parseFile :: String -> [Char] -> Either String ([Node], [Node], (UserDefinedTypes, Annotations Annotation))
parseFile fn text = 
    case P.runParser Parser.wholeProgramParser fn (filter (/= '\t') text) of
        Right ns -> case typeCheckedScope ns of
            Left err -> Left $ show err
            Right a -> Right a
        Left e -> Left $ P.errorBundlePretty e

replaceExtenstion :: FilePath -> String -> String
replaceExtenstion fn ext = reverse (dropWhile (/= '.') (reverse fn)) ++ ext

main :: IO ()
main = do
    args <- getArgs
    let fn = head args
    text <- readFile fn
    case parseFile fn text of
        Right (ms, ns, (usts, as)) -> do
            printUsts usts *> print (f as)
            writeFile (replaceExtenstion fn "lua") $ "require 'runtime'\n\n" ++ intercalate "" (map (forwardDeclare Lua usts) nodes) ++ "\n\n" ++ intercalate "\n" (map (generate Lua usts) nodes)
            invoke Lua $ replaceExtenstion fn "lua"
            where 
                nodes = ms ++ nxs
                nxs = evalState (mapM (changeNames . Set.fromList . map show $ Map.keys baseMapping) ns) (Map.empty, 0)
        Left a -> putStrLn a
    where 
        p (LhsIdentifer k _) _
            | null $ tail k = True
            | head k == '_' && head (tail k) == '_' = False
            | otherwise = True
        p a _ = error $ "Unexpected pattern " ++ show a
        f (Annotations (mp, s) r) = Annotations (Map.filterWithKey p mp, s) r

        printUsts :: UserDefinedTypes -> IO ()
        printUsts usts = sequence_ $ Map.mapWithKey (\k v -> putStrLn $ show k ++ " = " ++ show v) usts