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
import TypeChecker
import System.Process

generateLhsLua (LhsIdentifer id _) = id
generateLhsLua (LhsAccess accNode lhs _) = generateLua accNode ++ "." ++ show lhs

generateLuaDecl :: Decl -> [Char]
generateLuaDecl (Decl lhs rhs _ _) = "local " ++ generateLhsLua lhs ++ " = " ++ generateLua rhs
generateLuaDecl (Assign lhs rhs _) = generateLhsLua lhs ++ " = " ++ generateLua rhs
generateLuaDecl (FunctionDecl lhs _ _) = "local " ++ generateLhsLua lhs
generateLuaDecl (StructDef lhs ann _) = "Is" ++ generateLhsLua lhs ++ " = " ++ generateLuaTypes ann
generateLuaDecl (OpenFunctionDecl lhs _ _) = "local " ++ generateLhsLua lhs
generateLuaDecl (ImplOpenFunction lhs _ _ _ _ _) = "local " ++ generateLhsLua lhs
generateLuaDecl (NewTypeDecl lhs (NewTypeAnnotation id args mp) _) = 
    "function " ++ id ++ "(" ++ intercalate ", " genArgs ++ ") return { _type = \"" ++ id ++ "\", _args = {" ++ intercalate ", " genArgs ++ "}, " ++ intercalate ", " (zipWith (\k v -> show k ++ " = " ++ v) (map fst (Map.toList mp)) genArgs) ++ "} end" where 
        genArgs = map (("x" ++) . show) [1 .. length args]
generateLuaDecl (NewTypeDecl lhs ann _) = error $ "The parser should only put NewTypeAnnotation here, not " ++ show ann
generateLuaDecl (Expr e) = generateLua e

generateLuaLit :: Lit -> String
generateLuaLit (LitInt i _) = show i
generateLuaLit (LitString s _) = show s
generateLuaLit (LitBool b _) = map toLower $ show b

generateLuaConstraints :: Constraint -> String
generateLuaConstraints (ConstraintHas lhs cn) = generateLhsLua lhs ++ " = " ++ generateLuaConstraints cn
generateLuaConstraints (AnnotationConstraint ann) = generateLuaTypes ann

generateLuaTypes :: Annotation -> String
generateLuaTypes (Annotation id) = "function(a) return Is" ++ id ++ "(a) end"
generateLuaTypes (AnnotationLiteral id) = "function(a) return Is" ++ id ++ "(a) end"
generateLuaTypes (FunctionAnnotation args ret) = "function(a) return IsFunction" ++ "(" ++ show (length args) ++ ")(a) end"
generateLuaTypes (StructAnnotation mp) = "function(a) return IsStruct({structSpec = {"++ intercalate ", " (map (\ (k, v) -> generateLhsLua k ++ " = " ++ generateLuaTypes v) $ Map.toList mp) ++ "}})(a) end"
generateLuaTypes (GenericAnnotation _ cns) = "function(a) return AnyMatching({constraintSpec = {" ++ intercalate ", " (map generateLuaConstraints cns) ++ "}})(a) end"
generateLuaTypes (NewTypeInstanceAnnotation id args) = "function(a) return IsNamedType({namedTypeSpec = {name = " ++ show id ++ ", args = {" ++ intercalate ", " (map generateLuaTypes args) ++ "}}})(a) end"
generateLuaTypes (TypeUnion ts) = "function(a) return Choice({" ++ intercalate ", " (Set.toList $ Set.map generateLuaTypes ts) ++ "})(a) end"
generateLuaTypes a = error $ "Cannot reach type annotation " ++ show a 

generateLua :: Node -> String
generateLua (DeclN decl) = generateLuaDecl decl
generateLua (Identifier id _) = id
generateLua (Lit lit) = generateLuaLit lit
generateLua (FunctionDef args _ body _) = "function(" ++ intercalate ", " (map (generateLhsLua . fst) args) ++ ")\n" ++ indent (intercalate "\n" (map forwardDeclareWholeLua body ++ map generateLua body)) ++ "\nend"
generateLua (Return n _) = "return " ++ generateLua n
generateLua (Call e as _) = generateLua e ++ "(" ++ intercalate ", " (map generateLua as) ++ ")"
generateLua (StructN (Struct mp _)) = "{" ++ intercalate ", " (Map.elems $ Map.mapWithKey (\k v -> generateLhsLua k ++ " = " ++ generateLua v) mp) ++ "}"
generateLua (Access n lhs _) = generateLua n ++ "." ++ show lhs
generateLua (IfStmnt c ts es _) = "if " ++ generateLua c ++ " then\n" ++ indent (intercalate "\n" (map forwardDeclareWholeLua ts ++ map generateLua ts)) ++ "\nelse\n" ++ indent (intercalate "\n" (map forwardDeclareWholeLua es ++ map generateLua es)) ++ "\nend"
generateLua (IfExpr c t e _) = generateLua c ++ " and " ++ generateLua t ++ " or " ++ generateLua e
generateLua (CreateNewType lhs args _) = generateLhsLua lhs ++ "(" ++ intercalate ", " (map generateLua args) ++ ")"
generateLua (CastNode lhs ann _) = "IsType(" ++ generateLhsLua lhs ++ ", " ++ generateLuaTypes ann ++ ")"
generateLua (RemoveFromUnionNode lhs ann _) = "not IsType(" ++ generateLhsLua lhs ++ ", " ++ generateLuaTypes ann ++ ")"

forwardDeclareLua :: Node -> Set.Set String
forwardDeclareLua (DeclN (StructDef lhs ann _)) = Set.fromList ["Is" ++ generateLhsLua lhs, generateLhsLua lhs]
forwardDeclareLua (DeclN (FunctionDecl lhs _ _)) = Set.singleton $ generateLhsLua lhs
forwardDeclareLua (DeclN (Decl lhs@LhsIdentifer{} _ _ _)) = Set.singleton $ generateLhsLua lhs
forwardDeclareLua (DeclN (OpenFunctionDecl lhs _ _)) = Set.singleton $ generateLhsLua lhs
forwardDeclareLua (DeclN (NewTypeDecl lhs ann _)) = Set.fromList ["Is" ++ generateLhsLua lhs, generateLhsLua lhs]
forwardDeclareLua _ = Set.empty

forwardDeclareWholeLua n = intercalate "\n" $ Set.toList $ Set.map (\x -> "local " ++ x ++ "\n") $ forwardDeclareLua n

class CodeGen a where
    generate :: a -> Node -> String
    forwardDeclare :: a -> Node -> String
    invoke :: a -> FilePath -> IO ()

data Lua = Lua

instance CodeGen Lua where
    generate = const generateLua
    forwardDeclare = const forwardDeclareWholeLua
    invoke Lua fn = callCommand $ "luajit " ++ fn

parseFile :: String -> [Char] -> Either String ([Node], [Node], (UserDefinedTypes, Annotations Annotation))
parseFile fn text = 
    case P.runParser Parser.wholeProgramParser fn (filter (/= '\t') text) of
        Right ns -> typeCheckedScope ns
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
            writeFile (replaceExtenstion fn "lua") $ "require 'runtime'\n\n" ++ intercalate "" (map (forwardDeclare Lua) (ms++ns)) ++ "\n\n" ++ intercalate "\n" (map (generate Lua) (ms++ns))
            invoke Lua $ replaceExtenstion fn "lua"
        Left a -> putStrLn a
    where 
        p (LhsIdentifer k _) _
            | null $ tail k = True
            | head k == '_' && head (tail k) == '_' = False
            | otherwise = True
        p a _ = error $ "Unexpected pattern " ++ show a
        f (Annotations mp r) = Annotations (Map.filterWithKey p mp) r

        printUsts :: UserDefinedTypes -> IO ()
        printUsts usts = sequence_ $ Map.mapWithKey (\k v -> putStrLn $ show k ++ " = " ++ show v) usts