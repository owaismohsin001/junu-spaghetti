module Nodes where
import qualified Data.Map as Map
import Control.Monad.State ( State )
import Data.List
import Text.Megaparsec as P hiding (State)

data BinOp = BinOpNode Node String Node Pos

data Annotation = 
    Annotation String
    | AnnotationLiteral String
    | FunctionAnnotation [Annotation] Annotation 
    | StructAnnotation (Map.Map Lhs Annotation)
    deriving (Eq, Ord)

instance Show Annotation where
    show (Annotation id) = id
    show (AnnotationLiteral id) = id
    show (FunctionAnnotation anns an) = "(" ++ intercalate ", " (map show anns) ++ ") -> " ++ show an
    show (StructAnnotation anns) = 
        "{" ++ intercalate ", " (Map.elems $ Map.mapWithKey (\k v -> show k ++ ": " ++ show v) anns) ++ "}"

data LhsNoPos = 
    LhsIdentiferNoPos String 
    | LhsAccessNoPos NodeNoPos LhsNoPos
    deriving(Eq, Ord)

data Lhs = 
    LhsIdentifer String P.SourcePos
    | LhsAccess Node Lhs P.SourcePos

toLhsNoPos (LhsIdentifer a _) = LhsIdentiferNoPos a
toLhsNoPos (LhsAccess accNode id _) = LhsAccessNoPos (toNodeNoPos accNode) (toLhsNoPos id)

instance Show Lhs where
    show (LhsIdentifer a _) = a
    show (LhsAccess accNode id _) = show accNode ++ "." ++ show id

instance Eq Lhs where
    a == b = toLhsNoPos a == toLhsNoPos b

instance Ord Lhs where
    a `compare` b = toLhsNoPos a `compare` toLhsNoPos b

data Lit =
    LitInt Int P.SourcePos
    | LitBool Bool P.SourcePos
    | LitString String P.SourcePos
    deriving(Show)

data LitNoPos =
    LitIntNoPos Int
    | LitBoolNoPos Bool
    | LitStringNoPos String
    deriving(Show, Eq, Ord)

toLitNoPos :: Lit -> LitNoPos
toLitNoPos (LitInt i _) = LitIntNoPos i
toLitNoPos (LitBool b _) = LitBoolNoPos b
toLitNoPos (LitString s _) = LitStringNoPos s

instance Eq Lit where
    a == b = toLitNoPos a == toLitNoPos b

instance Ord Lit where
    a `compare` b = toLitNoPos a `compare` toLitNoPos b

data Decl =
    Decl Lhs Node (Maybe Annotation) P.SourcePos
    | Assign Lhs Node P.SourcePos
    | FunctionDecl Lhs Annotation P.SourcePos
    | StructDef Lhs Annotation P.SourcePos
    | Expr Node
    deriving(Show)

data DeclNoPos =
    DeclNoPos Lhs Node
    | AssignNoPos Lhs Node
    | FunctionDeclNoPos Lhs
    | StructDefNoPos Lhs Annotation
    | ExprNoPos Node
    deriving(Show, Eq, Ord)

toDeclNoPos :: Decl -> DeclNoPos
toDeclNoPos (Decl a b _ _) = DeclNoPos a b
toDeclNoPos (Assign a b _) = AssignNoPos a b
toDeclNoPos (StructDef a b _) = StructDefNoPos a b
toDeclNoPos (FunctionDecl a _ _) = FunctionDeclNoPos a
toDeclNoPos (Expr e) = ExprNoPos e

instance Eq Decl where
    a == b = toDeclNoPos a == toDeclNoPos b

instance Ord Decl where
    a `compare` b = toDeclNoPos a `compare` toDeclNoPos b

data Struct = Struct (Map.Map Lhs Node) P.SourcePos deriving(Show)
newtype StructNoPos = StructNoPos (Map.Map Lhs Node) deriving(Eq, Ord)

toStructNoPos :: Struct -> StructNoPos
toStructNoPos (Struct xs _) = StructNoPos xs

instance Eq Struct where
    a == b = toStructNoPos a == toStructNoPos b

instance Ord Struct where
    a `compare` b = toStructNoPos a `compare` toStructNoPos b

data Node =
    DeclN Decl
    | Identifier String P.SourcePos
    | Lit Lit
    | FunctionDef [(Lhs, Annotation)] (Maybe Annotation) [Node] P.SourcePos
    | Return Node P.SourcePos
    | Call Node [Node] P.SourcePos
    | StructN Struct
    | Access Node Lhs P.SourcePos
    | IfStmnt Node [Node] [Node] P.SourcePos
    | IfExpr Node Node Node P.SourcePos
    deriving(Show)

data NodeNoPos =
    DeclNNoPos Decl
    | IdentifierNoPos String
    | LitNoPos Lit
    | FunctionDefNoPos [(Lhs, Annotation)] (Maybe Annotation) [Node]
    | ReturnNoPos Node
    | CallNoPos Node [Node]
    | StructNNoPos Struct
    | AccessNoPos Node Lhs
    | IfStmntNoPos Node [Node] [Node]
    | IfExprNoPos Node Node Node
    deriving(Show, Ord, Eq)

toNodeNoPos :: Node -> NodeNoPos
toNodeNoPos (DeclN d) = DeclNNoPos d
toNodeNoPos (Identifier s _) = IdentifierNoPos s
toNodeNoPos (FunctionDef xs a b _) = FunctionDefNoPos xs a b
toNodeNoPos (Return n _) = ReturnNoPos n
toNodeNoPos (Call e as _) = CallNoPos e as
toNodeNoPos (StructN st) = StructNNoPos st
toNodeNoPos (Access a b _) = AccessNoPos a b
toNodeNoPos (IfStmnt a b c _) = IfStmntNoPos a b c
toNodeNoPos (IfExpr a b c _) = IfExprNoPos a b c

instance Eq Node where
    a == b = toNodeNoPos a == toNodeNoPos b

instance Ord Node where
    a `compare` b = toNodeNoPos a `compare` toNodeNoPos b

newtype Program = Program [Node] deriving (Show)

data Annotations = Annotations (Map.Map Lhs Annotation) (Maybe Annotations) deriving (Show)

type UserDefinedTypes = Map.Map Lhs Annotation

type AnnotationState = State (Annotation, (Annotations, UserDefinedTypes))

type Result = Either
