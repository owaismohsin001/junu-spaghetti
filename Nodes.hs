module Nodes where
import qualified Data.Map as Map
import Control.Monad.State ( State )
import Data.List
import qualified Data.Set as Set
import Text.Megaparsec as P hiding (State)

data BinOp = BinOpNode Node String Node Pos

data Constraint = 
    AnnotationConstraint Annotation
    | ConstraintHas Lhs Constraint
    deriving(Eq, Ord)

instance Show Constraint where
    show (AnnotationConstraint ann) = show ann
    show (ConstraintHas lhs constr) = "." ++ show lhs ++ ": " ++ show constr

data Annotation = 
    Annotation String
    | AnnotationLiteral String
    | GenericAnnotation String [Constraint]
    | FunctionAnnotation [Annotation] Annotation 
    | StructAnnotation (Map.Map Lhs Annotation)
    | OpenFunctionAnnotation [Annotation] Annotation Annotation [Annotation]
    | NewTypeAnnotation String [Annotation] (Map.Map Lhs Annotation)
    | NewTypeInstanceAnnotation String [Annotation]
    | TypeUnion (Set.Set Annotation)

data AnnotationNoImpl = 
    AnnotationNoImpl String
    | AnnotationLiteralNoImpl String
    | GenericAnnotationNoImpl String [Constraint]
    | FunctionAnnotationNoImpl [AnnotationNoImpl] AnnotationNoImpl 
    | StructAnnotationNoImpl (Map.Map Lhs AnnotationNoImpl)
    | OpenFunctionAnnotationNoImpl [AnnotationNoImpl] AnnotationNoImpl AnnotationNoImpl
    | NewTypeAnnotationNoImpl String [AnnotationNoImpl] (Map.Map Lhs AnnotationNoImpl)
    | NewTypeInstanceAnnotationNoImpl String [AnnotationNoImpl]
    | TypeUnionNoImpl (Set.Set AnnotationNoImpl)
    deriving (Eq, Ord)

toAnnotationNoImpl :: Annotation -> AnnotationNoImpl
toAnnotationNoImpl (Annotation a) = AnnotationNoImpl a
toAnnotationNoImpl (AnnotationLiteral a) = AnnotationLiteralNoImpl a
toAnnotationNoImpl (GenericAnnotation a b) = GenericAnnotationNoImpl a b
toAnnotationNoImpl (FunctionAnnotation a b) = FunctionAnnotationNoImpl (map toAnnotationNoImpl a) (toAnnotationNoImpl b)
toAnnotationNoImpl (StructAnnotation map) = StructAnnotationNoImpl (Map.map toAnnotationNoImpl map)
toAnnotationNoImpl (OpenFunctionAnnotation a b c _) = OpenFunctionAnnotationNoImpl (map toAnnotationNoImpl a) (toAnnotationNoImpl b) (toAnnotationNoImpl c)
toAnnotationNoImpl (NewTypeAnnotation s a b) = NewTypeAnnotationNoImpl s (map toAnnotationNoImpl a) (Map.map toAnnotationNoImpl b)
toAnnotationNoImpl (NewTypeInstanceAnnotation a b) = NewTypeInstanceAnnotationNoImpl a (map toAnnotationNoImpl b)
toAnnotationNoImpl (TypeUnion as) = TypeUnionNoImpl $ Set.map toAnnotationNoImpl as

instance Eq Annotation where a == b = toAnnotationNoImpl a == toAnnotationNoImpl b
instance Ord Annotation where a `compare` b = toAnnotationNoImpl a `compare` toAnnotationNoImpl b

instance Show Annotation where
    show (Annotation id) = id
    show (AnnotationLiteral id) = id
    show (FunctionAnnotation anns an) = "(" ++ intercalate ", " (map show anns) ++ ") -> " ++ show an
    show (GenericAnnotation id consts) = id ++ "{" ++ intercalate ", " (map show consts) ++ "}"
    show (StructAnnotation anns) = 
        "{" ++ intercalate ", " (Map.elems $ Map.mapWithKey (\k v -> show k ++ ": " ++ show v) anns) ++ "}"
    show (OpenFunctionAnnotation anns ret for impls) = "(" ++ intercalate ", " (map show anns) ++ ") -> " ++ show ret ++ 
        " in {" ++ intercalate ", " (map show impls) ++ "} for " ++ show for
    show (NewTypeAnnotation n as res) = n ++ "(" ++ intercalate ", " (map show as) ++ ") = " ++ show res
    show (NewTypeInstanceAnnotation n as) = n ++ "(" ++ intercalate ", " (map show as) ++ ")"
    show (TypeUnion as) = intercalate " | " (map show (Set.toList as))

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
    | OpenFunctionDecl Lhs Annotation P.SourcePos
    | ImplOpenFunction Lhs [(Lhs, Annotation)] (Maybe Annotation) [Node] Annotation P.SourcePos
    | NewTypeDecl Lhs Annotation P.SourcePos
    | Expr Node
    deriving(Show)

data DeclNoPos =
    DeclNoPos Lhs Node
    | AssignNoPos Lhs Node
    | FunctionDeclNoPos Lhs
    | StructDefNoPos Lhs Annotation
    | OpenFunctionDeclNoPos Lhs Annotation
    | ImplOpenFunctionNoPos Lhs [(Lhs, Annotation)] (Maybe Annotation) [Node] Annotation
    | NewTypeDeclNoPos Lhs Annotation
    | ExprNoPos Node
    deriving(Show, Eq, Ord)

toDeclNoPos :: Decl -> DeclNoPos
toDeclNoPos (Decl a b _ _) = DeclNoPos a b
toDeclNoPos (Assign a b _) = AssignNoPos a b
toDeclNoPos (StructDef a b _) = StructDefNoPos a b
toDeclNoPos (FunctionDecl a _ _) = FunctionDeclNoPos a
toDeclNoPos (OpenFunctionDecl a b _) = OpenFunctionDeclNoPos a b
toDeclNoPos (ImplOpenFunction a b c d e _) = ImplOpenFunctionNoPos a b c d e
toDeclNoPos (NewTypeDecl a b _) = NewTypeDeclNoPos a b
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
    | CreateNewType Lhs [Node] P.SourcePos
    | CastNode Lhs Annotation P.SourcePos
    | RemoveFromUnionNode Lhs Annotation P.SourcePos 
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
    | CreateNewTypeNoPos Lhs [NodeNoPos]
    | CastNodeNoPos Lhs Annotation
    | RemoveFromUnionNodeNoPos Lhs Annotation
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
toNodeNoPos (CreateNewType a b _) = CreateNewTypeNoPos a (map toNodeNoPos b)
toNodeNoPos (CastNode a b _) = CastNodeNoPos a b
toNodeNoPos (RemoveFromUnionNode a b _) =  RemoveFromUnionNodeNoPos a b

instance Eq Node where
    a == b = toNodeNoPos a == toNodeNoPos b

instance Ord Node where
    a `compare` b = toNodeNoPos a `compare` toNodeNoPos b

newtype Program = Program [Node] deriving (Show)

data Annotations = Annotations (Map.Map Lhs Annotation) (Maybe Annotations)

instance Show Annotations where
    show (Annotations mp res) = (intercalate "\n" $ Map.elems $ Map.mapWithKey (\k v -> show k ++ ": " ++ show v) mp) -- ++ " -> " ++ show res

type UserDefinedTypes = Map.Map Lhs Annotation

type AnnotationState = State (Annotation, (Annotations, UserDefinedTypes))

type TypeRelations = Map.Map Annotation (Set.Set Annotation)
type SubstituteState = State (Annotation, ((TypeRelations, Map.Map Annotation Annotation), UserDefinedTypes))

newtype GenericPolicy = GenericPolicy{specifyGenericsAllowed :: Bool}

type Result = Either
data ComparisionReturns a b = 
    ComparisionReturns {
        success :: b -> Either a b, 
        failiure :: a -> Either a b,
        failout :: b -> b -> P.SourcePos -> Either a b
    }

openMethodGp :: GenericPolicy
openMethodGp = GenericPolicy{specifyGenericsAllowed = False}