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
    | RigidAnnotation String [Constraint]
    | FunctionAnnotation [Annotation] Annotation 
    | StructAnnotation (Map.Map Lhs Annotation)
    | OpenFunctionAnnotation [Annotation] Annotation Annotation [Annotation]
    | NewTypeAnnotation String [Annotation] (Map.Map Lhs Annotation)
    | NewTypeInstanceAnnotation String [Annotation]
    | TypeUnion (Set.Set Annotation)
    
data AnnotationNoImpl = 
    AnnotationNoImpl String
    | AnnotationLiteralNoImpl String
    | GenericAnnotationNoImpl String
    | RigidAnnotationNoImpl String
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
toAnnotationNoImpl (RigidAnnotation a _) = RigidAnnotationNoImpl a 
toAnnotationNoImpl (GenericAnnotation a _) = GenericAnnotationNoImpl a 
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
    show (RigidAnnotation id consts) = "rigid " ++ id ++ "{" ++ intercalate ", " (map show consts) ++ "}"
    show (GenericAnnotation id consts) = id ++ "{" ++ intercalate ", " (map show consts) ++ "}"
    show (StructAnnotation anns) = 
        "{" ++ intercalate ", " (Map.elems $ Map.mapWithKey (\k v -> show k ++ ": " ++ show v) anns) ++ "}"
    show (OpenFunctionAnnotation anns ret for impls) = "(" ++ intercalate ", " (map show anns) ++ ") -> " ++ show ret ++ 
        " in {" ++ intercalate ", " (map show impls) ++ "} for " ++ show for
    show (NewTypeAnnotation n as res) = n ++ "(" ++ intercalate ", " (map show as) ++ ") = " ++ show res
    show (NewTypeInstanceAnnotation n as) = n ++ "(" ++ intercalate ", " (map show as) ++ ")"
    show (TypeUnion as) = "(" ++ intercalate " | " (map show (Set.toList as)) ++ ")"

data ConsistencyPass = RefineAssumtpions | VerifyAssumptions deriving(Eq)

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

instance Show Lit where
    show (LitInt i _) = show i
    show (LitBool b _) = show b
    show (LitString str _) = str

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

instance Show Decl where
    show (Decl lhs rhs ann _) = case ann of
        Just ann -> "let " ++ show lhs ++ ": " ++ show ann ++ " = " ++ show rhs
        Nothing -> "let " ++ show lhs ++ " = " ++ show rhs
    show (Assign lhs rhs _) = show lhs ++ " = " ++ show rhs
    show (FunctionDecl lhs ann _) = show lhs ++ " :: " ++ show ann
    show (StructDef lhs ann _) = show lhs ++ " :: " ++ show ann
    show (OpenFunctionDecl lhs ann _) = "open " ++ show lhs ++ " :: " ++ show ann
    show (ImplOpenFunction lhs args ret body ftr _) = "impl " ++ show lhs ++ "(" ++ intercalate ", " (map show args) ++ ") => " ++ show ret ++ "{\n" ++ indent (intercalate "\n" (map show body)) ++ "\n} for " ++ show ftr
    show (NewTypeDecl lhs ann _) = "newtype " ++ show lhs ++ ": " ++ show ann
    show (Expr n) = "Top-level Expr: " ++ show n

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

type Generic = Annotation

showPos :: SourcePos -> String
showPos (P.SourcePos s ln cn) = 
    "In file: " ++ s ++ ", at line: " ++ tail (dropWhile (/= ' ') (show ln)) ++ ", at colounm: " ++ tail (dropWhile (/= ' ') (show cn))

data ErrorType =
    InDefinitiveReturn (Maybe String) P.SourcePos
    | UnmatchedType Annotation Annotation P.SourcePos
    | UnmatchedConstraint Constraint Constraint P.SourcePos
    | ExpectedSomething String Annotation P.SourcePos
    | FieldNotFound Lhs Annotation P.SourcePos
    | UnsearchableType Lhs Annotation P.SourcePos
    | NoEstablishedRelationWith Annotation P.SourcePos 
    | UnmatchablePredicates Annotation P.SourcePos 
    | UnificationError Generic ErrorType
    | UnInferrableType (Maybe ErrorType) P.SourcePos
    | UnCallableType Annotation P.SourcePos
    | NoInstanceFound Annotation Annotation P.SourcePos
    | IrreconcilableAnnotatatedType Lhs Annotation Annotation P.SourcePos
    | InfiniteTypeError Generic Annotation P.SourcePos
    | UnExtendableType Annotation P.SourcePos
    | UninstantiableType Annotation P.SourcePos
    | UnspecifiableTypeSpecified P.SourcePos
    | NotOccuringTypeOpenFunction Annotation P.SourcePos
    | NoDefinitionFound Lhs P.SourcePos
    | CallError [Annotation] [Annotation] P.SourcePos
    | UnequalArguments [Annotation] [Annotation] P.SourcePos
    | NoTypeFound String P.SourcePos

instance Show ErrorType where
    show (InDefinitiveReturn Nothing pos) = "Function does not return\n" ++ showPos pos
    show (InDefinitiveReturn (Just id) pos) = "Function " ++ id ++ " does not return\n" ++ showPos pos
    show (UnmatchedType a b pos) = "Can't match expected type " ++ show a ++ " with given type " ++ show b ++ "\n" ++ showPos pos
    show (NotOccuringTypeOpenFunction ann pos) = "The argument " ++ show ann ++ " does not even once occur in the whole method\n" ++ showPos pos
    show (NoDefinitionFound lhs pos) = show lhs ++ " not found in this scope\n" ++ showPos pos
    show (UnCallableType ann pos) = "Can't call a value of type " ++ show ann ++ "\n" ++ showPos pos
    show (NoInstanceFound opf ann pos) = "Could find instance " ++ show opf ++ " for " ++ show ann ++ "\n" ++ showPos pos
    show (UnInferrableType (Just errT) pos) = "Could not infer the return type: " ++ show errT ++ "\n" ++ showPos pos
    show (UnInferrableType Nothing pos) = "Could not infer the type of function at \n" ++ showPos pos
    show (UnExtendableType ann pos) = "Cannot extend function " ++ show ann ++ "\n" ++ showPos pos
    show (UnspecifiableTypeSpecified pos) = "Forbidden to specify specified type variables\n" ++ showPos pos
    show (UninstantiableType ann pos) = show ann ++ " is not an instantiable type\n" ++ showPos pos
    show (ExpectedSomething s ann pos) = "Expected a type " ++ s ++ ", got type " ++ show ann ++ " from " ++ show ann ++ "\n" ++ showPos pos
    show (FieldNotFound lhs ann pos) = "No field named " ++ show lhs ++ " found in " ++ show ann ++ "\n" ++ showPos pos
    show (UnequalArguments anns1 anns2 pos) = "Unequal arguments " ++ show anns1 ++ " can't be matched with " ++ show anns2
    show (UnsearchableType lhs ann pos) = "Can't search for field " ++ show lhs ++ " in " ++ show ann ++ "\n" ++ showPos pos
    show (UnmatchedConstraint a b pos) = "Can't match expected constraint " ++ show a ++ " with the given constraint " ++ show b ++ "\n" ++ showPos pos
    show (UnmatchablePredicates ann pos) = "No set matching predicate notis " ++ show ann ++ "\n" ++ showPos pos
    show (NoEstablishedRelationWith r pos) = "No relation on " ++ show r ++ " has been established\n" ++ showPos pos
    show (CallError fargs args pos) = "Expected " ++ show fargs ++ " arguments but got " ++ show args ++ " args"
    show (UnificationError g err) = "Impossible unification in " ++  show g ++ " because of the error: " ++ show err
    show (IrreconcilableAnnotatatedType lhs ann val pos) = "In the definition of " ++ show lhs ++ " it wan not possible to reconcile annotated " ++ show ann ++ " with " ++ show val ++ "\n" ++ showPos pos
    show (InfiniteTypeError g ann pos) = "Cannot create infinite type " ++ show g ++ " in " ++ show g ++ " ~ " ++ show ann ++ "\n" ++ showPos pos 
    show (NoTypeFound annString pos) = "No type named " ++ annString ++ " found\n" ++ showPos pos

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
    | TypeDeductionNode Lhs TypeDeductionExpr P.SourcePos

indent = intercalate "\n" . map ("\t" ++) . lines

instance Show Node where
    show (DeclN decl) = show decl
    show (Identifier id _) = id
    show (Lit lit) = show lit
    show (FunctionDef args retAnn body _) = "(" ++ intercalate ", " (map show args) ++ ")" ++ " => " ++ show retAnn ++ " {\n" ++ indent (intercalate "\n" (map show body)) ++ "\n}"
    show (Return n _) = "return " ++ show n
    show (Call e args _) = show e ++ "(" ++ intercalate ", " (map show args) ++ ")"
    show (StructN struct) = show struct
    show (Access n lhs _) = show n ++ "." ++ show lhs
    show (IfStmnt c ts es _) = "if " ++ show c ++ "{\n" ++ indent (intercalate "\n" (map show ts)) ++ "\n}" ++ " else {\n" ++ indent (intercalate "\n" (map show es)) ++ "\n}"
    show (IfExpr c t e _) = "if " ++ show c ++ " then " ++ show t ++ " else " ++ show e
    show (CreateNewType lhs args _) = show lhs ++ "(" ++ intercalate ", " (map show args) ++ ")"
    show (TypeDeductionNode lhs t pos) = show lhs ++ " => " ++ show t ++ "\n" ++ show pos

data TypeDeductionExpr =
    IsType Lhs Annotation
    | NotIsType Lhs Annotation
    | NegateTypeDeduction TypeDeductionExpr
    deriving(Show, Ord, Eq)

negateDeduction :: TypeDeductionExpr -> TypeDeductionExpr
negateDeduction (IsType lhs ann) = NotIsType lhs ann
negateDeduction (NotIsType lhs ann) = IsType lhs ann
negateDeduction (NegateTypeDeduction typ) = NegateTypeDeduction $ negateDeduction typ

deductionNodesToDeductions :: Node -> TypeDeductionExpr
deductionNodesToDeductions (TypeDeductionNode lhs a pos) = a
deductionNodesToDeductions a = error $ "Can't remove types from " ++ show a

getFirstDeductionLhs :: TypeDeductionExpr -> Lhs
getFirstDeductionLhs (IsType lhs _) = lhs
getFirstDeductionLhs (NotIsType lhs _) = lhs
getFirstDeductionLhs (NegateTypeDeduction typ) = getFirstDeductionLhs typ

data NodeNoPos =
    DeclNNoPos Decl
    | IdentifierNoPos String
    | LitNoPos LitNoPos
    | FunctionDefNoPos [(Lhs, Annotation)] (Maybe Annotation) [Node]
    | ReturnNoPos Node
    | CallNoPos Node [Node]
    | StructNNoPos Struct
    | AccessNoPos Node Lhs
    | IfStmntNoPos Node [Node] [Node]
    | IfExprNoPos Node Node Node
    | CreateNewTypeNoPos Lhs [NodeNoPos]
    | TypeDeductionNodeNoPos Lhs TypeDeductionExpr
    deriving(Show, Ord, Eq)

toNodeNoPos :: Node -> NodeNoPos
toNodeNoPos (DeclN d) = DeclNNoPos d
toNodeNoPos (Identifier s _) = IdentifierNoPos s
toNodeNoPos (Lit lit) = LitNoPos $ toLitNoPos lit
toNodeNoPos (FunctionDef xs a b _) = FunctionDefNoPos xs a b
toNodeNoPos (Return n _) = ReturnNoPos n
toNodeNoPos (Call e as _) = CallNoPos e as
toNodeNoPos (StructN st) = StructNNoPos st
toNodeNoPos (Access a b _) = AccessNoPos a b
toNodeNoPos (IfStmnt a b c _) = IfStmntNoPos a b c
toNodeNoPos (IfExpr a b c _) = IfExprNoPos a b c
toNodeNoPos (CreateNewType a b _) = CreateNewTypeNoPos a (map toNodeNoPos b)
toNodeNoPos (TypeDeductionNode a b _) =  TypeDeductionNodeNoPos a b

instance Eq Node where
    a == b = toNodeNoPos a == toNodeNoPos b

instance Ord Node where
    a `compare` b = toNodeNoPos a `compare` toNodeNoPos b

newtype Program = Program [Node]

instance Show Program where
    show (Program ns) = intercalate "\n" $ map show ns

data Annotations a = Annotations (Map.Map Lhs a, Set.Set a) (Maybe (Annotations a))

instance Show a => Show (Annotations a) where
    show (Annotations (mp, _) res) = 
        intercalate "\n" $ Map.elems $ Map.mapWithKey (\k v -> show k ++ ": " ++ show v) mp

showTypes :: Show a => Annotations a -> String
showTypes (Annotations (_, types) rest) = "{" ++ intercalate ", " (Set.toList (Set.map show types)) ++ "}" ++ case rest of
    Just x -> " -> " ++ showTypes x
    Nothing -> ""

type UserDefinedTypes = Map.Map Lhs Annotation

type AnnotationState a = State (Annotation, ((Int, a), UserDefinedTypes))
type DefineTypesState a = State (Annotation, ((Int, Annotations a), Map.Map Annotation Lhs))

data Finalizeable a = Finalizeable Bool a

showWhole (Finalizeable b x) = "Finzalizeable " ++ show b ++ " " ++ show x 

instance Show a => Show (Finalizeable a) where
    show (Finalizeable _ a) = show a

instance Eq a => Eq (Finalizeable a) where
    (Finalizeable _ a) == (Finalizeable _ b) = a == b

instance Ord a => Ord (Finalizeable a) where
    (Finalizeable _ a) `compare` (Finalizeable _ b) = a `compare` b

fromFinalizeable :: Finalizeable a -> a
fromFinalizeable (Finalizeable _ a) = a

flipFinalizeable :: Finalizeable a -> Finalizeable a
flipFinalizeable (Finalizeable b a) = Finalizeable (not b) a

finalize :: Finalizeable a -> Finalizeable a
finalize (Finalizeable _ a) = Finalizeable True a

type TypeRelations = Map.Map Annotation (Set.Set Generic)
type SubstituteState = State (Annotation, ((TypeRelations, Map.Map Generic Annotation), UserDefinedTypes))

type TraversableNodeState = State (Int, [Decl])

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

data TwoSets a = TwoSets (Set.Set a) (Set.Set a) deriving(Show)

emptyTwoSets :: TwoSets a
emptyTwoSets = TwoSets Set.empty Set.empty

fromUnionLists :: (Ord a, Foldable f1, Foldable f2) => (f1 (Set.Set a), f2 (Set.Set a)) -> TwoSets a
fromUnionLists (s1, s2) = TwoSets (Set.unions s1) (Set.unions s2)

primary :: TwoSets a -> Set.Set a
primary (TwoSets set _) = set

secondary :: TwoSets a -> Set.Set a
secondary (TwoSets set _) = set

primaryMember :: Ord a => a -> TwoSets a -> Bool
primaryMember k (TwoSets set _) = Set.member k set

primaryIsNull :: TwoSets a -> Bool
primaryIsNull (TwoSets set _) = Set.null set

secondaryMember :: Ord a => a -> TwoSets a -> Bool
secondaryMember k (TwoSets _ set) = Set.member k set

secondaryIsNull :: TwoSets a -> Bool
secondaryIsNull (TwoSets _ set) = Set.null set