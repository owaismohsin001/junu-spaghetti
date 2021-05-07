import qualified Data.Map as Map
import Control.Monad
import Debug.Trace
import Control.Monad.State

data Annotation = 
    Annotation String
    | FunctionAnnotation [Annotation] Annotation
    deriving (Show, Eq, Ord)

data Lhs = LhsIdentifer String deriving(Show, Eq, Ord)

data Lit =
    LitInt Int
    | LitBool Bool
    deriving(Show, Eq, Ord)

data Decl =
    Decl Lhs Node (Maybe Annotation)
    | Assign Lhs Node (Maybe Annotation)
    | FunctionDecl (Map.Map Lhs Annotation) Annotation [Node]
    deriving(Show, Eq, Ord)

data Node =
    DeclN Decl
    | Identifier String
    | Lit Lit
    | FunctionDef (Map.Map Lhs Annotation) Annotation [Node]
    | Return Node
    deriving(Show, Eq, Ord)

newtype Program = Program [Node]

data Annotations = Annotations (Map.Map Lhs Annotation) (Maybe Annotations)

type AnnotationState = State (Annotation, Annotations)

type Result = Either

insertAnnotation :: Lhs -> Annotation -> AnnotationState Annotation
insertAnnotation k v = do
    modify (\(a, Annotations b o) -> (a, Annotations (Map.insert k v b) o))
    return v

getAnnotation :: Lhs -> Annotations -> Maybe Annotation
getAnnotation k (Annotations anns rest) = do
    case Map.lookup k anns of
        Just v -> Just v
        Nothing -> 
            case rest of
                Just a -> getAnnotation k a
                Nothing -> Nothing

getAnnotationState :: Lhs -> AnnotationState (Maybe Annotation)
getAnnotationState k = get >>= \(_, anns) -> return $ getAnnotation k anns

mapRight :: Monad m => m (Either a t) -> (t -> m (Either a b)) -> m (Either a b)
mapRight f f1 = do
        a <- f
        case a of
            Right a -> f1 a
            Left err -> return $ Left err

getAssumptionType :: Node -> AnnotationState (Result String Annotation)
getAssumptionType (DeclN (Decl lhs n a)) = case a of 
    Just a -> return $ Right a
    Nothing -> mapRight (getAssumptionType n) (fmap Right . insertAnnotation lhs)
getAssumptionType (DeclN (Assign lhs n a)) = case a of 
    Just a -> return $ Right a
    Nothing -> mapRight (getAssumptionType n) (fmap Right . insertAnnotation lhs)
getAssumptionType (FunctionDef args ret _) = return . Right $ FunctionAnnotation (Map.elems args) ret
getAssumptionType (Lit (LitInt _)) = return . Right $ Annotation "Int"
getAssumptionType (Lit (LitBool _)) = return . Right $ Annotation "Bool"
getAssumptionType (Identifier x) = do
    ann <- getAnnotationState (LhsIdentifer x)
    case ann of
        Just a -> return $ Right a
        Nothing  -> return . Left $ "Couldn't find any variable named " ++ x

assumeProgramMapping :: Program -> Annotations
assumeProgramMapping (Program xs) = snd $ execState (mapM getAssumptionType $ filter nonDecls xs) (Annotation "_", Annotations Map.empty Nothing) where
    nonDecls a@(DeclN Decl{}) = True
    nonDecls _ = False

assumeProgram :: Program -> Annotations
assumeProgram = assumeProgramMapping

sameTypes a b = if a == b then Just a else Nothing

consistentTypes :: Annotations -> Node -> Maybe Annotation
consistentTypes ans (DeclN (Decl lhs rhs _)) = join (sameTypes <$> consistentTypes ans rhs <*> getAnnotation lhs ans)
consistentTypes ans (DeclN (Assign lhs rhs _)) = join (sameTypes <$> consistentTypes ans rhs <*> getAnnotation lhs ans)
consistentTypes ans (FunctionDef args ret body) = 
    case mapM (consistentTypes ans') body of 
        Right a -> 
    where 
    ans' = Annotations args (Just ans)
consistentTypes ans (Identifier x) = getAnnotation (LhsIdentifer x) ans
consistentTypes _ (Lit (LitInt _)) = Just $ Annotation "Int"
consistentTypes _ (Lit (LitBool _)) = Just $ Annotation "Bool"

tests = map (consistentTypes (assumeProgram $ Program program)) program where 
    program = [
        DeclN $ Decl (LhsIdentifer "x") (Lit $ LitBool True) Nothing,
        DeclN $ Decl (LhsIdentifer "m") (Identifier "x") Nothing,
        DeclN $ Decl (LhsIdentifer "y") (Lit $ LitInt 0) Nothing,
        DeclN $ Assign (LhsIdentifer "x") (Lit $ LitInt 1) Nothing,
        DeclN $ Assign (LhsIdentifer "m") (Identifier "x") Nothing,
        DeclN $ Decl (LhsIdentifer "x") (
            FunctionDef 
                (Map.fromList [(LhsIdentifer "x", Annotation "Int")]) 
                (Annotation "Int") 
                [Return $ Identifier "x"]
            ) Nothing
        ]