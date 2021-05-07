module Parser where

import Data.Void ( Void )
import Data.Char ( toLower )
import Data.List ( intercalate, partition, concat )
import Text.Megaparsec as P hiding (State)
import Text.Megaparsec.Char ( string, char, space, numberChar )
import Debug.Trace ( trace )
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Data.Set as Set
import Control.Monad
import qualified Data.Map.Ordered as Map
import Nodes

type Parser = Parsec Void String

lower :: Parser Char
lower = oneOf "abcdefghijklmnopqrstuvwxyz" :: Parser Char
upper = oneOf "ABCDEFGHIJKLMNOPQRSTUVWXYZ" :: Parser Char
digit = oneOf "1234567890" :: Parser Char
newline = oneOf "\n;" :: Parser Char
newlines = P.many Parser.newline
skipLines = newlines *> spaces *> newlines *> spaces
space = oneOf " " :: Parser Char
spaces = P.many Parser.space
mspaces = Parser.space *> Parser.spaces
dollar = oneOf "$" :: Parser Char
keyword k = Text.Megaparsec.Char.string (showL k) :: Parser String

eofParser :: Parser String
eofParser = "" <$ eof

data Keyword =
    If
    | Else
    | True
    | False
    | Let
    | Return
    deriving(Show, Eq, Enum)

notKeyword :: Parser ()
notKeyword = try $ notFollowedBy $ choice keywords *> (Text.Megaparsec.Char.string " " <|> Text.Megaparsec.Char.string "\n") where
    keywords = map ((\a -> Text.Megaparsec.Char.string a :: Parser String) . showL) [If ..]

showL k = toLower x : xs where (x:xs) = show k

numberParser :: Parser Node
numberParser =
    do
        pos <- getSourcePos
        fs <- digit :: Parser Char
        str <- P.many digit :: Parser String
        return . Lit $ LitInt (read (fs : str)) pos

booleanParser :: Parser Node
booleanParser =
    do
        pos <- getSourcePos
        b <- keyword Parser.True <|> keyword Parser.False
        return . Lit $ LitBool (read b) pos

stringParser :: Char -> Parser Node
stringParser c =
    do
        pos <- getSourcePos
        str <- (char c *> manyTill L.charLiteral (char c)) :: Parser String
        return . Lit $ LitString str pos

returnParser :: Parser Node
returnParser = flip Nodes.Return <$> getSourcePos <*> (keyword Parser.Return *> spaces *> exprParser <* spaces)

identifierPrefixParser f fs sn =
    do
        pos <- getSourcePos
        notKeyword
        fc <- fs
        lst <- P.many sn
        let ident = f (fc : lst) pos
        return ident

lhsLittleId :: Parser Lhs
lhsLittleId = identifierPrefixParser LhsIdentifer lower (lower <|> upper <|> digit)

littleId :: Parser Node
littleId = identifierPrefixParser Identifier lower (lower <|> upper <|> digit)

bigAnnotationId = identifierPrefixParser (\id _ -> Annotation id) upper (lower <|> upper <|> digit)

lhsParser :: Parser Lhs
lhsParser = choice $ map try [
    lhsLittleId
    ]

blockParser :: Parser a -> Parser [a]
blockParser p = spaces *> Text.Megaparsec.Char.string "{" *> P.many (skipLines *> p <* skipLines) <* Text.Megaparsec.Char.string "}"

blockOrExprParser :: Parser [Node]
blockOrExprParser = concat <$> (blockParser programStmntParser <|> ((\pos a -> [[Nodes.Return a pos]]) <$> getSourcePos <*> exprParser))

containerFunction :: [Char] -> String -> [Char] -> ([a] -> SourcePos -> b) -> Parser a -> Parser b
containerFunction strt end sep f p =
    do
        pos <- getSourcePos
        Text.Megaparsec.Char.string strt
        spaces
        exprs <- p `sepBy` comma
        spaces
        Text.Megaparsec.Char.string end
        return $ f exprs pos
    where comma = spaces *> Text.Megaparsec.Char.string sep <* spaces

tuple :: ([a] -> SourcePos -> b) -> Parser a -> Parser b
tuple = Parser.containerFunction "(" ")" ","

binOp mod f ops ret = do
  t1 <- f
  loop t1
  where termSuffix t1 = try (do
          pos <- getSourcePos
          spaces
          op <- ops
          spaces
          t2 <- f
          loop (ret t1 (mod op) t2 pos))
        loop t = termSuffix t <|> return t

unaryOp mod ops f ret = (\pos op exp -> ret (mod op) exp pos)
    <$> getSourcePos 
    <*> ops
    <*> (spaces *> f <* spaces)


binCall :: Node -> String -> Node -> SourcePos -> Node
binCall a op b pos = Call (Identifier op pos) [a, b] pos

unaryCall op a pos = Call (Identifier op pos) [a] pos

modOp "==" = "eq"
modOp "!=" = "neq"
modOp ">=" = "gte"
modOp ">" = "gt"
modOp "<" = "lt"
modOp "<=" = "lte"
modOp "&" = "and"
modOp "|" = "or"
modOp "+" = "add"
modOp "-" = "sub"
modOp "/" = "div"
modOp "*" = "mul"

modUnaryOp "!" = "not"
modUnaryOp "-" = "neg"

exprParser :: Parser Node
exprParser = binOp modOp compExprParser (Text.Megaparsec.Char.string "&" <|> Text.Megaparsec.Char.string "|") binCall

compExprParser :: Parser Node
compExprParser = binOp modOp arithExprParser ops binCall where
    ops =
        (
        Text.Megaparsec.Char.string "==" 
        <|> Text.Megaparsec.Char.string "!="
        <|> Text.Megaparsec.Char.string ">="
        <|> Text.Megaparsec.Char.string ">"
        <|> Text.Megaparsec.Char.string "<="
        <|> Text.Megaparsec.Char.string "<"
        ) :: Parser String


arithExprParser :: Parser Node
arithExprParser = binOp modOp termParser (Text.Megaparsec.Char.string "+" <|> Text.Megaparsec.Char.string "-") binCall

termParser :: Parser Node
termParser = binOp modOp atomParser (Text.Megaparsec.Char.string "*" <|> Text.Megaparsec.Char.string "/") binCall

atomParser :: Parser Node
atomParser = do
        exp <- possibles
        pos <- getSourcePos
        (foldToCalls exp pos <$> calls exp) <|> return exp
    where 
        foldToCalls exp pos xs = foldl (\a b -> Call a b pos) exp xs
        calls exp = (:) <$> tuple const exprParser <*> many (tuple const exprParser)
        possibles = choice $ map try [
            numberParser,
            booleanParser,
            stringParser '\"',
            returnParser,
            unaryOp modUnaryOp (Text.Megaparsec.Char.string "-") atomParser unaryCall,
            unaryOp modUnaryOp (Text.Megaparsec.Char.string "!") compExprParser unaryCall,
            funExprParser,
            littleId,
            Text.Megaparsec.Char.string "(" *> exprParser <* Text.Megaparsec.Char.string ")"
            ]

annotationParser :: Parser Annotation
annotationParser = 
    bigAnnotationId
    <|> (FunctionAnnotation <$> tuple const annotationParser <*> (spaces *> Text.Megaparsec.Char.string "->" *> spaces *> annotationParser))

declParser :: Parser Decl
declParser = (\pos lhs ann expr -> Decl lhs expr ann pos) 
    <$> getSourcePos 
    <*> (keyword Let *> spaces *> lhsParser <* spaces)
    <*> (
        try (Just <$> (spaces *> Text.Megaparsec.Char.string ":" *> spaces *> annotationParser <* spaces))
        <|> (Nothing <$ Text.Megaparsec.Char.string "")
        )
    <*> rhsEq
    where rhsEq = spaces *> Text.Megaparsec.Char.string "=" *> spaces *> exprParser

funDeclAssignParser :: Parser [Decl]
funDeclAssignParser = (\pos lhs args ret expr -> [
        FunctionDecl lhs (FunctionAnnotation (map snd args) ret) pos,
        Assign lhs (FunctionDef args (Just ret) expr pos) pos
        ])
    <$> getSourcePos
    <*> lhsLittleId
    <*> ls
    <*> (spaces *> Text.Megaparsec.Char.string "=>" *> spaces *> annotationParser)
    <*> blockOrExprParser
    where
        ls = tuple const ((,) <$> lhsLittleId <*> (spaces *> Text.Megaparsec.Char.string ":" *> spaces *> annotationParser))

funExprParser :: Parser Node
funExprParser = (\pos args ret expr -> FunctionDef args ret expr pos)
    <$> getSourcePos
    <*> ls
    <*> (spaces *> Text.Megaparsec.Char.string "=>" *> spaces *> ((Just <$> annotationParser) <|> return Nothing))
    <*> blockOrExprParser
    where
        ls = tuple const ((,) <$> lhsLittleId <*> (spaces *> Text.Megaparsec.Char.string ":" *> spaces *> annotationParser))

funDeclParser = (\pos lhs argTypes ret -> FunctionDecl lhs (FunctionAnnotation argTypes ret) pos)
    <$> getSourcePos
    <*> lhsLittleId
    <*> ls
    <*> (spaces *> Text.Megaparsec.Char.string "=>" *> spaces *> annotationParser)
    where
        ls = tuple const annotationParser


assignmentParser :: Parser Decl
assignmentParser = (\pos lhs expr -> Assign lhs expr pos)
    <$> getSourcePos 
    <*> lhsParser 
    <*> (spaces *> Text.Megaparsec.Char.string "=" *> spaces *> exprParser)

singleStmntParser :: Parser Node
singleStmntParser = choice $ map try [
        DeclN <$> declParser,
        DeclN <$> assignmentParser
        ]

programStmntParser :: Parser [Node]
programStmntParser = choice $ map try [
    (:[]) <$> singleStmntParser,
    try (map DeclN <$> funDeclAssignParser),
    (: []) . DeclN <$> funDeclParser,
    (:[]) <$> exprParser
    ]

wholeProgramParser :: Parser [Node]
wholeProgramParser = (concat <$> (programStmntParser `endBy` (eofParser <|> skipLines))) <* eof