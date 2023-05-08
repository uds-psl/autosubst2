module Autosubst.Parser
  ( parseFrom -- for testing
  , parseFile
  , parseStdIn
  ) where

import           Autosubst.Names
import           Autosubst.Types
import           Control.Applicative  ((*>), (<$>), (<*), (<*>))
import           Control.Monad.Except
import           Control.Monad.State
import           Data.Either          (partitionEithers)
import qualified Data.Map             as M
import qualified Data.Set             as S
import           Text.Parsec          hiding (satisfy, token, tokens)
import           Text.Parsec.String

-- This file contains: 
-- 1. A ** lexer ** from String to [TokenPos]
-- 2. A ** parser ** from [TokenPos] to SpecAST
-- 3. A ** semantic analysis ** from SpecAST to Spec


--
-- Part 1: ** Lexing ** from String to [TokenPos]
--

-- Type of tokens
data Token = Ident String 
              | Quotes String String -- needed for the names/parameters of functors. First argument describes the functor name itself, second the (potential) parameters the user fills in, e.g. "vector 5"
              | Comment String 
              | TypeVariable String -- needed for type parameters
              | Comma 
              | LParen | RParen -- Parentheses
              | KColon 
              | KType -- Sorts
              | KArrow 
              | FType -- Functor declaration
              | LAngle | RAngle -- Used for functor applications
              | Begin String | End String -- Definition of a feature 
              | KMod -- Definition of a variant, :+:
              | KDef -- Definition of a variant, :=
             deriving (Show, Eq)  

type TokenPos = (Token, SourcePos)

parsePos :: Parser Token -> Parser TokenPos
parsePos p = flip (,) <$> getPosition <*> p

ident :: Parser Token
ident = Ident <$> ((:) <$> oneOf firstChar <*> (many $ oneOf rest))
  where firstChar = ['A'..'Z'] ++ ['a'..'z']
        rest      = firstChar ++ ['0'..'9']

typevar :: Parser Token
typevar = TypeVariable <$> ((:) <$> oneOf firstChar <*> (many $ oneOf rest))
  where firstChar = ['\'']
        rest      = ['a'..'z']

comm :: Parser Token
comm = Comment <$> (string "--" *> (many $ noneOf "\n"))

quoting :: Parser Token
quoting = do
  string "\""
  x <- many $ oneOf (['A'..'Z'] ++ ['a' .. 'z'])
  y <- many $ noneOf "\""
  string "\""
  return $ Quotes x y

begin :: Parser Token
begin = Begin <$> (string "begin " *> ((:) <$> oneOf firstChar <*> (many $ oneOf rest)))
  where firstChar = ['A'..'Z'] ++ ['a'..'z']
        rest      = firstChar ++ ['0'..'9']

end :: Parser Token
end = End <$> (string "end " *> ((:) <$> oneOf firstChar <*> (many $ oneOf rest)))
  where firstChar = ['A'..'Z'] ++ ['a'..'z']
        rest      = firstChar ++ ['0'..'9']

identifier, typevariable, comment, lparen, rparen, ftype, begin_, end_, ktype, karrow, kcolon, kmod, kdef, quotes :: Parser TokenPos
identifier = parsePos $ ident
comment = parsePos $ comm
lparen = parsePos $ char '(' >> return LParen
rparen = parsePos $ char ')' >> return RParen
comma = parsePos $ char ',' >> return Comma
kcolon = parsePos $ char ':' >> return KColon
ktype = parsePos $ string "Type" >> return KType
ftype = parsePos $ string "Functor" >> return FType
karrow = parsePos $ string "->" >> return KArrow
begin_ = parsePos $ begin
end_ = parsePos $ end
kmod = parsePos $ string ":+:" >> return KMod
kdef = parsePos $ string ":=" >> return KDef
typevariable = parsePos $ typevar
quotes = parsePos $ quoting
langle = parsePos $ char '<' >> return LAngle
rangle = parsePos $ char '>' >> return RAngle

token :: Parser TokenPos
token = choice [lparen, rparen, langle, rangle, comma, try kdef, try kmod, kcolon, try begin_, try end_, try ktype, try ftype, typevariable, identifier, try comment, try quotes, karrow]

tokens :: Parser [TokenPos]
tokens = spaces *> many (token <* spaces)

tokenize :: SourceName -> String -> Either ParseError [TokenPos]
tokenize = runParser tokens ()

--
-- Part 2: ** Parsing ** from [TokenPos] to SpecAST
--

-- Types, Etypes, Coercions, constructors

-- A specfication AST contains:
type SpecAST = (
                [TId], -- - The list of declared sorts
                [FId], -- - A list of declared functors 
                [ConstructorAST],  -- - A list of ASTs for constructors on the top-level
                [(FId, [ConstructorAST])], -- - A list of ASTs for constructors in features 
                [(TId, [TId])] -- - A list of variants (name of the variant and its subfeatures)  
                )

-- A constructor contains its name CId, a list of parameters (name and type), and its type.
type ConstructorAST = (CId, [(String, TId)], TypeAST) 

-- A TypeAST is constructed of arrows. Each node is then either a FunctorAST (possibly being an atomic type), or a VariadicAST which describes a variadic binder and can later only appear in a negative position.
data TypeAST = FunAST FunctorAST | ArrowAST TypeAST TypeAST | VariadicAST String TId deriving Show

-- A FunctorAST consists of either an atomic, or a functor with name of the functor (and optional parameters of the functor) and a list of types.
data FunctorAST = FunctorAST FId FId [FunctorAST] | AtomAST TId deriving Show 

-- a Parser on streams of Tokens, tagged with source positions
type TokParser a = Parsec [TokenPos] () a

advance :: SourcePos -> t -> [TokenPos] -> SourcePos
advance _ _ ((_, pos) : _) = pos
advance pos _ []           = pos

satisfy :: (TokenPos -> Bool) -> TokParser Token
satisfy f = tokenPrim show advance (\c -> if f c then Just (fst c) else Nothing)

-- Utility parser that recognizes (and yields) a specific token in the input stream
tok :: Token -> TokParser Token
tok t = (satisfy $ (== t) . fst) <?> show t

-- Test to recognize a generic comment in the input stream,
-- used for filtering out comments later.
isComment :: TokenPos -> Bool
isComment (Comment _, _) = True
isComment _              = False

-- Test to recognize a quote expression in the input stream,
-- used to implement the quote parser below.
isQuotes :: TokenPos -> Bool
isQuotes (Quotes _ _ , _) = True
isQuotes _                = False

parseQuote :: TokParser (Id, Id)
parseQuote = do
  Quotes i j <- (satisfy $ isQuotes)
  return (i,j)

-- Test to recognize an identifier in the input stream,
-- used to implement the ID parser below.
isIdent :: TokenPos -> Bool
isIdent (Ident _ , _) = True
isIdent _             = False

parseId :: TokParser Id
parseId = do
  Ident i <- (satisfy $ isIdent)
  return i

-- Test to recognize a type variable in the input stream,
-- used to implement the var parser below.
isTypevar :: TokenPos -> Bool
isTypevar (TypeVariable _ , _) = True
isTypevar _                    = False

parseTypevar :: TokParser Typevar
parseTypevar = do
  TypeVariable i <- (satisfy $ isTypevar)
  return i

-- For modular syntax
isBegin :: TokenPos -> Bool
isBegin (Begin _ , _) = True
isBegin _             = False

parseBegin :: TokParser Id
parseBegin = do
  Begin i <- (satisfy $ isBegin)
  return i

isEnd :: TokenPos -> Bool
isEnd (End _ , _) = True
isEnd _           = False

parseEnd :: TokParser Id
parseEnd = do
  End i <- (satisfy $ isEnd)
  return i

-- Top-level Parser: Parse all definitions
parseSpec :: TokParser SpecAST
parseSpec = do
  xs <- many parseDef
  let (x1, ys) = partitionEithers xs
      (x11, x12) = partitionEithers x1
      (x2, zs) = partitionEithers ys
      (x3, x4) = partitionEithers zs
  return $ (x11, x12, x2, x3, x4)

-- High-level definition of statements: Either the name of a sort, or a constructor with a type, or a feature declaration, or a variant declaration.
parseDef :: TokParser (Either (Either TId FId) (Either ConstructorAST (Either (FId, [ConstructorAST]) (TId, [TId]))))
parseDef = (Left <$> ((Left <$> (try parseTypeDef)) <|> (Right <$> (try parseFunvarDef)))) <|> (Right <$> ((Left <$> try parseConstructorDef) <|>  (Right <$> ((Left <$> try parseFeature)
    <|> Right <$> parseVariant))))

-- 1. Parser for type declarations
parseTypeDef :: TokParser TId
parseTypeDef = parseId <* tok KColon <* tok KType

-- 2. Parser for functor declarations
parseFunvarDef :: TokParser FId
parseFunvarDef = parseId <* tok KColon <* tok FType

-- 3. Parser for ConstructorAST 
parseConstructorDef :: TokParser (CId, [(String, TId)], TypeAST)
parseConstructorDef =  do
  x <- parseId
  pms <- many parseParameterDef -- requires parser for parameters
  t <- tok KColon *> parseCType -- requires parser for types 
  return (x, pms, t)

-- 3a. Parser for parameters  
parseParameterDef :: TokParser (String, TId)
parseParameterDef = do
  tok LParen
  x <- parseId
  tok KColon
  t <- parseId
  tok RParen
  return (x, t)

-- 3b. Parser for types
parseCType :: TokParser TypeAST
parseCType = foldr1 ArrowAST <$> parseAtomicCType `sepBy1` tok KArrow

-- atomic constructor types
parseAtomicCType :: TokParser TypeAST
parseAtomicCType = (tok LParen *> parseCType <* tok RParen) <|> (tok LAngle *> parseLType <* tok RAngle) <|> (FunAST <$> parseFType)

-- parser for variadic binders
parseLType :: TokParser TypeAST
parseLType = do
  m <- parseId
  tok Comma
  s <- parseId
  return (VariadicAST m s)

-- Functor Types
parseAtomicFType :: TokParser FunctorAST
parseAtomicFType = parseFType <|> (parseFType <* tok Comma)

parseFType :: TokParser FunctorAST
parseFType = (do
    (x, y) <- parseQuote
    tok LParen
    ts <- parseFType `sepBy1` tok Comma
    tok RParen
    return $ FunctorAST x y (ts)) <|>
    (do
    x <- parseId
    return $ AtomAST x)

-- 4. Parser for Features  
parseFeature :: TokParser (TId, [(CId, [(String, TId)], TypeAST)])
parseFeature = do
  x <- parseBegin
  xs <- many parseConstructorDef
  y <- parseEnd
  if (x == y) then return (x, xs) else unexpected ("Modular syntax block start " ++ x ++ " and block end " ++ y ++ " do not coincide.")

-- 5. Parser for Variants
parseVariant :: TokParser (TId, [TId])
parseVariant = do
  x <- parseId
  tok KDef
  xs <- parseId `sepBy1` tok KMod
  return $ (x, xs)


-- Part 3: ** Semantic Analysis / Input Validation ** from SpecAST to Spec

-- State Monad for Semantic Analysis, with a specification, used identifiers (possibly within a feature), and available injections (needed for modular syntax).
data SaState = SaState
  { spec       :: Spec -- specification
  , usedIds    :: [TId] -- used identifiers, possibly within a feature
  , usedFIds :: [FId]
  , injections :: [(TId, TId)] -- available injections
  }

type SA = StateT SaState (Except String)

-- Run of the state monad 
runSA :: Spec -> SA () -> Either String (Spec, [TId], [(TId, TId)]) 
runSA s sa = runExcept $ f <$> s'
  where initialState = SaState s [] [] []
        s' = execStateT sa initialState
        f :: SaState -> (Spec, [TId], [(TId, TId)])
        f s = (spec s, usedIds s, injections s)

-- List of identifiers which cannot be used in Coq definitions.
reservedIds :: S.Set Id
reservedIds = S.fromList
  -- Keywords according to the Coq manual
  ["as", "at", "cofix", "else", "end", "exists", "exists2", "fix",
   "for", "forall", "fun", "if", "IF", "in", "let", "match", "mod",
   "Prop", "return", "Set", "then", "Type", "using", "where", "with",
  -- Additional reserved identifiers
   "lazymatch", "multimatch", "Definition", "Fixpoint", "CoFixpoint",
   "Axiom", "Inductive", "CoInductive", "Theorem",
  -- Identifiers used by Autosubst
  "fin", "shift", "None", "Some", "scons", "var_zero", "fun_comp", "ap_ren", 
  "ap", "apc", "up_ren_ren", "id", "scons_eta", "scons_comp", "scons_eta_id", 
  "up_ren", "size_ind", retract_, "retract_inj", "retract_option", "lift",
  "get_In", "some_none_explosion", "Some_inj"
   ]

-- Top-Level checking of the specification. 
-- Yields a parser specfication, i.e. existing sorts, existing functors, the specification, injections, and variants
checkSpec :: SpecAST -> Either String ParserSpec
checkSpec (tps, fs, cs, features, combinations) = do
  (spec, tps', dps) <- runSA emptySpec $ declareTypes >> declareFunctors >> mapM_ (checkConstructor Nothing) cs >> mapM_ checkFeature features -- dps yields the injections
  return (reverse tps', fs, spec, dpf dps, combinations)
  where emptySpec = M.fromList $ map (\k -> (k,[])) tps
        declareTypes = mapM_ declareId tps 
        declareFunctors = mapM_ declareFId fs
        dpf dps x = concatMap (\(y, z) -> if (y == x) then [z] else []) dps

-- a. Declaration of types, check that no type name is a keyword according to the Coq manual and no type is defined twice
declareId :: Id -> SA ()
declareId x = do
  ids <- usedIds <$> get
  if x `elem` ids
    then throwError $ "identifier '" ++ x ++ "' is defined twice" 
    else if x `S.member` reservedIds
     then throwError $ "identifier '" ++ x ++ "' is reserved"
     else modify $ \state -> state{ usedIds = x : ids }

declareFId :: Id -> SA ()
declareFId x = do
  ids <- usedFIds <$> get
  if x `elem` ids
    then throwError $ "identifier '" ++ x ++ "' is defined twice" 
    else if x `S.member` reservedIds
     then throwError $ "identifier '" ++ x ++ "' is reserved"
     else modify $ \state -> state{ usedFIds = x : ids }

-- b. Checking of constructors, optional argument for feature ctx. 
checkConstructor :: Maybe String -> ConstructorAST -> SA ()
checkConstructor ctx (x,pms,typ) = do
  (_, ps,tp) <- checkPositions ctx typ
  declareConstructor tp (Constructor pms x ps)

-- i. Checking of positions: Gets a syntax tree and yields a position.

-- The first argument states whether we are in feature, the second is the syntax tree to examine.
-- Yields (optionally) parameters, a list of positions, and the result type.
checkPositions :: Maybe String -> TypeAST -> SA ([(String, TId)], [Position], TId)
checkPositions Nothing (FunAST (AtomAST x)) = return ([], [], x) -- simple constructor without any parameters or arguments
checkPositions (Just ctx) (FunAST (AtomAST x)) = do
  ids <- usedIds <$> get
  if (type_ x ctx) `elem` ids then return () else declareId (type_ x ctx) >> declareConstructor x (Constructor [] (in_ x ctx) [Position [] (Atom (type_ x ctx))]) -- add the feature sort in both the list of sorts and add a fitting constructor
  injs <- injections <$> get
  modify $ \state -> state{ injections = (type_ x ctx, x) : injs } -- Add the corresponding injection
  return ([], [], (type_ x ctx))
checkPositions ctx (ArrowAST b tp) = do
  (pm,p) <- checkPosition b
  (pms, ps, t) <- checkPositions ctx tp
  return (pm ++ pms, p:ps, t)
checkPositions _ (VariadicAST _ s) = throwError ("Variadic binder " ++ " " ++ show s ++ " not supported in the result type.")


-- Check of a single position.  
checkPosition :: TypeAST -> SA ([(String, TId)],Position)
checkPosition (FunAST f) = do -- position without binders 
  f' <- checkArgument f
  return $ ([], Position [] f')
checkPosition (ArrowAST (FunAST (AtomAST x)) b) = do -- atomic binder
  checkTId x
  (pms, Position bs a) <- checkPosition b
  return $ (pms, Position (Single x:bs) a)
checkPosition (ArrowAST (VariadicAST m x) b) = do -- variadic binder 
  checkTId x
  (pms, Position bs a) <- checkPosition b
  return $ (pms, Position ((BinderList m x) : bs) a)
checkPosition (ArrowAST (ArrowAST _ _) _) = throwError "third-order constructors are not supported"
checkPosition _ = throwError "binding of functors is not supported"

-- Check an argument
checkArgument :: FunctorAST -> SA Argument
checkArgument (AtomAST x) = do
    checkTId x
    return $ Atom x
checkArgument (FunctorAST f pms xs) = do
    checkFId f 
    xs' <- mapM checkArgument xs
    return $ FunApp f pms xs'

-- Check an identifier
checkTId :: TId -> SA ()
checkTId tp = do
  s <- spec <$> get
  if tp `M.member` s
    then return ()
    else throwError $ "unknown sort '" ++ tp ++ "'"

checkFId :: FId -> SA ()
checkFId tp = do
  s <- usedFIds <$> get
  if tp `elem` s
    then return ()
    else throwError $ "unknown functor '" ++ tp ++ "'"

-- ii. Declaration of constructor: Update to the specification after checking positions, and add the new constructor to the specification.
declareConstructor :: TId -> Constructor -> SA ()
declareConstructor tp c =
  modify $ \state -> state{ spec = updateSpec $ spec state }
  where updateSpec = M.insertWith (flip (++)) tp [c]

--  c. Checking of features : Check that all constructors are correct.
checkFeature :: (TId, [ConstructorAST]) -> SA ()
checkFeature (x, cs) =  mapM_ (checkConstructor (Just x)) cs

-- d. Checking of combinations : So far, nothing is checked to ensure that all features exist.
checkCombination :: [(TId, [TId])] -> SA ()
checkCombination xs = return ()

--
-- ** Top Level Interface **
--
parseFrom :: String -> String -> Either String ParserSpec
parseFrom src input =
  case tokenize src input of
    Left err -> Left $ show err
    Right ts -> either (Left . show) checkSpec $ runParser parseSpec () src . filter (not . isComment) $ ts

parseFile :: FilePath -> IO (Either String ParserSpec)
parseFile f = do
  input <- readFile f
  return $ parseFrom f input

parseStdIn :: IO (Either String ParserSpec)
parseStdIn = do
  s <- getContents
  return $ parseFrom ":stdin:" s

--
-- ** Testing Interface **
--
testParser :: String -> String -> IO ()
testParser src cnt =
  case tokenize src cnt of
    Left e    -> putStrLn $ show e
    Right ts' -> parseTest parseSpec . filter (not . isComment) $ ts'
