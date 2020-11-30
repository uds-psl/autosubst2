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

--
-- ** Lexing ** from String to [TokenPos]
--

data Token = Ident String | Quotes String String | Comment String | TypeVariable String | LAngle | RAngle | Comma | LParen | RParen | KColon | KType | FType | KArrow | Begin String | End String | KMod | KDef deriving (Show, Eq)

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
kmod = parsePos $ string "mod" >> return KMod
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
-- ** Parsing ** from [TokenPos] to SpecAST
--

-- Types, Etypes, Coercions, constructors
-- SpecASt contains: The list of sorts, the list of general constructors, a feature list with name of the feature + constructors, a modular list with name of the combining sort and subfeatures.
type SpecAST = ([TId], [FId], [ConstructorAST], [(TId, [ConstructorAST])], [(TId, [TId])])
type ConstructorAST = (CId, [(String, TId)], TypeAST)
data FunctorAST = FunctorAST FId FId [FunctorAST] | AtomAST TId deriving Show
data TypeAST = FunAST FunctorAST | ArrowAST TypeAST TypeAST | ListAST String TId deriving Show

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

-- Test to recognize an identifier in the input stream,
-- used to implemnt the ID parser below.
isIdent :: TokenPos -> Bool
isIdent (Ident _ , _) = True
isIdent _             = False

-- Test to recognize a type variable in the input stream,
-- used to implemnt the var parser below.
isTypevar :: TokenPos -> Bool
isTypevar (TypeVariable _ , _) = True
isTypevar _                    = False

isQuotes :: TokenPos -> Bool
isQuotes (Quotes _ _ , _) = True
isQuotes _                = False

-- The actual parsers

-- identifiers
parseId :: TokParser Id
parseId = do
  Ident i <- (satisfy $ isIdent)
  return i

parseQuote :: TokParser (Id, Id)
parseQuote = do
  Quotes i j <- (satisfy $ isQuotes)
  return (i,j)

-- identifiers
parseTypevar :: TokParser Typevar
parseTypevar = do
  TypeVariable i <- (satisfy $ isTypevar)
  return i

-- Functor Types
parseAtomicFType :: TokParser FunctorAST
parseAtomicFType = parseFType <|> (parseFType <* tok Comma)  -- (tok LParen *> parseFType <* tok RParen) <|> (AtomAST <$> parseId)

parseFType :: TokParser FunctorAST
parseFType = (do
    (x, y) <- parseQuote
    tok LParen
    ts <- parseFType `sepBy1` tok Comma
    --ts <- many (parseFType <* tok Comma)
    --t <- try parseFType
    tok RParen
    return $ FunctorAST x y (ts)) <|>
    (do
    x <- parseId
    return $ AtomAST x)

-- constructor types
parseAtomicCType :: TokParser TypeAST
parseAtomicCType = (tok LParen *> parseCType <* tok RParen) <|> (tok LAngle *> parseLType <* tok RAngle) <|> (FunAST <$> parseFType)

parseLType :: TokParser TypeAST
parseLType = do
  m <- parseId
  tok Comma
  s <- parseId
  return (ListAST m s)

parseCType :: TokParser TypeAST
parseCType = foldr1 ArrowAST <$> parseAtomicCType `sepBy1` tok KArrow

-- Parser: Either the name of a sort, or a constructor with a type, or a feature declaration, or a variant declaration.
parseDef :: TokParser (Either (Either TId FId) (Either (CId, [(String, TId)], TypeAST) (Either (TId, [(CId, [(String, TId)], TypeAST)]) (TId, [TId]))))
parseDef = (Left <$> ((Left <$> (try parseTypeDef)) <|> (Right <$> (try parseFunvarDef)))) <|> (Right <$> ((Left <$> try parseConstructorDef) <|>  (Right <$> ((Left <$> try parseFeature)
    <|> Right <$> parseCombination))))

parseTypeDef :: TokParser TId
parseTypeDef = parseId <* tok KColon <* tok KType

parseFunvarDef :: TokParser FId
parseFunvarDef = parseId <* tok KColon <* tok FType

parseParameterDef :: TokParser (String, TId)
parseParameterDef = do
  tok LParen
  x <- parseId
  tok KColon
  t <- parseId
  tok RParen
  return (x, t)

parseParametersDef :: TokParser [(String, TId)]
parseParametersDef = Text.Parsec.many parseParameterDef

parseConstructorDef :: TokParser (CId, [(String, TId)], TypeAST)
parseConstructorDef =  do
  x <- parseId
  pms <- parseParametersDef
  t <- tok KColon *> parseCType
  return (x, pms, t)

-- Parsers for modular syntax
isBegin :: TokenPos -> Bool
isBegin (Begin _ , _) = True
isBegin _             = False

isEnd :: TokenPos -> Bool
isEnd (End _ , _) = True
isEnd _           = False

parseBegin :: TokParser Id
parseBegin = do
  Begin i <- (satisfy $ isBegin)
  return i

parseEnd :: TokParser Id
parseEnd = do
  End i <- (satisfy $ isEnd)
  return i

parseFeature :: TokParser (TId, [(CId, [(String, TId)], TypeAST)])
parseFeature = do
  x <- parseBegin
  xs <- many parseConstructorDef
  y <- parseEnd
  return $ if (x == y) then (x, xs) else (x, xs)

parseCombination :: TokParser (TId, [TId])
parseCombination = do
  tok KMod
  x <- parseId
  tok KDef
  xs <- many parseId
  return $ (x, xs)

-- top level ASTs
parseSpec :: TokParser SpecAST
parseSpec = do
  xs <- many parseDef
  let (x1, ys) = partitionEithers xs
      (x11, x12) = partitionEithers x1
      (x2, zs) = partitionEithers ys
      (x3, x4) = partitionEithers zs
  return $ (x11, x12, x2, x3, x4)

-- ** Semantic Analysis / Input Validation ** from SpecAST to Spec

-- State Monad for Semantic Analysis

data SaState = SaState
  { spec       :: Spec
  , usedIds    :: [TId]
  , injections :: [(TId, TId)]
  }

type SA = StateT SaState (Except String)

runSA :: Spec -> SA () -> Either String (Spec, [TId], [(TId, TId)])
runSA s sa = runExcept $ f <$> s' -- (spec <$> s', usedIds <$> s')
  where initialState = SaState s [] []
        s' = execStateT sa initialState
        f :: SaState -> (Spec, [TId], [(TId, TId)])
        f s = (spec s,  (usedIds s), injections s)

-- Incomplete (?) list of identifiers which cannot be used in Coq definitions.
reservedIds :: S.Set Id
reservedIds = S.fromList
  -- Keywords according to the Coq manual
  ["as", "at", "cofix", "else", "end", "exists", "exists2", "fix",
   "for", "forall", "fun", "if", "IF", "in", "let", "match", "mod",
   "Prop", "return", "Set", "then", "Type", "using", "where", "with",
  -- Additional reserved identifiers
   "lazymatch", "multimatch", "Definition", "Fixpoint", "CoFixpoint",
   "Axiom", "Inductive", "CoInductive", "Theorem"]

declareId :: Id -> SA ()
declareId x = do
  ids <- usedIds <$> get
  if x `elem` ids
    then return () -- throwError $ "identifier '" ++ x ++ "' is defined twice" -- TODO: FIX
    else if x `S.member` reservedIds
    then throwError $ "identifier '" ++ x ++ "' is reserved"
    else modify $ \state -> state{ usedIds = x : ids }

declareConstructor :: TId -> Constructor -> SA ()
declareConstructor tp c =
  modify $ \state -> state{ spec = updateSpec $ spec state }
  where updateSpec = M.insertWith (flip (++)) tp [c]

checkTId :: TId -> SA ()
checkTId tp = do
  s <- spec <$> get
  if True -- tp `M.member` s
    then return ()
    else throwError $ "unknown type '" ++ tp ++ "'"

-- Check specifications
checkArgument :: FunctorAST -> SA Argument
checkArgument (AtomAST x) = do
    checkTId x
    return $ Atom x
checkArgument (FunctorAST f pms xs) = do
    checkTId f -- TODO: Change to checkFId.
    xs' <- mapM checkArgument xs
    return $ FunApp f pms xs'

-- Gets a syntax tree and yields a position.
checkPosition :: TypeAST -> SA ([(String, TId)],Position)
checkPosition (FunAST f) = do
  f' <- checkArgument f
  return $ ([], Position [] f')
checkPosition (ArrowAST (FunAST (AtomAST x)) b) = do
  checkTId x
  (pms, Position bs a) <- checkPosition b
  return $ (pms, Position (Single x:bs) a)
checkPosition (ArrowAST (ListAST m x) b) = do
  checkTId x
  (pms, Position bs a) <- checkPosition b
  return $ (pms, Position ((BinderList m x) : bs) a)
checkPosition (ArrowAST (ArrowAST _ _) _) = throwError "third-order constructors are not supported"
checkPosition _ = throwError "binding of functors is not supported"

-- The first argument states whether we are in feature, the second is the syntax tree to examine.
-- Yields (optionally) parameters, a list of positions, and the result type.
checkPositions :: Maybe String -> TypeAST -> SA ([(String, TId)], [Position], TId)
checkPositions Nothing (FunAST (AtomAST x)) = return ([], [], x)
checkPositions ctx (ArrowAST b tp) = do
  (pm,p) <- checkPosition b
  (pms, ps, t) <- checkPositions ctx tp
  return (pm ++ pms, p:ps, t)
-- checkPositions s = throwError ("result type must be pure" ++ " " ++ show s)
checkPositions (Just ctx) (FunAST (AtomAST x)) = do
  ids <- usedIds <$> get
  if (type_ x ctx) `elem` ids then return () else declareConstructor x (Constructor [] (in_ x ctx) [Position [] (Atom (type_ x ctx))])
  declareId (type_ x ctx)
  injs <- injections <$> get
  modify $ \state -> state{ injections = (type_ x ctx, x) : injs }
  return ([],  [], (type_ x ctx))


checkConstructor :: Maybe String -> ConstructorAST -> SA ()
checkConstructor ctx (x,pms,typ) = do
--  declareId x
  (_, ps,tp) <- checkPositions ctx typ
  declareConstructor tp (Constructor pms x ps)

checkSpec :: SpecAST -> Either String ([TId],[FId], Spec,TId -> [TId])
checkSpec (tps, fs, cs, features, combinations) = do
  (spec, tps', dps) <- runSA emptySpec $ declareTypes >>  mapM_ (checkConstructor Nothing) cs >> mapM_ checkFeature features
  return (reverse tps', fs, spec, dpf dps)
  where emptySpec = M.fromList $ map (\k -> (k,[])) tps
        declareTypes = mapM_ declareId tps
        dpf dps x = concatMap (\(y, z) -> if (y == x) then [z] else []) dps

-- TODO Think of additional necessary tests.

checkFeature :: (TId, [ConstructorAST]) -> SA ()
checkFeature (x, cs) =  mapM_ (checkConstructor (Just x)) cs

-- Combination : [(TId, [TId])]
checkCombination :: [(TId, [TId])] -> SA ()
checkCombination xs = return ()


--
-- ** Top Level Interface **
--
parseFrom :: String -> String -> Either String ([TId], [FId], Spec, TId -> [TId])
parseFrom src input =
  case tokenize src input of
    Left err -> Left $ show err
    Right ts -> either (Left . show) checkSpec $ runParser parseSpec () src . filter (not . isComment) $ ts
    -- Debugging: Left $ show ts
--    where f ts =

parseFile :: FilePath -> IO (Either String ([TId], [FId], Spec, TId -> [TId]))
parseFile f = do
  input <- readFile f
  return $ parseFrom f input

parseStdIn :: IO (Either String ([TId], [FId], Spec, TId -> [TId]))
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
