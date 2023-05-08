module Main where

import           Autosubst.GenCode
import           Autosubst.GenM
import           Autosubst.Parser
import           Autosubst.Signature
import           Autosubst.Types
import           Data.Semigroup          ((<>))
import           Options.Applicative
import           System.Directory
import           System.Environment
import           System.IO
import           Text.PrettyPrint.Leijen (Doc, displayS, renderPretty)
import           Data.List  

-- cmd argument structure
data Arguments = Args
  { inputFile      :: Maybe String
  , prover         :: Prover
  , forceOverwrite :: Bool
  , coqFile        :: Maybe String
  , lineWidth      :: Int }
  deriving (Show, Read)

-- the parser for comamnd line args
-- TODO: Update.
args :: Parser Arguments
args = Args
  <$> (optional $ strOption
      ( long "input"
      <> short 'i'
      <> metavar "SPEC"
      <> help "File containing the syntax specification. Reads from stdin if omitted." ))
  <*> (option auto
      ( long "prover"
      <> short 'p'
      <> metavar "PROVER"
      <> value Coq
      <> help "Prover for which code is generated. Choose Coq for well-scoped de Bruijn, UCoq for unscoped de Bruijn, ECoq to generate unscoped modular boilerplate without substitution boilerplate. Default is well-scoped Coq code." ))
  <*> switch
      ( short 'f'
      <> help "If set, program writes output files without checking if said files already exist.")
  <*> (optional $ strOption
      ( long "output"
      <> short 'o'
      <> metavar "OUT"
      <> help "The generated base Coq source file, extension of this name might be used when modular boilerplate is used. Writes to stdout if omitted." ))
  <*> option auto
      ( long "width"
      <> short 'w'
      <> metavar "WIDTH"
      <> value 140
      <> help "Sets the line width of the output document to WIDTH. Defaults to 140 characters.")

-- top level combines busniess logic and argument parsing
main :: IO ()
main = mainProg =<< execParser opts
  where
    opts = info (args <**> helper)
      ( fullDesc
     <> progDesc "Compiles a HOAS style syntax specification SPEC to a Coq source file with corresponding inductively defined de Bruijn sorts and corresponding multivariate parallel substitution operations."
     <> header "Autosubst 2 - Automatically generating substitutions for mutually recursive syntactic specifications" )

--
-- the actual business logic
--

-- writes a file.
writeFileOverwrite :: FilePath -> String -> IO ()
writeFileOverwrite file content = do hFlush stdout; appendFile file content

-- if the file already exists, the user is prompted for overwrite permission for each file 
-- the boolean flag is used to force write and don't prompt
checkProtection :: Bool -> FilePath -> IO Bool
checkProtection forced file = do 
    exists <- doesFileExist file 
    if not exists
      then return True
    else if forced 
      then removeFile file >> return True -- remove the file
    else do
      putStr $ "The file " ++ file ++ " already exists; overwrite? [y/n] "
      hFlush stdout
      c <- getLine
      if c /= "y"
          then (putStrLn $ "Not writing to " ++ file ++ " and all subsequent files.") >> return False
          else  removeFile file >> return True -- remove the file

generate :: Arguments -> Signature -> IO ()
generate args sig = do
  let prettyCodeE = either Left 
                          (Right . (\codes -> map  (\(loc, c) -> (loc, (($ "") . displayS . renderPretty 1.0 (lineWidth args)) c)) codes)) -- printing according to arguments
                          $ runGen sig (generateCode (prover args) (getFile (coqFile args))) -- run the code generation
  case (coqFile args) of -- Printing of code
    Just out -> either putStrLn 
                      (\mfiles -> mapM (\f -> checkProtection (forceOverwrite args) (prependName f out)) (nub (map fst mfiles)) -- check whether all files can be overwritten 
                                  >>= \bs -> if (foldl (&&) True bs) then mapM_ (\(f, c) -> writeFileOverwrite (prependName f out) c) mfiles else return ()) -- write all files
                      prettyCodeE
    Nothing -> putStrLn $ either id (\xs -> concat $ (map snd) xs) prettyCodeE

-- Get the prefix of the Coq file so that we can later on export the right file.
getFile :: Maybe String -> String 
getFile (Just ('.' : xs)) = []
getFile (Just (x : xs)) = x : getFile (Just xs)
getFile _ = []

mainProg :: Arguments -> IO ()
mainProg args = do
  specification <- case (inputFile args) of
    Just file -> parseFile file
    Nothing   -> parseStdIn
  either putStrLn (generate args) $ either Left buildSignature specification


prependName :: String -> FilePath -> FilePath
prependName prefix file  = reverse (f (reverse file))
  where f [] = reverse prefix 
        f (x : xs) = if (x : []) == "/" then  reverse prefix ++ x : xs else x : f xs