{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Autosubst.GenCode (generateCode) where

import           Autosubst.Generator
import           Autosubst.ModularGenerator
import           Autosubst.Types
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.RWS          hiding ((<>))

import           Autosubst.GenM
import qualified Data.Map                   as M
import           Data.Maybe                 as Maybe
import           Prelude                    hiding ((<$>))
import           Text.PrettyPrint.Leijen

import           Autosubst.GenAutomation
import           Autosubst.Signature
import           Autosubst.Syntax
import           Data.List                  as L

import           Autosubst.PrintScoped
import           Autosubst.PrintUnscoped



genBindersFromList :: [TId] -> [(Binder, TId)]
genBindersFromList xs = [(Single x, y) | x <- xs, y <- xs] ++ [(BinderList "p" x, y) | x <- xs, y <- xs]


lastName :: String -> FilePath -> FilePath
lastName prefix file  = reverse (f (reverse file))
  where f [] = reverse prefix 
        f (x : xs) = if (x : []) == "/" then  reverse prefix else x : f xs

-- Main function, taking the corresponding prover and the suffix for the output file.
generateCode :: Prover -> String -> GenM ()
generateCode p out = do
  checkIncompatibility p
  spec <- components -- get all components
  fullspec <- fullComponents
  varSorts <- getVarSorts
  substSorts <- getSubstSorts
  allSorts <- allSorts'
  ups <- sigActualBinders 
  variants <- asks sigVariants  
  isMod <- sigMod
  let sortsWithoutFeatures = filter (\(x, y, m) -> not (isJust m)) fullspec
      allFeatures = nub $ concat $ map (\(x,y,m) -> maybeToList m) fullspec
  -- Generation of code
  printPreamble p Nothing isMod >> mapM (\x -> printPreamble p (Just x) isMod) allFeatures -- printing of the preamble in all files
  tellProver p Nothing [SentenceRequireExport (map (\x -> lastName x out) allFeatures)] -- Printing of exports in the base file
  genCode p out ups fullspec Nothing -- Generate          
  generateModCode p ups spec -- Generate modular code, TODO: Ensure this is printed in the version directly
  auto <- genAutomation varSorts allSorts substSorts ups -- Generate automation
  tellProver p Nothing auto -- Printing of the automation
  mapM (\(name, vs) -> put (Just vs) >> genCode p out ups sortsWithoutFeatures (Just name) >> tellProver p (Just name) auto) variants -- Print code for all variants
  return ()


-- Generates code for a list of up-pairs [(Binder, TId)] and   a list of components [([TId], [TId])].
genCode :: Prover -> String -> [(Binder, TId)] -> [([TId], [TId], Maybe String)] -> Maybe String -> GenM ()
genCode p out all xs file = do
  possibleFeatures <- get
  case possibleFeatures of
    Just possibleFeatures -> tellProver p file [SentenceRequireExport (map (\x -> lastName x out) possibleFeatures)]
    Nothing -> return ()
  (_, code) <- foldM (\(ups,sentences) (x, dps, feature) -> do
                                  xs <- substOf (L.head x) -- All elements of a component have the same substitutions.
                                  mdps <- mapM realDeps x 
                                  let up_x = genBindersFromList xs
                                  code_x <- genSentences x (concat mdps) (L.filter (`elem` ups) up_x) -- TODO: Before dps
                                  tellProver p (if isJust file then file else feature) code_x
                                  return (if null dps then L.filter (\(p,q) -> (p,q) `notElem` up_x) ups else ups, sentences ++ [code_x ])) 
                                  (all, []) xs
  return ()

-- Generation of Modular Code
generateModCode :: Prover -> [(Binder, TId)] -> [([TId], [TId])]-> GenM [Sentence]
generateModCode ECoq all xs = do
  (_, code) <- foldM (\(ups,sentences) (x, dps) -> do
                                  xs <- substOf (L.head x)
                                  let up_x = genBindersFromList xs
                                  code_x <- genSentencesMod True x dps (L.filter (`elem` ups) up_x)
                                  return (L.filter (`notElem` up_x) ups, sentences ++ [code_x]))
                                  (all, []) xs
  return $ concat code
generateModCode _ _ _ = return []

-- Printing of the corresponding preamble
printPreamble :: Prover -> Maybe String -> Bool -> GenM ()
printPreamble Coq file b = tell [(fromMaybe "" file, coqPreamble <$$> empty)]
printPreamble UCoq file b = tell [(fromMaybe "" file, ucoqPreamble b <$$> empty)]
printPreamble ECoq file b = tell [(fromMaybe "" file, ecoqPreamble <$$> empty)]

-- Printing of a list of sentences with the corresponding prover.
-- tellProver p f s prints with a printer p, into a file with possible prefix f, the list of sentences s.
tellProver :: Prover -> Maybe String -> [Sentence] -> GenM ()
tellProver Coq  file c  = tell ([(fromMaybe "" file,  empty <$$> vsep (map (\s -> coqShow s <$$> empty) c))])
tellProver UCoq file c = tell ([(fromMaybe "" file,  empty <$$> vsep (map (\s -> ucoqShow s <$$> empty) c))])
tellProver ECoq file c = tell ([(fromMaybe "" file,  empty <$$> vsep (map (\s -> ucoqShow s <$$> empty) c))])

