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

import           Autosubst.Automation
import           Autosubst.Signature
import           Autosubst.Syntax
import           Data.List                  as L

import           Autosubst.Agda
import           Autosubst.Coq
import           Autosubst.Lean
import           Autosubst.UCoq


-- TODO: Find a good solution for all up pairs.

genCode :: [(Binder, TId)] -> [([TId], [TId])] -> GenM [Sentence]
genCode all xs = do
-- let all = [(Single x, y) | x <- concat (map fst xs), y <- concat (map fst xs)] ++ [(BinderList "p" x, y) | x <- concat (map fst xs), y <- concat (map fst xs)]  -- get all up-pairs
--  xs <- filterM (\y -> fmap (not . null) (substOf (head y))) xs -- Filter xs to contain only those which have variables.
  (_, code) <- foldM (\(ups,sentences) (x, dps) -> do
                                  xs <- substOf (L.head x) -- All elements of a component have the same substitutions.
                                  mdps <- mapM realDeps x -- TODO: Wrong type.
                                  let up_x = [(Single x, y) | x <- xs, y <- xs] ++ [(BinderList "p" x, y) | x <- xs, y <- xs]
                                  code_x <- genCodeT x dps (L.filter (`elem` ups) up_x)
                                  return (if null dps then L.filter (\(p,q) -> (p,q) `notElem` up_x) ups else ups, sentences ++ [code_x])) -- || p `elem` concat mdps|| q `elem` concat mdps
                                  (all, []) xs
  return $ concat code

genE :: [(Binder, TId)] -> [([TId], [TId])]-> GenM [Sentence]
genE all xs = do
--  let all = [(Single x, y) | x <- concat (map fst xs), y <- concat (map fst xs)] ++ [(BinderList "p" x, y) | x <- concat (map fst xs), y <- concat (map fst xs)]  -- get all up-pairs
--  xs <- filterM (\y -> fmap (not . null) (substOf (head y))) xs -- Filter xs to contain only those which have variables.
  (_, code) <- foldM (\(ups,sentences) (x, dps) -> do
                                  xs <- substOf (L.head x)
                                  let up_x = [(Single x, y) | x <- xs, y <- xs] ++ [(BinderList "p" x, y) | x <- xs, y <- xs]
                                  code_x <- genModularSyntax True x dps (L.filter (`elem` ups) up_x)
                                  return (L.filter (`notElem` up_x) ups, sentences ++ [code_x]))
                                  (all, []) xs
  return $ concat code


-- Embedding in the monadic structure
generateCode :: Prover -> GenM ()
generateCode p = do
  spec <- components
  varSorts <- filterM isOpen (concat (map fst spec))
  substSorts <- filterM (\x -> do
                               xs <- substOf x
                               return $ not $ null xs) (concat (map fst spec))
  ups <- mapM (\x -> do
                     xs <- substOf (L.head x)
                     return $ [(Single x,y) | x <- xs, y <- xs] ++ [(BinderList "p" x,y) | x <- xs, y <- xs, p == Coq]) (map fst spec)
  let all = nub (concat ups)
  code <- genCode all spec
  modularCode <- genE all spec
  auto <- genAutomation varSorts (concat (map fst spec)) substSorts all
  renamingVector <- mapM hasRenamings (concatMap fst spec)
--  specVector <- mapM getSpec (concatMap fst spec)
  case p of Coq -> tell ([("", coqPreamble <$$> empty <$$> vsep (map (\s -> coqShow s <$$> empty) (code ++ auto)))]) -- tell [("", text ("Renamings: " ++ show renamingVector ++ "Specification:" ))]
            UCoq -> tell ([("", ucoqPreamble <$$> empty <$$> vsep (map (\s -> ucoqShow s <$$> empty) (code ++ auto)))])
            Lean -> tell ([("", leanPreamble <$$> empty <$$> vsep (map (\s -> leanShow s <$$> empty) (code ++ auto)))])
            Agda -> tell ([("", agdaPreamble <$$> empty <$$> vsep (map (\s -> agdaShow s <$$> empty) (code ++ auto)))])
            ECoq -> tell ([("", ecoqPreamble <$$> empty <$$> vsep (map (\s -> ucoqShow s <$$> empty) modularCode))])
  return ()
