{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Autosubst.Automation (genAutomation) where

import           Autosubst.Coq
import           Autosubst.GenM
import           Autosubst.Names
import           Autosubst.Syntax
import           Autosubst.Tactics
import           Autosubst.Types
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Lazy
import           Data.List                as L

ifB :: Bool -> [a] -> [a]
ifB b xs = if b then xs else []

{- Generates the most basic automation for Autosusbt 2:
Assumes
- A list of sorts which contain variables (varSorts)
- A list of all sorts (xs)
- A list of all sorts which have substitution on them (substSorts)
- A list of up pairs. (upList)
-}
genAutomation :: [TId] -> [TId] -> [TId] ->[(Binder,TId)] -> GenM [Sentence]
genAutomation varSorts xs substSorts upList = do
  sortsWithRenamings <- filterM hasRenamings substSorts
  varRenSorts <- filterM hasRenamings varSorts
  substVSorts <- filterM (\x -> do
                                b <- (isFeature x)
                                return $ not b) substSorts
  upRenList <- filterM (\(b,x) ->  (hasRenamings x)) upList
  renVSorts <- filterM (\x -> do
                                b <- (isFeature x)
                                return $ not b) sortsWithRenamings
  let substFunctions = map subst_ substSorts ++  (map ren_ sortsWithRenamings)
      upFunctions = ["up_ren"] ++  (map (\(x,y) -> upRen_ x y) upRenList) ++ map (\(x,y) -> up_ x y) upList
      monadLemmas = concatMap (\x -> ["instId_" ++ x] ++ ["compComp_" ++ x, "compComp'_" ++ x]) substSorts
                    ++ concatMap (\x -> ["rinstId_" ++ x, "compRen_" ++x, "compRen'_" ++ x, "renComp_" ++ x, "renComp'_" ++ x, "renRen_" ++ x, "renRen'_" ++ x]) sortsWithRenamings
      varLemmas = concatMap (\x -> ["varL_" ++ x]) varSorts ++ concatMap (\x ->  ["varLRen_" ++ x]) varRenSorts
      starify = map (\x -> x ++ " in *")
      unfoldLemmas = ["subst1",  "subst2", "Subst1", "Subst2", "ids"] ++ ["ren1", "ren2",  "Ren1",  "Ren2"] ++ map substtc_ substVSorts ++  (map rentc_ renVSorts) ++ map vartc_ varSorts
      foldLemmas = map vartc_ varSorts ++ map (\x -> "(@ids _ " ++ vartc_ x ++ ")") varSorts
      unfold = SentenceTactic "auto_unfold"  (TacticRepeat $ TacticUnfold unfoldLemmas Nothing)
      unfold_star = SentenceTacticNotation ["\"auto_unfold\"", "\"in\"", "\"*\""] (TacticRepeat $ TacticUnfold unfoldLemmas (Just "in *"))
      asimpl' = SentenceTactic "asimpl'" (TacticRewrite Nothing substFunctions upFunctions (monadLemmas ++ varLemmas))
      autocase = SentenceTacticNotation ["\"auto_case\""] (TacticId "auto_case (asimpl; cbn; eauto)")
  implicits <- genScopeImplicits
  instances <- genInstances substSorts varSorts
  notation <- genNotation varSorts substSorts upList
  return $ implicits  ++ instances ++ notation ++ [unfold, unfold_star, asimpl', SentenceTactic "asimpl" (TacticSeq [TacticRepeat (TacticId "try unfold_funcomp"), TacticId "auto_unfold in *", TacticId "asimpl'", TacticRepeat (TacticId "try unfold_funcomp")])
              , SentenceId "Tactic Notation \"asimpl\" \"in\" hyp(J) := revert J; asimpl; intros J."
              , autocase
              , SentenceTacticNotation ["\"asimpl\"", "\"in\"", "\"*\""] (TacticSeq [TacticId "auto_unfold in *", TacticRewrite (Just "in *") substFunctions upFunctions (monadLemmas ++ varLemmas)])
              ] ++  (genSubstifyTactics sortsWithRenamings)

genSubstifyTactics :: [TId] ->  [Sentence]
genSubstifyTactics xs = [substify, renamify]
  where substify = SentenceTactic "substify" (TacticSeq $ [TacticId "auto_unfold"] ++  map (\x -> TacticId ("try repeat (erewrite " ++ rinstInstFun_ x ++ ")")) xs )
        renamify = SentenceTactic "renamify" (TacticSeq $ [TacticId "auto_unfold"] ++  map (\x -> TacticId ("try repeat (erewrite <- " ++ rinstInstFun_ x ++ ")")) xs )

genScopeImplicits :: GenM [Sentence]
genScopeImplicits = do
  sorts <- components
  fmap concat $ mapM (\x -> do
              b <- isOpen x
              nec <- fmap (not . null) (substOf x)
              cs' <- constructors x
              (n, _) <- introScopeVar "n" x
              return $ if nec then (map (\(Constructor _ c _) -> SentenceCommand $ Arguments c (sty_terms n))
                ([Constructor [] (var_ x) [] | b] ++ cs')) else [])
              (concat (map fst sorts))

genNotation :: [TId] -> [TId] -> [(Binder, TId)]-> GenM [Sentence]
genNotation varsorts substSorts upList = do
  upNotation <- mapM genUpNotationPrint upList
  substNotation <- mapM genSubstNotation substSorts
  varvar <- mapM extend_ varsorts
  return $ concat (map genNotationClass varvar) ++ concat upNotation ++ concat substNotation

genSubstNotation :: TId -> GenM [Sentence]
genSubstNotation x = do
  xs <- substOf x
  isRen <- hasRenamings x
  let subst_full = SentenceNotation ("s [ " ++ stringApp (map (\y -> "sigma" ++ y) xs) " ; " ++ " ]") (idApp (subst_ x)
            ((map (\y -> TermId ("sigma" ++ y)) xs) ++ [TermId "s"])) ("at level 7, left associativity, only printing") "subst_scope"
      ren_full = SentenceNotation ("s ⟨ " ++ stringApp (map (\y -> "xi" ++ y) xs) " ; " ++ " ⟩") (idApp (ren_ x)
                ((map (\y -> TermId ("xi" ++ y)) xs) ++ [TermId "s"])) ("at level 7, left associativity, only printing") "subst_scope"
      subst_comp = SentenceNotation ("[ " ++ stringApp (map (\y -> "sigma" ++ y) xs) " ; " ++ " ]") (idApp (subst_ x)
                ((map (\y -> TermId ("sigma" ++ y)) xs) )) ("at level 1, left associativity, only printing") "fscope"
      ren_comp = SentenceNotation ("⟨ " ++ stringApp (map (\y -> "xi" ++ y) xs) " ; " ++ " ⟩") (idApp (ren_ x)
                ((map (\y -> TermId ("xi" ++ y)) xs) )) ("at level 1, left associativity, only printing") "fscope"
  return $ [subst_full, subst_comp] ++ ifB isRen [ren_full, ren_comp]

stringApp :: [String] -> String -> String
stringApp [] z     = ""
stringApp [x] z    = x
stringApp (x:xs) z = x ++ z ++ stringApp xs z

genInstances :: [TId] -> [TId] -> GenM [Sentence]
genInstances substSorts varSorts = do
  substVSorts <- filterM (\x -> do
                                b <- (isFeature x)
                                return $ not b) substSorts
  isRen <- hasRenamings (head substSorts)
  substInstances <- mapM genSubstInstance substVSorts
  renInstances <- mapM genRenInstance substVSorts
  varInstances <- mapM genVarInstance varSorts
  return $ substInstances ++ ifB isRen renInstances ++ concat varInstances

genSubstInstance :: TId -> GenM Sentence
genSubstInstance x = do
  ((m,n), bmn) <- introRenScope ("m", "n") x
  (sigma, b)<- genSubst x "" (m,n)
  let bs = getTypes b
  xs <- substOf x
  return $ SentenceInstance bmn (substtc_ x)  (idApp ("Subst" ++ show (length xs)) (bs ++ [genType x m, genType x n])) (idApp ("@" ++ subst_ x) (sty_terms m ++ sty_terms n))

genRenInstance :: TId -> GenM Sentence
genRenInstance x = do
  ((m,n), bmn) <- introRenScope ("m", "n") x
  (sigma, b)<- genRen x "" (m,n)
  let bs = getTypes b
  xs <- substOf x
  return $ SentenceInstance bmn (rentc_ x)  (idApp ("Ren" ++ show (length xs)) (bs ++ [genType x m, genType x n])) (idApp ("@" ++ ren_ x) (sty_terms m ++ sty_terms n))


genVarInstance :: TId -> GenM [Sentence]
genVarInstance x = do
  (m, bm) <- introScopeVar "m" x
  xs <- substOf x
  mx <- toVar x m
  let varI = SentenceInstance bm (vartc_ x) (idApp "Var" [fin_ mx, genType x m]) (idApp ("@" ++ var_ x) (sty_terms m))
      varIPrint = SentenceNotation ("x '__" ++ x ++ "'") (idApp "@ids" [TermUnderscore, TermUnderscore, TermId (vartc_ x), TermId "x"]) ("at level 5, only printing, format \"" ++ "x __" ++ x ++ "\"")  "subst_scope"
      varPrint = SentenceNotation ("x '__" ++ x ++ "'") (idApp (var_ x) [TermId "x"]) ("at level 5, format \"" ++ "x __" ++ x ++ "\"")  "subst_scope"
      idPrint = SentenceNotation "'var'" (TermId (var_ x)) "only printing, at level 1" "subst_scope"
  return $ [varI, varPrint, varIPrint, idPrint]

genNotationClass :: TId ->  [Sentence]
genNotationClass x =
  let cl = [SentenceClass ("Up_" ++ x) [BinderName "X", BinderName "Y"] [("up_" ++ x, TermFunction (TermId "X") (TermId "Y"))]]
      notation = [SentenceNotation ("↑__" ++ x) (TermId ("up_" ++ x) ) ("only printing") "subst_scope"]
      in (cl ++ notation)

genUpNotationPrint :: (Binder, TId) -> GenM [Sentence]
genUpNotationPrint (Single b,y) = do
    ((m,n), bs) <- introSubstScopeS ("m", "n") y
    n' <- upSubst y [Single b] n
    let m' = succ_ m y (Single b)
        up_not_print = SentenceNotation ("↑__" ++ b) (TermId ( up_ (Single b) y) ) ("only printing") "subst_scope"
        up_instance = SentenceInstance bs ("Up" ++ "_" ++ b ++ "_" ++ y) (idApp ("Up_" ++ y) [TermUnderscore, TermUnderscore]) (idApp ("@" ++ up_ (Single b) y) ([m] ++ sty_terms n))
    return $ [up_not_print, up_instance]
genUpNotationPrint _ = return []
