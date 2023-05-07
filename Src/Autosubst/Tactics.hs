{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Autosubst.Tactics where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.RWS       hiding ((<>))
import           Data.List               as L
import           Text.PrettyPrint.Leijen

import           Autosubst.GenM
import           Autosubst.Names
import           Autosubst.Syntax
import           Autosubst.Types

-- This file contains various functions to handle substitution objects

-- 1. Handling of Substitution Objects SubstTy 

-- Transforming substitution objects into a term
substToTerm :: TId -> SubstTy -> Term
substToTerm x xs = idApp x (substTerms xs)

-- -- TODO: FIX
-- toVar :: TId -> SubstTy -> GenM Term
-- toVar x ts = do
--   xs <- substOf x
--   x' <- extend_ x
--   let zs = filter (\(y, _) -> x' == y) (zip xs (substTerms ts))
--   if null zs then throwError ("Error in toVar function, sort " ++ show x ++ " does not exist.") else return $ snd $ head $ zs

-- Returns the corresponding component of a substitution vector
toVar :: TId -> SubstTy -> GenM Term
toVar x ts = do
  xs <- substOf x
  x' <- extend_ x
  let zs = filter (\(y, _) -> x' == y) (zip xs (substTerms ts))
  return $  if null zs then (idApp x [TermId "Error in toVar function.", TermId (show (null zs)), TermSubst ts]) else snd $ head $ zs

-- 1a) Casting 

cast :: TId -> TId -> [a] -> GenM [a]
cast x y xs = do
  arg_x <- substOf x
  arg_y <- substOf y
  return $ L.foldr (\(x, v) ws -> if x `elem` arg_y then v : ws else ws) [] (zip arg_x xs)

-- Going from sort x to y in a substitution object 
castSubst :: TId -> TId -> SubstTy -> GenM SubstTy
castSubst x y (SubstScope xs) = fmap SubstScope (cast x y xs)
castSubst x y (SubstRen xs)   = fmap SubstRen (cast x y xs)
castSubst x y (SubstSubst xs) = fmap SubstSubst (cast x y xs)
castSubst x y (SubstEq xs f)  = liftM2 SubstEq (cast x y xs) (return f)
castSubst x y (SubstConst xs) = return $ SubstConst xs

-- 1b) Lifting 

-- Lifting by a binder b.
up :: TId -> (TId -> Binder -> a -> a) -> [a] -> Binder -> GenM [a]
up x f n b = do
  xs <- substOf x
  return  $ map (\(p, n_i) -> f p b n_i)
            (zip xs n)

-- Lifting by a list of binders
ups :: TId -> (TId -> Binder -> a -> a) -> [a] -> [Binder] -> GenM [a]
ups x f = foldM (up x f)

upRen :: TId -> [Binder] -> Terms -> GenM Terms
upRen x bs xs = ups x (\z b xi -> idApp (upRen_ b z) (fst (variadicScopeParameters b) ++ [xi])) xs bs

upScope :: TId -> [Binder] -> Terms -> GenM Terms
upScope x bs terms = ups x (\z b n -> succ_ n z b ) terms bs

upSubstS :: TId -> [Binder] -> Terms -> GenM Terms
upSubstS x bs xs = ups x (\z b xi ->  idApp (up_ b z) (fst (variadicScopeParameters b) ++ [xi])) xs bs

up' :: TId -> (TId -> Binder -> a -> GenM a) -> [a] -> Binder -> GenM [a]
up' x f n b = do
  xs <- substOf x
  mapM (\(p, n_i) -> f p b n_i) (zip xs n)

upEq :: TId -> [Binder] -> Terms -> (TId -> Binder -> Term -> GenM Term)-> GenM Terms
upEq x bs xs f = foldM (up' x f) xs bs

-- Bind newly the binders bs in sort x in a substiution object
upSubst :: TId -> [Binder] -> SubstTy -> GenM SubstTy
upSubst x bs (SubstScope xs) = fmap SubstScope (upScope x bs xs)
upSubst x bs (SubstRen xs)   = fmap SubstRen (upRen x bs xs)
upSubst x bs (SubstSubst xs) = fmap SubstSubst (upSubstS x bs xs)
upSubst x bs (SubstEq xs f)  = liftM2 SubstEq (upEq x bs xs f) (return f)
upSubst x bs (SubstConst xs) = return $ SubstConst xs

-- 1c) Casting + Lifting

-- Mixture of casting and uping: Cast from x to y, while binding newly the list of binders bs.
castUpSubst :: TId -> [Binder] -> TId -> SubstTy -> GenM SubstTy
castUpSubst x bs y arg = do
  arg' <- castSubst x y arg
  upSubst y bs arg'

-- 2.) Small helpers

-- Making binders explicit
makeExplicitSingle :: CBinder -> CBinder
makeExplicitSingle (BinderImplicitName s)            = BinderName s
makeExplicitSingle (BinderImplicitNameType s t)      = BinderNameType s t
makeExplicitSingle (BinderImplicitScopeNameType s t) = BinderScopeNameType s t
makeExplicitSingle s                                 = s

makeExplicit :: [CBinder] -> [CBinder]
makeExplicit = map makeExplicitSingle

-- Construction of objects
variadicScopeParameters :: Binder -> ([Term], [CBinder])
variadicScopeParameters (Single x)       = ([], [])
variadicScopeParameters (BinderList m x) = ([TermId m], [BinderNameType [m] (TermConst Nat)])

variadicScopeParametersImplicit :: Binder -> ([Term], [CBinder])
variadicScopeParametersImplicit (Single x)       = ([], [])
variadicScopeParametersImplicit (BinderList m x) = ([TermId m], [BinderImplicitNameType [m] (TermConst Nat)])

-- Generation of names for a list of positions
genPatternNames :: String -> [Position] -> [String]
genPatternNames s xs = map (\x -> s ++ show x) (L.findIndices (const True) xs)

-- Construction of patterns, needed for lifting -- yields a fitting pattern of S and id corresponding to the base sort x and the binder b'
patternSId :: TId -> Binder -> GenM [Term]
patternSId x b = do
  xs <- substOf x
  hasRen <- hasRenamings x
  let shift = \y -> if hasRen then shift_ else (shift_ >>> idApp (var_ y) [TermSubst (SubstScope (map (const TermUnderscore) xs))])
  let shiftp = \p y -> if hasRen then idApp shift_p_ [TermId p] else (idApp shift_p_ [TermId p] >>> idApp (var_ y) [TermSubst (SubstScope (map (const TermUnderscore) xs))])
  up x (\y b _ -> case b of Single z -> if y == z then shift y else (TermConst Id)
                            BinderList p z -> if y == z then shiftp p y else (TermConst Id)) (map TermId xs) b

-- Same as PatternSId in the case that the sort needs no renamings
patternSIdNoRen :: TId -> Binder -> GenM [Term]
patternSIdNoRen x b = do
  xs <- substOf x
  let shift = \y -> shift_ 
  let shiftp = \p y -> idApp shift_p_ [TermId p]
  up x (\y b _ -> case b of Single z -> if y == z then shift y else (id_ TermUnderscore)
                            BinderList p z -> if y == z then shiftp p y else (id_ TermUnderscore)) (map TermId xs) b

-- Generation of arguments
introScopeTy :: (MonadReader Signature m, MonadError String m) => TId -> Term -> m Term
introScopeTy x s = do
                  args <- substOf x
                  return $ L.foldl (\t _ -> TermFunction nat t) s args

-- 3. Generation of Substitution Objects
introScopeVar :: String -> TId -> GenM (SubstTy, [CBinder])
introScopeVar s x = do
  args <- substOf x
  let scope = map (\x -> s ++ x) args
  return (SubstScope (map TermId scope), [BinderImplicitScopeNameType scope nat])

introRenScope :: (String, String) -> TId -> GenM ((SubstTy, SubstTy), [CBinder])
introRenScope (m, n) x = do
  (m, bm) <- introScopeVar m x
  (n, bn)<- introScopeVar n x
  return ((m, n), bm ++ bn)

introScopeVarS :: String -> GenM (Term, [CBinder])
introScopeVarS s = return (TermVar (TermId s), [BinderImplicitScopeNameType [s] nat])

introRenScopeS :: (String, String) -> GenM ((Term, Term), [CBinder])
introRenScopeS (m, n) = do
  (m, b_m) <- introScopeVarS m
  (n, b_n) <- introScopeVarS n
  return ((m, n), b_m ++ b_n)

--- Generation of terms and bindings for one renaming
genRenS :: String -> (Term, Term) -> GenM (Term, [CBinder])
genRenS s (m,n) = do
  s <- tfresh s
  return $ (TermId s, [BinderNameType [s] (renType m n)])

-- Generation of substitution objects for a list of renamings
genRen :: TId -> String -> (SubstTy, SubstTy) -> GenM (SubstTy, [CBinder])
genRen x xi (m,n) = do
  xs <- substOf x
  let xis = map (\x -> xi ++ x) xs
  let tys = map (\(m, n) -> TermFunction (fin_ m) (fin_ n)) (zip (substTerms m) (substTerms n))
  return $ (SubstRen (map TermId xis), map (\(x,t) -> BinderNameType [x] t) (zip xis tys))

genSubst :: TId -> String -> (SubstTy, SubstTy) -> GenM (SubstTy, [CBinder])
genSubst x sigma (m,n) = do
  xs <- substOf x
  let sigmas = map (\x -> sigma ++ x) xs
  tys <- mapM (\(y, m) -> do
      n' <- castSubst x y n
      return $ TermFunction (fin_ m) (idSubstApp y n')) (zip xs (substTerms m))
  return $ (SubstSubst (map TermId sigmas), map (\(x,t) -> BinderNameType [x] t) (zip sigmas tys))

introSubstScopeS :: (String, String) -> TId -> GenM ((Term, SubstTy), [CBinder])
introSubstScopeS (m,n) y = do
  (m, bm) <- introScopeVarS m
  (n, bn) <- introScopeVar n y
  return ((m, n), bm ++ bn)

genSubstS :: String -> (Term, SubstTy) -> TId -> GenM (Term, [CBinder])
genSubstS s (m, n) z = do
  s <- tfresh s
  return (TermId s, [BinderNameType [s] (substType m n z)])

-- Generation of equations
genEq :: TId -> String -> Term -> Term -> GenM (Term, [CBinder])
genEq x s sigma tau = do
  s <- tfresh s
  return $ (TermId s, [BinderNameType [s] (equiv_ sigma tau)])

genEqs :: TId -> String -> Terms -> Terms -> (TId -> Binder -> Term -> GenM Term) -> GenM (SubstTy, [CBinder])
genEqs x e sigma tau f = do
  xs <- substOf x
  let eq_names = map (\x -> e ++ x) xs
  let eqs =  map (\(sigma, tau) -> (equiv_ sigma tau)) (zip sigma tau)
  return $ (SubstEq (map TermId eq_names) f, map (\(s, t) -> BinderNameType [s] t) (zip eq_names eqs))


-- 4. Abbreviation for Terms 
var :: TId -> SubstTy -> Term
var x xs = idApp (var_ x) (substTerms xs)

renType :: Term -> Term -> Term
renType m n = TermFunction (fin_ m) (fin_ n)

substType :: Term -> SubstTy -> TId -> Term
substType m n y = TermFunction (fin_ m) (idSubstApp y n)

equiv_ :: Term -> Term -> Term
equiv_ s t =  TermForall [BinderName "x"] (TermEq (TermApp s [TermId "x"]) (TermApp t  [TermId "x"]))

-- Get the scope corresponding to x
finVar :: TId -> TmScope -> GenM Term
finVar x n = fmap fin_ (toVar x (SubstScope n))


-- TODO
cons__ :: TId -> Binder -> Term -> SubstTy -> Term
cons__ z (Single y) sigma m = if (z == y) then TermApp cons_ [zero_ z (Single y) m, sigma] else sigma
cons__ z (BinderList p y) sigma m = if (z == y) then idApp "scons_p " [TermId p, zero_ z (BinderList p y) m, sigma] else sigma

zero_ :: TId -> Binder -> SubstTy -> Term
zero_ x (Single y) m       = TermApp (var x m) [varZero_]
zero_ x (BinderList p y) m = idApp "zero_p" [TermId p] >>> var x m
