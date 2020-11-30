{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Autosubst.Tactics where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.RWS       hiding ((<>))
import           Data.List               as L
import           Text.PrettyPrint.Leijen


import           Autosubst.Coq
import           Autosubst.GenM
import           Autosubst.Names
import           Autosubst.Syntax
import           Autosubst.Types


instance Show SubstTy where
  show (SubstScope _) = "substscope"
  show (SubstEq _ _)  = "substeq"
  show (SubstRen _)   = "substren"
  show (SubstSubst _) = "substsubst"

-- Handling of Vector Objects
toVar :: TId -> SubstTy -> GenM Term
toVar x ts = do
  xs <- substOf x
  x' <- extend_ x
  let zs = filter (\(y, _) -> x' == y) (zip xs (sty_terms ts))
  -- if (null zs) then throwError ("Error in toVar. Sort " ++ show ts ++ show x ++ " with extension " ++ show x' ++ ". Substitution vector of the sort: " ++ show xs) else return ()
  return $  if null zs then (idApp x [TermId "HERE in toVar.", TermId (show (null zs)), TermSubst ts]) else snd $ head $ zs

-- Going from one sort to another sort.
castSubst :: TId -> TId -> SubstTy -> GenM SubstTy
castSubst x y (SubstScope xs) = fmap SubstScope (cast x y xs)
castSubst x y (SubstRen xs)   = fmap SubstRen (cast x y xs)
castSubst x y (SubstSubst xs) = fmap SubstSubst (cast x y xs)
castSubst x y (SubstEq xs f)  = liftM2 SubstEq (cast x y xs) (return f)
castSubst x y (SubstConst xs) = return $ SubstConst xs

-- Lifting by a binder b.
up :: TId -> (TId -> Binder -> a -> a) -> [a] -> Binder -> GenM [a]
up x f n b = do
  xs <- substOf x
  return  $ map (\(p, n_i) -> f p b n_i)
            (zip xs n)

ups :: TId -> (TId -> Binder -> a -> a) -> [a] -> [Binder] -> GenM [a]
ups x f = foldM (up x f)

genType :: TId -> SubstTy -> Term
genType x xs = idApp x (sty_terms xs)

--upRenT :: TId -> Binder -> Term -> Term
--upRenT y b xi       = up_ren_ y b xi

upRen :: TId -> [Binder] -> Terms -> GenM Terms
upRen x bs xs = ups x (\z b xi -> idApp (upRen_ b z) (fst (bparameters b) ++ [xi])) xs bs

-- Successor has to be newly defined. succ_n should be dependent on what sort we have.
upScope :: TId -> [Binder] -> Terms -> GenM Terms
upScope x bs terms = ups x (\z b n -> succ_ n z b ) terms bs

upSubstS :: TId -> [Binder] -> Terms -> GenM Terms
upSubstS x bs xs = ups x (\z b xi ->  idApp (up_ b z) (fst (bparameters b) ++ [xi])) xs bs

up' :: TId -> (TId -> Binder -> a -> GenM a) -> [a] -> Binder -> GenM [a]
up' x f n b = do
  xs <- substOf x
  mapM (\(p, n_i) -> f p b n_i) (zip xs n)

upEq :: TId -> [Binder] -> Terms -> (TId -> Binder -> Term -> GenM Term)-> GenM Terms
upEq x bs xs f = foldM (up' x f) xs bs

-- Bind newly the binders bs.
upSubst :: TId -> [Binder] -> SubstTy -> GenM SubstTy
upSubst x bs (SubstScope xs) = fmap SubstScope (upScope x bs xs)
upSubst x bs (SubstRen xs)   = fmap SubstRen (upRen x bs xs)
upSubst x bs (SubstSubst xs) = fmap SubstSubst (upSubstS x bs xs)
upSubst x bs (SubstEq xs f)  = liftM2 SubstEq (upEq x bs xs f) (return f)-- m
upSubst x bs (SubstConst xs) = return $ SubstConst xs

cast :: TId -> TId -> [a] -> GenM [a]
cast x y xs = do
  arg_x <- substOf x
  arg_y <- substOf y
  return $ L.foldr (\(x, v) ws -> if x `elem` arg_y then v : ws else ws) [] (zip arg_x xs)

-- Mixture of casting and uping: Cast from x to y, while binding newly the list of binders bs.
castUpSubst :: TId -> [Binder] -> TId -> SubstTy -> GenM SubstTy
castUpSubst x bs y arg = do
  arg' <- castSubst x y arg
  upSubst y bs arg'

-- Handling of [CBinder]
explicitS_ :: CBinder -> CBinder
explicitS_ (BinderImplicitName s)            = BinderName s
explicitS_ (BinderImplicitNameType s t)      = BinderNameType s t
explicitS_ (BinderImplicitScopeNameType s t) = BinderScopeNameType s t
explicitS_ s                                 = s

explicit_ :: [CBinder] -> [CBinder]
explicit_ = map explicitS_

-- Construction of objects
finT_ :: TId -> TmScope -> GenM Term
finT_ x n = fmap fin_ (toVar x (SubstScope n))

bparameters :: Binder -> ([Term], [CBinder])
bparameters (Single x)       = ([], [])
bparameters (BinderList m x) = ([TermId m], [BinderNameType [m] (TermConst Nat)])

binvparameters :: Binder -> ([Term], [CBinder])
binvparameters (Single x)       = ([], [])
binvparameters (BinderList m x) = ([TermId m], [BinderImplicitNameType [m] (TermConst Nat)])


-- Construct S/Id patterns, needed for uping.
-- TODO: Generalize the shift. Instead of Single => Up by the number of the list.
patternSId :: TId -> Binder -> GenM [Term]
patternSId x b' = do
  xs <- substOf x
  hasRen <- hasRenamings x
  let shift = \y -> if hasRen then shift_ else (shift_ >>> idApp (var_ y) (map (const TermUnderscore) xs))
  let shiftp = \p y -> if hasRen then idApp "shift_p" [TermId p] else ( idApp "shift_p" [TermId p] >>> idApp (var_ y) (map (const TermUnderscore) xs))
  up x (\y b _ -> case b of Single z -> if y == z then shift y else (TermConst Id)
                            BinderList p z -> if y == z then shiftp p y else (TermConst Id)) (map TermId xs) b'

patternSIdNoRen :: TId -> Binder -> GenM [Term]
patternSIdNoRen x b' = do
  xs <- substOf x
  let hasRen = True
  let shift = \y -> if hasRen then shift_ else (shift_ >>> idApp (var_ y) (map (const TermUnderscore) xs))
  let shiftp = \p y -> if hasRen then idApp "shift_p" [TermId p] else ( idApp "shift_p" [TermId p] >>> idApp (var_ y) (map (const TermUnderscore) xs))
  up x (\y b _ -> case b of Single z -> if y == z then shift y else (id_ TermUnderscore)
                            BinderList p z -> if y == z then shiftp p y else (id_ TermUnderscore)) (map TermId xs) b'

var :: TId -> SubstTy -> Term
var x xs = idApp (var_ x) (sty_terms xs)

renT :: Term -> Term -> Term
renT m n = TermFunction (fin_ m) (fin_ n)

substT :: Term -> SubstTy -> TId -> Term
substT m n y = TermFunction (fin_ m) (sortType y n)

equiv_ :: Term -> Term -> Term
equiv_ s t =  TermForall [BinderName "x"] (TermEq (TermApp s [TermId "x"]) (TermApp t  [TermId "x"]))

-- TODO: Rename. introPatternScope?
getPattern :: String -> [Position] -> [String]
getPattern s xs = map (\x -> s ++ show x) (L.findIndices (const True) xs)


-- Generation of arguments
introScopeTy :: (MonadReader Signature m, MonadError String m) => TId -> Term -> m Term
introScopeTy x s = do
                  args <- substOf x
                  return $ L.foldl (\t _ -> TermFunction nat t) s args

-- FRESH: introScopeVar
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

--- Generation of names for renamings.
genRenS :: String -> (Term, Term) -> GenM (Term, [CBinder])
genRenS s (m,n) = do
  s <- tfresh s
  return $ (TermId s, [BinderNameType [s] (renT m n)])

-- Generation of names for renamings.
genRen :: TId -> String -> (SubstTy, SubstTy) -> GenM (SubstTy, [CBinder])
genRen x xi (m,n) = do
  xs <- substOf x
  let xis = map (\x -> xi ++ x) xs
  let tys = map (\(m, n) -> TermFunction (fin_ m) (fin_ n)) (zip (sty_terms m) (sty_terms n))   -- map (\(x, (m, n)) -> SingleRen (xi ++ x) m n) (zip xs (zip (sty_terms m) (sty_terms n)))
  return $ (SubstRen (map TermId xis), map (\(x,t) -> BinderNameType [x] t) (zip xis tys))

genSubst :: TId -> String -> (SubstTy, SubstTy) -> GenM (SubstTy, [CBinder])
genSubst x sigma (m,n) = do
  xs <- substOf x
  let sigmas = map (\x -> sigma ++ x) xs
  tys <- mapM (\(y, m) -> do
      n' <- castSubst x y n
      return $ TermFunction (fin_ m) (sortType y n')) (zip xs (sty_terms m))
  return $ (SubstSubst (map TermId sigmas), map (\(x,t) -> BinderNameType [x] t) (zip sigmas tys))

introSubstScopeS :: (String, String) -> TId -> GenM ((Term, SubstTy), [CBinder])
introSubstScopeS (m,n) y = do
  (m, bm) <- introScopeVarS m
  (n, bn) <- introScopeVar n y
  return ((m, n), bm ++ bn)

genSubstS :: String -> (Term, SubstTy) -> TId -> GenM (Term, [CBinder])
genSubstS s (m, n) z = do
  s <- tfresh s
  return (TermId s, [BinderNameType [s] (substT m n z)])

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
