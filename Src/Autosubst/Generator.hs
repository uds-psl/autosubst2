{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Autosubst.Generator (genSentences,genSentencesMod) where

import           Autosubst.GenM
import           Autosubst.ModularGenerator
import           Autosubst.Names
import           Autosubst.Syntax
import           Autosubst.Tactics
import           Autosubst.Types
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.RWS          hiding ((<>))
import           Control.Monad.State.Lazy
import           Data.List                  as L
import qualified Text.PrettyPrint.Leijen    as P


-- Generation of syntax from a signature

-- 1. Generation of the inductive type of expressions
genVar :: TId -> SubstTy -> GenM [InductiveCtor]
genVar x n = do
  open_x <- isOpen x
  s <- finVar x (substTerms n)
  let t = [s] ==> idSubstApp x n
  return [InductiveCtor (var_ x) (Just t) | open_x]

genArg :: TId -> SubstTy -> [Binder] -> Argument  -> GenM Term
genArg x n bs (Atom y)  = liftM2 idApp (addFeatureArgs y) (fmap substTerms $ castUpSubst x bs y n)
genArg x n bs (FunApp f p xs) = do
  xs' <- mapM (genArg x n bs) xs
  return $ idApp (funname_ (f ++ p)) xs'

-- Generation of constructor.
genCons :: TId -> SubstTy -> Constructor -> GenM InductiveCtor
genCons x n (Constructor pms cname pos) = do
  t <- do
    up_n_x <- mapM (\(Position bs y) -> genArg x n bs y) pos
    return $  up_n_x ==> idSubstApp x n
  return $ InductiveCtor (constructor_ cname) (Just (if null pms then t else TermForall (createBinders pms) t))

-- Generation of a whole inductive body 
genBody :: TId -> GenM InductiveBody
genBody x = do
  cs <- constructors x
  (n,b) <- introScopeVar "n" x
  varCons <- genVar x n
  constructors <- mapM (genCons x n) cs
  return $ InductiveBody x (makeExplicit b) (TermSort Type) (varCons ++ constructors)


-- 2. Generationof the Congruence Proofs
genCongruence :: TId -> Constructor -> GenM Lemma
genCongruence x (Constructor pms cname pos) = do
    (m, bm) <- introScopeVar "m" x
    let s = genPatternNames "s" pos
    let t = genPatternNames "t" pos
    let bs s = mapM (\(s, Position binders arg) -> do
                                                  arg_type <-  genArg x m binders arg 
                                                  return $ BinderImplicitNameType [s] arg_type
                                                    ) (zip s pos) -- index, pattern, binders.
    bes <- bs s
    bt <- bs t
    cname' <- posExtend_ x cname
    let bpms = createImpBinders pms
    let pms' = map TermId (map fst pms)
    let eqs = zipWith TermEq (map TermId s) (map TermId t)
    let eq = TermEq (idApp cname' ( substTerms m ++ pms' ++ map TermId s)) (idApp cname' (substTerms m ++ pms' ++ map TermId t))
    let beqs = map (\(n,s) -> BinderNameType ["H" ++ show n] s) (zip [1..] eqs)
    let eq' n = idApp cname' ( substTerms m ++ pms' ++ map (\m -> if (m == n) then TermId "x" else TermUnderscore) [1..(length eqs)])
    let p = repRew (map (\n -> (TermId ("H" ++ show n), (TermAbs [BinderName "x"] (eq' n)))) [1..(length eqs)])
    return $ Lemma (congr_ cname') (bpms ++ bm ++ bes ++ bt ++ beqs) eq (ProofString "congruence.")-- p

genCongruences :: TId -> GenM [Lemma]
genCongruences x = join $ fmap (mapM (genCongruence x)) (constructors x)

-- 3. General Traversal Definition 
traversal :: TId -> SubstTy -> (TId -> String) -> (TId -> GenM [Term]) ->(Term -> Term) ->  (Term -> Term) -> [CBinder] -> [SubstTy] -> (Term -> Term)  -> ([String] -> CId -> [Term] -> GenM Term) -> (FId -> [Term] -> Term) -> GenM FixpointBody
traversal x scope name extras no_args ret bargs args var_case sem funsem = do
  let s = "s"
  cs <- constructors x
  open_x <- isOpen x
  let underscore_pattern = TermSubst (SubstScope (map (const TermUnderscore) (substTerms scope)))
  let var_pattern = [Equation (PatternConstructor (idApp (var_ x) [underscore_pattern]) [s]) (var_case (TermId s)) | open_x]
  -- computes the result for a constructor.   
  let cons_pattern (Constructor pms cname pos) =  let s = genPatternNames "s" pos in
                                              let arg_map (bs) arg = (case arg of
                                                                      Atom y -> (do
                                                                                  b <- hasSubst y
                                                                                  extra <- extras y
                                                                                  arg <- mapM (castUpSubst x bs y) args
                                                                                  return $ if b then idApp (name y) (extra ++ map TermSubst arg) else (TermAbs [BinderName "x"] (no_args (TermId "x"))))
                                                                      FunApp f p xs -> (do
                                                                                        res <- mapM (arg_map bs) xs
                                                                                        return $ funsem f res)) in do
                                              positions <- mapM (\(s, Position bs arg) -> liftM2 TermApp (arg_map bs arg) (return [TermId s])) (zip s pos)
                                              res <- sem (map fst pms) cname positions
                                              return $ Equation (PatternConstructor (idApp cname (underscore_pattern : map TermId (map fst pms))) s) res
  cons_pat <- mapM cons_pattern cs
  let t = TermMatch (MatchItem (TermId s))  (Just $ ret (TermId s)) (var_pattern ++ cons_pat)
  return $ FixpointBody (name x) (bargs ++ [BinderNameType [s] (idApp x (substTerms scope))]) (ret (TermId s)) t 


-- 4. Definition of Instantiation of Renamings
genUpRenS :: Binder -> TId -> GenM Definition
genUpRenS b z = do
  ((m,n), bs) <- introRenScopeS ("m", "n")
  (xi, bxi) <- genRenS "xi" (m,n)
  let (_, bpms) = variadicScopeParameters b
      m' = succ_ m z b
      n' = succ_ n z b
  return $ Definition (upRen_ b z) (bpms ++ bs ++ bxi) (Just (renType m' n')) (up_ren_ z b xi) --

genRenaming :: TId -> GenM FixpointBody
genRenaming x = do
  ((m,n),bs) <- introRenScope ("m", "n") x
  (xi,bxi) <- genRen x "xi" (m,n)
  toVarT <- toVar x xi
  x' <- extend_ x
  b_ext <- isExtension x
  traversal x m ren_ (liftM renDeps . genDepRecord) id (const $ idApp x' (substTerms n)) (bs ++ bxi) [xi]
                      (\s -> TermApp (var x' n) [TermApp toVarT [s]])
                      (\pms c s -> return $ idApp (modConstructor b_ext (x == x') c) (substTerms n ++ map TermId pms ++ s)) map_

genRenamings :: [TId] -> GenM Fixpoint
genRenamings xs = do
  fs <- mapM genRenaming xs
  isRec <- recursive xs
  return $ Fixpoint isRec fs


-- 5. Definition of Instantiation of Substitutions 
upsubstType :: Binder -> TId -> SubstTy -> Term -> GenM Term
upsubstType b z m sigma = do
    pat <- patternSId z b
    m <- upSubst z [b] m
    hasRen <- hasRenamings z
    let sigma' = sigma >>> idApp (if hasRen then (ren_ z) else (subst_ z)) pat
    return $ cons__ z b sigma' m

genUpS :: Binder -> TId -> GenM Definition
genUpS b z = do
  ((m,n), bs) <- introSubstScopeS ("m", "n") z
  (sigma, b_sigma) <- genSubstS "sigma" (m,n) z
  sigma <- upsubstType b z n sigma
  let (pms, bpms) = variadicScopeParameters b
      m' = succ_ m z b
  n' <- upSubst z [b] n
  return $ Definition (up_ b z) (bpms ++ bs ++ b_sigma) (Just (substType m' n' z)) sigma

genSubstitution :: TId -> GenM FixpointBody
genSubstitution x = do
  ((m, n), bmn) <- introRenScope ("m", "n") x
  (sigma, bs) <- genSubst x "sigma" (m,n)
  toVarT <- toVar x sigma
  x' <- extend_ x
  b_ext <- isExtension x
  traversal x m subst_ (liftM substDeps . genDepRecord) id (const $ idApp x' (substTerms n)) (bmn ++ bs) [sigma]
                       (\s -> TermApp toVarT [s])
                       (\pms c s -> return $ idApp (modConstructor b_ext (x == x') c) (substTerms n ++ map TermId pms ++ s)) map_

genSubstitutions :: [TId] -> GenM Fixpoint
genSubstitutions xs = do
  if null xs then throwError "Error: in genSubstitutions the list of substitutions is empty." else return ()
  fs <- mapM genSubstitution xs
  isRec <- recursive [L.head xs]
  return $ Fixpoint isRec fs


-- 6. Generation of left identity lemma
genUpId :: Binder -> TId -> GenM Definition
genUpId y z = do
  (m, bm) <- introScopeVar "m" z
  m_var <- toVar z m
  (sigma, b_sigma) <- genSubstS "sigma" (m_var, m) z
  (eq, b_eq) <- genEq z "Eq" sigma (var z m)
  n <- tfresh "n"
  m <- upSubst z [y] m
  let (pms, bpms) = variadicScopeParametersImplicit y
  let ret = equiv_ (idApp (up_ y z) (pms ++ [sigma])) (var z m)
  shift <- patternSId z y
  hasRen <- hasRenamings z
  let t n = ap_ [idApp (if hasRen then ren_ z else subst_ z) shift, TermApp eq [n]]
      t' n = eqTrans_ (t n) (TermId (ren_var_ z)) 
  let u = case y of Single z' -> if z == z' then matchFin_ (TermId n) t eq_refl_ else t (TermId n)
                    BinderList p z' -> if z == z' then scons_p_eta_ (var z m) (TermAbs [BinderName n] (t (TermId n))) (TermAbs [BinderName n] eq_refl_) else (t (TermId n))
  return $ Definition (upId_ y z) (bpms ++ bm ++ b_sigma ++ b_eq) (Just ret) (TermAbs [BinderName n] u)


genIdL :: TId -> GenM FixpointBody
genIdL x = do
  (m, bm) <- introScopeVar "m" x
  (sigma, bs) <- genSubst x "sigma" (m, m)
  xs <- substOf x
  eqs' <- mapM (\y -> liftM2 idApp (return $ var_ y) (fmap substTerms (castSubst x y m))) xs
  (eqs, beqs) <- genEqs x "Eq" (substTerms sigma) eqs' (\x y s -> return $ idApp (upId_ y x) [TermUnderscore, s]) 
  toVarT <- toVar x eqs
  x' <- extend_ x
  b_ext <- isExtension x
  let s' s = if (x == x') then s else idApp inj_ [s] 
      ret s = TermEq (idApp (subst_ x) (substTerms sigma ++ [s])) (s' s)
  traversal x m idSubst_ (liftM idSubstDeps . genDepRecord) (\s -> TermApp eq_refl_ [s]) ret (bm ++ bs ++ beqs) [sigma, eqs]
                       (\s -> TermApp toVarT [s])
                       (\pms c cs -> return$ idApp (if b_ext then "" else congr_ (if x == x' then c else smart_ c)) cs) mapId_


-- 7. Composition law 

-- 7a. Composition of renamings and renamings 
genUpRenRen :: Binder -> TId -> GenM Definition
genUpRenRen y z = do
 (k, bk) <- introScopeVarS "k"
 (l, bl) <- introScopeVarS "l"
 (m, bm) <- introScopeVarS "m"
 (xi, bxi) <- genRenS "xi" (k, l)
 (tau, btau) <- genRenS "tau" (l, m)
 (theta, btheta) <- genRenS "theta" (k, m)
 (eq, b_eq) <- genEq z "Eq" (xi >>> tau) theta
 n <- tfresh "n"
 let (pms, bpms) = variadicScopeParametersImplicit y
 let ret = equiv_ (idApp (upRen_ y z) (pms ++ [xi]) >>> idApp (upRen_ y z) (pms ++ [tau]) ) (idApp (upRen_ y z) (pms ++ [theta]))
 shift <- patternSId z y
 let u = case y of Single z' -> if (z == z') then idApp up_ren_ren_ [xi,tau,theta,eq] else eq
                   BinderList p z' -> if z == z' then idApp up_ren_ren_p_ [eq] else eq
 return $ Definition (up_ren_renName_ y z) (bpms ++ bk ++ bl ++ bm ++ bxi ++ btau ++ btheta ++ b_eq) (Just ret) ( u)

genCompRenRen :: TId -> GenM FixpointBody
genCompRenRen x = do
  ((k,l), bkl) <- introRenScope ("k", "l") x
  (m, bm) <- introScopeVar "m" x
  (xi, bxi) <- genRen x "xi" (m,k)
  (zeta,bzeta) <- genRen x "zeta" (k,l)
  (rho, brho) <- genRen x "rho" (m, l)
  b_ext <- isExtension x
  x' <- extend_ x
  xs' <- substOf x'
  let b = x == x'
  (eqs, beqs) <- genEqs x "Eq" (zipWith (>>>) (substTerms xi) (substTerms zeta)) (substTerms rho) (\x y s -> return $ case y of 
                                                                                                              Single z -> if z == x then idApp (if b then up_ren_ren_ else  ("up_ren_ren" ++ sep ++ x ++ sep ++ z) ) [TermUnderscore, TermUnderscore, TermUnderscore, s] else s
                                                                                                              BinderList p x' -> if x' == x then idApp "up_ren_ren_p" [s] else s)
  toVarT <- toVar x eqs
  let ret s = TermEq (idApp (ren_ x') (substTerms zeta ++ [idApp (ren_ x) $ substTerms xi  ++ [s]])) (idApp (ren_ x) (substTerms rho ++ [s]))
      sem zs c xs = do
                    return $ if b_ext then idApp "" xs else if (x == x') then idApp (congr_ c) xs else eqTrans_ (idApp (retract_ren_ x') ((map (const TermUnderscore) xs') ++ [idApp c (map (const TermUnderscore) xs)])) (idApp (congr_ (smart_ c)) xs)
      varC n = ap_ [var x' l, TermApp toVarT [n]]
      varS n = eqTrans_ (idApp (retract_ren_ x') ((map (const TermUnderscore) xs') ++ [idApp (var_ x) [idApp ("xi" ++ x') [n]] ]) ) (varC n)
  traversal x m compRenRen_ (liftM compRenRenDeps . genDepRecord) (\s -> TermApp eq_refl_ [s]) ret (bkl ++ bm ++ bxi ++ bzeta ++ brho ++ beqs) [xi, zeta, rho, eqs]
                  (\n -> if b then varC n else varS n)
                  sem mapComp_


-- Definition of the two lemmas for the rewriting system 
genLemmaRenRenComp :: TId -> GenM (Lemma, Lemma) 
genLemmaRenRenComp x = do
  ((k,l), bkl) <- introRenScope ("k", "l") x
  (m, bm) <- introScopeVar "m" x
  (xi, bxi) <- genRen x "xi" (m,k)
  (zeta,bzeta) <- genRen x "zeta" (k,l)
  xs <- substOf x
  x' <- extend_ x
  let sigmazeta = zipWith (>>>) (substTerms xi) (substTerms zeta)
  let s = "s"
  let ret = TermEq (idApp (ren_ x') (substTerms zeta ++ [idApp (ren_ x) $ substTerms xi  ++ [TermId s]])) (idApp (ren_ x) (sigmazeta ++ [TermId s]))
  let proof = idApp (compRenRen_ x) (substTerms xi ++ substTerms zeta ++ map (const TermUnderscore) xs ++ map (const (TermAbs [BinderName "n"] eq_refl_)) xs ++ [TermId s])
  let ret' = TermEq ((idApp (ren_ x) (substTerms xi)) >>> (idApp (ren_ x') (substTerms zeta))) (idApp (ren_ x) sigmazeta) 
  let proof' = TermApp fext_ [TermAbs [BinderName "n"] (idApp (renRen_ x) (substTerms xi ++ substTerms zeta ++ [TermId "n"]))]
  return (Lemma (renRen_ x) (bkl ++ bm ++ bxi ++ bzeta ++ [BinderNameType [s] (idApp x (substTerms m))]) ret (ProofExact proof),
          Lemma (renRen'_ x) (bkl ++ bm ++ bxi ++ bzeta) ret' (ProofExact proof'))


-- 7b. Compositio nof Renamings and Substitutions 
genUpRenSubst :: Binder -> TId -> GenM Definition
genUpRenSubst y z = do
  (k, bk) <- introScopeVarS "k"
  (l, bl) <- introScopeVarS "l"
  (m, bm) <- introScopeVar "m" z
  (xi, bxi) <- genRenS "xi" (k, l)
  (tau, btau) <- genSubstS "tau" (l, m) z
  (theta, btheta) <- genSubstS "theta" (k, m) z
  m_var <- toVar z m
  (eq, b_eq) <- genEq z "Eq" (xi >>> tau) theta
  n <- tfresh "n"
  m <- upSubst z [y] m
  let (pms, bpms) = variadicScopeParametersImplicit y
  let ret = equiv_ (idApp (upRen_ y z) (pms ++ [xi]) >>> idApp (up_ y z) (pms ++ [tau]) ) (idApp (up_ y z) (pms ++ [theta]))
  shift <- patternSId z y
  let t n = ap_ [idApp (ren_ z) shift, TermApp eq [n]]
  let s = eqTrans_ (scons_p_comp' (TermId n)) (scons_p_congr_  (TermAbs [BinderName "z"] (eqTrans_ (scons_p_tail' (TermApp xi [TermId "z"])) (t (TermId "z")))) (TermAbs [BinderName "z"] (scons_p_head' (TermId "z"))))
  let u = case y of Single z' ->  if z == z' then matchFin_ (TermId n) t eq_refl_  else t (TermId n)
                    BinderList p z' -> if z == z' then s else t (TermId n)
  return $ Definition (up_ren_subst_ y z) (bpms ++ bk ++ bl ++ bm ++ bxi ++ btau ++ btheta ++ b_eq ) (Just ret) (TermAbs [BinderName "n"] u)

genCompRenSubst :: TId -> GenM FixpointBody
genCompRenSubst x = do
  ((k,l), bkl) <- introRenScope ("k", "l") x
  (m, bm) <- introScopeVar "m" x
  (xi, bxi) <- genRen x "xi" (m,k)
  (zeta,bzeta) <- genSubst x "tau" (k,l)
  (rho, brho) <- genSubst x "theta" (m, l)
  (eqs, beqs) <- genEqs x "Eq" (zipWith (>>>) (substTerms xi) (substTerms zeta)) (substTerms rho) (\x y s -> return $ idApp (up_ren_subst_ y x) [TermUnderscore, TermUnderscore, TermUnderscore, s])
  toVarT <- toVar x eqs
  x' <- extend_ x
  xs' <- substOf x'
  b_ext <- isExtension x
  let b = x == x'
      ret s = TermEq (idApp (subst_ x') (substTerms zeta ++ [idApp (ren_ x) $ substTerms xi  ++ [s]])) (idApp (subst_ x) (substTerms rho ++ [s]))
      sem zs c xs = return $ if b_ext then idApp "" xs else if (x == x') then (idApp (congr_ c) xs) else eqTrans_ (idApp (retract_subst_ x') (map (const TermUnderscore) xs' ++ [idApp c (map (const TermUnderscore) xs)])) (idApp (congr_ (smart_ c)) xs)
      varC n = TermApp toVarT [n]
      varS n = eqTrans_ (idApp (retract_subst_ x') ((map (const TermUnderscore) xs') ++ [idApp (var_ x) [idApp ("xi" ++ x') [n]] ]) ) (varC n)
  traversal x m compRenSubst_ (liftM compRenSubstDeps . genDepRecord) (\s -> TermApp eq_refl_ [s]) ret (bkl ++ bm ++ bxi ++ bzeta ++ brho ++ beqs) [xi, zeta, rho, eqs]
                  (\n -> if b then varC n else varS n)
                  sem
                  mapComp_

genLemmaCompRenSubst :: TId -> GenM (Lemma, Lemma) 
genLemmaCompRenSubst x = do
  ((k,l), bkl) <- introRenScope ("k", "l") x
  (m, bm) <- introScopeVar "m" x
  (sigma, bsigma) <- genSubst x "sigma" (m,k)
  (zeta,bzeta) <- genRen x "zeta" (k,l)
  xs <- substOf x
  x' <- extend_ x
  let s = "s"
  sigmazeta <- mapM (\(y, sigma) -> do
                zeta' <- castSubst x y zeta
                return $ sigma >>> idApp (ren_ y) (substTerms zeta')) (zip xs  (substTerms sigma))
  let ret = TermEq (idApp (ren_ x') (substTerms zeta ++ [idApp (subst_ x) $ substTerms sigma  ++ [TermId s]])) (idApp (subst_ x) (sigmazeta ++ [TermId s]))
  let proof = idApp (compSubstRen_ x) (substTerms sigma ++ substTerms zeta ++ map (const TermUnderscore) xs ++ map (const (TermAbs [BinderName "n"] eq_refl_)) xs ++ [TermId s])
  let ret' = TermEq ((idApp (subst_ x) (substTerms sigma)) >>> (idApp (ren_ x') (substTerms zeta))) (idApp (subst_ x) sigmazeta) 
  let proof' = TermApp fext_ [TermAbs [BinderName "n"] (idApp ("compRen_" ++ x) (substTerms sigma ++ substTerms zeta ++ [TermId "n"]))]
  return (Lemma ("compRen_" ++ x) (bkl ++ bm ++ bsigma ++ bzeta ++ [BinderNameType [s] (idApp x (substTerms m))]) ret (ProofExact proof),
          Lemma ("compRen'_" ++ x) (bkl ++ bm ++ bsigma ++ bzeta) ret' (ProofExact proof'))


-- 7c.) Composition of Substitutions and Renamings 
genUpSubstRen :: Binder -> TId -> GenM Definition
genUpSubstRen y z = do
  (k, bk) <- introScopeVarS "k"
  (l, bl) <- introScopeVar "l" z
  (m, bm) <- introScopeVar "m" z
  (sigma, bsigma) <- genSubstS "sigma" (k, l) z
  (zeta, bzeta) <- genRen z "zeta" (l, m)
  (theta, btheta) <- genSubstS "theta" (k, m) z
  (eq, b_eq) <- genEq z "Eq" (sigma >>> idApp (ren_ z) (substTerms zeta)) theta
  n <- tfresh "n"
  m <- upSubst z [y] m
  zs <- substOf z
  zeta' <- upSubst z [y] zeta
  pat <- patternSId z y
  let (pms, bpms) = variadicScopeParametersImplicit y
  let ret = equiv_ (idApp (up_ y z) (pms ++[sigma]) >>> idApp (ren_ z) (substTerms zeta')) (idApp (up_ y z) (pms ++ [theta]))
  shift <- patternSId z y
  let t n = eqTrans_ (idApp (compRenRen_ z) (pat ++ substTerms zeta' ++ zipWith (>>>) (substTerms zeta) pat ++ map (const (TermAbs [BinderName "x"] eq_refl_)) pat ++ [ TermApp sigma [n]]))
                (eqTrans_ (eqSym_ (idApp (compRenRen_ z) (substTerms zeta ++ pat ++ zipWith (>>>) (substTerms zeta) pat ++ map (const ((TermAbs [BinderName "x"] eq_refl_))) pat ++ [ TermApp sigma [n]])))
                (ap_ [idApp (ren_ z) pat, TermApp eq [n]]))
  let t' n z' = eqTrans_ (idApp (compRenRen_ z) (pat ++ substTerms zeta' ++ zipWith (>>>) (substTerms zeta) pat ++ map (\x -> (TermAbs [BinderName "x"] (if (x == z') then  scons_p_tail' (TermId "x") else eq_refl_))) zs ++ [ TermApp sigma [n]]))
                (eqTrans_ (eqSym_ (idApp (compRenRen_ z) (substTerms zeta ++ pat ++ zipWith (>>>) (substTerms zeta) pat ++ map (const ((TermAbs [BinderName "x"] eq_refl_))) pat ++ [ TermApp sigma [n]])))
                (ap_ [idApp (ren_ z) pat, TermApp eq [n]]))
  let hd = TermAbs [BinderName "x"] (ap_ [var z m, scons_p_head' (TermId "x")])
  let u = case y of Single z' ->  if z == z' then  matchFin_ (TermId n) t eq_refl_ else t (TermId n)
                    BinderList p z' -> if z == z' then ((eqTrans_ (scons_p_comp' (TermId "n")) (scons_p_congr_  (TermAbs [BinderName "n"] (t' (TermId "n") z') ) hd))) else t' (TermId n) z'
  return $ Definition (up_subst_ren_ y z) (bpms ++ bk ++ bl ++ bm ++ bsigma ++ bzeta ++ btheta ++ b_eq ) (Just ret) (TermAbs [BinderName "n"] u)


genCompSubstRen :: TId -> GenM FixpointBody
genCompSubstRen x = do
  ((k,l), bkl) <- introRenScope ("k", "l") x
  (m, bm) <- introScopeVar "m" x
  (sigma, bsigma) <- genSubst x "sigma" (m,k)
  (zeta,bzeta) <- genRen x "zeta" (k,l)
  (theta, btheta) <- genSubst x "theta" (m, l)
  xs <- substOf x
  sigmazeta <- mapM (\(y, sigma) -> do
                zeta' <- castSubst x y zeta
                return $ sigma >>> idApp (ren_ y) (substTerms zeta')) (zip xs  (substTerms sigma))
  (eqs, beqs) <- genEqs x "Eq" sigmazeta (substTerms theta) (\z y s -> do
                                  sigma' <- toVar z sigma
                                  zeta' <- castSubst x z zeta
                                  theta' <- toVar z  theta
                                  return $ idApp (up_subst_ren_ y z) ([TermUnderscore] ++ map (const TermUnderscore) (substTerms zeta') ++ [TermUnderscore, s])) 
  toVarT <- toVar x eqs
  x' <- extend_ x
  b_ext <- isExtension x
  let ret s = TermEq (idApp (ren_ x') (substTerms zeta ++ [idApp (subst_ x) $ substTerms sigma  ++ [s]])) (idApp (subst_ x) (substTerms theta ++ [s]))
      sem _ c xs = return $ if b_ext then idApp "" xs else if (x == x') then (idApp (congr_ c) xs) else eqTrans_ (idApp (retract_ren_ x') [TermUnderscore, idApp c (map (const TermUnderscore) xs)]) (idApp (congr_ (smart_ c)) xs)
      varC n = TermApp toVarT [n]
      varS n = eqTrans_ (idApp (retract_ren_ x') [TermUnderscore, idApp (var_ x) [idApp ("xi" ++ x') [n]] ] ) (varC n)
  traversal x m compSubstRen_ (liftM compSubstRenDeps . genDepRecord)  (\s -> TermApp eq_refl_ [s]) ret (bkl ++ bm ++ bsigma ++ bzeta ++ btheta ++ beqs) [sigma, zeta, theta, eqs]
                  (\n -> if b_ext then varC n else varC n)
                  sem mapComp_

genLemmaCompSubstRen :: TId -> GenM (Lemma, Lemma)
genLemmaCompSubstRen x = do
  ((k,l), bkl) <- introRenScope ("k", "l") x
  (m, bm) <- introScopeVar "m" x
  (xi, bxi) <- genRen x "xi" (m,k)
  (zeta,bzeta) <- genSubst x "tau" (k,l)
  xs <- substOf x
  x' <- extend_ x
  let sigmazeta = zipWith (>>>) (substTerms xi) (substTerms zeta)
  let s = "s"
  let ret = TermEq (idApp (subst_ x') (substTerms zeta ++ [idApp (ren_ x) $ substTerms xi  ++ [TermId s]])) (idApp (subst_ x) (sigmazeta ++ [TermId s]))
  let proof = idApp (compRenSubst_ x) (substTerms xi ++ substTerms zeta ++ map (const TermUnderscore) xs ++ map (const (TermAbs [BinderName "n"] eq_refl_)) xs ++ [TermId s])
  let ret' = TermEq ((idApp (ren_ x) (substTerms xi)) >>> (idApp (subst_ x') (substTerms zeta))) (idApp (subst_ x) sigmazeta) 
  let proof' = TermApp fext_ [TermAbs [BinderName "n"] (idApp ("renComp_" ++ x) (substTerms xi ++ substTerms zeta ++ [TermId "n"]))]
  return (Lemma ("renComp_" ++ x) (bkl ++ bm ++ bxi ++ bzeta ++ [BinderNameType [s] (idApp x (substTerms m))]) ret (ProofExact proof),
          Lemma ("renComp'_" ++ x) (bkl ++ bm ++ bxi ++ bzeta) ret' (ProofExact proof'))

-- 7d.) Composition of substiutions and substitutions
genUpSubstSubst :: Binder -> TId -> GenM Definition
genUpSubstSubst y z = do
  (k, bk) <- introScopeVarS "k"
  (l, bl) <- introScopeVar "l" z
  (m, bm) <- introScopeVar "m" z
  (sigma, bsigma) <- genSubstS "sigma" (k, l) z
  (tau, btau) <- genSubst z "tau" (l, m)
  (theta, btheta) <- genSubstS "theta" (k, m) z
  (eq, b_eq) <- genEq z "Eq" (sigma >>> idApp (subst_ z) (substTerms tau)) theta
  n <- tfresh "n"
  m <- upSubst z [y] m
  l' <- upSubst z [y] l
  zeta' <- upSubst z [y] tau
  pat <- patternSId z y
  let (pms, bpms) = variadicScopeParametersImplicit y
  let ret = equiv_ (idApp (up_ y z) (pms ++ [sigma]) >>> idApp (subst_ z) (substTerms zeta')) (idApp (up_ y z) (pms ++ [theta]))
  shift <- patternSId z y
  zs <- substOf z
  pat' <- mapM (\(tau, z') -> do
                      p' <- castSubst z z' (SubstSubst pat)
                      return $ tau >>> (idApp (ren_ z') (substTerms p')) ) (zip (substTerms tau) zs)
  let t n = (eqTrans_ (idApp (compRenSubst_ z) (pat ++ substTerms zeta'  ++ (map (\(z, p) -> p >>> z) (zip (substTerms zeta') pat)) ++ map (const ((TermAbs [BinderName "x"] eq_refl_))) pat ++ [ TermApp sigma [n]]))
                (eqTrans_ (eqSym_ (idApp (compSubstRen_ z) (substTerms tau ++ pat ++ pat' ++ map (const ((TermAbs [BinderName "x"] eq_refl_))) pat ++ [ TermApp sigma [n]])))
                (ap_ [(idApp (ren_ z) pat), TermApp eq [n]])))
  let t' n z' = (eqTrans_ (idApp (compRenSubst_ z) (pat ++ substTerms zeta'  ++ (map (\(z, p) -> p >>> z) (zip (substTerms zeta') pat)) ++ map (const ((TermAbs [BinderName "x"] eq_refl_))) pat ++ [ TermApp sigma [n]]))
                (eqTrans_ (eqSym_ (idApp (compSubstRen_ z) ( substTerms tau ++ pat ++ map (const TermUnderscore) pat' ++ map (\x -> ((TermAbs [BinderName "x"] (eqSym_ (if (x == z') then scons_p_tail' (TermId "x") else eq_refl_))))) zs ++ [ TermApp sigma [n]])))
                (ap_ [(idApp (ren_ z) pat), TermApp eq [n]])))
  let hd = TermAbs [BinderName "x"] (idApp "scons_p_head'" [TermUnderscore, TermAbs [BinderName "z"] (idApp (ren_ z) (shift ++ [TermUnderscore])), TermId "x"])
  let u = case y of Single z' ->  if z == z' then  matchFin_ (TermId n) t eq_refl_ else t (TermId n)
                    BinderList p z' -> if z == z' then ((eqTrans_ (idApp "scons_p_comp'" [(idApp "zero_p" [TermId p]) >>> (var z l'), TermUnderscore, TermUnderscore, TermId "n"]) (scons_p_congr_  (TermAbs [BinderName "n"] (t' (TermId "n") z') ) hd))) else t' (TermId n) z'
  return $ Definition (up_subst_subst_ y z) (bpms ++ bk ++ bl ++ bm ++ bsigma ++ btau ++ btheta ++ b_eq ) (Just ret) (TermAbs [BinderName "n"] u)

genUpSubstSubstNoRen :: Binder -> TId -> GenM Definition
genUpSubstSubstNoRen y z = do
  (k, bk) <- introScopeVarS "k"
  (l, bl) <- introScopeVar "l" z
  (m, bm) <- introScopeVar "m" z
  (sigma, bsigma) <- genSubstS "sigma" (k, l) z
  (tau, btau) <- genSubst z "tau" (l, m)
  (theta, btheta) <- genSubstS "theta" (k, m) z
  (eq, b_eq) <- genEq z "Eq" (sigma >>> idApp (subst_ z) (substTerms tau)) theta
  n <- tfresh "n"
  m <- upSubst z [y] m
  l' <- upSubst z [y] l
  zeta' <- upSubst z [y] tau
  pat <- patternSId z y
  let (pms, bpms) = variadicScopeParametersImplicit y
  let ret = equiv_ (idApp (up_ y z) (pms ++ [sigma]) >>> idApp (subst_ z) (substTerms zeta')) (idApp (up_ y z) (pms ++ [theta]))
  shift <- patternSIdNoRen z y
  zs <- substOf z
  pat' <- mapM (\(tau, z') -> do
                      p' <- castSubst z z' (SubstSubst pat)
                      return $ tau >>> (idApp (subst_ z') (substTerms p')) ) (zip (substTerms tau) zs)
  let t n = (eqTrans_ (idApp (compSubstSubst_ z) (pat ++ substTerms zeta'  ++ (map (\(z, p) -> p >>> z) (zip (substTerms zeta') shift)) ++ map (const ((TermAbs [BinderName "x"] eq_refl_))) pat ++ [ TermApp sigma [n]]))
                (eqTrans_ (eqSym_ (idApp (compSubstSubst_ z) (substTerms tau ++ pat ++ pat' ++ map (const ((TermAbs [BinderName "x"] eq_refl_))) pat ++ [ TermApp sigma [n]])))
                (ap_ [(idApp (subst_ z) pat), TermApp eq [n]])))
  let t' n z' = (eqTrans_ (idApp (compSubstSubst_ z) (pat ++ substTerms zeta'  ++ (map (\(z, p) -> p >>> z) (zip (substTerms zeta') shift)) ++ map (const ((TermAbs [BinderName "x"] eq_refl_))) pat ++ [ TermApp sigma [n]]))
                (eqTrans_ (eqSym_ (idApp (compSubstSubst_ z) ( substTerms tau ++ pat ++ map (const TermUnderscore) pat' ++ map (\x -> ((TermAbs [BinderName "x"] (eqSym_ (if (x == z') then scons_p_tail' (TermId "x") else eq_refl_))))) zs ++ [ TermApp sigma [n]])))
                (ap_ [(idApp (subst_ z) pat), TermApp eq [n]])))
  let hd = TermAbs [BinderName "x"] (idApp "scons_p_head'" [TermUnderscore, TermAbs [BinderName "z"] (idApp (subst_ z) (pat ++ [TermUnderscore])), TermId "x"])
  let u = case y of Single z' ->  if z == z' then  matchFin_ (TermId n) t eq_refl_ else t (TermId n)
                    BinderList p z' -> if z == z' then ((eqTrans_ (idApp "scons_p_comp'" [(idApp "zero_p" [TermId p]) >>> (var z l'), TermUnderscore, TermUnderscore, TermId "n"]) (scons_p_congr_  (TermAbs [BinderName "n"] (t' (TermId "n") z') ) hd))) else t' (TermId n) z'
  return $ Definition (up_subst_subst_ y z) (bpms ++ bk ++ bl ++ bm ++ bsigma ++ btau ++ btheta ++ b_eq ) (Just ret) (TermAbs [BinderName "n"] u)


genCompSubstSubst :: TId -> GenM FixpointBody
genCompSubstSubst x = do
  ((k,l), bkl) <- introRenScope ("k", "l") x
  (m, bm) <- introScopeVar "m" x
  (sigma, bsigma) <- genSubst x "sigma" (m,k)
  (tau,btau) <- genSubst x "tau" (k,l)
  (theta, btheta) <- genSubst x "theta" (m, l)
  xs <- substOf x
  sigmatau <- mapM (\(y, sigma) -> do
                tau' <- castSubst x y tau
                return $ sigma >>> idApp (subst_ y) (substTerms tau')) (zip xs  (substTerms sigma))
  (eqs, beqs) <- genEqs x "Eq" sigmatau (substTerms theta) (\z y s -> do
                                  sigma' <- toVar z sigma
                                  tau' <- castSubst x z tau
                                  theta' <- toVar z  theta
                                  return $ idApp (up_subst_subst_ y z) ([TermUnderscore] ++ map (const TermUnderscore) (substTerms tau') ++ [TermUnderscore, s])) 
  toVarT <- toVar x eqs
  x' <- extend_ x
  b_ext <- isExtension x
  let ret s = TermEq (idApp (subst_ x') (substTerms tau ++ [idApp (subst_ x) $ substTerms sigma  ++ [s]])) (idApp (subst_ x) (substTerms theta ++ [s]))
      sem _ c xs = return $ if b_ext then idApp "" xs else if (x == x') then idApp (congr_ c) xs else eqTrans_ (idApp (retract_subst_ x') [TermUnderscore, idApp c (map (const TermUnderscore) xs)]) (idApp (congr_ (smart_ c)) xs)
      varC n = TermApp toVarT [n]
      varS n = eqTrans_ (idApp (retract_subst_ x') [TermUnderscore, idApp (var_ x) [idApp ("sigma" ++ x') [n]] ] ) (varC n)
  traversal x m compSubstSubst_  (liftM compSubstSubstDeps . genDepRecord) (\s -> TermApp eq_refl_ [s]) ret (bkl ++ bm ++ bsigma ++ btau ++ btheta ++ beqs) [sigma, tau, theta, eqs]
                  (\n -> if b_ext then varC n else varC n) sem mapComp_

genLemmaCompSubstSubst :: TId -> GenM (Lemma, Lemma) 
genLemmaCompSubstSubst x = do
  ((k,l), bkl) <- introRenScope ("k", "l") x
  (m, bm) <- introScopeVar "m" x
  (sigma, bsigma) <- genSubst x "sigma" (m,k)
  (tau,btau) <- genSubst x "tau" (k,l)
  xs <- substOf x
  x' <- extend_ x
  let s = "s"
  sigmatau <- mapM (\(y, sigma) -> do
                tau' <- castSubst x y tau
                return $ sigma >>> idApp (subst_ y) (substTerms tau')) (zip xs  (substTerms sigma))
  let ret = TermEq (idApp (subst_ x') (substTerms tau ++ [idApp (subst_ x) $ substTerms sigma  ++ [TermId s]])) (idApp (subst_ x) (sigmatau ++ [TermId s]))
  let proof = idApp (compSubstSubst_ x) (substTerms sigma ++ substTerms tau ++ map (const TermUnderscore) xs ++ map (const (TermAbs [BinderName "n"] eq_refl_)) xs ++ [TermId s])
  let ret' = TermEq ((idApp (subst_ x) (substTerms sigma)) >>> (idApp (subst_ x') (substTerms tau))) (idApp (subst_ x) sigmatau) 
  let proof' = TermApp fext_ [TermAbs [BinderName "n"] (idApp ("compComp_" ++ x) (substTerms sigma ++ substTerms tau ++ [TermId "n"]))]
  return (Lemma ("compComp_" ++ x) (bkl ++ bm ++ bsigma ++ btau ++ [BinderNameType [s] (idApp x (substTerms m))]) ret (ProofExact proof),
          Lemma ("compComp'_" ++ x) (bkl ++ bm ++ bsigma ++ btau) ret' (ProofExact proof'))

-- 8. Extensionsality lemmas
genUpExtRen :: Binder -> TId -> GenM Definition
genUpExtRen y z = do
  (m, bm) <- introScopeVarS "m"
  (n, bn) <- introScopeVarS "n"
  (xi, bxi) <- genRenS "xi" (m, n)
  (zeta,bzeta) <- genRenS "zeta" (m,n)
  (eq, b_eq) <- genEq z "Eq" xi zeta
  let (pms,bpms) = variadicScopeParametersImplicit y
  let ret = equiv_ (idApp (upRen_ y z) (pms ++ [xi])) (idApp (upRen_ y z) (pms ++[zeta]))
  n <- tfresh "n"
  let t n = TermApp eq [n]
  let s = matchFin_ (TermId n) (\n -> ap_ [shift_, t n]) eq_refl_
  let u = case y of Single z' -> if z == z' then s else t (TermId n)
                    BinderList p z' -> if z == z' then scons_p_congr_ (TermAbs [BinderName "n"] (ap_ [idApp shift_p_ [TermId p], t (TermId "n")])) (TermAbs [BinderName "n"] eq_refl_) else t (TermId n)
  return $ Definition (upExtRen_ y z) (bpms ++ bm ++ bn ++ bxi ++ bzeta ++ b_eq) (Just ret) (TermAbs [BinderName "n"] u)

genExtRen :: TId -> GenM FixpointBody
genExtRen x = do
  ((m,n), bmn) <- introRenScope ("m", "n") x
  (xi, bxi) <- genRen x "xi" (m,n)
  (zeta, bzeta) <- genRen x "zeta" (m,n)
  xs <- substOf x
  (eqs, beqs) <- genEqs x "Eq" (substTerms xi) (substTerms zeta) (\x y s -> return $ idApp (upExtRen_ y x) [TermUnderscore, TermUnderscore, s]) 
  x' <- extend_ x
  b_ext <- isExtension x
  let ret s = TermEq (idApp (ren_ x) (substTerms xi ++ [s])) (idApp (ren_ x) (substTerms zeta ++ [s]))
  toVarT <- toVar x eqs
  traversal x m extRen_ (liftM extRenDeps . genDepRecord) (\s -> TermApp eq_refl_ [s]) ret (bmn ++ bxi ++ bzeta ++ beqs) [xi, zeta, eqs]
                  (\z -> ap_ [var x' n, TermApp toVarT [z]])
                  (\_ c cs -> return $ idApp  (if b_ext then "" else congr_ (if x == x' then c else smart_ c)) cs)
                  mapExt_

genUpExt :: Binder -> TId -> GenM Definition
genUpExt y z = do
  (m, bm) <- introScopeVarS "m"
  (n, bn) <- introScopeVar "n" z
  (sigma, bsigma) <- genSubstS "sigma" (m, n) z
  (tau,btau) <- genSubstS "tau" (m,n) z
  (eq, b_eq) <- genEq z "Eq" sigma tau
  let (pms, bpms) = variadicScopeParametersImplicit y
  let ret = equiv_ (idApp (up_ y z) (pms ++ [sigma])) (idApp (up_ y z) (pms ++ [tau]))
  shift <- patternSId z y
  n <- tfresh "n"
  hasRen <- hasRenamings z
  let t n = ap_ [idApp (if hasRen then ren_ z else subst_ z) shift, TermApp eq [n]]
  let u = case y of Single z' -> if z == z' then matchFin_ (TermId n) t eq_refl_ else t (TermId n)
                    BinderList p z' -> if z == z' then scons_p_congr_ (TermAbs [BinderName "n"] (t (TermId "n"))) (TermAbs [BinderName "n"] eq_refl_) else t (TermId n)
  return $ Definition (upExt_ y z) (bpms ++ bm ++ bn ++ bsigma ++ btau ++ b_eq ) (Just ret) (TermAbs [BinderName "n"] u)

genExt :: TId -> GenM FixpointBody
genExt x = do
  ((m,n), bmn) <- introRenScope ("m", "n") x
  (sigma, bsigma) <- genSubst x "sigma" (m,n)
  (tau, btau) <- genSubst x "tau" (m,n)
  xs <- substOf x
  (eqs, beqs) <- genEqs x "Eq" (substTerms sigma) (substTerms tau) (\x y s -> return$  idApp (upExt_ y x) [TermUnderscore, TermUnderscore, s]) 
  let ret s = TermEq (idApp (subst_ x) (substTerms sigma ++ [s])) (idApp (subst_ x) (substTerms tau ++ [s]))
  toVarT <- toVar x eqs
  x' <- extend_ x
  b_ext <- isExtension x
  traversal x m ext_ (liftM extDeps . genDepRecord) (\s -> TermApp eq_refl_ [s]) ret (bmn ++ bsigma ++ btau ++ beqs) [sigma, tau, eqs]
                  (\z ->  TermApp toVarT [z])   
                  (\_ c cs -> return$ idApp (if b_ext then "" else congr_ (if x == x' then c else smart_ c)) cs)
                  mapExt_


-- 9. Coincidence of instantiation of renamings and substitutions
genUpRinstInst :: Binder -> TId -> GenM Definition
genUpRinstInst b z = do
  (m, bm) <- introScopeVarS "m"
  (n, bn) <- introScopeVar "n" z
  n_var <- toVar z n
  (xi, bxi) <- genRenS "xi" (m, n_var)
  (sigma, bsigma) <- genSubstS "sigma" (m, n) z
  (eq, b_eq) <- genEq z "Eq" (xi >>> var z n) sigma
  n' <- upSubst z [b] n
  let (pms, bpms) = variadicScopeParametersImplicit b
  let ret = equiv_ (idApp (upRen_ b z) (pms ++ [xi]) >>> var z n') (idApp (up_ b z) (pms ++ [sigma]))
  shift <- patternSId z b
  let t n = ap_ [idApp (ren_ z) shift, TermApp eq [n]]
  n <- tfresh "n"
  let s = eqTrans_ (idApp "scons_p_comp'" [TermUnderscore, TermUnderscore, var z n', TermId n]) (scons_p_congr_ (TermAbs [BinderName n] (t (TermId n))) (TermAbs [BinderName "z"] eq_refl_))
  let u = case b of Single z' ->  if z == z' then matchFin_ (TermId n) t (eq_refl_)  else t (TermId n)
                    BinderList p z' -> if z == z' then s else t (TermId n)
  return $ Definition (up_rinstInst_ b z) (bpms ++ bm ++ bn ++ bxi ++ bsigma ++ b_eq ) (Just ret) (TermAbs [BinderName "n"] u)

genRinstInst :: TId -> GenM FixpointBody
genRinstInst x = do
  ((m,n), bmn) <- introRenScope ("m", "n") x
  (xi, bxi) <- genRen x "xi" (m,n)
  (sigma, bsigma) <- genSubst x "sigma" (m,n)
  xs <- substOf x
  xis' <- mapM (\(y, xi) -> do
    n' <- castSubst x y n
    return$  xi >>> var y n') (zip xs (substTerms xi))
  (eqs, beqs) <- genEqs x "Eq" xis' (substTerms sigma) (\x y s -> return $  idApp (up_rinstInst_ y x) [TermUnderscore, TermUnderscore, s]) 
  x' <- extend_ x
  b_ext <- isExtension x
  let ret s = TermEq (idApp (ren_ x) (substTerms xi ++ [s])) (idApp (subst_ x) (substTerms sigma ++ [s]))
  toVarT <- toVar x eqs
  traversal x m rinstInst_ (liftM rinstInstDeps . genDepRecord) (\s -> TermApp eq_refl_ [s]) ret (bmn ++ bxi ++ bsigma ++ beqs) [xi, sigma, eqs]
                  (\n -> TermApp toVarT [n])
                  (\_ c xs -> return $  if b_ext then idApp "" xs else if x == x' then idApp (congr_ c) xs else idApp (congr_ (smart_ c)) xs)
                  mapExt_

genLemmaRinstInst :: TId -> GenM Lemma
genLemmaRinstInst x = do
  ((m,n), bmn) <- introRenScope ("m", "n") x
  (xi, bxi) <- genRen x "xi" (m,n)
  xs <- substOf x
  xis' <- mapM (\(y, xi) -> do
    n' <- castSubst x y n
    return$  xi >>> var y n') (zip xs (substTerms xi))
  let ret = TermEq (idApp (ren_ x) (substTerms xi)) (idApp (subst_ x) xis')
  let proof = TermApp fext_ [TermAbs [BinderName "x"] $ idApp (rinstInst_ x) (substTerms xi ++ map (const TermUnderscore) xs ++ (map (const (TermAbs [BinderName "n"] eq_refl_)) xs) ++ [TermId "x"])]
  return (Lemma (rinstInstFun_ x) (bmn ++ bxi) ret (ProofExact proof))

-- 9. Second identity lemma

genLemmaVarL :: TId -> GenM Lemma
genLemmaVarL x = do
  ((m,n), bmn) <- introRenScope ("m", "n") x
  (sigma,bsigma) <- genSubst x "sigma" (m,n)
  sigma' <- toVar x sigma
  let ret = TermEq ((var x m) >>> (idApp (subst_ x) (substTerms sigma))) sigma'
  let proof = TermApp fext_ [TermAbs [BinderName "x"] eq_refl_]
  return $ Lemma ("varL_" ++ x) (bmn ++ bsigma) ret (ProofExact proof)

genLemmaVarLRen :: TId -> GenM Lemma
genLemmaVarLRen x = do
  ((m,n), bmn) <- introRenScope ("m", "n") x
  (xi,bxi) <- genRen x "xi" (m,n)
  xi' <- (toVar x xi)
  x' <- extend_ x
  let ret = TermEq ((var x m) >>> (idApp (ren_ x) (substTerms xi))) (xi' >>> (var x' n))
  let proof = TermApp fext_ [TermAbs [BinderName "x"] eq_refl_]
  return $ Lemma ("varLRen_" ++ x) (bmn ++ bxi) ret (ProofExact proof)

genLemmaInstId :: TId -> GenM Lemma
genLemmaInstId x = do
  (m, bm) <- introScopeVar "m" x
  xs <- substOf x
  vars <- mapM (\y -> liftM2 idApp (return $ var_ y) (liftM substTerms (castSubst x y m))) xs 
  x' <- extend_ x
  let mid = if x == x' then TermConst (Id) else TermId inj_
      ret = TermEq (idApp (subst_ x) vars) mid
  let proof = TermApp fext_ [TermAbs [BinderName "x"] (idApp (idSubst_ x) ( vars ++ (map (const (TermAbs [BinderName "n"] eq_refl_)) xs) ++ [TermApp (TermConst Id) [TermId "x"]]))] 
  return $ Lemma ("instId_" ++ x) bm ret (ProofExact proof)

genLemmaRinstId :: TId -> GenM Lemma
genLemmaRinstId x = do
  (m, bm) <- introScopeVar "m" x
  xs <- substOf x
  vars <- mapM (\y -> liftM2 idApp (return $ var_ y) (liftM substTerms (castSubst x y m))) xs
  x' <- extend_ x
  let mid = if x == x' then (TermConst (Id)) else TermId inj_
      ret = TermEq (idApp ("@" ++ ren_ x) (substTerms m ++ substTerms m  ++ map (const (TermConst Id)) xs)) mid
  let proof = eqTrans_ (idApp ("rinstInst_" ++ x) (map (const (id_ TermUnderscore)) xs)) (TermId ("instId_" ++ x))
  return $ Lemma ("rinstId_" ++ x) bm ret (ProofExact proof)


-- 10. Generation of Boilerplate 

genSentences :: [TId] -> [TId] -> [(Binder,TId)] -> GenM [Sentence]
genSentences xs dps upList' = do
  if null xs && null upList' then throwError "Error: The list of sorts to generate is empty." else return ()
  upList <- return $ if null dps then upList' else [] -- If we are in a variant, then ups are provided by the specific feature.
  varSorts <- filterM isOpen xs -- Sorts which have variables
  hasbinders <- fmap (not. null) (substOf (head xs)) -- head xs suffices as all sorts in a component have the same substitution vector
  xs_nonempty <- filterM nonEmptySort xs -- Only sorts which have at least one constructor
  hasRen <- hasRenamings (head xs) -- Tests whether the sort requires renamings
  isRec <- recursive xs -- Test whether the component is recursive, otherwise replace Fixpoints by Definitions
  -- Types + Congruence lemmas
  types <- mapM genBody xs_nonempty
  congruences <- mapM genCongruences xs
  -- Code for instantiation
  upRen <- ifM hasRen $ mapM (uncurry genUpRenS) upList
  renamings <- ifM hasRen $ liftM (\x -> [SentenceFixpoint x]) $ genRenamings xs
  ups <- ifM hasRen $ mapM (uncurry genUpS) upList
  upsNoRen <- ifM (not hasRen) $ mapM (uncurry genUpS) upList
  substitutions <- genSubstitutions xs
  -- Id lemmas
  upId <- mapM (uncurry genUpId) upList
  idlemmas <- mapM genIdL xs
  -- Extensionality lemmas
  extUpRen <- ifM hasRen $ mapM (uncurry genUpExtRen) upList
  extRen <- ifM hasRen $ liftM (\x -> [SentenceFixpoint $ Fixpoint isRec x]) $ mapM genExtRen xs
  extUp <- mapM (uncurry genUpExt) upList
  ext <- mapM genExt xs
  -- Composition lemmas 
  upRenRen <- ifM hasRen $ mapM (uncurry genUpRenRen) upList
  compRenRen <- ifM hasRen $ liftM (\x -> [SentenceFixpoint $ Fixpoint isRec x]) $ mapM genCompRenRen xs
  upRenSubst <- ifM hasRen $ mapM (uncurry genUpRenSubst) upList
  compRenSubst <- ifM hasRen $ liftM (\x -> [SentenceFixpoint $ Fixpoint isRec x]) $ mapM genCompRenSubst xs
  upSubstRen <- ifM hasRen $ mapM (uncurry genUpSubstRen) upList
  compSubstRen <- ifM hasRen $ liftM (\x -> [SentenceFixpoint $ Fixpoint isRec x]) $ mapM genCompSubstRen xs
  upSubstSubst <- ifM hasRen $ mapM (uncurry genUpSubstSubst) upList
  compSubstSubst <- liftM (\x -> [SentenceFixpoint $ Fixpoint isRec x]) $ mapM genCompSubstSubst xs
  upSubstSubstNoRen <- ifM (not hasRen) $ mapM (uncurry genUpSubstSubstNoRen) upList
  -- Coincidence of Instantiation
  upRinstInst <- ifM hasRen $ mapM (uncurry genUpRinstInst) upList
  rinstInst <- ifM hasRen $ liftM (\x -> [SentenceFixpoint $ Fixpoint isRec x]) $ mapM genRinstInst xs
  -- Lemmas for the rewriting system
  lemmaRinstId <- ifM hasRen $  mapM genLemmaRinstId xs
  lemmaInstId <- mapM genLemmaInstId xs
  lemmaVarL <- mapM genLemmaVarL varSorts
  lemmaVarLRen <- ifM hasRen $ mapM genLemmaVarLRen varSorts
  lemmaRenSubst <- ifM hasRen $ mapM genLemmaRinstInst xs
  lemmaSubstRenRen <- ifM hasRen $ mapM genLemmaRenRenComp xs
  lemmaSubstCompRen <- ifM hasRen $ mapM genLemmaCompRenSubst xs
  lemmaSubstRenComp <- ifM hasRen $ mapM genLemmaCompSubstRen xs
  lemmaSubstComp <- mapM genLemmaCompSubstSubst xs
  let (l1, l2) = unzip lemmaSubstComp
  let (l3, l4) = if hasRen then unzip lemmaSubstCompRen else ([], [])
  let (l5, l6) = if hasRen then unzip lemmaSubstRenComp else ([], [])
  let (l7, l8) = if hasRen then unzip lemmaSubstRenRen else ([], [])
  -- Definitions for modular syntax
  -- a. Generation of corresponding information
  let open = not $ null $ varSorts
  inFeature <- isFeature (head xs)
  extensions <- extensionList xs -- Generates a list of all sorts and their extension, if available
  prevExt <- dependencyPairs xs -- Get a list of all pairs of features depending on xs and xs
  extSorts <- filterM isExtension xs
  -- b. Generation of actual code for modular syntax
--  hypoSentences <- (if (null dps) then return [] else  genSentences dps [] upList' >>= hypos xs open)  -- Generation of hypotheses
  -- upList' 
  hypoSentences <- (if (null dps) then return [] else 
                      do
                        last <- genSentences [head (reverse dps)] [] upList'
                        first <- mapM (\x -> genSentences [x] [] []) (reverse (tail (reverse dps)))
                        hypos xs open (concat first ++ last))  -- Generation of hypotheses
  retractAssumptions <- genRetractAssumptions extensions -- Generation of hypotheses of retracts
  retractsRenamings <- mapM genRetractRen xs
  retractsSubstitutions <- mapM genRetractSubst xs
  retracts <- genRetracts prevExt -- Generation of proofs for retracts
  depSmarts <- mapM genSmarts (if (null dps) then [] else xs) -- Generation of smart constructors if we have dependencies
  inFcts <- genIns extensions -- Generation of In functions
  inProofs <- mapM genInProof extSorts -- Generation of alternative induction principle
  -- Full Generation of Sentences
  return $ nonEmptySection (concat xs)
          ( -- Possible dependencies
            hypoSentences
          -- Types
          ++ [SentenceInductive (Inductive types) | (not . null) types] 
          -- Retracts + smart constructors
          ++ retractAssumptions ++ concat depSmarts
          -- Congruence lemmas
          ++ map SentenceLemma (concat congruences)
          -- Proofs for retractAssumptions
          ++ retracts
          -- Instantiation of renamings/substitutions
          ++ (if hasbinders then map SentenceDefinition upRen ++ renamings ++ concat retractsRenamings
          ++ map SentenceDefinition ups ++ [SentenceFixpoint substitutions] ++ map SentenceDefinition upsNoRen ++ concat retractsSubstitutions
          -- Identity Lemma
          ++ map SentenceDefinition upId ++ [SentenceFixpoint $ Fixpoint isRec idlemmas]
          -- Extensionality Lemmas
          ++ map SentenceDefinition extUpRen ++ extRen ++ map SentenceDefinition extUp ++ [SentenceFixpoint $ Fixpoint isRec ext]
          -- Composition Lemma
          ++ map SentenceDefinition upRenRen ++ compRenRen
          ++ map SentenceDefinition upRenSubst ++ compRenSubst
          ++ map SentenceDefinition upSubstRen ++ compSubstRen
          ++ map SentenceDefinition upSubstSubst  ++ compSubstSubst ++ map SentenceDefinition upSubstSubstNoRen
          -- Coincidence of instantiation of renamings and substitutions
          ++ map SentenceDefinition upRinstInst ++ rinstInst
          -- Lemmas for the rewriting system
          ++ map SentenceLemma (lemmaRenSubst ++  lemmaInstId ++ lemmaRinstId ++  lemmaVarL  ++ lemmaVarLRen ++l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7 ++ l8 ) 
          -- In Functions for features
          ++ map SentenceDefinition inFcts 
          -- ++ [SentenceFixpoint (Fixpoint True inProofs) | not (null inProofs) && not inFeature]
          else []))


-- 11. Generator for Modular Syntax, Generation of only the boilerplate for modular syntax.
genSentencesMod :: Bool -> [TId] -> [TId] -> [(Binder,TId)] -> GenM [Sentence]
genSentencesMod b xs dps upList = do
  x_open <- isOpen (head xs)
  hypoSentences <- if (null dps) then return [] else mapM (\x -> genSentencesMod False (nub dps) [] [] >>= hypos xs x_open) (nub dps)
  depSmarts <- mapM genSmarts (if (null (concat hypoSentences)) then [] else xs)
  extensions <- extensionList xs
  prevExt <- dependencyPairs xs
  retractAssumptions <- genRetractAssumptions extensions -- TODO: Change.
  retracts <- genRetracts prevExt
  inFcts <- genIns extensions
  extSorts <- filterM isExtension xs
  inProofs <- mapM genInProof extSorts
  ys <- filterM nonEmptySort xs
  types <- mapM genBody ys
  congruences <- mapM genCongruences xs
  return $ nonEmptySection (concat xs) (concat hypoSentences ++ [SentenceInductive (Inductive types) | (not . null) types] ++ map SentenceDefinition inFcts ++ [SentenceFixpoint (Fixpoint True inProofs) | not (null inProofs) && b]++
   retractAssumptions ++  (concat depSmarts) ++ map SentenceLemma (concat congruences)  ++ retracts)

