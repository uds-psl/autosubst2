{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Autosubst.Generator (genCodeT,genModularSyntax) where

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

-- Additional things for modular syntax
genConstructor :: Bool -> Bool -> TId -> TId
genConstructor True _ _      = ""
genConstructor False True c  = c
genConstructor False False c = smart_ c

data DepRecord = DepRecord
  { renDeps            :: [Term]
  , substDeps          :: [Term]
  , idSubstDeps        :: [Term]
  , extRenDeps         :: [Term]
  , extDeps            :: [Term]
  , rinstInstDeps      :: [Term]
  , compRenRenDeps     :: [Term]
  , compRenSubstDeps   :: [Term]
  , compSubstRenDeps   :: [Term]
  , compSubstSubstDeps :: [Term]
  }

-- All really appearing combinatiions of binders.
directUps :: TId -> GenM [(Binder, TId)]
directUps x = do
  cs <- constructors x
  ps <- return $ map (\(Position bs p) -> [(b, p) | b <- bs]) (concat $ map (\(Constructor _ _ ps) -> ps) cs)  -- :: [[(Binder, Argument)]]
  return $ concatMap (\(b, xs) -> map (\x -> (b, x)) (getIds xs)) (concat ps)

realDepsB :: Binder -> GenM Binder
realDepsB b = return b

genDepRecord :: TId -> GenM DepRecord
genDepRecord x = do
  b <- isFeature x
  dps <- realDeps x
  substsorts <- return $ if b then dps else []
  varsorts <- filterM isOpenComponent (if b then dps else [])
  mups <- directUps x
  let dups :: [(Binder, TId)]
      dups = if b then mups else [] -- [(p,y) | y <- dps, (p,y) `elem` mups]
      types = map (const TermUnderscore) ["x" | b] -- All sub-appearing sorts with dependencies.
      uprens = map (\(p,q) -> TermId (upRen_ p q)) dups -- All scope changes (x,y)
      rens = map (\x -> TermUnderscore) ["x" | b] -- Renamings for all sub-appearing sorts.
      mrens = map (\x -> TermId (ren_ x)) substsorts -- Renamings for all sub-appearing sorts.
      ups = map (\(p,q) -> TermId (up_ p q)) dups
      substs = map (const TermUnderscore) ["x" | b]
      msubsts = map (\x -> TermId (subst_ x)) substsorts
      instances = map (const TermUnderscore) ["x" | b] -- Instances for all sub-appearing sorts.
      minstances = map (const TermUnderscore) dps -- Instances for all sub-appearing sorts.
      vars = map (\x -> TermId (var_ x)) varsorts -- All subsorts with variables.
      upids = map (\(p,q) -> TermId (upId_ p q)) dups
      idSubsts = map (\x -> TermId (idSubst_ x)) dps
      upRenExts = map (\(p,q) -> TermId (upExtRen_ p q)) dups
      extRens = map (\x -> TermId (extRen_ x)) dps
      upexts = map (\(p,q) -> TermId (upExt_ p q)) dups
      upRinstInsts = map (\(p,q) -> TermId (up_rinstInst_ p q)) dups
      exsts = map (\x -> TermId (ext_ x)) dps
      upRenRens = map (\(p,q) -> TermId (up_ren_renName_ p q)) dups
      upRenSubsts = map (\(p,q) -> TermId (up_ren_subst_ p q)) dups
      upSubstRens = map (\(p,q) -> TermId (up_subst_ren_ p q)) dups
      upSubstSubsts = map (\(p,q) -> TermId (up_subst_subst_ p q)) dups
      rinstInsts = map (\x -> TermId (rinstInst_ x)) dps
      compRenRens = map (\x -> TermId (compRenRen_ x)) dps
      compRenSubsts = map (\x -> TermId (compRenSubst_ x)) dps
      compSubstRens = map (\x -> TermId (compSubstRen_ x)) dps
      compSubstSubsts = map (\x -> TermId (compSubstSubst_ x)) dps
      renRetracts = map (\x -> TermAbs [BinderName "x", BinderName "y"] eq_refl_) ["x" | b]
      mrenRetracts = map (\x -> TermAbs [BinderName "x", BinderName "y"] eq_refl_) dps
      substRetracts = map (\x -> TermAbs [BinderName "x", BinderName "y"] eq_refl_) ["x" | b]
      msubstRetracts = map (\x -> TermAbs [BinderName "x", BinderName "y"] eq_refl_) dps
      renDeps = types ++ uprens ++ mrens ++ instances
      substDeps = types ++ ups ++ msubsts ++ minstances
      idSubstDeps = types ++ vars ++ ups ++ msubsts ++ upids ++ idSubsts ++ instances
      extRenDeps = types ++ uprens ++ mrens ++ upRenExts ++ extRens ++ instances
      extDeps = types ++ ups ++ msubsts ++ upexts ++ exsts ++ minstances
      rinstInstDeps = types ++ vars ++ uprens ++ mrens ++ ups ++ msubsts ++ upRinstInsts ++ rinstInsts ++  instances
      compRenRenDeps = types ++ uprens ++ rens ++ upRenRens ++ compRenRens ++ instances ++ renRetracts
      compRenSubstDeps = types ++ uprens ++ mrens ++ ups ++ substs ++ upRenSubsts ++ compRenSubsts ++ instances ++ substRetracts
      compSubstRenDeps = types ++ uprens ++ rens ++ ups ++ msubsts ++ upSubstRens ++ compSubstRens ++ minstances ++ mrenRetracts
      compSubstSubstDeps = types ++ ups ++ substs ++ upSubstSubsts ++ compSubstSubsts ++ minstances ++ msubstRetracts
  return $ DepRecord renDeps substDeps idSubstDeps extRenDeps extDeps rinstInstDeps compRenRenDeps compRenSubstDeps compSubstRenDeps compSubstSubstDeps


posExtend_ :: TId -> TId -> GenM TId
posExtend_ x cname = do
  x' <- extend_ x
  return $ if (x == x') then cname else (smart_ cname)

emptyT :: TId -> GenM [Term]
emptyT x = return []

ren_var_ :: TId -> String
ren_var_ x = "ren_var_" ++ x

retract_ren_ :: TId -> String
retract_ren_ x = "retract_ren_" ++ x

retract_subst_ :: TId -> String
retract_subst_ x = "retract_subst_" ++ x

-- fext_ :: String
-- fext_ = "FunctionalExtensionality.functional_extensionality _ _"


-- Generation of syntax from a signature

genVar :: TId -> SubstTy -> GenM [InductiveCtor]
genVar x n = do
  open_x <- isOpen x
  s <- finT_ x (sty_terms n)
  let t = [s] ==> sortType x n
  return [InductiveCtor (var_ x) (Just t) | open_x]


createBinders :: [(String, TId)] -> [CBinder]
createBinders = map (\p -> BinderNameType [fst p] (TermId (snd p)))

createImpBinders :: [(String, TId)] -> [CBinder]
createImpBinders = map (\p -> BinderImplicitNameType [fst p] (TermId (snd p)))

genArg :: TId -> SubstTy -> [Binder] -> Argument  -> GenM Term
genArg x n bs (Atom y)  = liftM2 idApp (complete_ y) (fmap sty_terms $ castUpSubst x bs y n)
genArg x n bs (FunApp f p xs) = do
  xs' <- mapM (genArg x n bs) xs
  return $ idApp (funname_ (f ++ p)) xs'

-- Generation of constructor.
genCons :: TId -> SubstTy -> Constructor -> GenM InductiveCtor
genCons x n (Constructor pms cname pos) = do
  t <- do
    up_n_x <- mapM (\(Position bs y) -> genArg x n bs y) pos
    return $  up_n_x ==> sortType x n
  return $ InductiveCtor (constructor_ cname) (Just (if null pms then t else TermForall (createBinders pms) t))

genBody :: TId -> GenM InductiveBody
genBody x = do
  cs <- constructors x
  (n,b) <- introScopeVar "n" x
  varCons <- genVar x n
  constructors <- mapM (genCons x n) cs
  return $ InductiveBody x (explicit_ b) (TermSort Type) (varCons ++ constructors)


-- arg' <- complete_ arg
-- xs' <-  castUpSubst x (Position binders arg) m
-- return $ BinderImplicitNameType [y] (sortType arg' xs')) (zip s pos)
genCongruence :: TId -> Constructor -> GenM Lemma
genCongruence x (Constructor pms cname pos) = do
    (m, bm) <- introScopeVar "m" x
    let s = getPattern "s" pos
    let t = getPattern "t" pos
    let bs s = mapM (\(s, Position binders arg) -> do
                                                  arg_type <-  genArg x m binders arg -- castUpSubst x bs arg m
                                                  return $ BinderImplicitNameType [s] arg_type
                                                    ) (zip s pos) -- index, pattern, binders.
    bes <- bs s
    bt <- bs t
    cname' <- posExtend_ x cname
    let bpms = createImpBinders pms
    let pms' = map TermId (map fst pms)
    let eqs = zipWith TermEq (map TermId s) (map TermId t)
    let eq = TermEq (idApp cname' ( sty_terms m ++ pms' ++ map TermId s)) (idApp cname' (sty_terms m ++ pms' ++ map TermId t))
    let beqs = map (\(n,s) -> BinderNameType ["H" ++ show n] s) (zip [1..] eqs)
    let eq' n = idApp cname' ( sty_terms m ++ pms' ++ map (\m -> if (m == n) then TermId "x" else TermUnderscore) [1..(length eqs)])
    let p = repRew (map (\n -> (TermId ("H" ++ show n), (TermAbs [BinderName "x"] (eq' n)))) [1..(length eqs)])
    return $ Lemma (congr_ cname') (bpms ++ bm ++ bes ++ bt ++ beqs) eq (ProofString "congruence.")-- p

genCongruences :: TId -> GenM [Lemma]
genCongruences x = join $ fmap (mapM (genCongruence x)) (constructors x)


traversal :: TId -> SubstTy -> (TId -> String) -> (TId -> GenM [Term]) ->(Term -> Term) ->  (Term -> Term) -> [CBinder] -> [SubstTy] -> (Term -> Term)  -> ([String] -> CId -> [Term] -> Term) -> (FId -> [Term] -> Term) -> GenM FixpointBody
traversal x scope name extras no_args ret bargs args var_case sem funsem = do
  let s = "s"
  cs <- constructors x
  open_x <- isOpen x
  let underscore_pattern = TermSubst (SubstScope (map (const TermUnderscore) (sty_terms scope)))
  let var_pattern = [Equation (PatCtor (idApp (var_ x) [underscore_pattern]) [s]) (var_case (TermId s)) | open_x]
  -- computes the result for a constructor.
  let cons_pattern (Constructor pms cname pos) =  let s = getPattern "s" pos in
                                              let arg_map (bs) arg = (case arg of
                                                                      Atom y -> (do
                                                                                  b <- hasArgs y
                                                                                  extra <- extras y
                                                                                  arg <- mapM (castUpSubst x bs y) args
                                                                                  return $ if b then idApp (name y) (extra ++ map TermSubst arg) else (TermAbs [BinderName "x"] (no_args (TermId "x"))))
                                                                      FunApp f p xs -> (do
                                                                                        res <- mapM (arg_map bs) xs
                                                                                        return $ funsem f res)) in do
                                              positions <- mapM (\(s, Position bs arg) -> liftM2 TermApp (arg_map bs arg) (return [TermId s])) (zip s pos)
                                              return $ Equation (PatCtor (idApp cname (underscore_pattern : map TermId (map fst pms))) s) (sem (map fst pms) cname positions)
  cons_pat <- mapM cons_pattern cs
  let t = TermMatch (MatchItem (TermId s) Nothing)  (Just $ ret (TermId s)) (var_pattern ++ cons_pat)
  return $ FixpointBody (name x) (bargs ++ [BinderNameType [s] (idApp x (sty_terms scope))]) (ret (TermId s)) t -- Command for BinderNameType


-- Renamings

-- UpRen in sort x by the binder b.
genUpRenS :: Binder -> TId -> GenM Definition
genUpRenS b z = do
  ((m,n), bs) <- introRenScopeS ("m", "n")
  (xi, bxi) <- genRenS "xi" (m,n)
  let (_, bpms) = bparameters b
      m' = succ_ m z b
      n' = succ_ n z b
  return $ Definition (upRen_ b z) (bpms ++ bs ++ bxi) (Just (renT m' n')) (up_ren_ z b xi) --

genRenaming :: TId -> GenM FixpointBody
genRenaming x = do
  ((m,n),bs) <- introRenScope ("m", "n") x
  (xi,bxi) <- genRen x "xi" (m,n)
  toVarT <- toVar x xi
  x' <- extend_ x
  b_ext <- isExtension x
  traversal x m ren_ (liftM renDeps . genDepRecord) id (const $ idApp x' (sty_terms n)) (bs ++ bxi) [xi]
                      (\s -> TermApp (var x' n) [TermApp toVarT [s]])
                      (\pms c s -> idApp (genConstructor b_ext (x == x') c) (sty_terms n ++ map TermId pms ++ s)) map_

genRetractRen :: TId -> GenM [Sentence]
genRetractRen x = do
  ((m,n),bs) <- introRenScope ("m", "n") x
  (xi,bxi) <- genRen x "xi" (m,n)
  toVarT <- toVar x xi
  x' <- extend_ x
  return $ [SentenceVariable (retract_ren_ x') (TermForall (bs ++ bxi ++ [BinderName "s"]) (TermEq (idApp (ren_ x') (sty_terms xi ++ [idApp inj_ [TermId "s"]])) (idApp (ren_ x) (sty_terms xi ++ [TermId "s"]))))  | x' /= x]


genRenamings :: [TId] -> GenM Fixpoint
genRenamings xs = do
  fs <- mapM genRenaming xs
  r <- recursive xs
  return $ Fixpoint r fs

-- TODO Change according to whether this is a renaming.
upSubstT :: Binder -> TId -> SubstTy -> Term -> GenM Term
upSubstT b z m sigma = do
    pat <- patternSId z b
    m <- upSubst z [b] m
    hasRen <- hasRenamings z
    let sigma' = sigma >>> idApp (if hasRen then (ren_ z) else (subst_ z)) pat
    return $ cons__ z b sigma' m

cons__ :: TId -> Binder -> Term -> SubstTy -> Term
cons__ z (Single y) sigma m = if (z == y) then TermApp cons_ [zero_ z (Single y) m, sigma] else sigma
cons__ z (BinderList p y) sigma m = if (z == y) then idApp "scons_p " [TermId p, zero_ z (BinderList p y) m, sigma] else sigma

zero_ :: TId -> Binder -> SubstTy -> Term
zero_ x (Single y) m       = TermApp (var x m) [varZero_]
zero_ x (BinderList p y) m = idApp "zero_p" [TermId p] >>> var x m

genUpS :: Binder -> TId -> GenM Definition
genUpS b z = do
  ((m,n), bs) <- introSubstScopeS ("m", "n") z
  (sigma, b_sigma) <- genSubstS "sigma" (m,n) z
  sigma <- upSubstT b z n sigma
  let (pms, bpms) = bparameters b
      m' = succ_ m z b
  n' <- upSubst z [b] n
  return $ Definition (up_ b z) (bpms ++ bs ++ b_sigma) (Just (substT m' n' z)) sigma

-- Version of genUp in case there aren't renamings
genUpS_ :: Binder -> TId -> GenM Definition
genUpS_ b z = do
  ((m,n), bs) <- introSubstScopeS ("m", "n") z
  (sigma, b_sigma) <- genSubstS "sigma" (m,n) z
  sigma <- upSubstT b z n sigma
  let (pms, bpms) = bparameters b
      m' =  succ_ m z b
  n' <- upSubst z [b] n
  return $ Definition (up_ b z) (bpms ++ bs ++ b_sigma) (Just (substT m' n' z)) sigma

genSubstitution :: TId -> GenM FixpointBody
genSubstitution x = do
  ((m, n), bmn) <- introRenScope ("m", "n") x
  (sigma, bs) <- genSubst x "sigma" (m,n)
  toVarT <- toVar x sigma
  x' <- extend_ x
  b_ext <- isExtension x
  traversal x m subst_ (liftM substDeps . genDepRecord) id (const $ idApp x' (sty_terms n)) (bmn ++ bs) [sigma]
                       (\s -> TermApp toVarT [s])
                       (\pms c s -> idApp (genConstructor b_ext (x == x') c) (sty_terms n ++ map TermId pms ++ s)) map_

genRetractSubst :: TId -> GenM [Sentence]
genRetractSubst x = do
  ((m,n),bs) <- introRenScope ("m", "n") x
  (sigma,bsigma) <- genSubst x "sigma" (m,n)
  toVarT <- toVar x sigma
  x' <- extend_ x
  return $ [SentenceVariable (retract_subst_ x') (TermForall (bs ++ bsigma ++ [BinderName "s"]) (TermEq (idApp (subst_ x') (sty_terms sigma ++ [idApp inj_ [TermId "s"]])) (idApp (subst_ x) (sty_terms sigma ++ [TermId "s"]))))  | x' /= x]


genSubstitutions :: [TId] -> GenM Fixpoint
genSubstitutions xs = do
  if null xs then throwError "Error: in genSubstitutions the list of substitutions is empty." else return ()
  fs <- mapM genSubstitution xs
  r <- recursive [L.head xs]
  return $ Fixpoint r fs

genUpId :: Binder -> TId -> GenM Definition
genUpId y z = do
  (m, bm) <- introScopeVar "m" z
  m_var <- toVar z m
  (sigma, b_sigma) <- genSubstS "sigma" (m_var, m) z
  (eq, b_eq) <- genEq z "Eq" sigma (var z m)
  n <- tfresh "n"
  m <- upSubst z [y] m
  let (pms, bpms) = binvparameters y
  let ret = equiv_ (idApp (up_ y z) (pms ++ [sigma])) (var z m)
  shift <- patternSId z y
  hasRen <- hasRenamings z
  let t n = ap_ [idApp (if hasRen then ren_ z else subst_ z) shift, TermApp eq [n]]
      t' n = eqTrans_ (t n) (TermId (ren_var_ z)) -- y instead of Z
  let u = case y of Single z' -> if z == z' then matchFin_ (TermId n) t eq_refl_ else t (TermId n)
                    BinderList p z' -> if z == z' then scons_p_eta_ (var z m) (TermAbs [BinderName n] (t (TermId n))) (TermAbs [BinderName n] eq_refl_) else (t (TermId n))
  return $ Definition (upId_ y z) (bpms ++ bm ++ b_sigma ++ b_eq) (Just ret) (TermAbs [BinderName n] u)


scons_p_eta_ :: Term -> Term ->  Term ->  Term
scons_p_eta_ h f g = idApp "scons_p_eta" [h, f, g]

genIdL :: TId -> GenM FixpointBody
genIdL x = do
  (m, bm) <- introScopeVar "m" x
  (sigma, bs) <- genSubst x "sigma" (m, m)
  xs <- substOf x
  eqs' <- mapM (\y -> liftM2 idApp (return $ var_ y) (fmap sty_terms (castSubst x y m))) xs
  (eqs, beqs) <- genEqs x "Eq" (sty_terms sigma) eqs' (\x y s -> return $ idApp (upId_ y x) [TermUnderscore, s]) -- TODO: Generate ID in a sensible way.
  toVarT <- toVar x eqs
  x' <- extend_ x
  b_ext <- isExtension x
  let s' s = if (x == x') then s else idApp inj_ [s] -- NEW
      ret s = TermEq (idApp (subst_ x) (sty_terms sigma ++ [s])) (s' s)
  traversal x m idSubst_ (liftM idSubstDeps . genDepRecord) (\s -> TermApp eq_refl_ [s]) ret (bm ++ bs ++ beqs) [sigma, eqs]
                       (\s -> TermApp toVarT [s])
                       (\pms c cs -> idApp (if b_ext then "" else congr_ (if x == x' then c else smart_ c)) cs) mapId_


genUpRenRen :: Binder -> TId -> GenM Definition
genUpRenRen y z = do
 (k, bk) <- introScopeVarS "k"
 (l, bl) <- introScopeVarS "l"
 (m, bm) <- introScopeVarS "m"
 (xi, bxi) <- genRenS "xi" (k, l)
 (tau, btau) <- genRenS "tau" (l, m)
 (theta, btheta) <- genRenS "theta" (k, m)
 -- m_var <- toVar z m
 (eq, b_eq) <- genEq z "Eq" (xi >>> tau) theta
 n <- tfresh "n"
 -- m <- upSubst z [y] m
 let (pms, bpms) = binvparameters y
 let ret = equiv_ (idApp (upRen_ y z) (pms ++ [xi]) >>> idApp (upRen_ y z) (pms ++ [tau]) ) (idApp (upRen_ y z) (pms ++ [theta]))
 shift <- patternSId z y
 -- let t n = ap_ [idApp (ren_ z) shift, TermApp eq [n]]
 let u = case y of Single z' -> if (z == z') then idApp up_ren_ren_ [xi,tau,theta,eq] else eq
                   BinderList p z' -> if z == z' then idApp "up_ren_ren_p" [eq] else eq
--   if y == Single z then idApp up_ren_ren_ [xi,tau,theta,eq]  {- matchFin_ (TermId n) t eq_refl_ -}  else eq_refl_ -- t (TermId n) -- TODO: Update to BinderList
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
  let b = x == x'
  (eqs, beqs) <- genEqs x "Eq" (zipWith (>>>) (sty_terms xi) (sty_terms zeta)) (sty_terms rho) (\x y s -> return$ case y of Single z -> if z == x then idApp (if b then up_ren_ren_ else  ("up_ren_ren" ++ sep ++ x ++ sep ++ z) ) [TermUnderscore, TermUnderscore, TermUnderscore, s] else s
                                                                                                                            BinderList p x' -> if x' == x then idApp "up_ren_ren_p" [s] else s)
  toVarT <- toVar x eqs
  let ret s = TermEq (idApp (ren_ x') (sty_terms zeta ++ [idApp (ren_ x) $ sty_terms xi  ++ [s]])) (idApp (ren_ x) (sty_terms rho ++ [s]))
      sem _ c xs = if b_ext then idApp "" xs else if (x == x') then idApp (congr_ c) xs else eqTrans_ (idApp (retract_ren_ x') [TermUnderscore, idApp c (map (const TermUnderscore) xs)]) (idApp (congr_ (smart_ c)) xs)
      varC n = ap_ [var x' l, TermApp toVarT [n]]
      varS n = eqTrans_ (idApp (retract_ren_ x') [TermUnderscore, idApp (var_ x) [idApp ("xi" ++ x') [n]] ] ) (varC n)
  traversal x m compRenRen_ (liftM compRenRenDeps . genDepRecord) (\s -> TermApp eq_refl_ [s]) ret (bkl ++ bm ++ bxi ++ bzeta ++ brho ++ beqs) [xi, zeta, rho, eqs]
                  (\n -> if b then varC n else varS n)
                  sem mapComp_



genLemmaRenRenComp :: TId -> GenM (Lemma, Lemma) --(Lemma, [Lemma])
genLemmaRenRenComp x = do
  ((k,l), bkl) <- introRenScope ("k", "l") x
  (m, bm) <- introScopeVar "m" x
  (xi, bxi) <- genRen x "xi" (m,k)
  (zeta,bzeta) <- genRen x "zeta" (k,l)
  xs <- substOf x
  x' <- extend_ x
  let sigmazeta = zipWith (>>>) (sty_terms xi) (sty_terms zeta)
  let s = "s"
  let ret = TermEq (idApp (ren_ x') (sty_terms zeta ++ [idApp (ren_ x) $ sty_terms xi  ++ [TermId s]])) (idApp (ren_ x) (sigmazeta ++ [TermId s]))
  let proof = idApp (compRenRen_ x) (sty_terms xi ++ sty_terms zeta ++ map (const TermUnderscore) xs ++ map (const (TermAbs [BinderName "n"] eq_refl_)) xs ++ [TermId s])
  let ret' = TermEq ((idApp (ren_ x) (sty_terms xi)) >>> (idApp (ren_ x') (sty_terms zeta))) (idApp (ren_ x) sigmazeta) -- (sty_terms sigma >>> idApp (subst_ x) (sty_terms tau)))
  let proof' = TermApp fext_ [TermAbs [BinderName "n"] (idApp ("renRen_" ++ x) (sty_terms xi ++ sty_terms zeta ++ [TermId "n"]))]
  return (Lemma ("renRen_" ++ x) (bkl ++ bm ++ bxi ++ bzeta ++ [BinderNameType [s] (idApp x (sty_terms m))]) ret (ProofExact proof),
          Lemma ("renRen'_" ++ x) (bkl ++ bm ++ bxi ++ bzeta) ret' (ProofExact proof'))


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
  let (pms, bpms) = binvparameters y
  let ret = equiv_ (idApp (upRen_ y z) (pms ++ [xi]) >>> idApp (up_ y z) (pms ++ [tau]) ) (idApp (up_ y z) (pms ++ [theta]))
  shift <- patternSId z y
  let t n = ap_ [idApp (ren_ z) shift, TermApp eq [n]]
  let s = eqTrans_ (scons_p_comp' (TermId n)) (scons_p_congr_  (TermAbs [BinderName "z"] (eqTrans_ (scons_p_tail' (TermApp xi [TermId "z"])) (t (TermId "z")))) (TermAbs [BinderName "z"] (scons_p_head' (TermId "z"))))
  let u = case y of Single z' ->  if z == z' then matchFin_ (TermId n) t eq_refl_  else t (TermId n)
                    BinderList p z' -> if z == z' then s else t (TermId n)
  return $ Definition (up_ren_subst_ y z) (bpms ++ bk ++ bl ++ bm ++ bxi ++ btau ++ btheta ++ b_eq ) (Just ret) (TermAbs [BinderName "n"] u)

scons_p_comp' :: Term -> Term
scons_p_comp' x = idApp "scons_p_comp'" [TermUnderscore, TermUnderscore, TermUnderscore, x]

scons_p_tail' :: Term -> Term
scons_p_tail' x = idApp "scons_p_tail'" [TermUnderscore, TermUnderscore, x]

scons_p_head' :: Term -> Term
scons_p_head' x = idApp "scons_p_head'" [ TermUnderscore, TermUnderscore, x]

genCompRenSubst :: TId -> GenM FixpointBody
genCompRenSubst x = do
  ((k,l), bkl) <- introRenScope ("k", "l") x
  (m, bm) <- introScopeVar "m" x
  (xi, bxi) <- genRen x "xi" (m,k)
  (zeta,bzeta) <- genSubst x "tau" (k,l)
  (rho, brho) <- genSubst x "theta" (m, l)
  (eqs, beqs) <- genEqs x "Eq" (zipWith (>>>) (sty_terms xi) (sty_terms zeta)) (sty_terms rho) (\x y s -> return $ idApp (up_ren_subst_ y x) [TermUnderscore, TermUnderscore, TermUnderscore, s])
  toVarT <- toVar x eqs
  x' <- extend_ x
  b_ext <- isExtension x
  let b = x == x'
      ret s = TermEq (idApp (subst_ x') (sty_terms zeta ++ [idApp (ren_ x) $ sty_terms xi  ++ [s]])) (idApp (subst_ x) (sty_terms rho ++ [s]))
      sem _ c xs = if b_ext then idApp "" xs else if (x == x') then (idApp (congr_ c) xs) else eqTrans_ (idApp (retract_subst_ x') [TermUnderscore, idApp c (map (const TermUnderscore) xs)]) (idApp (congr_ (smart_ c)) xs)
      varC n = TermApp toVarT [n]
      varS n = eqTrans_ (idApp (retract_subst_ x') [TermUnderscore, idApp (var_ x) [idApp ("xi" ++ x') [n]] ] ) (varC n)
  traversal x m compRenSubst_ (liftM compRenSubstDeps . genDepRecord) (\s -> TermApp eq_refl_ [s]) ret (bkl ++ bm ++ bxi ++ bzeta ++ brho ++ beqs) [xi, zeta, rho, eqs]
                  (\n -> if b then varC n else varS n)
                  sem
                  mapComp_

genLemmaSubstRenComp :: TId -> GenM (Lemma, Lemma) --(Lemma, [Lemma])
genLemmaSubstRenComp x = do
  ((k,l), bkl) <- introRenScope ("k", "l") x
  (m, bm) <- introScopeVar "m" x
  (xi, bxi) <- genRen x "xi" (m,k)
  (zeta,bzeta) <- genSubst x "tau" (k,l)
  xs <- substOf x
  x' <- extend_ x
  let sigmazeta = zipWith (>>>) (sty_terms xi) (sty_terms zeta)
  let s = "s"
  let ret = TermEq (idApp (subst_ x') (sty_terms zeta ++ [idApp (ren_ x) $ sty_terms xi  ++ [TermId s]])) (idApp (subst_ x) (sigmazeta ++ [TermId s]))
  let proof = idApp (compRenSubst_ x) (sty_terms xi ++ sty_terms zeta ++ map (const TermUnderscore) xs ++ map (const (TermAbs [BinderName "n"] eq_refl_)) xs ++ [TermId s])
  let ret' = TermEq ((idApp (ren_ x) (sty_terms xi)) >>> (idApp (subst_ x') (sty_terms zeta))) (idApp (subst_ x) sigmazeta) -- (sty_terms sigma >>> idApp (subst_ x) (sty_terms tau)))
  let proof' = TermApp fext_ [TermAbs [BinderName "n"] (idApp ("renComp_" ++ x) (sty_terms xi ++ sty_terms zeta ++ [TermId "n"]))]
  return (Lemma ("renComp_" ++ x) (bkl ++ bm ++ bxi ++ bzeta ++ [BinderNameType [s] (idApp x (sty_terms m))]) ret (ProofExact proof),
          Lemma ("renComp'_" ++ x) (bkl ++ bm ++ bxi ++ bzeta) ret' (ProofExact proof'))



genUpSubstRen :: Binder -> TId -> GenM Definition
genUpSubstRen y z = do
  (k, bk) <- introScopeVarS "k"
  (l, bl) <- introScopeVar "l" z
  (m, bm) <- introScopeVar "m" z
  (sigma, bsigma) <- genSubstS "sigma" (k, l) z
  (zeta, bzeta) <- genRen z "zeta" (l, m)
  (theta, btheta) <- genSubstS "theta" (k, m) z
  (eq, b_eq) <- genEq z "Eq" (sigma >>> idApp (ren_ z) (sty_terms zeta)) theta
  n <- tfresh "n"
  m <- upSubst z [y] m
  zs <- substOf z
  zeta' <- upSubst z [y] zeta
  pat <- patternSId z y
  let (pms, bpms) = binvparameters y
  let ret = equiv_ (idApp (up_ y z) (pms ++[sigma]) >>> idApp (ren_ z) (sty_terms zeta')) (idApp (up_ y z) (pms ++ [theta]))
  shift <- patternSId z y
  let t n = eqTrans_ (idApp (compRenRen_ z) (pat ++ sty_terms zeta' ++ zipWith (>>>) (sty_terms zeta) pat ++ map (const (TermAbs [BinderName "x"] eq_refl_)) pat ++ [ TermApp sigma [n]]))
                (eqTrans_ (eqSym_ (idApp (compRenRen_ z) (sty_terms zeta ++ pat ++ zipWith (>>>) (sty_terms zeta) pat ++ map (const ((TermAbs [BinderName "x"] eq_refl_))) pat ++ [ TermApp sigma [n]])))
                (ap_ [idApp (ren_ z) pat, TermApp eq [n]]))
  let t' n z' = eqTrans_ (idApp (compRenRen_ z) (pat ++ sty_terms zeta' ++ zipWith (>>>) (sty_terms zeta) pat ++ map (\x -> (TermAbs [BinderName "x"] (if (x == z') then  scons_p_tail' (TermId "x") else eq_refl_))) zs ++ [ TermApp sigma [n]]))
                (eqTrans_ (eqSym_ (idApp (compRenRen_ z) (sty_terms zeta ++ pat ++ zipWith (>>>) (sty_terms zeta) pat ++ map (const ((TermAbs [BinderName "x"] eq_refl_))) pat ++ [ TermApp sigma [n]])))
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
                return $ sigma >>> idApp (ren_ y) (sty_terms zeta')) (zip xs  (sty_terms sigma))
  (eqs, beqs) <- genEqs x "Eq" sigmazeta (sty_terms theta) (\z y s -> do
                                  sigma' <- toVar z sigma
                                  zeta' <- castSubst x z zeta
                                  theta' <- toVar z  theta
                                  return $ idApp (up_subst_ren_ y z) ([TermUnderscore] ++ map (const TermUnderscore) (sty_terms zeta') ++ [TermUnderscore, s])) -- ([sigma'] ++ sty_terms zeta' ++[theta', s]))
  toVarT <- toVar x eqs
  x' <- extend_ x
  b_ext <- isExtension x
  let ret s = TermEq (idApp (ren_ x') (sty_terms zeta ++ [idApp (subst_ x) $ sty_terms sigma  ++ [s]])) (idApp (subst_ x) (sty_terms theta ++ [s]))
      sem _ c xs = if b_ext then idApp "" xs else if (x == x') then (idApp (congr_ c) xs) else eqTrans_ (idApp (retract_ren_ x') [TermUnderscore, idApp c (map (const TermUnderscore) xs)]) (idApp (congr_ (smart_ c)) xs)
      varC n = TermApp toVarT [n]
      varS n = eqTrans_ (idApp (retract_ren_ x') [TermUnderscore, idApp (var_ x) [idApp ("xi" ++ x') [n]] ] ) (varC n)
  traversal x m compSubstRen_ (liftM compSubstRenDeps . genDepRecord)  (\s -> TermApp eq_refl_ [s]) ret (bkl ++ bm ++ bsigma ++ bzeta ++ btheta ++ beqs) [sigma, zeta, theta, eqs]
                  (\n -> if b_ext then varC n else varC n)
                  sem mapComp_
--                  (const $ idApp . congr_) mapComp_



genLemmaSubstCompRen :: TId -> GenM (Lemma, Lemma) --(Lemma, [Lemma])
genLemmaSubstCompRen x = do
  ((k,l), bkl) <- introRenScope ("k", "l") x
  (m, bm) <- introScopeVar "m" x
  (sigma, bsigma) <- genSubst x "sigma" (m,k)
  (zeta,bzeta) <- genRen x "zeta" (k,l)
  xs <- substOf x
  x' <- extend_ x
  let s = "s"
  sigmazeta <- mapM (\(y, sigma) -> do
                zeta' <- castSubst x y zeta
                return $ sigma >>> idApp (ren_ y) (sty_terms zeta')) (zip xs  (sty_terms sigma))
  let ret = TermEq (idApp (ren_ x') (sty_terms zeta ++ [idApp (subst_ x) $ sty_terms sigma  ++ [TermId s]])) (idApp (subst_ x) (sigmazeta ++ [TermId s]))
  let proof = idApp (compSubstRen_ x) (sty_terms sigma ++ sty_terms zeta ++ map (const TermUnderscore) xs ++ map (const (TermAbs [BinderName "n"] eq_refl_)) xs ++ [TermId s])
  let ret' = TermEq ((idApp (subst_ x) (sty_terms sigma)) >>> (idApp (ren_ x') (sty_terms zeta))) (idApp (subst_ x) sigmazeta) -- (sty_terms sigma >>> idApp (subst_ x) (sty_terms tau)))
  let proof' = TermApp fext_ [TermAbs [BinderName "n"] (idApp ("compRen_" ++ x) (sty_terms sigma ++ sty_terms zeta ++ [TermId "n"]))]
  return (Lemma ("compRen_" ++ x) (bkl ++ bm ++ bsigma ++ bzeta ++ [BinderNameType [s] (idApp x (sty_terms m))]) ret (ProofExact proof),
          Lemma ("compRen'_" ++ x) (bkl ++ bm ++ bsigma ++ bzeta) ret' (ProofExact proof'))



genUpSubstSubst :: Binder -> TId -> GenM Definition
genUpSubstSubst y z = do
  (k, bk) <- introScopeVarS "k"
  (l, bl) <- introScopeVar "l" z
  (m, bm) <- introScopeVar "m" z
  (sigma, bsigma) <- genSubstS "sigma" (k, l) z
  (tau, btau) <- genSubst z "tau" (l, m)
  (theta, btheta) <- genSubstS "theta" (k, m) z
  (eq, b_eq) <- genEq z "Eq" (sigma >>> idApp (subst_ z) (sty_terms tau)) theta
  n <- tfresh "n"
  m <- upSubst z [y] m
  l' <- upSubst z [y] l
  zeta' <- upSubst z [y] tau
  pat <- patternSId z y
  let (pms, bpms) = binvparameters y
  let ret = equiv_ (idApp (up_ y z) (pms ++ [sigma]) >>> idApp (subst_ z) (sty_terms zeta')) (idApp (up_ y z) (pms ++ [theta]))
  shift <- patternSId z y
  zs <- substOf z
  pat' <- mapM (\(tau, z') -> do
                      p' <- castSubst z z' (SubstSubst pat)
                      return $ tau >>> (idApp (ren_ z') (sty_terms p')) ) (zip (sty_terms tau) zs)
  let t n = (eqTrans_ (idApp (compRenSubst_ z) (pat ++ sty_terms zeta'  ++ (map (\(z, p) -> p >>> z) (zip (sty_terms zeta') pat)) ++ map (const ((TermAbs [BinderName "x"] eq_refl_))) pat ++ [ TermApp sigma [n]]))
                (eqTrans_ (eqSym_ (idApp (compSubstRen_ z) (sty_terms tau ++ pat ++ pat' ++ map (const ((TermAbs [BinderName "x"] eq_refl_))) pat ++ [ TermApp sigma [n]])))
                (ap_ [(idApp (ren_ z) pat), TermApp eq [n]])))
  let t' n z' = (eqTrans_ (idApp (compRenSubst_ z) (pat ++ sty_terms zeta'  ++ (map (\(z, p) -> p >>> z) (zip (sty_terms zeta') pat)) ++ map (const ((TermAbs [BinderName "x"] eq_refl_))) pat ++ [ TermApp sigma [n]]))
                (eqTrans_ (eqSym_ (idApp (compSubstRen_ z) ( sty_terms tau ++ pat ++ map (const TermUnderscore) pat' ++ map (\x -> ((TermAbs [BinderName "x"] (eqSym_ (if (x == z') then scons_p_tail' (TermId "x") else eq_refl_))))) zs ++ [ TermApp sigma [n]])))
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
  (eq, b_eq) <- genEq z "Eq" (sigma >>> idApp (subst_ z) (sty_terms tau)) theta
  n <- tfresh "n"
  m <- upSubst z [y] m
  l' <- upSubst z [y] l
  zeta' <- upSubst z [y] tau
  pat <- patternSId z y
  let (pms, bpms) = binvparameters y
  let ret = equiv_ (idApp (up_ y z) (pms ++ [sigma]) >>> idApp (subst_ z) (sty_terms zeta')) (idApp (up_ y z) (pms ++ [theta]))
  shift <- patternSIdNoRen z y
  zs <- substOf z
  pat' <- mapM (\(tau, z') -> do
                      p' <- castSubst z z' (SubstSubst pat)
                      return $ tau >>> (idApp (subst_ z') (sty_terms p')) ) (zip (sty_terms tau) zs)
  let t n = (eqTrans_ (idApp (compSubstSubst_ z) (pat ++ sty_terms zeta'  ++ (map (\(z, p) -> p >>> z) (zip (sty_terms zeta') shift)) ++ map (const ((TermAbs [BinderName "x"] eq_refl_))) pat ++ [ TermApp sigma [n]]))
                (eqTrans_ (eqSym_ (idApp (compSubstSubst_ z) (sty_terms tau ++ pat ++ pat' ++ map (const ((TermAbs [BinderName "x"] eq_refl_))) pat ++ [ TermApp sigma [n]])))
                (ap_ [(idApp (subst_ z) pat), TermApp eq [n]])))
  let t' n z' = (eqTrans_ (idApp (compSubstSubst_ z) (pat ++ sty_terms zeta'  ++ (map (\(z, p) -> p >>> z) (zip (sty_terms zeta') shift)) ++ map (const ((TermAbs [BinderName "x"] eq_refl_))) pat ++ [ TermApp sigma [n]]))
                (eqTrans_ (eqSym_ (idApp (compSubstSubst_ z) ( sty_terms tau ++ pat ++ map (const TermUnderscore) pat' ++ map (\x -> ((TermAbs [BinderName "x"] (eqSym_ (if (x == z') then scons_p_tail' (TermId "x") else eq_refl_))))) zs ++ [ TermApp sigma [n]])))
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
                return $ sigma >>> idApp (subst_ y) (sty_terms tau')) (zip xs  (sty_terms sigma))
  (eqs, beqs) <- genEqs x "Eq" sigmatau (sty_terms theta) (\z y s -> do
                                  sigma' <- toVar z sigma
                                  tau' <- castSubst x z tau
                                  theta' <- toVar z  theta
                                  return $ idApp (up_subst_subst_ y z) ([TermUnderscore] ++ map (const TermUnderscore) (sty_terms tau') ++ [TermUnderscore, s]))  -- ([sigma'] ++ sty_terms tau' ++[theta', s]))
  toVarT <- toVar x eqs
  x' <- extend_ x
  b_ext <- isExtension x
  let ret s = TermEq (idApp (subst_ x') (sty_terms tau ++ [idApp (subst_ x) $ sty_terms sigma  ++ [s]])) (idApp (subst_ x) (sty_terms theta ++ [s]))
      sem _ c xs = if b_ext then idApp "" xs else if (x == x') then idApp (congr_ c) xs else eqTrans_ (idApp (retract_subst_ x') [TermUnderscore, idApp c (map (const TermUnderscore) xs)]) (idApp (congr_ (smart_ c)) xs)
      varC n = TermApp toVarT [n]
      varS n = eqTrans_ (idApp (retract_subst_ x') [TermUnderscore, idApp (var_ x) [idApp ("sigma" ++ x') [n]] ] ) (varC n)
  traversal x m compSubstSubst_  (liftM compSubstSubstDeps . genDepRecord) (\s -> TermApp eq_refl_ [s]) ret (bkl ++ bm ++ bsigma ++ btau ++ btheta ++ beqs) [sigma, tau, theta, eqs]
                  (\n -> if b_ext then varC n else varC n) sem mapComp_

genLemmaSubstComp :: TId -> GenM (Lemma, Lemma) --(Lemma, [Lemma])
genLemmaSubstComp x = do
  ((k,l), bkl) <- introRenScope ("k", "l") x
  (m, bm) <- introScopeVar "m" x
  (sigma, bsigma) <- genSubst x "sigma" (m,k)
  (tau,btau) <- genSubst x "tau" (k,l)
  xs <- substOf x
  x' <- extend_ x
  let s = "s"
  sigmatau <- mapM (\(y, sigma) -> do
                tau' <- castSubst x y tau
                return $ sigma >>> idApp (subst_ y) (sty_terms tau')) (zip xs  (sty_terms sigma))
  let ret = TermEq (idApp (subst_ x') (sty_terms tau ++ [idApp (subst_ x) $ sty_terms sigma  ++ [TermId s]])) (idApp (subst_ x) (sigmatau ++ [TermId s]))
  let proof = idApp (compSubstSubst_ x) (sty_terms sigma ++ sty_terms tau ++ map (const TermUnderscore) xs ++ map (const (TermAbs [BinderName "n"] eq_refl_)) xs ++ [TermId s])
  let ret' = TermEq ((idApp (subst_ x) (sty_terms sigma)) >>> (idApp (subst_ x') (sty_terms tau))) (idApp (subst_ x) sigmatau) -- (sty_terms sigma >>> idApp (subst_ x) (sty_terms tau)))
  let proof' = TermApp fext_ [TermAbs [BinderName "n"] (idApp ("compComp_" ++ x) (sty_terms sigma ++ sty_terms tau ++ [TermId "n"]))]
  return (Lemma ("compComp_" ++ x) (bkl ++ bm ++ bsigma ++ btau ++ [BinderNameType [s] (idApp x (sty_terms m))]) ret (ProofExact proof),
          Lemma ("compComp'_" ++ x) (bkl ++ bm ++ bsigma ++ btau) ret' (ProofExact proof'))


genUpExtRen :: Binder -> TId -> GenM Definition
genUpExtRen y z = do
  (m, bm) <- introScopeVarS "m"
  (n, bn) <- introScopeVarS "n"
  (xi, bxi) <- genRenS "xi" (m, n)
  (zeta,bzeta) <- genRenS "zeta" (m,n)
  (eq, b_eq) <- genEq z "Eq" xi zeta
  let (pms,bpms) = binvparameters y
  let ret = equiv_ (idApp (upRen_ y z) (pms ++ [xi])) (idApp (upRen_ y z) (pms ++[zeta]))
  n <- tfresh "n"
  let t n = TermApp eq [n]
  let s = matchFin_ (TermId n) (\n -> ap_ [shift_, t n]) eq_refl_
  let u = case y of Single z' -> if z == z' then s else t (TermId n)
                    BinderList p z' -> if z == z' then scons_p_congr_ (TermAbs [BinderName "n"] (ap_ [idApp "shift_p" [TermId p], t (TermId "n")])) (TermAbs [BinderName "n"] eq_refl_) else t (TermId n)
  return $ Definition (upExtRen_ y z) (bpms ++ bm ++ bn ++ bxi ++ bzeta ++ b_eq) (Just ret) (TermAbs [BinderName "n"] u)

scons_p_congr_ :: Term -> Term -> Term
scons_p_congr_ s t = idApp "scons_p_congr" [t,s]


genExtRen :: TId -> GenM FixpointBody
genExtRen x = do
  ((m,n), bmn) <- introRenScope ("m", "n") x
  (xi, bxi) <- genRen x "xi" (m,n)
  (zeta, bzeta) <- genRen x "zeta" (m,n)
  xs <- substOf x
  (eqs, beqs) <- genEqs x "Eq" (sty_terms xi) (sty_terms zeta) (\x y s -> return $ idApp (upExtRen_ y x) [TermUnderscore, TermUnderscore, s]) -- TODO: Shouldn't this want SubsttTy instead of Terms?
  x' <- extend_ x
  b_ext <- isExtension x
  let ret s = TermEq (idApp (ren_ x) (sty_terms xi ++ [s])) (idApp (ren_ x) (sty_terms zeta ++ [s]))
  toVarT <- toVar x eqs
  traversal x m extRen_ (liftM extRenDeps . genDepRecord) (\s -> TermApp eq_refl_ [s]) ret (bmn ++ bxi ++ bzeta ++ beqs) [xi, zeta, eqs]
                  (\z -> ap_ [var x' n, TermApp toVarT [z]])
                  (\_ c cs -> idApp  (if b_ext then "" else congr_ (if x == x' then c else smart_ c)) cs)
                  mapExt_


genUpExt :: Binder -> TId -> GenM Definition
genUpExt y z = do
  (m, bm) <- introScopeVarS "m"
  (n, bn) <- introScopeVar "n" z
  (sigma, bsigma) <- genSubstS "sigma" (m, n) z
  (tau,btau) <- genSubstS "tau" (m,n) z
  (eq, b_eq) <- genEq z "Eq" sigma tau
  let (pms, bpms) = binvparameters y
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
  (eqs, beqs) <- genEqs x "Eq" (sty_terms sigma) (sty_terms tau) (\x y s -> return$  idApp (upExt_ y x) [TermUnderscore, TermUnderscore, s]) -- TODO: Shouldn't this want SubsttTy instead of Terms?
  let ret s = TermEq (idApp (subst_ x) (sty_terms sigma ++ [s])) (idApp (subst_ x) (sty_terms tau ++ [s]))
  toVarT <- toVar x eqs
  x' <- extend_ x
  b_ext <- isExtension x
  traversal x m ext_ (liftM extDeps . genDepRecord) (\s -> TermApp eq_refl_ [s]) ret (bmn ++ bsigma ++ btau ++ beqs) [sigma, tau, eqs]
                  (\z ->  TermApp toVarT [z])   -- TODO: I didn't need the renaming case for Up. Dive into that.
                  (\_ c cs -> idApp (if b_ext then "" else congr_ (if x == x' then c else smart_ c)) cs)
                  mapExt_


genUpRinstInst :: Binder -> TId -> GenM Definition
genUpRinstInst b z = do
  (m, bm) <- introScopeVarS "m"
  (n, bn) <- introScopeVar "n" z
  n_var <- toVar z n
  (xi, bxi) <- genRenS "xi" (m, n_var)
  (sigma, bsigma) <- genSubstS "sigma" (m, n) z
  (eq, b_eq) <- genEq z "Eq" (xi >>> var z n) sigma
  n' <- upSubst z [b] n
  let (pms, bpms) = binvparameters b
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
    return$  xi >>> var y n') (zip xs (sty_terms xi))
  (eqs, beqs) <- genEqs x "Eq" xis' (sty_terms sigma) (\x y s -> return $  idApp (up_rinstInst_ y x) [TermUnderscore, TermUnderscore, s]) -- TODO: Make this last part general: Allow a function whihc takes SubstTy arguments and then automatically gives right terms.
  x' <- extend_ x
  b_ext <- isExtension x
  let ret s = TermEq (idApp (ren_ x) (sty_terms xi ++ [s])) (idApp (subst_ x) (sty_terms sigma ++ [s]))
  toVarT <- toVar x eqs
  traversal x m rinstInst_ (liftM rinstInstDeps . genDepRecord) (\s -> TermApp eq_refl_ [s]) ret (bmn ++ bxi ++ bsigma ++ beqs) [xi, sigma, eqs]
                  (\n -> TermApp toVarT [n])
                  (\_ c xs -> if b_ext then idApp "" xs else if x == x' then idApp (congr_ c) xs else idApp (congr_ (smart_ c)) xs)
                  mapExt_


genLemmaInstId :: TId -> GenM Lemma
genLemmaInstId x = do
  (m, bm) <- introScopeVar "m" x
  xs <- substOf x
  vars <- mapM (\y -> liftM2 idApp (return $ var_ y) (liftM sty_terms (castSubst x y m))) xs -- TODO: FUnction for vars.
  x' <- extend_ x
  let mid = if x == x' then TermConst (Id) else TermId inj_
      ret = TermEq (idApp (subst_ x) vars) mid
  let proof = TermApp fext_ [TermAbs [BinderName "x"] (idApp (idSubst_ x) ( vars ++ (map (const (TermAbs [BinderName "n"] eq_refl_)) xs) ++ [TermApp (TermConst Id) [TermId "x"]]))] -- (idApp x (sty_terms m))
  return $ Lemma ("instId_" ++ x) bm ret (ProofExact proof)

genLemmaRinstId :: TId -> GenM Lemma
genLemmaRinstId x = do
  (m, bm) <- introScopeVar "m" x
  xs <- substOf x
  vars <- mapM (\y -> liftM2 idApp (return $ var_ y) (liftM sty_terms (castSubst x y m))) xs
  x' <- extend_ x
  let mid = if x == x' then (TermConst (Id)) else TermId inj_
      ret = TermEq (idApp ("@" ++ ren_ x) (sty_terms m ++ sty_terms m  ++ map (const (TermConst Id)) xs)) mid
  let proof = eqTrans_ (idApp ("rinstInst_" ++ x) (map (const (id_ TermUnderscore)) xs)) (TermId ("instId_" ++ x))
  return $ Lemma ("rinstId_" ++ x) bm ret (ProofExact proof)

genLemmaVarL :: TId -> GenM Lemma
genLemmaVarL x = do
  ((m,n), bmn) <- introRenScope ("m", "n") x
  (sigma,bsigma) <- genSubst x "sigma" (m,n)
  sigma' <- toVar x sigma
  let ret = TermEq ((var x m) >>> (idApp (subst_ x) (sty_terms sigma))) sigma'
  let proof = TermApp fext_ [TermAbs [BinderName "x"] eq_refl_]
  return $ Lemma ("varL_" ++ x) (bmn ++ bsigma) ret (ProofExact proof)

genLemmaVarLRen :: TId -> GenM Lemma
genLemmaVarLRen x = do
  ((m,n), bmn) <- introRenScope ("m", "n") x
  (xi,bxi) <- genRen x "xi" (m,n)
  xi' <- (toVar x xi)
  x' <- extend_ x
  let ret = TermEq ((var x m) >>> (idApp (ren_ x) (sty_terms xi))) (xi' >>> (var x' n))
  let proof = TermApp fext_ [TermAbs [BinderName "x"] eq_refl_]
  return $ Lemma ("varLRen_" ++ x) (bmn ++ bxi) ret (ProofExact proof)

genLemmaRenSubst :: TId -> GenM Lemma
genLemmaRenSubst x = do
  ((m,n), bmn) <- introRenScope ("m", "n") x
  (xi, bxi) <- genRen x "xi" (m,n)
  xs <- substOf x
  xis' <- mapM (\(y, xi) -> do
    n' <- castSubst x y n
    return$  xi >>> var y n') (zip xs (sty_terms xi))
  let ret = TermEq (idApp (ren_ x) (sty_terms xi)) (idApp (subst_ x) xis')
  let proof = TermApp fext_ [TermAbs [BinderName "x"] $ idApp (rinstInst_ x) (sty_terms xi ++ map (const TermUnderscore) xs ++ (map (const (TermAbs [BinderName "n"] eq_refl_)) xs) ++ [TermId "x"])]
  return (Lemma (rinstInstFun_ x) (bmn ++ bxi) ret (ProofExact proof))

ifM :: Monad m => Bool -> m [a] -> m [a]
ifM b xs = do
  xs' <- xs
  return $ if b then xs' else []


-- Generation of modular boilerplat++ map SentenceDefinition inFcte + binder boilerplate.
genCodeT :: [TId] -> [TId] -> [(Binder,TId)] -> GenM [Sentence]
genCodeT xs dps upList' = do
  if null xs then throwError "Error: In genCodeT the list of features is empty." else return ()
  depSentences <- if (null dps) then return [] else genCodeT (nub dps) [] upList'
  upList <- return $ if null dps then upList' else []
  x_open <- isOpen (head xs)
  deps <- hypos x_open depSentences
  depSmarts <- mapM genSmarts (if (null dps) then [] else xs)
  extensions <- genE xs
  prevExt <- genPrec xs
  retracts <- genRetracts extensions -- TODO: Change.
  retractProofs <- genRetractProofs prevExt
  varSorts <- filterM isOpen xs -- Sorts which have variables
  hasbinders <- fmap (not. null) (substOf (head xs))
  substSorts <- filterM (const (return True)) xs
  ys <- filterM definable xs
  types <- mapM genBody ys
  isRen <- hasRenamings (head xs)
  r <- recursive xs
  congruences <- mapM genCongruences xs
  upRen <- ifM isRen $ mapM (uncurry genUpRenS) upList
  renamings <- ifM isRen $ liftM (\x -> [SentenceFixpoint x]) $ genRenamings substSorts
  retractsRenamings <- mapM genRetractRen substSorts
  ups <- ifM isRen $ mapM (uncurry genUpS) upList
  upsNoRen <- ifM (not isRen) $ mapM (uncurry genUpS) upList
  substitutions <- genSubstitutions substSorts
  retractssubstitutions <- mapM genRetractSubst substSorts
  upId <- mapM (uncurry genUpId) upList
  idlemmas <- mapM genIdL substSorts
  extUpRen <- ifM isRen $ mapM (uncurry genUpExtRen) upList
  extRen <- ifM isRen $ liftM (\x -> [SentenceFixpoint $ Fixpoint r x]) $ mapM genExtRen substSorts
  extUp <- mapM (uncurry genUpExt) upList
  ext <- mapM genExt substSorts
  upRenRen <- ifM isRen $ mapM (uncurry genUpRenRen) upList
  compRenRen <- ifM isRen $ liftM (\x -> [SentenceFixpoint $ Fixpoint r x]) $ mapM genCompRenRen substSorts
  upRenSubst <- ifM isRen $ mapM (uncurry genUpRenSubst) upList
  compRenSubst <- ifM isRen $ liftM (\x -> [SentenceFixpoint $ Fixpoint r x]) $ mapM genCompRenSubst substSorts
  upSubstRen <- ifM isRen $ mapM (uncurry genUpSubstRen) upList
  compSubstRen <- ifM isRen $ liftM (\x -> [SentenceFixpoint $ Fixpoint r x]) $ mapM genCompSubstRen substSorts
  upSubstSubst <- ifM isRen $ mapM (uncurry genUpSubstSubst) upList
  compSubstSubst <- liftM (\x -> [SentenceFixpoint $ Fixpoint r x]) $ mapM genCompSubstSubst substSorts
  upSubstSubstNoRen <- ifM (not isRen) $ mapM (uncurry genUpSubstSubstNoRen) upList
  upRinstInst <- ifM isRen $ mapM (uncurry genUpRinstInst) upList
  rinstInst <- ifM isRen $ liftM (\x -> [SentenceFixpoint $ Fixpoint r x]) $ mapM genRinstInst substSorts
  extensions <- genE xs
  inFcts <- genIns extensions
  extSorts <- filterM isExtension xs
  lemmaRinstId <- ifM isRen $  mapM genLemmaRinstId substSorts
  lemmaInstId <- mapM genLemmaInstId substSorts
  lemmaVarL <- mapM genLemmaVarL varSorts
  lemmaVarLRen <- ifM isRen $ mapM genLemmaVarLRen varSorts
  lemmaRenSubst <- ifM isRen $ mapM genLemmaRenSubst substSorts
  lemmaSubstRenRen <- ifM isRen $ mapM genLemmaRenRenComp substSorts
  lemmaSubstCompRen <- ifM isRen $ mapM genLemmaSubstCompRen substSorts
  lemmaSubstRenComp <- ifM isRen $ mapM genLemmaSubstRenComp substSorts
  lemmaSubstComp <- mapM genLemmaSubstComp substSorts
  inProofs <- mapM genInProof extSorts
  isf <- isFeature (head xs)
  let (l1, l2) = unzip lemmaSubstComp
  let (l3, l4) = if isRen then unzip lemmaSubstCompRen else ([], [])
  let (l5, l6) = if isRen then unzip lemmaSubstRenComp else ([], [])
  let (l7, l8) = if isRen then unzip lemmaSubstRenRen else ([], [])
  return $ nonEmptySection (concat xs) (deps ++ [SentenceInductive (Inductive types) | (not . null) types] ++ retracts ++  (concat depSmarts) ++ map SentenceLemma    (concat congruences) -- FEATURE: Different intermediate values. --}
          ++ retractProofs
          ++ (if hasbinders then map SentenceDefinition upRen ++ renamings ++ concat retractsRenamings
          ++ map SentenceDefinition ups ++ [SentenceFixpoint substitutions] ++ map SentenceDefinition upsNoRen ++ concat retractssubstitutions
          ++ map SentenceDefinition upId ++ [SentenceFixpoint $ Fixpoint r idlemmas]
          ++ map SentenceDefinition extUpRen ++ extRen
          ++ map SentenceDefinition extUp ++ [SentenceFixpoint $ Fixpoint r ext]
         ++ map SentenceDefinition upRenRen ++ compRenRen
         ++ map SentenceDefinition upRenSubst ++ compRenSubst
          ++ map SentenceDefinition upSubstRen ++ compSubstRen
          ++ map SentenceDefinition upSubstSubst  ++ compSubstSubst ++ map SentenceDefinition upSubstSubstNoRen
          ++ map SentenceDefinition upRinstInst ++ rinstInst
          ++ map SentenceLemma (lemmaRenSubst ++  lemmaInstId ++ lemmaRinstId ++  lemmaVarL  ++ lemmaVarLRen ++l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7 ++ l8 ) ++ map SentenceDefinition inFcts -- ++ [SentenceFixpoint (Fixpoint True inProofs) | not (null inProofs) && not isf]
          else []))


genE :: [TId] -> GenM [(TId, TId)]
genE xs = liftM concat (mapM (\x -> do
  y <- extend_ x
  return $ if (x == y) then [] else [(x,y)]
  ) xs)

-- Generation of only the boilerplate for modular syntax.
genModularSyntax :: Bool -> [TId] -> [TId] -> [(Binder,TId)] -> GenM [Sentence]
genModularSyntax b xs dps upList = do
  depSentences <- if (null dps) then return [] else genModularSyntax False (nub dps) [] []
  x_open <- isOpen (head xs)
  deps <- hypos x_open depSentences
  depSmarts <- mapM genSmarts (if (null dps) then [] else xs)
  extensions <- genE xs
  prevExt <- genPrec xs
  retracts <- genRetracts extensions -- TODO: Change.
  retractProofs <- genRetractProofs prevExt
  inFcts <- genIns extensions
  extSorts <- filterM isExtension xs
  inProofs <- mapM genInProof extSorts
  ys <- filterM definable xs
  types <- mapM genBody ys
  congruences <- mapM genCongruences xs
  return $ nonEmptySection (concat xs) (deps ++ [SentenceInductive (Inductive types) | (not . null) types] ++ map SentenceDefinition inFcts ++ [SentenceFixpoint (Fixpoint True inProofs) | not (null inProofs) && b]++
   retracts ++  (concat depSmarts) ++ map SentenceLemma (concat congruences)  ++ retractProofs)
