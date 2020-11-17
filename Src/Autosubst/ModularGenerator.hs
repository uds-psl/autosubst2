{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Autosubst.ModularGenerator where

import           Autosubst.GenM
import           Autosubst.Names
import           Autosubst.Syntax
import           Autosubst.Tactics
import           Autosubst.Types
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Lazy
import           Data.List                as L



-- Depending on the arguments, create a constructor or its smart constructor
modConstructor :: Bool -> Bool -> TId -> TId
modConstructor True _ _      = ""
modConstructor False True c  = c
modConstructor False False c = smart_ c

-- 1.) Code for turning definitions into hypotheses

-- Assuming definitions.
hypoDef :: Definition -> [Sentence]
hypoDef (Definition name bs (Just t) _) = [SentenceVariable name (TermForall bs t)]
hypoDef _ = []

-- Assuming fixpoints.
hypoFix :: Bool -> FixpointBody -> [Sentence]
hypoFix False (FixpointBody name bs t _) = [SentenceVariable name (TermForall bs t)]
hypoFix True (FixpointBody ('r' : 'e' : 'n' : '_' : xs) bs t _) = [SentenceVariable ("ren_" ++ xs) (TermForall bs t)]
hypoFix True (FixpointBody ('s' : 'u' : 'b' : 's' : 't' : '_' : xs) bs t _) = [SentenceVariable ("subst_" ++ xs) (TermForall bs t)]
hypoFix _ _ = []

-- Assuming lemmas. 
hypoLemma :: Lemma -> Sentence
hypoLemma (Lemma name bs t _) = SentenceVariable name (TermForall bs t)

-- Assuming indcutive types.
hypoInductive :: [TId] -> Bool -> InductiveBody -> GenM [Sentence]
hypoInductive z open (InductiveBody x _ _ _) = do
  b <- isOpenComponent x
  (n,bs) <- introScopeVar "n" x
  s <- finVar x (substTerms n)
  z' <- mapM extend_ z
  return $ [SentenceVariable x (TermSort Type)] ++ [SentenceVariable (var_ x) ([s] ==> idSubstApp x n) | b, not open || not (elem x z') ]

-- Assuming a sentence.
hypo :: [TId] -> Bool -> Sentence -> GenM [Sentence]
hypo _ b (SentenceDefinition d)             = return $ if b then [] else hypoDef d
hypo x b (SentenceInductive (Inductive bs)) = liftM concat $ mapM (hypoInductive x b) bs
hypo _ b (SentenceFixpoint (Fixpoint _ bs)) = return$ concatMap (hypoFix b) bs
hypo z b (SentenceSection x xs)             = liftM concat $ mapM (hypo z b) xs
hypo _ b _                                  = return $ []

-- Assuming lists of sentences.
hypos :: [TId] ->  Bool -> [Sentence] -> GenM [Sentence]
hypos x b xs = liftM concat $ mapM  (hypo x b) xs

-- 2.) Generation of Smart Constructors 

-- Generation of Modular Boilerplate
genSmartArg :: TId -> SubstTy -> [Binder] -> Argument  -> GenM Term
genSmartArg x n bs (Atom y)  = liftM2 idApp (addFeatureArgs y) (fmap substTerms $ castUpSubst x bs y n)
genSmartArg x n bs (FunApp f p xs) = do
  xs' <- mapM (genSmartArg x n bs) xs
  return $ idApp (funname_ (f ++ p)) xs'

-- Generation of smart constructors.
genSmart :: TId ->  Constructor -> GenM Definition
genSmart x (Constructor pms cname pos) = do
    x' <- return x -- getExtension x, TODO: What do I want here?
    (m, bm) <- introScopeVar "m" x
    let s = genPatternNames "s" pos
    let bs s = mapM (\(y, Position binders arg) -> do
                                                  arg_type <- genSmartArg x m binders arg
                                                  return $ BinderNameType [y] arg_type
                                                  ) (zip s pos)
    bes <- bs s
    return $ Definition (smart_ cname) (bm ++ bes) Nothing (idApp inj_ [idApp cname (map TermId s)])

genSmartVariableConstructor :: TId -> GenM [Sentence]
genSmartVariableConstructor x = do
  b <- isOpen x
  (m, bm) <- introScopeVar "m" x
  x' <- extend_ x
  return $  if b then [SentenceDefinition $ Definition (var_ x') (bm ++ [BinderName "x"]) Nothing (idApp inj_ [idApp (var_ x) [TermId "x"]])] else [] 

genSmarts :: TId -> GenM [Sentence]
genSmarts x = do
  cs <- constructors x
  dfs <- mapM (genSmart x) cs
  dfv <- genSmartVariableConstructor x
  return $ dfv ++ map SentenceDefinition dfs

-- 3.) Generation of Retracts 

-- Generation of retracts assumption.
-- TODO: Generalize retract name.
genRetractAssumption :: TId -> TId -> GenM Sentence
genRetractAssumption x y = do
  let s = idApp retract_ [TermId x, TermId y]
  return $ SentenceVariable (retractId_ x) s

genRetractAssumptions :: [(TId, TId)] -> GenM [Sentence]
genRetractAssumptions xs = do
  retr <- mapM (\(x,y) -> genRetractAssumption x y) xs
  return $ retr

-- Generation of retract proof
genRetractProof :: TId -> TId -> GenM Sentence
genRetractProof x y = do
  x' <- addFeatureArgs x
  b' <- isOpen y
  cs <- constructors y
  let b = b' || length cs > 1
      ret = idApp retract_ [TermId ("(" ++ x' ++ ")"), TermId y]
      rdef = TermAbs [BinderName "x"] (TermMatch (MatchItem (TermId "x")) Nothing ([Equation (PatternConstructor (idApp (in'_ x "") [TermId "s"]) []) (TermApp dsome_ [TermId "s"]) ] ++ [Equation PatternUnderscore dnone_ | b]))
      p1 = TermAbs [BinderName "s"] eq_refl_
      p2 = TermAbs [BinderName "s", BinderName "t"] (TermMatch (MatchItem (TermId "t")) Nothing ([Equation (PatternConstructor (idApp (in'_ x "") [TermId "t'"]) []) (TermAbs [BinderName "H"] (idApp (congr_ (in'_ x "")) [eqSym_ (idApp "Some_inj" [TermId "H"])]))] ++ [Equation PatternUnderscore some_none_ | b]))
      tm = idApp buildRetract_ [TermId (in'_ x ""), rdef, p1, p2]
  return $ SentenceInstance [] (retrName x y) ret tm

genRetracts :: [(TId, TId)] -> GenM [Sentence]
genRetracts xs = do
  retr <- mapM (\(x,y) -> genRetractProof x y) xs
  ass <- mapM extend_ [x | (x, y) <- xs]
  ass' <- liftM nub (filterM isOpenComponent ass)
  return $ retr ++ [SentenceCommand (Arguments (var_ x) [TermUnderscore, TermUnderscore]) | x <- ass']

-- Generation of renaming retracts
genRetractRen :: TId -> GenM [Sentence]
genRetractRen x = do
  ((m,n),bs) <- introRenScope ("m", "n") x
  (xi,bxi) <- genRen x "xi" (m,n)
  toVarT <- toVar x xi
  x' <- extend_ x
  return $ [SentenceVariable (retract_ren_ x') (TermForall (bs ++ bxi ++ [BinderName "s"]) (TermEq (idApp (ren_ x') (substTerms xi ++ [idApp inj_ [TermId "s"]])) (idApp (ren_ x) (substTerms xi ++ [TermId "s"]))))  | x' /= x]

-- Generation of substitution retracts
genRetractSubst :: TId -> GenM [Sentence]
genRetractSubst x = do
  ((m,n),bs) <- introRenScope ("m", "n") x
  (sigma,bsigma) <- genSubst x "sigma" (m,n)
  toVarT <- toVar x sigma
  x' <- extend_ x
  return $ [SentenceVariable (retract_subst_ x') (TermForall (bs ++ bsigma ++ [BinderName "s"]) (TermEq (idApp (subst_ x') (substTerms sigma ++ [idApp inj_ [TermId "s"]])) (idApp (subst_ x) (substTerms sigma ++ [TermId "s"]))))  | x' /= x]


-- 4.) Generation of In definition and corresponding proofs

-- Generation of In Definition
genIn :: TId -> TId -> GenM Definition
genIn x y = do
  cs <- constructors y
  b <- isOpen y
  let b1 = BinderNameType ["s"] (TermId x)
      b2 = BinderNameType ["t"] (TermId y)
      args = map (\(Constructor pms c ps) -> map (\(Position bs a) -> a) ps) cs
      ps = map (\(Constructor pms c ps) -> (c, (genPatternNames "t" ps)) ) cs
      body = TermMatch (MatchItem (TermId "t")) Nothing ([Equation PatternUnderscore (false_)| b] ++ zipWith equation ps args)
  return $ Definition (isIn_ x y) [b1,b2] (Just (TermSort Prop)) body
      where equation (c,pat) ts = Equation (PatternConstructor (idApp c (map TermId pat)) []) (ors (eqs (f ts pat)))
            f ts xs = map snd (filter (\(z, _) -> z == Atom x) (zip ts xs))
            eqs xs = map (\x -> TermEq (TermId "s") (TermId x)) xs

genIns :: [(TId, TId)] -> GenM [Definition]
genIns xs = mapM (\(x,y) -> genIn y x) xs

-- Generation of induction lemma for In predicate. 
-- Attention: Not compatible with scoped syntax and parameters so far.
genInProof :: TId -> GenM FixpointBody
genInProof x = do
  cs <- constructors x -- The in-things.
  let args = map (\(Constructor pms c ps) -> map (\(Position bs a) -> a) ps) cs -- List of below arguments. TODO: Handle parameters
      p = BinderNameType ["P"] (TermFunction (TermId x) (TermSort Prop)) -- main predicate
      ihbs = map (\(Constructor pms c [Position _ y']) -> case y' of Atom y -> BinderNameType ["IH_" ++ c] -- TODO: Take care of parameters.
                                                                              (TermForall [BinderName "t"]
                                                                              (TermFunction (TermForall [BinderName "x"]
                                                                              (TermFunction (idApp (isIn_ x y) [TermUnderscore, TermId "x", TermId "t"])
                                                                              (idApp "P" [TermId "x"])))
                                                                              (idApp "P" [idApp c [TermId "t"]])))
                                                                     _ -> BinderScopeNameType [] (TermId "Error.")) cs 
      ihs = binderTerms ihbs
      e = BinderNameType ["s"] (TermId x)
      bs = [p] ++ ihbs ++ [e]
      ret = idApp "P" [TermId "s"]
      solve t eq = idApp "eq_ind_r" [TermUnderscore, idApp (inProof_ x) (TermUnderscore : ihs ++ [t]), eq]
      hs ps = orPattern (length $ filter (\(Position _ a) -> a == Atom x) ps) (TermId "H") -- TODO: Handle other case than Atom
      term c css ps (Atom y) = TermAbs [BinderName "t", BinderNameType ["H"] (idApp (isIn_ x y) [TermUnderscore, TermUnderscore, idApp c (map (\x -> TermUnderscore) css ++ map (\x -> TermUnderscore) ps)])] (TermMatch
        (MatchItem (TermId "H")) Nothing (map (\x -> Equation (PatternConstructor x []) (solve TermUnderscore (TermId "H"))) (hs (ps))))
      term _ _ _ _ = TermId "Error"
  ccs <- mapM (\y -> constructors y) (concat [[x]]) -- TODO: Should be args instead of [x] for more complicated types
  pat <- mapM (\(Constructor pms c [Position bs z]) -> do -- TODO: Take care of parameters.
                          let ps = [Position bs z]
                          css <- liftM concat (mapM (\(Position bs a) -> constructors x) ps) -- x should be a
                          zs <- realDeps x 
                          return $ map (\(Constructor pms c' ps) -> (c, c', zs, ps, [idApp c' (map (\x -> TermUnderscore) zs ++ (map TermId  (genPatternNames "s" ps)))], z)) css -- TODO: Take care of parameters.
                    ) cs
  let equations (c, c', css, ps, [p], y) = Equation (PatternConstructor (idApp c [p]) []) (getTerm ("IH_" ++ c) (term c' css ps y))
      body = TermMatch (MatchItem (TermId "s")) Nothing (map equations (concat pat)) -- equations
  return $ FixpointBody (inProof_ x) bs ret body
    where getTerm ih eq = idApp ih [TermUnderscore, eq]


-- 5.) Dependency Record

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

genDepRecord :: TId -> GenM DepRecord
genDepRecord x = do
  b <- isFeature x
  subsorts <- realDeps x
  dps <- arguments x
  substsorts <- if b then filterM isOpenComponent subsorts else return [] -- TODO: This is not correct.
  substargsorts <- if b then filterM isOpenComponent dps else return []
  varsorts <- filterM isOpenComponent (if b then dps else [])
  mups <- directUps x
  let dups :: [(Binder, TId)]
      dups = if b then mups else [] -- [(p,y) | y <- dps, (p,y) `elem` mups]
      types = map TermId  [z | z <- subsorts, b] -- All sub-appearing sorts with dependencies.
      uprens = map (\(p,q) -> TermId (upRen_ p q)) dups -- All scope changes (x,y)
      rens = map (\x -> TermId (ren_ x)) substargsorts -- Renamings for all sub-appearing sorts.
      mrens = map (\x -> TermId (ren_ x)) substsorts -- Renamings for all sub-appearing sorts, including the sort itself
      ups = map (\(p,q) -> TermId (up_ p q)) dups
      substs = map (\x -> TermId (subst_ x)) substargsorts
      msubsts = map (\x -> TermId (subst_ x)) substsorts
      instances = map (const TermUnderscore) substsorts -- Instances for all sub-appearing sorts, including the sort itself
      minstances = map (const TermUnderscore) substargsorts -- Instances for all sub-appearing sorts in arguments
      vars = map (\x -> TermId (var_ x)) varsorts -- All subsorts with variables.
      upids = map (\(p,q) -> TermId (upId_ p q)) dups
      idSubsts = map (\x -> TermId (idSubst_ x)) substargsorts
      upRenExts = map (\(p,q) -> TermId (upExtRen_ p q)) dups
      extRens = map (\x -> TermId (extRen_ x)) substargsorts
      upexts = map (\(p,q) -> TermId (upExt_ p q)) dups
      upRinstInsts = map (\(p,q) -> TermId (up_rinstInst_ p q)) dups
      exsts = map (\x -> TermId (ext_ x)) substargsorts
      upRenRens = map (\(p,q) -> TermId (up_ren_renName_ p q)) dups
      upRenSubsts = map (\(p,q) -> TermId (up_ren_subst_ p q)) dups
      upSubstRens = map (\(p,q) -> TermId (up_subst_ren_ p q)) dups
      upSubstSubsts = map (\(p,q) -> TermId (up_subst_subst_ p q)) dups
      rinstInsts = map (\x -> TermId (rinstInst_ x)) substargsorts
      compRenRens = map (\x -> TermId (compRenRen_ x)) substargsorts
      compRenSubsts = map (\x -> TermId (compRenSubst_ x)) substargsorts
      compSubstRens = map (\x -> TermId (compSubstRen_ x)) substargsorts
      compSubstSubsts = map (\x -> TermId (compSubstSubst_ x)) substargsorts
      renRetracts = map (\x -> TermAbs [BinderName "x", BinderName "y"] eq_refl_) substargsorts
      mrenRetracts = map (\x -> TermAbs [BinderName "x", BinderName "y"] eq_refl_) substsorts
      substRetracts = map (\x -> TermAbs [BinderName "x", BinderName "y"] eq_refl_) substargsorts
      msubstRetracts = map (\x -> TermAbs [BinderName "x", BinderName "y"] eq_refl_) substsorts
      renDeps = types ++ uprens ++ rens ++ instances
      substDeps = types ++ ups ++ substs ++ minstances
      idSubstDeps = types ++ vars ++ ups ++ substs ++ upids ++ idSubsts ++ instances
      extRenDeps = types ++ uprens ++ rens ++ upRenExts ++ extRens ++ instances
      extDeps = types ++ ups ++ substs ++ upexts ++ exsts ++ minstances
      rinstInstDeps = types ++ vars ++ uprens ++ rens ++ ups ++ substs ++ upRinstInsts ++ rinstInsts ++  instances
      compRenRenDeps = types ++ uprens ++ mrens ++ upRenRens ++ compRenRens ++ instances ++ mrenRetracts
      compRenSubstDeps = types ++ uprens ++ rens ++ ups ++ msubsts ++ upRenSubsts ++ compRenSubsts ++ instances ++ msubstRetracts
      compSubstRenDeps = types ++ uprens ++ mrens ++ ups ++ substs ++ upSubstRens ++ compSubstRens ++ minstances ++ renRetracts
      compSubstSubstDeps = types ++ ups ++ msubsts ++ upSubstSubsts ++ compSubstSubsts ++ minstances ++ substRetracts
  return $ DepRecord renDeps substDeps idSubstDeps extRenDeps extDeps rinstInstDeps compRenRenDeps compRenSubstDeps compSubstRenDeps compSubstSubstDeps

