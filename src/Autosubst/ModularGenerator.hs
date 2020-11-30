{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Autosubst.ModularGenerator where

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

-- Code for Smart Constructors

-- Standard names for smart constructors

-- Name for injection of retracts.
inj_ :: String
inj_ = "inj"

-- Changed name for a smart constructor.
smart_ :: String -> String
smart_ c = c ++ "_"

-- Name of retract proof.
retrName :: TId -> TId -> String
retrName x y = "retract_" ++ x ++ "_" ++ y

-- Name of inclusion constructor.
in'_ :: TId -> TId -> String
in'_ x y = "In_" ++ x

-- Name of induction lemma.
isIn_ :: TId -> TId -> String
isIn_ x y = "isIn_" ++ x ++ "_" ++ y

inProof_ :: TId -> String
inProof_ x = "induction_" ++ x

some_none_ :: Term
some_none_ = TermId "some_none_explosion"

dsome_ :: Term
dsome_ = TermId "Datatypes.Some"

dnone_ :: Term
dnone_ = TermId "Datatypes.None"

ors :: [Term] -> Term
ors []       = TermId "False"
ors [x]      = x
ors (x : xs) = idApp "or" [x, ors xs]

orPattern :: Int -> Term -> [Term]
orPattern 0 _ = []
orPattern 1 s = [s]
orPattern n s = (idApp "or_introl" [s]) : map (\x -> idApp "or_intror" [x]) (orPattern (n-1) s)


-- Actions on the dependency graph.

-- TODO: Change.
-- Yiels the extended type of a type.
getExtension :: TId -> GenM TId
getExtension x = return x


-- Commands for assumptions.

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
hypoInductive :: Bool -> InductiveBody -> GenM [Sentence]
hypoInductive open (InductiveBody x _ _ _) = do
  b <- isOpenComponent x
  (n,bs) <- introScopeVar "n" x
  s <- finT_ x (sty_terms n)
  return $ [SentenceVariable x (TermSort Type)] ++ [SentenceVariable (var_ x) ([s] ==> sortType x n) | b, not open ]

-- Assuming a sentence.
hypo :: Bool -> Sentence -> GenM [Sentence]
hypo b (SentenceDefinition d)             = return $ if b then [] else hypoDef d
hypo b (SentenceInductive (Inductive bs)) = liftM concat $ mapM (hypoInductive b) bs
hypo b (SentenceFixpoint (Fixpoint _ bs)) = return$ concatMap (hypoFix b) bs
hypo b (SentenceSection x xs)             = liftM concat $ mapM (hypo b) xs
hypo b _                                  = return $ []

-- Assuming lists of sentences.
hypos :: Bool -> [Sentence] -> GenM [Sentence]
hypos b xs = liftM concat $ mapM  (hypo b) xs


-- Generation of Modular Boilerplate
genSmartArg :: TId -> SubstTy -> [Binder] -> Argument  -> GenM Term
genSmartArg x n bs (Atom y)  = liftM2 idApp (complete_ y) (fmap sty_terms $ castUpSubst x bs y n)
genSmartArg x n bs (FunApp f p xs) = do
  xs' <- mapM (genSmartArg x n bs) xs
  return $ idApp (funname_ (f ++ p)) xs'


-- Generation of smart constructors.
genSmart :: TId ->  Constructor -> GenM Definition
genSmart x (Constructor pms cname pos) = do
    x' <- getExtension x
    (m, bm) <- introScopeVar "m" x
    let s = getPattern "s" pos
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

-- Generation of retracts assumption.
-- TODO: Generalize retract name.
genRetract :: TId -> TId -> GenM Sentence
genRetract x y = do
  let s = idApp "retract" [TermId x, TermId y]
  return $ SentenceVariable ("retract_" ++ x) s

genRetracts :: [(TId, TId)] -> GenM [Sentence]
genRetracts xs = do
  retr <- mapM (\(x,y) -> genRetract x y) xs
  return $ retr

-- Generation of retract proof.
genRetractProof :: TId -> TId -> GenM Sentence
genRetractProof x y = do
  x' <- complete_ x
  b' <- isOpen y
  cs <- constructors y
  let b = b' || length cs > 1
      ret = idApp "retract" [TermId ("(" ++ x' ++ ")"), TermId y]
      rdef = TermAbs [BinderName "x"] (TermMatch (MatchItem (TermId "x") Nothing) Nothing ([Equation (PatQualId (idApp (in'_ x "") [TermId "s"])) (TermApp dsome_ [TermId "s"]) ] ++ [Equation PatUnderscore dnone_ | b]))
      p1 = TermAbs [BinderName "s"] eq_refl_
      p2 = TermAbs [BinderName "s", BinderName "t"] (TermMatch (MatchItem (TermId "t") Nothing) Nothing ([Equation (PatQualId (idApp (in'_ x "") [TermId "t'"])) (TermAbs [BinderName "H"] (idApp (congr_ (in'_ x "")) [eqSym_ (idApp "Some_inj" [TermId "H"])]))] ++ [Equation PatUnderscore some_none_ | b]))
      tm = idApp "Build_retract" [TermId (in'_ x ""), rdef, p1, p2]
  return $ SentenceInstance [] (retrName x y) ret tm

genRetractProofs :: [(TId, TId)] -> GenM [Sentence]
genRetractProofs xs = do
  retr <- mapM (\(x,y) -> genRetractProof x y) xs
  ass <- mapM extend_ [x | (x, y) <- xs]
  ass' <- filterM isOpenComponent ass
  return $ retr ++ [SentenceCommand (Arguments (var_ x) [TermUnderscore, TermUnderscore]) | x <- ass']


genPrec :: [TId] -> GenM [(TId, TId)]
genPrec xs = do
  liftM concat (mapM (\x -> do
                          ys <- prev_ x
                          return $ [(y, x) | y <- ys, x /= y]) xs)

genIn :: TId -> TId -> GenM Definition
genIn x y = do
  cs <- constructors y
  b <- isOpen y
  let b1 = BinderNameType ["s"] (TermId x)
      b2 = BinderNameType ["t"] (TermId y)
      args = map (\(Constructor pms c ps) -> map (\(Position bs a) -> a) ps) cs
      ps = map (\(Constructor pms c ps) -> (c, (getPattern "t" ps)) ) cs
      body = TermMatch (MatchItem (TermId "t") Nothing) Nothing ([Equation PatUnderscore (TermId "False")| b] ++ zipWith equation ps args)
  return $ Definition (isIn_ x y) [b1,b2] (Just (TermSort Prop)) body
      where equation (c,pat) ts = Equation (PatQualId (idApp c (map TermId pat))) (ors (eqs (f ts pat)))
            f ts xs = map snd (filter (\(z, _) -> z == Atom x) (zip ts xs))
            eqs xs = map (\x -> TermEq (TermId "s") (TermId x)) xs

genIns :: [(TId, TId)] -> GenM [Definition]
genIns xs = mapM (\(x,y) -> genIn y x) xs


-- Generation of induction lemma.
genInProof :: TId -> GenM FixpointBody
genInProof x = do
  cs <- constructors x -- The in-things.
  let args = map (\(Constructor pms c ps) -> map (\(Position bs a) -> a) ps) cs -- List of below arguments. TODO: Handle parameters
      p = BinderNameType ["P"] (TermFunction (TermId x) (TermSort Prop)) -- main predicate
      ihbs = map (\(Constructor pms c [Position _ y']) -> case y' of Atom y -> BinderNameType ["IH_" ++ c] -- TODO: Take care o parameters.
                                                                              (TermForall [BinderName "t"]
                                                                              (TermFunction (TermForall [BinderName "x"]
                                                                              (TermFunction (idApp (isIn_ x y) [TermUnderscore, TermId "x", TermId "t"])
                                                                              (idApp "P" [TermId "x"])))
                                                                              (idApp "P" [idApp c [TermId "t"]])))
                                                                     _ -> BinderScopeNameType [] (TermId "Error.")) cs -- TODO: inductive hypothesis
      ihs = getTerms ihbs
      e = BinderNameType ["s"] (TermId x)
      bs = [p] ++ ihbs ++ [e]
      ret = idApp "P" [TermId "s"]
      solve t eq = idApp "eq_ind_r" [TermUnderscore, idApp (inProof_ x) (TermUnderscore : ihs ++ [t]), eq]
      hs ps = orPattern (length $ filter (\(Position _ a) -> a == Atom x) ps) (TermId "H") -- TODO: Handle other case than Atom
      term c css ps (Atom y) = TermAbs [BinderName "t", BinderNameType ["H"] (idApp (isIn_ x y) [TermUnderscore, TermUnderscore, idApp c (map (\x -> TermUnderscore) css ++ map (\x -> TermUnderscore) ps)])] (TermMatch
        (MatchItem (TermId "H") Nothing) Nothing (map (\x -> Equation (PatQualId x) (solve TermUnderscore (TermId "H"))) (hs (ps))))
      term _ _ _ _ = TermId "Error"
  ccs <- mapM (\y -> constructors y) (concat [[x]]) -- TODO: SHould be args instead of [x]
  pat <- mapM (\(Constructor pms c [Position bs z]) -> do -- TODO: Take care of parameters.
                          let ps = [Position bs z]
                          css <- liftM concat (mapM (\(Position bs a) -> constructors x) ps) -- x should be a
                          zs <- realDeps x -- ahouls bw z
                          return $ map (\(Constructor pms c' ps) -> (c, c', zs, ps, [idApp c' (map (\x -> TermUnderscore) zs ++ (map TermId  (getPattern "s" ps)))], z)) css -- TODO: Take care of parameters.
                    ) cs
  let equations (c, c', css, ps, [p], y) = Equation (PatQualId (idApp c [p])) (getTerm ("IH_" ++ c) (term c' css ps y))
      body = TermMatch (MatchItem (TermId "s") Nothing) Nothing (map equations (concat pat)) -- equations
  return $ FixpointBody (inProof_ x) bs ret body
    where getTerm ih eq = idApp ih [TermUnderscore, eq]


nonEmptySection :: String -> [Sentence] -> [Sentence]
nonEmptySection s xs = [SentenceSection s xs | not (null xs)]

isExtension :: TId -> GenM Bool
isExtension x = do
  args <- arguments x
  ys <- filterM (\y -> do
               y' <- extend_ y
               return $ x == y') (filter (\z -> z /= x) args)
  return $ not (null (ys))
