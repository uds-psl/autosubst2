{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Autosubst.Syntax where

import           Autosubst.GenM
import           Autosubst.Types
import           Data.List            as L

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.RWS    hiding ((<>))

-- Contains syntax for functions, inductive datatypes...
type Identifier = String

data Command = Arguments String Terms

data CBinder = BinderName String
            | BinderNameType [String] Term
            | BinderImplicitName String
            | BinderImplicitNameType [String] Term
            | BinderScopeNameType [String] Term
            | BinderImplicitScopeNameType [String] Term

getType :: CBinder -> [Term]
getType (BinderNameType _ t)              = [t]
getType (BinderImplicitNameType _ t)      = [t]
getType (BinderScopeNameType _ t)         = [t]
getType (BinderImplicitScopeNameType _ t) = [t]
getType _                                 = []

getTypes :: [CBinder] -> [Term]
getTypes = concatMap getType

data Definition = Definition String [CBinder] (Maybe Term) Term

data Equation = Equation Pattern Term

data Fixpoint = Fixpoint Bool [FixpointBody]

data FixpointBody = FixpointBody String [CBinder] Term Term

type Identifiers = [Identifier]

data Inductive = Inductive [InductiveBody]

data InductiveBody = InductiveBody String [CBinder] Term [InductiveCtor]

data InductiveCtor = InductiveCtor String (Maybe Term)

data Lemma = Lemma String [CBinder] Term Proof

data Proof = ProofExact Term
          | ProofString String

data MatchItem = MatchItem Term (Maybe Term)

data Pattern = PatCtor Term Identifiers
             | PatCtorEx String [Pattern]
             | PatAtCtor Term Identifiers
             | PatAtCtorEx String [Pattern]
             | PatQualId Term
             | PatUnderscore

data Sentence = SentenceDefinition Definition
              | SentenceClass String [CBinder] [(String, Term)]
              | SentenceInductive Inductive
              | SentenceFixpoint Fixpoint
              | SentenceLemma Lemma
              | SentenceTactic Identifier Tactic
              | SentenceVariable Identifier Term
              | SentenceCommand Command
              | SentenceNotation String Term String String
              | SentenceInstance [CBinder] String Term Term
              | SentenceId String
              | SentenceTacticNotation [String] Tactic
              | SentenceSection String [Sentence]

data Tactic = TacticRewrite (Maybe String) [String] [String] [String]
              | TacticSeq [Tactic]
              | TacticId String
              | TacticUnfold [String] (Maybe String)
              | TacticFold [String] (Maybe String)
              | TacticRepeat Tactic

data Sort = Prop
          | Set
          | Type
          deriving ( Eq,Ord,Show)

data SubstTy =
  SubstScope Terms
  | SubstRen Terms
  | SubstSubst Terms
  | SubstEq Terms (TId -> Binder -> Term -> GenM Term)
  | SubstConst Terms

sty_terms :: SubstTy -> Terms
sty_terms (SubstScope xs) = map TermVar xs -- TODD: This is a hack.
sty_terms (SubstRen xs)   = xs
sty_terms (SubstSubst xs) = xs
sty_terms (SubstEq xs f)  = xs
sty_terms (SubstConst xs) = xs

data Const = Some | None
            | Refl | Sym | Trans
            | Nat | Suc
            | Fin
            | Id | Comp
            | Upren | Shift  | Cons | VarZero
            | Ap
            | Fext


-- head
none_ :: Term
none_ = TermConst None

-- tail
some_ :: Term
some_ = TermConst Some

eqSym_ :: Term -> Term
eqSym_ s = TermApp (TermConst Sym)  [s]

eqTrans_ :: Term -> Term -> Term
eqTrans_ s t = TermApp (TermConst Trans)  [s,t]

nat :: Term
nat = TermConst Nat

up_ren_ :: TId -> Binder -> Term -> Term
up_ren_ y (Single x) xi  =  if (y == x) then TermApp (TermConst Upren) [xi] else xi
up_ren_ y (BinderList m x) xi =  if (y == x) then idApp "upRen_p" [TermId m, xi] else xi

succ_ ::   Term -> TId -> Binder -> Term
succ_ n z (Single x) = if (z == x) then TermApp (TermConst Suc) [n] else n
succ_ n z (BinderList m x) = if (z == x) then idApp (m ++ "+") [n] else n


fin_ :: Term -> Term
fin_ n = TermApp (TermConst Fin) [n]

(>>>) :: Term -> Term -> Term
s >>> t = TermApp (TermConst Comp) [t, s]

eq_refl_ :: Term
eq_refl_ = TermConst Refl

shift_ :: Term
shift_ = TermConst Shift

id_ :: Term -> Term
id_ s = TermApp (TermConst Id) [s]

cons_ :: Term
cons_ = TermConst Cons

varZero_ :: Term
varZero_ = TermConst VarZero

repRew :: [(Term,Term)] -> Term
repRew s = foldl (\s (t, t_eq) -> TermApp (TermConst Trans) [s, TermApp (TermConst Ap) [t_eq, t]]) (TermConst Refl) s

ap_ :: [Term] -> Term
ap_ s =  TermApp (TermConst Ap) s

fext_ :: Term
fext_ = TermConst Fext


matchFin_ :: Term -> (Term -> Term) -> Term -> Term
matchFin_ s f b = TermMatch (MatchItem s Nothing) Nothing [Equation (PatCtor some_ ["fin_n"]) (f (TermId "fin_n")), Equation (PatQualId none_) b]


data Term =  TermImp Term
          | TermApp Term Terms
          | TermConst Const
          | TermNum Int
          | TermId String
          | TermSort Sort
          | TermFunction Term Term
          | TermAbs [CBinder] Term
          | TermForall [CBinder] Term
          | TermAnd Terms
          | TermEq Term Term
          | TermLet Term Term Term -- Get a pattern??
          | TermUnderscore
          | TermMatch MatchItem (Maybe Term) [Equation]
          | TupleTy Terms
          | Tuple Terms
          | Todo String
          | TermSubst SubstTy
          | TermVar Term
          | TermArg Term String Term

type Terms = [Term]

data Variable = Variable Identifier Term

type TmScope = Terms

idApp :: String -> Terms -> Term
idApp s t = TermApp (TermId s) t

-- Substitution related
sortType :: TId -> SubstTy -> Term
sortType x n = TermApp (TermId x) [TermSubst n]

getTerms' :: CBinder -> Terms
getTerms' (BinderName s)                = [TermId s]
getTerms' (BinderNameType xs s)         = map TermId xs
getTerms' (BinderImplicitName s)        = []
getTerms' (BinderImplicitNameType xs s) = []

getTerms :: [CBinder] -> Terms
getTerms = concatMap getTerms'

(==>) :: [Term] -> Term -> Term
s ==> t = foldr (\s t -> TermFunction s t) t s
