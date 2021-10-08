{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Autosubst.Syntax where

import           Autosubst.GenM
import           Autosubst.Types
import           Data.List            as L

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.RWS    hiding ((<>),Ap)

-- Contains syntax for functions, inductive datatypes...
type Identifier = String

data Command = Arguments String Terms

data CBinder = BinderName String
            | BinderNameType [String] Term
            | BinderImplicitName String
            | BinderImplicitNameType [String] Term
            | BinderScopeNameType [String] Term
            | BinderImplicitScopeNameType [String] Term

data Definition = Definition String [CBinder] (Maybe Term) Term

data Equation = Equation Pattern Term

data Fixpoint = Fixpoint Bool [FixpointBody]

data FixpointBody = FixpointBody String [CBinder] Term Term

type Identifiers = [Identifier]

data Inductive = Inductive [InductiveBody]

data InductiveBody = InductiveBody String [CBinder] Term [InductiveCtor]

data InductiveCtor = InductiveCtor String (Maybe Term)

data Lemma = Lemma String [CBinder] Term Proof

data Proof = ProofExact Term | ProofString String

data MatchItem = MatchItem Term

data Pattern = PatternConstructor Term Identifiers | PatternUnderscore

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
              | SentenceRequireExport [String]

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

-- Special type for substitution related primitives, needed to handle them specifically.
data SubstTy =
  SubstScope Terms
  | SubstRen Terms
  | SubstSubst Terms
  | SubstEq Terms (TId -> Binder -> Term -> GenM Term)
  | SubstConst Terms

-- Constants -- needed to print them differently depending on the theorem prover
data Const = Some | None
            | Refl | Sym | Trans
            | Nat | Suc
            | Fin
            | Id | Comp
            | Upren | Shift  | Cons | VarZero
            | Ap
            | Fext

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

-- Functions

createBinders :: [(String, TId)] -> [CBinder]
createBinders = map (\p -> BinderNameType [fst p] (TermId (snd p)))

createImpBinders :: [(String, TId)] -> [CBinder]
createImpBinders = map (\p -> BinderImplicitNameType [fst p] (TermId (snd p)))

-- Returns just the types of binders, omitting all names
binderType :: CBinder -> [Term]
binderType (BinderNameType _ t)              = [t]
binderType (BinderImplicitNameType _ t)      = [t]
binderType (BinderScopeNameType _ t)         = [t]
binderType (BinderImplicitScopeNameType _ t) = [t]
binderType _                                 = []

binderTypes :: [CBinder] -> [Term]
binderTypes = concatMap binderType

-- Returns just all names of the binders, omitting all types
binderTerm :: CBinder -> Terms
binderTerm (BinderName s)                = [TermId s]
binderTerm (BinderNameType xs s)         = map TermId xs
binderTerm (BinderImplicitName s)        = []
binderTerm (BinderImplicitNameType xs s) = []

binderTerms :: [CBinder] -> Terms
binderTerms = concatMap binderTerm

-- Converts a substitution object into a list of terms
substTerms :: SubstTy -> Terms
substTerms (SubstScope xs) = map TermVar xs
substTerms (SubstRen xs)   = xs
substTerms (SubstSubst xs) = xs
substTerms (SubstEq xs f)  = xs
substTerms (SubstConst xs) = xs

-- Abbreviations for syntax

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

ap_ :: [Term] -> Term
ap_ s =  TermApp (TermConst Ap) s

fext_ :: Term
fext_ = TermConst Fext

-- Application of an identifer to a list of terms 
idApp :: String -> Terms -> Term
idApp s t = TermApp (TermId s) t

-- Repeated function
(==>) :: [Term] -> Term -> Term
s ==> t = foldr (\s t -> TermFunction s t) t s

-- Proof term for repated rewriting
repRew :: [(Term,Term)] -> Term
repRew s = foldl (\s (t, t_eq) -> TermApp (TermConst Trans) [s, TermApp (TermConst Ap) [t_eq, t]]) (TermConst Refl) s

-- Substitution related

-- Application of an identifer to a substitution object
idSubstApp :: TId -> SubstTy -> Term
idSubstApp x n = TermApp (TermId x) [TermSubst n]


-- Matching on fin types
matchFin_ :: Term -> (Term -> Term) -> Term -> Term
matchFin_ s f b = TermMatch (MatchItem s) Nothing [Equation (PatternConstructor some_ ["fin_n"]) (f (TermId "fin_n")), Equation (PatternConstructor none_ []) b]

-- Create only a section, if the set of sentences is non-empty
nonEmptySection :: String -> [Sentence] -> [Sentence]
nonEmptySection s xs = [SentenceSection s xs | not (null xs)]

