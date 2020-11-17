module Autosubst.Types
  ( Id
  , Typevar
  , TId
  , CId
  , FId
  , FtId
  , VariantType
  , ParserSpec
  , Spec
  , Constructor(..)
  , Position(..)
  , Binder(..)
  , Argument(..)
  , Signature(..)
  , Prover (..)
  , argSorts
  , binderSorts
  ) where

import qualified Data.Map as M
import qualified Data.Set as S

-- Provers: Scoped Coq (Coq), unscoped Coq (UCoq), scoped Lean (Lean), scoped Agda (Agda), and only extensible syntax (ECoq).
data Prover = Coq | UCoq | ECoq deriving (Show, Read, Eq)

-- identifiers
type Id       = String
type Typevar  = String
type TId      = Id -- for sorts 
type CId      = Id -- for constructors 
type FId      = Id -- for functors 
type FtId     = Id -- for features 

type VariantType = [(TId, [FtId])] -- type for variants, consisting of the name of the variant and the features it contains
type ParserSpec = ([TId],[FId], Spec, TId -> [TId], VariantType) -- Existing sorts, existing functors, the specification, injections, and variants

-- specifications: maps from identifiers to a list of constructors
type Spec = M.Map TId [Constructor]

-- Constructor: Parameters, name, and positions of the constructor 
data Constructor = Constructor
  {  parameters :: [(String, TId)]
  , name        :: CId
  , positions   :: [Position]
  } deriving (Show)

-- Positions: A list of binders and the main argument
data Position = Position
  { binders  :: [Binder]
  , argument :: Argument
  } deriving (Eq, Show)

-- Binders: Can either be a simple, single binder, or BinderList m ty describes a list of binders of length m.
data Binder = Single TId | BinderList String TId deriving (Eq, Show)

-- Function to yield all binder sorts
binderSorts :: Binder -> [TId]
binderSorts (Single x)       = [x]
binderSorts (BinderList _ x) = [x]

-- Arguments: Either an atomic identifer or a functor application with possible parameters and again a list of arguments
data Argument = Atom TId | FunApp FId String [Argument] deriving (Eq, Show)

-- Yields all argument sorts
argSorts :: Argument -> [TId]
argSorts (Atom x)        = [x]
argSorts (FunApp _ _ xs) = concat (map argSorts xs)

-- signatures 
data Signature = Signature
  { sigSpec       :: Spec -- specification
  , sigSubstOf    :: M.Map TId [TId] -- Map from sort to its substitution vector
  , sigComponents :: [([TId], [TId], Maybe String)]-- List of sorts to define, list of dependencies, and optional name of feature
  , sigExt        :: M.Map TId TId -- gets the supersort for a sort
  , sigIsOpen     :: S.Set TId -- set of open sorts, i.e. sorts which contain variables
  , sigArguments  :: M.Map TId [TId] -- set of successors for each sort
  , sigVariants   :: VariantType -- set of variants
  } deriving (Show)
