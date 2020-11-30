module Autosubst.Types
  ( Id
  , Typevar
  , TId
  , CId
  , FId
  , Spec
  , Constructor(..)
  , Position(..)
  , Binder(..)
  , Argument(..)
  , getIds
  , getBinders
  , Signature(..)
  , Prover (..)
  ) where

import qualified Data.Map as M
import qualified Data.Set as S

-- Provers: Scoped Coq (Coq), unscoped Coq (UCoq), scoped Lean (Lean), scoped Agda (Agda), and only extensible syntax (ECoq).
data Prover = Coq | UCoq | Lean | Agda | ECoq deriving (Show, Read, Eq)

-- identifiers
type Id = String
type Typevar = String
type TId = Id
type CId = Id
type FId = Id

-- specifications -- TODO: nicer instance for Show, default is ugly as heck
-- A type has constructors and depends on a list of types.
type Spec = M.Map TId [Constructor] -- ([TId],[Constructor])

-- Should also contain a list of parameters for the length of a list.
data Constructor = Constructor
  {  parameters :: [(String, TId)]
  , name        :: CId
  , positions   :: [Position]
  } deriving (Show)

data Position = Position
  { binders  :: [Binder]
  , argument :: Argument
  } deriving (Eq, Show)

-- Binders: Can either be a single binder (as before!), or BinderList m ty describes a list of binders with arbitrary scope m.
data Binder = Single TId | BinderList String TId deriving (Eq, Show)
data Argument = Atom TId | FunApp FId FId [Argument] deriving (Eq, Show)

getBinders :: Binder -> [TId]
getBinders (Single x)       = [x]
getBinders (BinderList _ x) = [x]

-- TODO: Does not fit here.
getIds :: Argument -> [TId]
getIds (Atom x)        = [x]
getIds (FunApp _ _ xs) = concat (map getIds xs)

-- signatures -- TODO: same as above, show on signature looks messy

data Component = CSort [TId] | CFeature (String, [TId]) | CCompose [TId]

data Signature = Signature
  { sigSpec       :: Spec
  , sigSubstOf    :: M.Map TId [TId]
  , sigComponents :: [([TId], [TId])]-- [([TId], [TId])] -- List of things to define and list of dependencies.
  , sigExt        :: M.Map TId TId -- gets the supersort for a sort
  , sigIsOpen     :: S.Set TId
  , sigArguments  :: M.Map TId [TId]
  } deriving (Show)
