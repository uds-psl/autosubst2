{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Autosubst.GenM
  -- Signature reader monad
  ( SigM
  , runSig
  -- Generator monad
  , GenM
  , runGen
  -- Generating fresh names
  , fresh
  , tfresh
  , intern
  , realDeps
  , complete_
  , extend_
  , prev_
  , Scope
  , withScope
  -- Accessing the
  , constructors
  , substOf
  , components
  , isOpen
  , isOpenComponent
  , isFeature
  , hasRenamings
  , arguments
  -- Producing output
  , write
  , hasArgs
  , definable
  , recursive
  ) where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.RWS
import           Data.Char               (toLower)
import           Data.List               as L
import qualified Data.Map                as M
import qualified Data.Set                as S
import           Text.PrettyPrint.Leijen hiding ((<$>))

import           Autosubst.Types

-- FIXME: Are we using an outdated PP library? Why isn't this defined?
instance Monoid Doc where
  mappend = (Text.PrettyPrint.Leijen.<>)
  mempty = empty

type Scope = M.Map Id Int

type SigM = ReaderT Signature (Except String)
type GenM = RWST Signature [(String, Doc)] Scope (Except String)

runSig :: Signature -> SigM a -> Either String a
runSig sig m = runExcept $ runReaderT m sig

runGen :: Signature -> GenM () -> Either String [(String, Doc)]
runGen sig m = runExcept $ snd <$> evalRWST m sig M.empty

-- Generating fresh names
lookupScope :: Id -> Scope -> Int
lookupScope = M.findWithDefault 0

realDeps :: TId -> GenM [TId]
realDeps x = do
  args <- arguments x
  f <- asks sigExt
  return $ case (M.lookup x f) of
            Just y  -> [y | y `elem` args]
            Nothing -> []

complete_ :: TId -> GenM TId
complete_ x = do
  xs <- realDeps x
  return $  x ++ " " ++ concat (L.intersperse " " xs)

extend_ :: TId -> GenM TId
extend_ x = do
  f <- asks sigExt
  return $ case (M.lookup x f) of
            Just y  -> y
            Nothing -> x

isFeature :: TId -> GenM Bool
isFeature x = do
  y <- extend_ x
  return $ x /= y

types :: GenM [TId]
types = do
  c <- components
  return $ concat (map fst c)

-- Get all the sorts of the component of x.
getComponent :: TId -> GenM [TId]
getComponent x = do
  cmps <- components
  return $ concat [fst xs ++ snd xs | xs <- cmps, x `elem` (fst xs) || x `elem` (snd xs)]

prev_ :: TId -> GenM [TId]
prev_ x = do
  ts <- types
  (filterM (\t -> do
                  y <- extend_ t
                  return $ (x == y)) (filter (\z -> x /= z) ts))

isExtension :: TId -> GenM Bool
isExtension x = do
    xs <- prev_ x
    return (not (null xs))

fresh :: Id -> GenM Id
fresh id = do
  scope <- get
  let n = lookupScope id scope
  put $ M.insert id (n+1) scope
  if n > 0
    then return $ id ++ show n
    else return id

tfresh :: Id -> GenM Id
tfresh id = do
  scope <- get
  let n = lookupScope id scope
  if n > 0
    then return $ id ++ show n
    else return id

-- By default, use the first character of the type
intern :: TId -> GenM Id
intern (c:_) = fresh [toLower c]

withScope :: GenM a -> GenM a
withScope m = do
  scope <- get
  v <- m
  put scope
  return v

-- Accessing the signature
-- These functions work on both GenM and SigM

constructors :: (MonadReader Signature m, MonadError String m) => TId -> m [Constructor]
constructors id = do
  spec <- asks sigSpec;
  case M.lookup id spec of
    Just cs -> return cs
    Nothing -> throwError $ "constructors called on invalid type: " ++ id

substOf :: (MonadReader Signature m, MonadError String m) => TId -> m [TId]
substOf id = do
  substs <- asks sigSubstOf
  case M.lookup id substs of
    Just ts -> return ts
    Nothing -> throwError $ "substOf called on invalid type: " ++ id

components ::(MonadReader Signature m) => m [([TId], [TId])]
components = asks sigComponents

isOpen :: (MonadReader Signature m) => TId -> m Bool
isOpen id = S.member id <$> asks sigIsOpen

isOpenComponent :: TId -> GenM Bool
isOpenComponent x = do
    xs <- prev_ x -- TODO: all sorts that are features.
    ys <- filterM isOpen xs
    return $ not (null ys)

definable :: (MonadReader Signature m, MonadError String m) => TId -> m Bool
definable id = do
  b <- isOpen id
  cs <- constructors id
  return $  b || (not . null) cs

-- Yields true if at least one variable is contained.
hasArgs :: (MonadReader Signature m, MonadError String m) => TId -> m Bool
hasArgs id = fmap (not . null) (substOf id)

arguments :: (MonadReader Signature m, MonadError String m) => TId -> m [TId]
arguments id = do
  args <- asks sigArguments
  case M.lookup id args of
    Just ts -> return ts
    Nothing -> throwError $ "arguments called on invalid type: " ++ id

successors :: (MonadReader Signature m, MonadError String m) => TId -> m [TId]
successors id = do
  cs <- constructors id
  return $ concatMap (\(Constructor _ _ ps) -> concatMap (\(Position _ x) -> getIds x) ps) cs

-- Checks whether definitions will require recursive definitions.
-- This will be necessary later on, because Fixpoints don't reduce in the proper way in Coq, if there is no dedicated recursive argument.
recursive :: [TId] -> GenM Bool
recursive xs = do
  if (null xs) then throwError "Can't determine whether the component is recursive." else return ()
  args <- successors (head xs)
  zs <- mapM prev_ xs
  return $ (not . null) [x | x <- xs, x `elem` args] || (not . null) [z | z <- zs, not (null z)]

-- Computes all the bound binders in a specfication.
boundBinders :: [TId] -> GenM [TId]
boundBinders xs = do
  binders <- mapM (\x -> do
                cs <- constructors x
                return $ concatMap (\(Constructor _ _ ps) -> concatMap (\(Position bs _) -> concatMap getBinders bs) ps) cs) xs
  return $ concat binders


-- Checks whether a definition requires renamings.
-- A definition does require renamings, if at the same time 1. the respective component defines this binder, 2. the respective component binds the variable., or 3. a later component requires renamings.
hasRenamings :: TId -> GenM Bool
hasRenamings x = do
  y <- extend_ x
  xs <- getComponent y
  boundBinders <- boundBinders xs
  all <- types
  let occursIn = [x | x <- all, not (elem x xs)]
  occ <- filterM (\z -> do
                        zs <- successors z
                        return $ y `elem` zs) occursIn
  bs <- mapM hasRenamings occ
  return $ (not . null) ([x | x <- xs, x `elem` boundBinders]) || (not . null) [x | x <- bs, x]


write :: [(String, Doc)] -> GenM ()
write = tell
