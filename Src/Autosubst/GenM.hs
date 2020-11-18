{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Autosubst.GenM where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.RWS
import           Data.Maybe               
import           Data.Char               (toLower)
import           Data.List               as L
import qualified Data.Map                as M
import qualified Data.Set                as S
import           Text.PrettyPrint.Leijen hiding ((<$>))

import           Autosubst.Types

ifB :: Bool -> [a] -> [a]
ifB b xs = if b then xs else []

ifM :: Monad m => Bool -> m [a] -> m [a]
ifM b xs = do
  xs' <- xs
  return $ if b then xs' else []

instance Monoid Doc where
  mappend = (Text.PrettyPrint.Leijen.<>)
  mempty = empty

-- Scope type: Maps an identifier to a number.
type Scope = Maybe [FtId]

-- Reading a signature, yielding a String with possibly an exception
type SigM = ReaderT Signature (Except String)

-- Writing [(String, Doc)], reading signatures, having the state of a Scope, with exceptions in the state.
type GenM = RWST Signature [(String, Doc)] Scope (Except String)

runSig :: Signature -> SigM a -> Either String a
runSig sig m = runExcept $ runReaderT m sig

runGen :: Signature -> GenM () -> Either String [(String, Doc)]
runGen sig m = runExcept $ snd <$> evalRWST m sig Nothing

write :: [(String, Doc)] -> GenM ()
write = tell

tfresh :: Id -> GenM Id
tfresh id = return id

-- Get all the sorts of the component of x.
getComponent :: TId -> GenM [TId]
getComponent x = do
  cmps <- components
  return $ concat [fst xs ++ snd xs | xs <- cmps, x `elem` (fst xs) || x `elem` (snd xs)]


-- Accessing the signature

-- Return the constructors of a sort. If we are in a variant, then just return the corresponding subfeatures.
constructors ::  TId -> GenM [Constructor]
constructors id = do
  spec <- asks sigSpec;
  ftMap <- get
  case M.lookup id spec of
    Just cs -> case ftMap of 
                  Just features ->  return $ filter (filterFeatures features) cs 
                  Nothing -> return cs
    Nothing -> throwError $ "constructors called on invalid type: " ++ id

-- TODO: Explanation + right place on where to put them.
getFeature :: TId -> Maybe String 
getFeature [] = Nothing
getFeature ('_' : xs) = Just xs 
getFeature (x : xs) = getFeature xs

filterFeatures :: [FtId] -> Constructor -> Bool
filterFeatures features (Constructor pms ('I' : 'n' : '_' : c) m) = case (getFeature c) of  
                                                                              Just c' -> c' `elem` features || c `elem` features
                                                                              Nothing -> True   
filterFeatures _ _ = True

substOf :: (MonadReader Signature m, MonadError String m) => TId -> m [TId]
substOf id = do
  substs <- asks sigSubstOf
  case M.lookup id substs of
    Just ts -> return ts
    Nothing -> throwError $ "substOf called on invalid type: " ++ id

components ::(MonadReader Signature m) => m [([TId], [TId])]
components = do 
  xs <- asks sigComponents
  return $ map (\(x, y, z) -> (x, y)) xs

-- TODO: Sort which one I really want
fullComponents ::(MonadReader Signature m) => m [([TId], [TId], Maybe String)]
fullComponents = asks sigComponents

-- List of all Sorts
allSorts ::  GenM [TId]
allSorts = do
  c <- fullComponents
  fts <- get
  return $ concat (map (\(x, y, z) -> if (not (isJust fts) || not (isJust z) || fromMaybe "key" z `elem` fromMaybe [] fts) then x else []) c)

allSorts' ::  GenM [TId]
allSorts' = do
  c <- fullComponents
  return $ concat (map (\(x, y, z) -> x) c)

getSubstSorts :: GenM [TId]
getSubstSorts = do 
  spec <- components
  filterM (\x -> do
                xs <- substOf x
                return $ not $ null xs) (concat (map fst spec))

getVarSorts :: GenM [TId]
getVarSorts = do 
  spec <- components
  filterM isOpen (concat (map fst spec)) 

getUps :: Prover -> GenM [(Binder, TId)]
getUps p = do 
  spec <- components
  xs <- mapM (\x -> do
          xs <- substOf (L.head x)
          return $ [(Single x,y) | x <- xs, y <- xs] ++ [(BinderList "p" x,y) | x <- xs, y <- xs, p == Coq]) (map fst spec) -- condition with p == Coq is needed because variadic binders are only supported for scoped Coq code so far
  return $ nub (concat xs)

-- 1. Functions on all signatures

-- Yields whether a sort is open, i.e. has a variable constructor.
isOpen :: (MonadReader Signature m) => TId -> m Bool
isOpen id = S.member id <$> asks sigIsOpen

-- Yields true if the component of the identifier contains at least one identifier
hasSubst :: (MonadReader Signature m, MonadError String m) => TId -> m Bool
hasSubst id = fmap (not . null) (substOf id)

-- Yields all arguments of a sort, i.e. all sorts which appear in the sort transitively
arguments :: (MonadReader Signature m, MonadError String m) => TId -> m [TId]
arguments id = do
  args <- asks sigArguments
  case M.lookup id args of
    Just ts -> return ts
    Nothing -> throwError $ "arguments called on invalid type: " ++ id

-- Yields all direct successors of a sort
successors :: TId -> GenM [TId]
successors id = do
  cs <- constructors id
  return $ concatMap (\(Constructor _ _ ps) -> concatMap (\(Position _ x) -> argSorts x) ps) cs

-- Yields whether a sort is non-empty, i.e. either contains variables or has at least one constructor
nonEmptySort :: TId -> GenM Bool
nonEmptySort id = do
  b <- isOpen id
  cs <- constructors id
  return $  b || (not . null) cs

-- Checks whether definitions will require recursive definitions.
-- Necessary because Fixpoints don't reduce in Coq, if there is no dedicated recursive argument.
recursive :: [TId] -> GenM Bool
recursive xs = do
  if (null xs) then throwError "Can't determine whether the component is recursive, this component is empty." else return ()
  args <- successors (head xs)
  zs <- mapM dependencyList xs
  return $ (not . null) [x | x <- xs, x `elem` args] || (not . null) [z | z <- zs, not (null z)]

-- Checks whether a definition requires renamings.
-- A definition does require renamings, if at the same time 1. the respective component defines this binder, 2. the respective component binds the variable., or 3. a later component requires renamings.
hasRenamings :: TId -> GenM Bool
hasRenamings x = do
  y <- extend_ x
  xs <- getComponent y
  boundBinders <- boundBinders xs
  all <- allSorts
  let occursIn = [x | x <- all, not (elem x xs)]
  occ <- filterM (\z -> do
                        zs <- successors z
                        return $ y `elem` zs) occursIn
  bs <- mapM hasRenamings occ
  return $ (not . null) ([x | x <- xs, x `elem` boundBinders]) || (not . null) [x | x <- bs, x]

-- Computes all the bound binders in a list of sorts, needed to test whether a sort has renamings
boundBinders :: [TId] -> GenM [TId]
boundBinders xs = do
  binders <- mapM (\x -> do
                cs <- constructors x
                return $ concatMap (\(Constructor _ _ ps) -> concatMap (\(Position bs _) -> concatMap binderSorts bs) ps) cs) xs
  return $ concat binders


-- All really appearing combinations of binders. TODO: Overlook.
directUps :: TId -> GenM [(Binder, TId)]
directUps x = do
  cs <- constructors x
  ps <- return $ map (\(Position bs p) -> [(b, p) | b <- bs]) (concat $ map (\(Constructor _ _ ps) -> ps) cs) 
  return $ nub (concatMap (\(b, xs) -> map (\x -> (b, x)) (argSorts xs)) (concat ps))


-- 2. Functions for modular syntax

--- Does the whole signature require modular syntax?
sigMod :: GenM Bool 
sigMod = do 
  cs <- fullComponents
  return $ not $ null (filter (\(x, y, m) -> isJust m) cs)

-- Yields the super sort of a sort if it exists, and otherwise yields the sort itself
extend_ :: TId -> GenM TId
extend_ x = do
  f <- asks sigExt
  return $ case (M.lookup x f) of
            Just y  -> y
            Nothing -> x

-- Boolean function which yields whether a sort is a sort just used within a feature definition
isFeature :: TId -> GenM Bool
isFeature x = do
  f <- asks sigExt
  return $ case (M.lookup x f) of
            Just y  -> True 
            Nothing -> False
 
-- Yields whether a sort is a variant sort
isVariantSort :: TId -> GenM Bool
isVariantSort x = do
   -- y <- extend_ x
  --  return (x == y)
   xs <- dependencyList x
   return (not (null xs))

-- Yields all sorts whose extension is x, e.g. exp_lam and exp_arith for exp. 
dependencyList :: TId -> GenM [TId]
dependencyList x = do
  ts <- allSorts
  filterM (\z -> do
                  y <- extend_ z
                  return $ (x == y && x /= z)) ts

prev' :: TId -> GenM [TId]
prev' x = do
  ts <- allSorts'
  filterM (\z -> do
                  y <- extend_ z
                  return $ (x == y && x /= z)) ts

isExtension :: TId -> GenM Bool
isExtension x = do
  args <- arguments x
  ys <- filterM (\y -> do
               y' <- extend_ y
               return $ x == y') (filter (\z -> z /= x) args)
  return $ not (null (ys))

-- Generation of all sorts and its features, e.g. [ty, exp] generates a list [(ty_lam, ty), ..., (exp_lam, exp), (exp_arith, exp)]
dependencyPairs :: [TId] -> GenM [(TId, TId)]
dependencyPairs xs = do
  liftM concat (mapM (\x -> do
                          ys <- dependencyList x
                          return $ [(y, x) | y <- ys, x /= y]) xs)

-- Generation of a list of all sorts in xs and their strict extension, if available
extensionList :: [TId] -> GenM [(TId, TId)]
extensionList xs = liftM concat (mapM (\x -> do
  y <- extend_ x
  return $ if (x == y) then [] else [(x,y)]
  ) xs)


-- Checks whether any feature of a sort requires binders 
isOpenComponent :: TId -> GenM Bool
isOpenComponent x = do
    xs <- prev' x -- All feature components of a sort
    ys <- filterM isOpen xs
    return $ not (null ys)


sortby :: Eq a => [a] -> [a] -> [a]
sortby order xs = filter (\z -> elem z xs) order    

arguments_rt :: [TId] -> GenM [TId]
arguments_rt ids = do 
  xs <- mapM arguments ids 
  all <- allSorts
  if (ids == sortby all (ids ++ concat xs)) then return ids else arguments_rt (sortby all (ids ++ concat xs))

-- Only returns arguments for features -- this is the dependencies for defining this
realDeps :: TId -> GenM [TId]
realDeps x = do
  args <- arguments x 
  substs <- substOf x
  f <- asks sigExt
  args' <- mapM extend_ (x:args ++ substs)
  args'' <- filterM isVariantSort args' 
  all <- allSorts
  return $ sortby all (filter (\z -> z/= x) args'')

depsArgs :: TId -> GenM [TId]
depsArgs x = do
  args <- successors x 
  f <- asks sigExt
  args' <- mapM extend_ args
  args'' <- filterM isVariantSort args' 
  all <- allSorts
  return $ sortby all (filter (\z -> z/= x) args'')

-- Yields name + arguments of all subsorts
addFeatureArgs :: TId -> GenM TId
addFeatureArgs x = do
  xs <- depsArgs x
  return $  x ++ " " ++ concat (L.intersperse " " xs)

-- 3. Compatibility Checking

-- Yields a list of all binders that are actually used
sigActualBinders :: GenM [(Binder, TId)]
sigActualBinders = do
  xs <- allSorts' 
  cs <- mapM constructors xs 
  let 
    bs = concatMap (\(Constructor _ _ pos) -> concatMap (\(Position bs arg) -> map (\a -> map (\b -> (b, a)) bs) (argSorts arg)) pos) (concat cs)
  bs' <- mapM (\(b, a) -> do
                          as <- substOf a
                          return $ map (\a -> (b, a)) as) (concat bs)
  return $ nub (concat bs')

-- Checks whether 
hasVariadicBinders :: GenM Bool 
hasVariadicBinders = do 
  bs <- sigActualBinders 
  return $ not $ null $ (filter (\(b, _) -> case b of Single _ -> False
                                                      _ -> True) bs)

-- Yields an error message if incompatible modes are mixed.
checkIncompatibility :: Prover -> GenM ()
checkIncompatibility p = do
  isMod <- sigMod
  hasVariadicBinders <- hasVariadicBinders
  if (p == Coq && isMod)
    then throwError "The mix of modular and scoped syntax is not supported so far."
  else 
    if (p == UCoq && hasVariadicBinders)
    then throwError "The mix of unscoped and variadic syntax is not supported so far."
      else return ()
