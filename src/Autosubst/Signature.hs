module Autosubst.Signature
  ( buildSignature
  ) where

import           Data.Array      (bounds, (!))
import           Data.Either     (partitionEithers)
import           Data.Foldable   (toList)
import           Data.Graph      as G
import           Data.List       (filter, nub)
import qualified Data.Map        as M
import           Data.Maybe
import qualified Data.Set        as S
import qualified Data.Tree       as T

import           Autosubst.Types

-- Yields a graph from the specification. Nodes and keys are of type TId.
directContainment :: Spec -> [(TId,TId)] -> (Graph, Graph, Vertex -> TId, TId -> Maybe Vertex)
directContainment spec ext = (g,g',v2id,id2v)
  where getArgs xs   = nub $ concat $ concatMap (map getIds . map argument . positions) xs
        (g,v2e,id2v) = graphFromEdges [(k,k,getArgs a) | (k,a) <- M.toList spec]
        getArgs' k xs   = filter (\m -> not (elem (k,m) ext)) (getArgs xs)
        (g', _, _) = graphFromEdges [(k,k,getArgs' k a) | (k,a) <- M.toList spec]
        v2id v       = case v2e v of (id,_,_) -> id
--        noInjection (Constructor ('I' : 'n' : '_' :  _) s) = False
--        noInjection _                                      = True

-- A list of vertices reachable from a given vertex after one or more steps.
reachable1 :: Graph -> Vertex -> [Vertex]
reachable1 g v = concatMap toList $ dfs g (g ! v)

-- Transitive closure of a graph.
trCl :: Graph -> Graph
trCl g = buildG (bounds g) [(u,v) | u <- vertices g, v <- reachable1 g u]

-- Edge relation of an induced subgraph.
hasEdge :: Graph -> (a -> Maybe Vertex) -> a -> a -> Bool
hasEdge g lookUp x y = case (lookUp x, lookUp y) of
  (Just u, Just v) -> v `elem` (g ! u)
  _                -> False

-- A list of all types which require variable constructors, or a string describing all
-- vacuous binders in the specification.
binderAnalysis :: Spec -> (TId -> TId -> Bool) -> Either String (S.Set TId)
binderAnalysis spec reach =
  if null errors then Right $ S.fromList types else Left $ unlines errors
  where (errors, types) = partitionEithers $ do
          (tp, cs) <- M.toList spec
          c <- cs
          p <- positions c
          b' <- binders p
          b <- getBinders b'
          if any (\x -> reach x b) (getIds (argument p))
            then return $ Right b
            else return $ Left $ "The type " ++ tp ++
                 " contains a vacuous binding of a variable of type " ++ b ++
                 " in constructor " ++ name c ++ "."

sortby :: Eq a => [a] -> [a] -> [a]
sortby order xs = filter (\z -> elem z xs) order

-- Gets a graph, a mapping from vertices to type identifiers,
-- and yields the topological order in equivalence classes rerpresented via type identifiers.
topologicalSort :: Graph -> [TId] -> (Vertex -> TId) -> [[TId]]
topologicalSort g canonicalOrder f =  [sortby canonicalOrder (f <$> toList t) | t <- scc g]

-- Gets a graph (with translation functions) and a set of types with binders,
-- yields for each type a list of types substitution is necessary for.
subordination :: Graph -> [TId] ->(Vertex -> TId) -> (TId -> Maybe Vertex) -> S.Set TId -> TId -> [TId]
subordination g canonicalOrder f f' varTer x =
 sortby canonicalOrder [ f u | u <- vertices g, f u `S.member` varTer, f u == x || maybe False (\v -> u `elem` (g ! v)) (f' x)]

-- Gets a specification, yields a tuple with
-- 1.) the topological sorting or the type identifiers
-- 2.) the necessary substitutions.
--containment :: Spec -> Either String ([[TId]], TId -> [TId])
--containment spec =
--  let
--    (g, keyMap, lookUp) = directContainment spec
--    sorted = topologicalSort g keyMap
--    analysis = binderAnalysis spec $ hasEdge g lookUp
--  in analysis >>= \set ->
--    return (sorted, subordination (trCl g) keyMap lookUp set)

cut :: TId -> TId
cut ('_' : xs) = []
cut (x : xs)   = x : cut xs

buildSignature :: ([TId],[FId], Spec, TId -> [TId]) -> Either String Signature
buildSignature (canonicalOrder, fs, spec, deps) =
  let
    crcs = concatMap (\x -> [(x,y) | y <- deps x]) canonicalOrder
    (g,g', keyMap, lookUp) = directContainment spec crcs
    sorted   = topologicalSort g' canonicalOrder keyMap
    dps = map (\xs -> (xs, concatMap deps xs)) sorted
    analysis = binderAnalysis spec $ hasEdge (trCl g) lookUp
    extend = M.fromList [(x,cut x) | x <- canonicalOrder, not (null (deps x))]
    variants = concatMap (\x -> snd x) dps
  in
    case analysis of -- open sorts
      Right set ->
        let substs = subordination (trCl g) canonicalOrder keyMap lookUp set
            substMap = M.mapWithKey (\tp _ -> substs tp) spec
            arguments = M.mapWithKey (\tp _ -> argOf tp) spec
            argOf tp = case lookUp tp of
              Just v  -> map keyMap $ g ! v
              Nothing -> []
            all = filter (\z -> S.member z set && z `elem` variants) (concatMap fst dps) -- TODO: Upate to be all variants with variable constructor.
            substMap' = M.union substMap (M.fromList [(z ++ "_var", fromJust $ M.lookup z substMap) | z <- all])
            arguments' = M.union arguments (M.fromList [(z ++ "_var",   (fromJust $ M.lookup z arguments)) | z <- all])
      --      updatedspec =  [(x,  fromJust (M.lookup x spec)) | x <- all]
            spec'' = M.union (spec) (M.fromList ([(x ++ "_var", []) | x <- all] ))
            spec' = M.mapWithKey (\k x -> if k `elem` all then (Constructor [] ("In_" ++  k ++ "_var" ) [Position [] (Atom (k ++ "_var"))] : x) else x ) spec'' --  (Constructor [] () ()) : x else x) spec'
            dps' =  concatMap (\(xs, dps) -> let zs = [z | z <- xs, z `elem` all]
                                            in [([z ++ "_var"], z : dps) | z <- zs] ++ [(xs, dps)]) dps
            extend' =  M.union extend (M.fromList [(x ++ "_var", x) | x <- all])
            set' = S.union (S.filter (\z -> not (elem z all)) set) (S.fromList [x ++ "_var" | x <- all])
        in  Right $ Signature spec' substMap' ( {-( map (\x -> (x, [])) -}dps') extend' set' arguments' -- Left $ ("spec': " ++ show spec' ++ "substMap': " ++ show substMap' ++ "dps': " ++ show dps' ++ "extend': " ++ show extend' ++ "open sorts: " ++ show set' ++ "arguments': "++ show arguments')  --
      Left s -> Left s
