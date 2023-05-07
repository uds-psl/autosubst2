module Autosubst.Signature
  ( buildSignature
  ) where

import           Data.Array      (bounds, (!))
import           Data.Either     (partitionEithers)
import           Data.Foldable   (toList)
import           Data.Graph      as G
import           Data.List       
import qualified Data.Map        as M
import           Data.Maybe
import qualified Data.Set        as S
import qualified Data.Tree       as T

import           Autosubst.GenM
import           Autosubst.Names
import           Autosubst.Types

-- Yields a graph from the specification and a list of injections. Nodes and keys are of type TId.
-- Yields two graphs: One with, one without the injections. 
-- We need the graph without injections because otherwise features and the dpSorts would be a big mutually inductive sort.
-- v2id and id2v map vertices to identifers and vice versa, if available.
directContainment :: Spec -> [(TId,TId)] -> (Graph, Graph, Vertex -> TId, TId -> Maybe Vertex)
directContainment spec inj = (g,gNoInj,v2id,id2v)
  where getArgs xs   = nub $ concat $ concatMap (map (argSorts . argument) . positions) xs -- Get all successors of a list of ids.
        (g,v2e,id2v) = graphFromEdges [(k,k,getArgs a) | (k,a) <- M.toList spec] -- Graph generated from arguments
        getArgsNoInj k xs   = filter (\m -> (k, m) `notElem` inj) (getArgs xs) -- Remove all injections
        (gNoInj, _, _) = graphFromEdges [(k,k,getArgsNoInj k a) | (k,a) <- M.toList spec] -- Graph with edges without the injections
        v2id v       = case v2e v of (id,_,_) -> id

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
          b <- binderSorts b'
          if any (`reach` b) (argSorts (argument p))
            then return $ Right b
            else return $ Left $ "The type " ++ tp ++
                 " contains a vacuous binding of a variable of type " ++ b ++
                 " in constructor " ++ name c ++ "."

-- Gets a graph, a mapping from vertices to type identifiers,
-- and yields the topological order in equivalence classes rerpresented via type identifiers.
-- TOOD: Get rid of the feature if it is not used at all? -- I mean, it is used to define it in its own files. 
topologicalSort :: Graph -> [TId] -> (Vertex -> TId) -> [([TId], Maybe String)]
topologicalSort g canonicalOrder f = map (\x -> (x, getFeature (head x))) [sortby canonicalOrder (f <$> toList t) | t <- scc g]

-- Gets a graph (with translation functions) and a openSet of types with binders,
-- yields for each type a list of types substitution is necessary for.
subordination :: Graph -> [TId] ->(Vertex -> TId) -> (TId -> Maybe Vertex) -> S.Set TId -> TId -> [TId]
subordination g canonicalOrder f f' varTer x =
 sortby canonicalOrder [ f u | u <- vertices g, f u `S.member` varTer, f u == x || maybe False (\v -> u `elem` (g ! v)) (f' x)]


-- Constructs the signature which is later used throughout the code generation
-- Gets a parser specification, yields a tuple with
-- 1.) the topological sorting or the type identifiers
-- 2.) the necessary substitutions.
buildSignature :: ParserSpec -> Either String Signature
buildSignature (canonicalOrder, fs, spec, injf, mvariants) =
  let
    inj = concatMap (\x -> [(x,y) | y <- injf x]) canonicalOrder -- yields injections as list, sorted by the canonical order
    (g,gNoInj, keyMap, lookUp) = directContainment spec inj -- gets both the graph with and without injections, where gNoInj is the one without injections 
    analysis = binderAnalysis spec $ hasEdge (trCl g) lookUp -- run the binder analysis on the whole graph
  in
    case analysis of -- open sorts
      Right openSet ->
        let -- Order and variable sorts 
            sorted  = topologicalSort gNoInj canonicalOrder keyMap -- sorts the graph without injections according to its topological order 
            getinj xs = sortby canonicalOrder $ concatMap injf (concatMap (\z -> z : fromMaybe [] (M.lookup z arguments)) xs)
            components = map (\(xs,f) -> (xs, getinj xs, f)) sorted -- adds in dependencies on main sorts into the graph 
            dpSorts = concatMap (\(x, y, z) -> y) components -- all sorts on which another component depends on, e.g. exp_lam would depend on exp
            dpVarSorts = filter (\z -> S.member z openSet && z `elem` dpSorts) canonicalOrder -- All dpSorts with variable constructor.
             -- Subst maps  
            substs = subordination (trCl g) canonicalOrder keyMap lookUp openSet
            substMap = M.mapWithKey (\tp _ -> substs tp) spec
            -- Injections, TODO: This should be easier, if the parser would just add everything to itself.
            extensions = M.fromList [(x, head (injf x)) | x <- canonicalOrder, not (null (injf x))] -- KS
            -- Argument maps 
            argOf tp = case lookUp tp of
              Just v  -> map keyMap $ g ! v
              Nothing -> []
            arguments = M.mapWithKey (\tp _ -> argOf tp) spec
            -- Add variable components into all definitions
            componentsVar =  concatMap (\(xs, dps, m) -> let zs = [z | z <- xs, z `elem` dpVarSorts] -- all elements that are in the component needed now, and that need a variable constructor
                                                      in [([varFtSort z], zs ++ dps, Just (varFtSort z)) | z <- zs] ++ [(xs, dps, m)])
                                                      components
            extensionsVar =  M.union extensions (M.fromList [(varFtSort x, x) | x <- dpVarSorts])
            argumentsVar = M.union arguments (M.fromList [(varFtSort z,  []) | z <- dpVarSorts]) 
            substMapVar = M.union substMap (M.fromList [(varFtSort z, fromJust $ M.lookup z substMap) | z <- dpVarSorts]) -- Add same substitution set as for the main sort
            openSetVar = S.union (S.filter (\z -> not (elem z dpVarSorts)) openSet) (S.fromList [varFtSort x | x <- dpVarSorts]) -- New set of open sorts: Remove them from non-variable features, and push them into the variable feature components
            varFtSpec = M.fromList ([(varFtSort x, []) | x <- dpVarSorts]) -- add empty list of constructors for all variable feature sorts
            specVar = M.mapWithKey (\k x -> if k `elem` dpVarSorts then (Constructor [] (in_ k "var") [Position [] (Atom (varFtSort k))] : x) else x ) (M.union spec varFtSpec)
            variantsVar = map (\(x,dps) -> (x, dps ++ [varFtSort z | z <- dpVarSorts] )) mvariants -- Add the variable feature to all dpSorts
        in  Right $ Signature specVar substMapVar componentsVar extensionsVar openSetVar argumentsVar variantsVar 
      Left s -> Left s