module Autosubst.GenDot
  ( genDot
  , printDot
  , ulc
  , sysFw
  ) where

import           Control.Monad                       (forM)
import           Data.GraphViz.Attributes.Colors.X11
import           Data.GraphViz.Attributes.Complete
import qualified Data.GraphViz.Attributes.HTML       as H
import           Data.GraphViz.Types                 (printDotGraph)
import           Data.GraphViz.Types.Canonical
import           Data.List                           (intercalate, partition)
import           Data.String                         (fromString)
import qualified Data.Text.Lazy                      as T

import           Autosubst.GenM
import           Autosubst.Types

-- Debugging
import qualified Data.Map                            as M
ulc :: Spec
ulc = M.fromList [("tm", [app, lam])]
  where tm  = Position [] (Atom "tm")
        abs = Position [Single "tm"] (Atom "tm")
        app = Constructor []  "app" [tm, tm]
        lam = Constructor []  "lam" [abs]

--
-- kind, ty, tm : Type.
--
-- star : kind.
-- karrow : kind -> kind -> kind.
--
-- arrow : ty -> ty -> ty
-- ty_forall : kind -> (ty -> ty) -> ty
--
-- app  : tm -> tm -> tm
-- lam  : ty -> (tm -> tm) -> tm
-- tapp : tm -> ty -> tm
-- tlam : kind -> (ty -> tm) -> tm
--
sysFw :: Spec
sysFw = M.fromList [("kind", [star,karrow]), ("ty", [arrow,forall]), ("tm", [app,lam,tapp,tlam])]
  where pKind  = Position [] (Atom "kind")
        pType  = Position [] (Atom "ty")
        pTm    = Position [] (Atom "tm")
        pAll   = Position [Single "ty"] (Atom "ty")
        pTAbs  = Position [Single "ty"] (Atom "tm")
        pAbs   = Position [Single "tm"] (Atom "tm")
        star   = Constructor []  "star" []
        karrow = Constructor []  "karrow" [pKind, pKind]
        arrow  = Constructor []  "arrow" [pType, pType]
        forall = Constructor []  "ty_forall" [pKind, pAll]
        app    = Constructor []  "app" [pTm, pTm]
        lam    = Constructor []  "lam" [pType, pAbs]
        tapp   = Constructor []  "tapp" [pTm, pType]
        tlam   = Constructor []  "tlam" [pKind, pTAbs]

-- Format graphs with several components.

data Part = Part
  { componentNodes :: [DotNode Id]
  , componentEdges :: [DotEdge Id]
  } deriving (Show)

trivial :: Part -> Bool
trivial c = length (componentNodes c) <= 1

partSubGraph :: Part -> DotSubGraph Id
partSubGraph c = DotSG True Nothing statements
  where statements = DotStmts
          { attrStmts = []
          , subGraphs = []
          , nodeStmts = componentNodes c
          , edgeStmts = componentEdges c
          }

defaultNodeAttributes :: Attributes
defaultNodeAttributes = [Shape PlainText, FontSize 8.0]

digraph :: [Part] -> DotGraph Id
digraph components = DotGraph True True Nothing statements
  where statements = DotStmts
          { attrStmts = [NodeAttrs defaultNodeAttributes]
          , subGraphs = sccs
          , nodeStmts = nodes
          , edgeStmts = edges
          }
        (singles, multis) = partition trivial components
        sccs  = map partSubGraph multis
        nodes = concatMap componentNodes singles
        edges = concatMap componentEdges singles

-- Format specifications

slight :: H.Text -> H.Text
slight [] = []
slight ts = [H.Font [H.Color $ X11Color Gray] ts]

strong :: H.Text -> H.Text
strong ts = [H.Font [H.Color $ X11Color White] ts]

str :: String -> H.TextItem
str = H.Str . fromString

formatList :: [Id] -> H.Text
formatList  [] = []
formatList ids = [str $ "[" ++ intercalate "," ids ++ "]"]

formatType :: TId -> SigM H.Text
formatType tp = do
  open <- isOpen tp
  subs <- substOf tp
  let label = slight $ [if open then str "open " else str "closed "]
  return $ label ++ strong [str tp] ++ slight (formatList subs)

maybeParens :: Bool -> String -> String
maybeParens  True s = "(" ++ s ++ ")"
maybeParens False s = s

genBinders :: Binder -> String
genBinders (Single x) = x
genBinder (BinderList p x) = "<" ++ p ++ ", " ++ x ++ ">"

genArgument :: Argument -> String
genArgument (Atom x) = x
genArgument (FunApp x y z) = x ++ " " ++ y ++ (if (null y) then "" else " ") ++ intercalate "," (map genArgument z)


genPositions :: TId -> [Position] -> String
genPositions tp ps = formatTp (map genPosition ps) tp
  where genPosition (Position bs dst) = maybeParens (not $ null bs) $ formatTp (map genBinders bs) (genArgument dst)
        formatTp bs a = intercalate " → " (bs ++ [a])

td :: H.Attributes -> String -> H.Cell
td as s = H.LabelCell as $ H.Text [str s]

genConstructor :: TId -> Constructor -> H.Row
genConstructor tp c = H.Cells [nameCell, sepCell, typeCell]
  where nameCell = td [H.Align H.HRight] $ name c
        sepCell  = td [H.Align H.HCenter] ":"
        typeCell = td [H.Align H.HLeft] $ genPositions tp $ positions c

genHeader :: TId -> SigM H.Row
genHeader tp = do
  formatted <- formatType tp
  let attrs = [H.Align H.HCenter, H.ColSpan 3, H.BGColor $ X11Color Black]
  return $ H.Cells [H.LabelCell attrs $ H.Text formatted]

genNode :: TId -> SigM (DotNode Id)
genNode tp = do
  tableHeader <- genHeader tp
  cs <- constructors tp
  let rows = tableHeader : map (genConstructor tp) cs
      tableAttributes = [H.Border 1, H.CellBorder 0, H.CellSpacing 1]
      table = H.HTable Nothing tableAttributes rows
      attributes = [Label $ HtmlLabel $ H.Table $ table]
  return $ DotNode tp attributes

genComponent :: ([TId], [TId]) -> SigM Part
genComponent (tps, _) = do
  nodes <- mapM genNode tps
  edges <- concat <$> forM tps (\src -> do
    dsts <- arguments src
    return [DotEdge src dst [] | dst <- dsts])
  return $ Part nodes edges

-- Top level functions

genDot :: SigM (DotGraph Id)
genDot = digraph <$> (mapM genComponent =<< components)

printDot :: SigM String
printDot = T.unpack . printDotGraph <$> genDot
