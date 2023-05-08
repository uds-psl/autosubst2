{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Autosubst.Names where

import           Autosubst.GenM
import           Autosubst.Syntax
import           Autosubst.Types
import           Data.List        as L

-- Contains the names of the later functions / inductive datatypes etc.

-- TODO: Sort.

-- Separation symbol
sep :: String
sep = "_"

-- Variable constructors
var_ :: TId -> String
var_ x = "var" ++ sep ++ x

constructor_ :: TId -> String
constructor_ c = c

-- Name for toVarRen functions
toVarRen_ :: TId -> String
toVarRen_ x = "toVarRen" ++ sep ++ x

-- Name of types for renaming/substitutions
renTy_ :: TId -> String
renTy_ x = "renTy" ++ sep ++ x

substTy_ :: TId -> String
substTy_ x = "substTy" ++ sep ++ x

ren_ :: TId -> String
ren_ x = "ren" ++ sep ++ x

-- Name for Casts
castRen_ :: TId -> TId -> String
castRen_ x y = "castRen" ++ sep ++ x ++ sep ++ y

-- Up Functions
upRen_ :: Binder -> TId -> String
upRen_  (Single x) y       = "upRen" ++ sep ++ x ++ sep ++ y
upRen_  (BinderList m x) y = "upRenList" ++ sep ++ x ++ sep ++ y 

-- Definition of Substitution
cast_ :: TId -> TId -> String
cast_ x y = "cast" ++ sep ++ x ++ sep ++ y

toVar_ :: TId -> String
toVar_ x = "toVar" ++ sep ++ x

up_ ::  Binder -> TId -> String
up_ (Single x) y       = "up" ++ sep ++ x ++ sep ++ y
up_ (BinderList m x) y = "upList" ++ sep ++ x ++ sep ++ y 

subst_ :: TId -> String
subst_ x = "subst" ++ sep ++ x

substtc_ :: TId -> String
substtc_ x = "Subst" ++ sep ++ x

rentc_ :: TId -> String
rentc_ x = "Ren" ++ sep ++ x

vartc_ :: TId -> String
vartc_ x = "VarInstance" ++ sep ++ x


-- Name for predicate that two substitutions are eequivalent
eqRen_ :: TId -> String
eqRen_ x = "eqRen" ++ sep ++ x

eqSubst_ :: TId -> String
eqSubst_ x = "eqSubst" ++ sep ++ x

-- Lifting from x to y on component z
upId_ :: Binder -> TId -> String
upId_ (Single x) y       = "upId" ++ sep ++ x ++ sep ++ y
upId_ (BinderList p x) y = "upIdList" ++ sep ++ x ++ sep ++ y -- ++ " " ++ p

idSubst_ :: TId -> String
idSubst_ x = "idSubst" ++ sep ++ x

congr_ :: TId -> String
congr_ c = "congr" ++ sep ++ c

up_ren_ren_ = "up_ren_ren"

up_ren_renName_ :: Binder -> TId -> String
up_ren_renName_ (Single x) y       = "up_ren_ren" ++ sep ++ x ++ sep ++ y
up_ren_renName_ (BinderList p x) y = "up_ren_ren_list" ++ sep ++ x ++ sep ++ y

up_ren_subst_ :: Binder -> TId -> String
up_ren_subst_ (Single x) y       = "up_ren_subst" ++ sep ++ x ++ sep ++ y
up_ren_subst_ (BinderList p x) y = "up_ren_subst_list" ++ sep ++ x ++ sep ++ y -- ++ " " ++ p

up_subst_ren_ :: Binder -> TId -> String
up_subst_ren_ (Single x) y       = "up_subst_ren" ++ sep ++ x ++ sep ++ y
up_subst_ren_ (BinderList p x) y = "up_subst_ren_list" ++ sep ++ x ++ sep ++ y -- ++ " " ++ p


up_subst_subst_ :: Binder -> TId -> String
up_subst_subst_ (Single x) y = "up_subst_subst" ++ sep ++ x ++ sep ++ y
up_subst_subst_ (BinderList p x) y = "up_subst_subst_list" ++ sep ++ x ++ sep ++ y -- ++ " " ++ p

rinstInstFun_ :: TId -> String
rinstInstFun_ x = "rinstInst" ++ sep ++ x

rinstInst_ :: TId -> String
rinstInst_ x = "rinst_inst" ++ sep ++ x

up_rinstInst_ :: Binder -> TId -> String
up_rinstInst_ (Single x) y       = "rinstInst_up" ++ sep ++ x ++ sep ++ y
up_rinstInst_ (BinderList p x) y = "rinstInst_up_list" ++ sep ++ x ++ sep ++ y -- ++ " " ++ p

upExtRen_ :: Binder -> TId -> String
upExtRen_ (Single x) y       = "upExtRen" ++ sep ++ x ++ sep ++ y
upExtRen_ (BinderList p x) y = "upExtRen_list" ++ sep ++ x ++ sep ++ y -- ++ " " ++ p

upExt_ :: Binder -> TId -> String
upExt_ (Single x) y       = "upExt" ++ sep ++ x ++ sep ++ y
upExt_ (BinderList p x) y = "upExt_list" ++ sep ++ x ++ sep ++ y -- ++ " " ++ p

ext_ :: TId -> String
ext_ x = "ext" ++ sep ++ x

extRen_ :: TId -> String
extRen_ x = "extRen" ++ sep ++ x

compRenRen_ :: TId -> String
compRenRen_ x = "compRenRen" ++ sep ++ x

compRenSubst_ :: TId -> String
compRenSubst_ x = "compRenSubst" ++ sep ++ x

compSubstRen_ :: TId -> String
compSubstRen_ x = "compSubstRen" ++ sep ++ x

compSubstSubst_ :: TId -> String
compSubstSubst_ x = "compSubstSubst" ++ sep ++ x

lidComp_ :: TId -> String
lidComp_ x = "lidComp" ++ sep ++ x

-- Composable Syntax
type_ :: String -> String -> String
type_ x y = x ++ "_" ++ y

in_ :: String -> String -> String
in_ x y = "In" ++ "_" ++ x ++ "_" ++ y

-- map names
funname_ :: TId -> String
funname_ f = f

map_ :: FId -> [Term] -> Term
map_ f ts = idApp (f ++ "_map") ts

mapId_ :: FId -> [Term] -> Term
mapId_ f ts = idApp (f ++ "_id") ts

mapComp_ :: FId -> [Term] -> Term
mapComp_ f ts = idApp (f ++ "_comp") ts

mapExt_ :: FId -> [Term] -> Term
mapExt_ f ts = idApp (f ++ "_ext") ts


-- Successor function for the types of scoped terms
upRen_p_ :: String 
upRen_p_ = "upRen_p"

plus_ :: TId -> Term -> Term 
plus_ m t = idApp (m ++ " +") [t]

up_ren_ :: TId -> Binder -> Term -> Term
up_ren_ y (Single x) xi  =  if (y == x) then TermApp (TermConst Upren) [xi] else xi
up_ren_ y (BinderList m x) xi =  if (y == x) then idApp upRen_p_ [TermId m, xi] else xi

succ_ ::   Term -> TId -> Binder -> Term
succ_ n z (Single x) = if (z == x) then TermApp (TermConst Suc) [n] else n
succ_ n z (BinderList m x) = if (z == x) then plus_ m n else n


varFtSort :: TId -> String 
varFtSort x = x ++ "_var"

shift_p_ :: String 
shift_p_ = "shift_p"


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

retract_ :: String 
retract_ = "retract"

buildRetract_ :: String 
buildRetract_ = "Build_retract"

retractId_ :: TId -> String 
retractId_ x = "retract_" ++ x

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
ors []       = false_
ors [x]      = x
ors (x : xs) = idApp "or" [x, ors xs]

orPattern :: Int -> Term -> [Term]
orPattern 0 _ = []
orPattern 1 s = [s]
orPattern n s = (idApp "or_introl" [s]) : map (\x -> idApp "or_intror" [x]) (orPattern (n-1) s)

false_ :: Term 
false_ = TermId "False"

posExtend_ :: TId -> TId -> GenM TId
posExtend_ x cname = do
  x' <- extend_ x
  return $ if (x == x') then cname else (smart_ cname)

emptyT :: TId -> GenM [Term]
emptyT x = return []

ren_var_ :: TId -> String
ren_var_ x = "ren_var_" ++ x

retract_ren_ :: TId -> String
retract_ren_ x = "retract_ren_" ++ x

retract_subst_ :: TId -> String
retract_subst_ x = "retract_subst_" ++ x

scons_p_eta_ :: Term -> Term ->  Term ->  Term
scons_p_eta_ h f g = idApp "scons_p_eta" [h, f, g]

up_ren_ren_p_ :: String 
up_ren_ren_p_ = "up_ren_ren_p" 

renRen_ :: TId -> String 
renRen_ x = "renRen_" ++ x

renRen'_ :: TId -> String 
renRen'_ x = "renRen'_" ++ x

scons_p_comp' :: Term -> Term
scons_p_comp' x = idApp "scons_p_comp'" [TermUnderscore, TermUnderscore, TermUnderscore, x]

scons_p_tail' :: Term -> Term
scons_p_tail' x = idApp "scons_p_tail'" [TermUnderscore, TermUnderscore, x]

scons_p_head' :: Term -> Term
scons_p_head' x = idApp "scons_p_head'" [ TermUnderscore, TermUnderscore, x]

scons_p_congr_ :: Term -> Term -> Term
scons_p_congr_ s t = idApp "scons_p_congr" [t,s]


-- "compRen_" ++ x, "renCom_" ++ x, "scons_p_head", "scons_p_comp", "zero_p", "compComp_"

-- "varL_" ++ x, "varLRen_" ++ x, "instId_" ++ x, +rinstInst ++ x, "rinstId_" ++ x

