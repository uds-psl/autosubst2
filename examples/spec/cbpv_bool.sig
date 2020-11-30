-- Signature for Call-by-Push-Value with boolean values

-- the types
tm : Type
vl : Type

-- the constructors for tm
lam : (vl -> tm) -> tm
app  : tm -> vl -> tm
creturn: vl -> tm
clet: tm -> (vl -> tm) -> tm
force: vl -> tm
cif : vl -> tm -> tm -> tm

-- the constructors for vl
true: vl
false: vl
thunk : tm -> vl


-- the types for CBN
Tm : Type 

Lam : (Tm -> Tm) -> Tm 
App : Tm -> Tm -> Tm 
If : Tm -> Tm -> Tm -> Tm 
True : Tm 
False : Tm 
