-- Signature for System F

-- the types
ty : Type
tm : Type

-- the constructors for ty
arr : ty -> ty -> ty
all : (ty -> ty) -> ty

-- the constructors for tm
app  : tm -> tm -> tm
lam  : ty -> (tm -> tm) -> tm
tapp : tm -> ty -> tm
tlam : (ty -> tm) -> tm
