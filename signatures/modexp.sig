-- Main types
ty : Type
exp : Type
bool : Type
nat : Type

-- Feature for lambda terms
begin lam
arr : ty -> ty -> ty

ab : ty -> (exp -> exp) -> exp
app : exp -> exp -> exp
end lam

-- Feature for bool terms
begin bool
boolTy : ty

constBool : bool -> exp
If : exp -> exp -> exp -> exp

end bool

begin arith

natTy : ty
plus : exp -> exp -> exp
constNat : nat -> exp

end arith

begin case

natCase : exp -> exp -> (exp -> exp) -> exp

end case

begin or

sum : ty -> ty -> ty

sumCase : exp -> (exp -> exp) -> (exp -> exp) -> exp
inl : exp -> exp
inr : exp -> exp

end or

arithlam := lam :+: arith
onlybool := bool