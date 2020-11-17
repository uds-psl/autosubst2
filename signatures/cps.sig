typ : Type
imp   : typ -> typ -> typ    
and    : typ -> typ -> typ    
unit : typ

exp : Type
val : Type

value  : val -> exp

lam    : (val -> exp) -> val
app    : exp -> exp -> exp
mkpair : exp -> exp -> exp
pair   : val -> val -> val
fst    : exp -> exp
snd    : exp -> exp
one      : val
letC    : exp -> (val -> exp) -> exp
