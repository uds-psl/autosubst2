cod : Functor

term  : Type
form  : Type

Func (f : nat) : "cod (fin f)" (term) -> term
Fal : form
Pred (p : nat) : "cod (fin p)" (term) -> form
Impl : form -> form -> form
Conj : form -> form -> form
Disj : form -> form -> form
All  : (term -> form) -> form
Ex   : (term -> form) -> form
