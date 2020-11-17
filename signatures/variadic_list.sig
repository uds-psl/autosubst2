tm: Type

list : Functor

app : tm -> "list" (tm) -> tm
lam (p: nat) : ((<p,tm>) -> tm) -> tm
