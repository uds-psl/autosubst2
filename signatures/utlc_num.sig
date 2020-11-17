tm: Type
nat : Type

app : tm -> tm -> tm
lam : (tm -> tm) -> tm

const : nat -> tm 
Plus : tm -> tm -> tm


