-- System L

tm : Type
stack : Type
cmd : Type


lam : (tm -> tm) -> tm 
mu : (stack -> cmd) -> tm 

cons : tm -> stack -> stack 

cut : tm -> stack -> cmd

