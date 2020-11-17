-- Call-by-Push-Value with a recursive let, uses variadic syntax

value : Type
comp : Type
nat : Type

const : nat -> value
thunk: comp -> value

force: value -> comp
letrec (p : nat) : (<p,value>  -> "cod (fin p)" (comp)) -> (<p,value> -> comp) -> comp
prd : value -> comp
seq : comp -> (value -> comp) -> comp
app: comp -> value -> comp
op : value -> value -> value
if0 : value -> comp -> comp -> comp
