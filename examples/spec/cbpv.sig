-- Call-by-Push-Value
valtype : Type
comptype : Type
value : Type
comp : Type
bool : Type


zero: valtype
one: valtype
U: comptype -> valtype
Sigma: valtype -> valtype -> valtype
cross: valtype -> valtype -> valtype


cone: comptype
F: valtype -> comptype
Pi: comptype -> comptype -> comptype
arrow: valtype -> comptype -> comptype


u: value
pair: value -> value -> value
inj: bool -> value -> value
thunk: comp -> value


cu: comp
force: value -> comp
lambda: (value -> comp) -> comp
app: comp -> value -> comp
tuple: comp -> comp -> comp
ret: value -> comp
letin: comp -> (value -> comp) -> comp
proj: bool -> comp -> comp
caseZ: value -> comp
caseS: value -> (value -> comp) -> (value -> comp) -> comp
caseP: value -> (value -> value -> comp) -> comp.
