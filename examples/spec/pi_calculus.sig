-- Signature for the Pi Calculus 

-- the types
chan : Type
proc : Type

-- processes 
par : proc -> proc -> proc 
input : chan -> (chan -> proc) -> proc 
output : chan -> chan -> proc -> proc 
repl : proc -> proc 
restr : (chan -> proc) -> proc 
nil : proc
