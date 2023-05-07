-- Signature for System F

-- the types
chan : Type
proc : Type

-- the constructors for proc
Nil : proc 
Bang : proc -> proc 
Res : (chan -> proc) -> proc 
Par : proc -> proc -> proc 
In : chan -> (chan -> proc) -> proc 
Out : chan -> chan -> proc -> proc


