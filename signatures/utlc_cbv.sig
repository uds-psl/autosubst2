-- CBV-Version of UTLC
nf : Type
ne: Type

app : ne -> nf -> ne
val : ne -> nf
lam : (ne -> nf) -> nf

