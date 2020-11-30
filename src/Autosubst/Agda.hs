{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances  #-}
module Autosubst.Agda where

-- Pretty Printing of Syntax to Agda
import           Autosubst.Syntax
import           Text.PrettyPrint.Leijen


-- AgdaShow Class
class AgdaShow a where
  agdaShow :: a -> Doc

instance AgdaShow String where
  agdaShow = text

-- Generation of tuples accepted by Agda, no parentheses if there is just one component.
cTupled ::  [Doc] -> Doc
cTupled []  = empty
cTupled [x] = x
cTupled xs  = encloseSep lparen rparen (comma <+> empty) xs

agdaPreamble :: Doc
agdaPreamble = text "open import fintype" <$$> text "open import Relation.Binary.PropositionalEquality" <$$> text "open import Function" <$$> empty

-- Agda Primitives.
instance AgdaShow CBinder where
  agdaShow (BinderName s) = parens (agdaShow s <+> text ": _" )
  agdaShow (BinderNameType s t) = if null s then empty else parens $ hsep (map agdaShow s) <+> text ":" <+> agdaShow t
  agdaShow (BinderScopeNameType s t) = if null s then empty else parens $ hsep (map agdaShow s) <+> text ":" <+> agdaShow t
  agdaShow (BinderImplicitName s) = text "{" <+> agdaShow s <+> text "}"
  agdaShow (BinderImplicitNameType s t) = if null s then empty else text "{" <+> hsep (map agdaShow s) <+> text ":" <+> agdaShow t <+> text "}"
  agdaShow (BinderImplicitScopeNameType s t) = if null s then empty else text "{" <+> hsep (map agdaShow s) <+> text ":" <+> agdaShow t <+> text "}"


defBinder :: CBinder -> Doc
defBinder (BinderName s)            = agdaShow s
defBinder (BinderNameType s t)      = hsep (map agdaShow s)
defBinder (BinderScopeNameType s t) = hsep (map agdaShow s)
defBinder (BinderImplicitName s) = text "" <+> agdaShow s <+> text "}"
defBinder (BinderImplicitNameType s t) = hsep (map (\s -> text "{" <+> text s <+> text "}") s)
defBinder (BinderImplicitScopeNameType s t) = hsep (map (\s -> text "{" <+> text s <+> text "}") s)


instance AgdaShow Definition where
  agdaShow (Definition name bs mb (TermAbs _ (TermMatch _ _ eqs))) = agdaShow name <+> text ":" <+> hsep (map agdaShow bs) <+> (text "->" <+> agdaShow mb)
    <$$> vsep (map (\(Equation pat s) -> agdaShow name <+> hsep (map defBinder bs) <+> parens (agdaShow pat) <+> text "=" <+> agdaShow s) eqs)
  agdaShow (Definition name bs mb s) = agdaShow name <+> text ":" <+> hsep (map agdaShow bs) <+> (text "->" <+> agdaShow mb)
   <$$> agdaShow name <+> hsep (map defBinder bs) <+> text "=" <+> agdaShow s

instance AgdaShow Equation where
  agdaShow (Equation pat s) = indent 2 $ agdaShow pat <+> text "->" <+> agdaShow s

instance AgdaShow Fixpoint where
  agdaShow (Fixpoint r bs) = hcat (map agdaShow bs)

deleteLast :: [a] -> [a]
deleteLast []           = []
deleteLast [a]          = []
deleteLast (x : y : xs) = x : (deleteLast (y: xs))

instance AgdaShow FixpointBody where
  agdaShow (FixpointBody name bs ret (TermMatch _ _ eqs)) = agdaShow name <+> text ":" <+> hsep (map agdaShow bs) <+> text "->" <+> agdaShow ret
                                            <$$> vsep (map (\(Equation pat s) -> agdaShow name <+> hsep (map defBinder (deleteLast bs)) <+> (parens $ agdaShow pat) <+> text "=" <+> agdaShow s) eqs)

instance AgdaShow Lemma where
  agdaShow (Lemma name bs mb (ProofExact tm)) = agdaShow (Definition name bs (Just mb) tm)
  agdaShow _ = empty

instance AgdaShow Proof where
  agdaShow (ProofExact tm) = text "exact" <+> parens (agdaShow tm) <> text "."
  agdaShow (ProofString s) = text s

instance AgdaShow Inductive where
  agdaShow (Inductive bs) =
    vsep (map (\(InductiveBody name bs' s cs) ->
        text "data" <+> agdaShow name <+> text ":" <+> (if null bs' then empty else text "forall" <+> hsep (map agdaShow bs') <+> text "->") <+> agdaShow s) bs)
     <$$> empty <$$> vcat (map agdaShow bs)

instance AgdaShow InductiveBody where
  agdaShow (InductiveBody name bs s cs) = hang 2 (text "data" <+> agdaShow name <+> text "where")
      <$$> vsep (map (\(InductiveCtor name mt) -> indent 2 (text name  </> colon <+> hsep (map agdaShow bs) <+> text "->" <+> agdaShow mt)) cs)

instance AgdaShow InductiveCtor where
  agdaShow (InductiveCtor name mt) = indent 2 (text name  </> colon <+> agdaShow mt)

-- TODO: Is this how I should implement it...? If the two last thing have no sense, delete them.
instance AgdaShow MatchItem where
  agdaShow (MatchItem s mt) = agdaShow s

instance AgdaShow a => AgdaShow (Maybe a) where
  agdaShow Nothing  = text "_"
  agdaShow (Just t) = agdaShow t

-- TODO: Check whether this kind of pattern makes sense.
instance AgdaShow Pattern where
  agdaShow (PatCtor s ids) = agdaShow s <+> hsep (map agdaShow ids)
  agdaShow (PatQualId s)   = agdaShow s
  agdaShow s               = text "Implement patterns."

instance AgdaShow Command where
  agdaShow (Arguments s ts) = text ""

instance AgdaShow Sentence where
  agdaShow (SentenceCommand s)    = agdaShow s
  agdaShow (SentenceDefinition s) = agdaShow s
  agdaShow (SentenceInductive s)  = agdaShow s
  agdaShow (SentenceFixpoint s)   = agdaShow s
  agdaShow (SentenceLemma s)      = agdaShow s
  agdaShow _                      = empty

instance AgdaShow Sort where
  agdaShow Prop = text "Set"
  agdaShow Set  = text "Set"
  agdaShow Type = text "Set"

-- TODO: All the same printing?
instance AgdaShow SubstTy where
  agdaShow xs = hsep (map (\x -> case x of
                                                          TermId s -> agdaShow s
                                                          TermSubst s -> agdaShow s
                                                          _ -> parens $ agdaShow x) (sty_terms xs))

agdaShowParens :: Term -> Doc
agdaShowParens (TermId s)    = agdaShow s
agdaShowParens (TermSubst s) = agdaShow s
agdaShowParens s             = parens $ agdaShow s

instance AgdaShow Const where
  agdaShow Some    = text "some"
  agdaShow None    = text "none"
  agdaShow Refl    = text "refl"
  agdaShow Sym     = text "sym"
  agdaShow Trans   = text "trans"
  agdaShow Nat     = text "Nat"
  agdaShow Suc     = text "suc"
  agdaShow Fin     = text "fin"
  agdaShow Id      = text "id"
  agdaShow Comp    = text "funcomp"
  agdaShow Upren   = text "up_ren"
  agdaShow Cons    = text "scons"
  agdaShow VarZero = text "var_zero"
  agdaShow Ap      = text "cong"
  agdaShow Shift   = text "shift"
  agdaShow Fext    = text "funext _ _ "
  agdaShow _       = text "Missing constant."

instance AgdaShow Term where
  agdaShow (TermImp s) = text "@" <> agdaShow s
  agdaShow (Todo s)           = text ("Todo." ++ s)
  agdaShow (TermApp s ts)     = agdaShowParens s <+> hsep (map (\x -> case x of
                                                          TermId s -> agdaShow s
                                                          TermSubst s -> agdaShow s
                                                          _ -> parens $ agdaShow x) ts)
  agdaShow (TermId s)         = agdaShow s
  agdaShow (TermFunction s t) = agdaShow s <+> text "->" <+> agdaShow t
  agdaShow (TermSort s)       = agdaShow s
  agdaShow TermUnderscore   = text "_"
  agdaShow (TermForall bs t)  = text "forall" <+> hsep (map agdaShow bs) <+> text "->" <+> agdaShow t
  agdaShow (TermAbs bs t)     = text "\\" <+> hsep (map agdaShow bs) <+> text "->" <+> agdaShow t
  agdaShow (TermLet s t u)    = text "let" <+> agdaShow t <+> text ":=" <+> agdaShow s <+> text "in" <+> agdaShow u
  agdaShow (Tuple s)          = cTupled (map agdaShow s)
  agdaShow (TupleTy s)        = encloseSep empty empty (text " * ") (map (parens . agdaShow) s)
  agdaShow (TermMatch m _ s) = text "case" <+> agdaShow m <+> text "of" <$$> vcat (map agdaShow s) <$$> text "end" -- TODO: Version with Return clause
  agdaShow (TermAnd s)  = encloseSep empty empty (text " /\\") (map (parens . agdaShow) s)
  agdaShow (TermEq s t) = agdaShow s <+> text "≡" <+> agdaShow t
  agdaShow (TermSubst s) = agdaShow s
  agdaShow (TermVar s) = agdaShow s
  agdaShow (TermConst c) = agdaShow c
  agdaShow s                  = text "TODO"
