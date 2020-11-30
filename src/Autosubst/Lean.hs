{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances  #-}
module Autosubst.Lean where

-- Pretty Printing of Syntax to Coq
import           Autosubst.Syntax
import           Text.PrettyPrint.Leijen

-- TODO: More documentation what is what.


-- LeanShow Class
class LeanShow a where
  leanShow :: a -> Doc

instance LeanShow String where
  leanShow = text

-- Generation of tuples accepted by Coq, no parentheses if there is just one component.
cTupled ::  [Doc] -> Doc
cTupled []  = empty
cTupled [x] = x
cTupled xs  = encloseSep lparen rparen (comma <+> empty) xs

leanPreamble :: Doc
leanPreamble = text "Require Export fintype."

-- Coq Primitives.
instance LeanShow CBinder where
  leanShow (BinderName s) = leanShow s
  leanShow (BinderNameType s t) = parens $ hsep (map leanShow s) <+> text ":" <+> leanShow t
  leanShow (BinderImplicitName s) = text "{" <+> leanShow s <+> text "}"
  leanShow (BinderImplicitNameType s t) = text "{" <+> hsep (map leanShow s) <+> text ":" <+> leanShow t <+> text "}"

instance LeanShow Definition where
  leanShow (Definition name bs mb s) = text "Definition" <+> leanShow name <+> hsep (map leanShow bs) <+> (text ":" <+> leanShow mb) <+> text ":="
                                        <$$> indent 2 (leanShow s) <> text "."

instance LeanShow Equation where
  leanShow (Equation pat s) = text "|" <+> leanShow pat <+> text "=>" <+> leanShow s

instance LeanShow Fixpoint where
  leanShow (Fixpoint r bs) =  text "Fixpoint"
    <+> hcat (punctuate (line <> text " with ") (map (nest 2 . leanShow) bs)) <> dot

instance LeanShow FixpointBody where
  leanShow (FixpointBody name bs ret s) = leanShow name <+> hsep (map leanShow bs) <+> text ":" <+> leanShow ret
                                            <+> text ":=" <$$> indent 2 (leanShow s)

instance LeanShow Lemma where
  leanShow (Lemma name bs mb p) = text "Lemma" <+> leanShow name <+> hsep (map leanShow bs) <+> (text ":" <+> leanShow mb) <+> text "."
                                        <$$> text "Proof." <+>  leanShow p <+> text "Qed."

instance LeanShow Proof where
  leanShow (ProofExact tm) = text "exact" <+> parens (leanShow tm) <> text "."
  leanShow (ProofString s) = text s

instance LeanShow Inductive where
  leanShow (Inductive bs) = text "Inductive"
    <+> hcat (punctuate (line <> text " with ") (map (nest 2 . leanShow ) bs)) <> dot

instance LeanShow InductiveBody where
  leanShow (InductiveBody name bs s cs) = hang 2 (leanShow name </> hsep (map leanShow bs) </> colon <+> leanShow s <+> text ":=") <$$> vsep (map leanShow cs)

instance LeanShow InductiveCtor where
  leanShow (InductiveCtor name mt) = text "| " <> text name </> colon <+> leanShow mt

-- TODO: Is this how I should implement it...? If the two last thing have no sense, delete them.
instance LeanShow MatchItem where
  leanShow (MatchItem s mt) = leanShow s

instance LeanShow a => LeanShow (Maybe a) where
  leanShow Nothing  = text "_"
  leanShow (Just t) = leanShow t

-- TODO: Check whether this kind of pattern makes sense.
instance LeanShow Pattern where
  leanShow (PatCtor s ids) = leanShow s <+> hsep (map leanShow ids)
  leanShow (PatQualId s)   = leanShow s
  leanShow s               = text "Implement patterns."

instance LeanShow Sentence where
  leanShow (SentenceDefinition s) = leanShow s
  leanShow (SentenceInductive s)  = leanShow s
  leanShow (SentenceFixpoint s)   = leanShow s
  leanShow (SentenceLemma s)      = leanShow s
  leanShow _                      = text "TODO: Other sentence forms."

instance LeanShow Sort where
  leanShow Prop = text "Prop"
  leanShow Set  = text "Set"
  leanShow Type = text "Type"

-- TODO: All the same printing?
instance LeanShow SubstTy where
  leanShow xs = hsep (map (\x -> case x of
                                                          TermId s -> leanShow s
                                                          TermSubst s -> leanShow s
                                                          _ -> parens $ leanShow x) (sty_terms xs))

leanShowParens :: Term -> Doc
leanShowParens (TermId s)    = leanShow s
leanShowParens (TermSubst s) = leanShow s
leanShowParens s             = parens $ leanShow s

instance LeanShow Term where
  leanShow (TermImp s) = text "@" <> leanShow s
  leanShow (Todo s)           = text ("Todo." ++ s)
  leanShow (TermApp s ts)     = leanShowParens s <+> hsep (map (\x -> case x of
                                                          TermId s -> leanShow s
                                                          TermSubst s -> leanShow s
                                                          _ -> parens $ leanShow x) ts)
  leanShow (TermId s)         = leanShow s
  leanShow (TermFunction s t) = leanShow s <+> text "->" <+> leanShow t
  leanShow (TermSort s)       = leanShow s
  leanShow TermUnderscore   = text "_"
  leanShow (TermForall bs t)  = text "forall" <+> hsep (map leanShow bs) <> text "," <+> leanShow t
  leanShow (TermAbs bs t)     = text "fun" <+> hsep (map leanShow bs) <+> text "=>" <+> leanShow t
  leanShow (TermLet s t u)    = text "let" <+> leanShow t <+> text ":=" <+> leanShow s <+> text "in" <+> leanShow u
  leanShow (Tuple s)          = cTupled (map leanShow s)
  leanShow (TupleTy s)        = encloseSep empty empty (text " * ") (map (parens . leanShow) s)
  leanShow (TermMatch m _ s) = text "match" <+> leanShow m <+> text "with" <$$> vcat (map leanShow s) <$$> text "end" -- TODO: Version with Return clause
  leanShow (TermAnd s)  = encloseSep empty empty (text " /\\") (map (parens . leanShow) s)
  leanShow (TermEq s t) = leanShow s <+> text "=" <+> leanShow t
  leanShow (TermSubst s) = leanShow s
  leanShow s                  = text "TODO"
