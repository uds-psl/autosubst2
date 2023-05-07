{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances  #-}
module Autosubst.PrintScoped where

-- Pretty Printing of Syntax to scoped Coq Code
import           Autosubst.Syntax
import           Text.PrettyPrint.Leijen

-- CoqShow Type Class
class CoqShow a where
  coqShow :: a -> Doc

instance CoqShow String where
  coqShow = text

coqPreamble :: Doc
coqPreamble = coqShow (SentenceRequireExport ["fintype"]) 

-- Printing of constants
instance CoqShow Const where
  coqShow Some    = text "Some"
  coqShow None    = text "None"
  coqShow Refl    = text "eq_refl"
  coqShow Sym     = text "eq_sym"
  coqShow Trans   = text "eq_trans"
  coqShow Nat     = text "nat"
  coqShow Suc     = text "S"
  coqShow Fin     = text "fin"
  coqShow Id      = text "id"
  coqShow Comp    = text "funcomp"
  coqShow Upren   = text "up_ren"
  coqShow Cons    = text "scons"
  coqShow VarZero = text "var_zero"
  coqShow Ap      = text "ap"
  coqShow Shift = text "shift"
  coqShow Fext = text "FunctionalExtensionality.functional_extensionality _ _ "

-- Generation of tuples accepted by Coq, no parentheses if there is just one component.
cTupled ::  [Doc] -> Doc
cTupled []  = empty
cTupled [x] = x
cTupled xs  = encloseSep lparen rparen (comma <+> empty) xs

-- Coq Primitives.
instance CoqShow Sort where
  coqShow Prop = text "Prop"
  coqShow Set  = text "Set"
  coqShow Type = text "Type"

instance CoqShow CBinder where
  coqShow (BinderName s) = coqShow s
  coqShow (BinderNameType s t) = if null s then empty else parens $ hsep (map coqShow s) <+> text ":" <+> coqShow t
  coqShow (BinderScopeNameType s t) = if null s then empty else parens $ hsep (map coqShow s) <+> text ":" <+> coqShow t
  coqShow (BinderImplicitName s) = text "{" <+> coqShow s <+> text "}"
  coqShow (BinderImplicitNameType s t) = if null s then empty else text "{" <+> hsep (map coqShow s) <+> text ":" <+> coqShow t <+> text "}"
  coqShow (BinderImplicitScopeNameType s t) = if null s then empty else text "{" <+> hsep (map coqShow s) <+> text ":" <+> coqShow t <+> text "}"

instance CoqShow Definition where
  coqShow (Definition name bs mb s) = text "Definition" <+> coqShow name <+> hsep (map coqShow bs) <+> (text ":" <+> coqShow mb) <+> text ":="
                                        <$$> indent 2 (coqShow s) <> text "."

instance CoqShow Equation where
  coqShow (Equation pat s) = text "|" <+> coqShow pat <+> text "=>" <+> coqShow s

instance CoqShow Fixpoint where
  coqShow (Fixpoint r bs) =  (if r then text "Fixpoint" else text "Definition")
    <+> hcat (punctuate (line <> text " with ") (map (nest 2 . coqShow) bs)) <> dot

instance CoqShow FixpointBody where
  coqShow (FixpointBody name bs ret s) = coqShow name <+> hsep (map coqShow bs) <+> text ":" <+> coqShow ret
                                            <+> text ":=" <$$> indent 2 (coqShow s)

instance CoqShow Lemma where
  coqShow (Lemma name bs mb p) = text "Lemma" <+> coqShow name <+> hsep (map coqShow bs) <+> (text ":" <+> coqShow mb) <+> text "."
                                        <$$> text "Proof." <+> coqShow p <+> text "Qed."

instance CoqShow Proof where
  coqShow (ProofExact tm) = text "exact" <+> parens (coqShow tm) <> text "."
  coqShow (ProofString s) = text s

instance CoqShow Inductive where
  coqShow (Inductive bs) = text "Inductive"
    <+> hcat (punctuate (line <> text " with ") (map (nest 2 . coqShow ) bs)) <> dot

instance CoqShow InductiveBody where
  coqShow (InductiveBody name bs s cs) = hang 2 (coqShow name </> hsep (map coqShow bs) </> colon <+> coqShow s <+> text ":=") <$$> vsep (map coqShow cs)

instance CoqShow InductiveCtor where
  coqShow (InductiveCtor name mt) = text "| " <> text name </> colon <+> coqShow mt

instance CoqShow MatchItem where
  coqShow (MatchItem s) = coqShow s

instance CoqShow a => CoqShow (Maybe a) where
  coqShow Nothing  = text "_"
  coqShow (Just t) = coqShow t

instance CoqShow Pattern where
  coqShow (PatternConstructor s ids) = coqShow s <+> hsep (map coqShow ids)
  coqShow PatternUnderscore          = coqShow TermUnderscore

instance CoqShow Command where
  coqShow (Arguments s ts) = text "Arguments" <+> coqShow s <+> hsep (map braces (map coqShow ts)) <> text "."

instance CoqShow Sentence where
  coqShow (SentenceCommand s)    = coqShow s
  coqShow (SentenceClass n bs xs) = text "Class" <+> text n <+> hsep (map coqShow bs) <+> text ":=" <+> hsep (map (\(x,y) -> text x <+> text ":" <+> coqShow y) xs) <> text "."
  coqShow (SentenceDefinition s) = coqShow s
  coqShow (SentenceInductive s)  = coqShow s
  coqShow (SentenceFixpoint s)   = coqShow s
  coqShow (SentenceTactic name t) = text "Ltac" <+> text name <+> text ":=" <+> coqShow t <> text "."
  coqShow (SentenceLemma s)      = coqShow s
  coqShow (SentenceTacticNotation name t) = text "Tactic Notation" <+> hsep (map text name) <+> text ":=" <+> coqShow t <> text "."
  coqShow (SentenceId s) = text s
  coqShow (SentenceNotation x t y z) = text "Notation" <+> dquotes (text x) <+> text ":=" <+> parens (coqShow t) <+> parens (text y) <+> text ":" <+> text z <> text "."
  coqShow (SentenceInstance bs x s t) = text "Global Instance" <+> text x <+> hsep (map coqShow bs) <+> text ":" <+> coqShow s <+> text ":=" <+> coqShow t <+> text "."
  coqShow (SentenceSection name xs) = (text "Section" <+> text name <> text ".") <$$> vsep (map (\s -> coqShow s <$$> empty) xs) <$$> (text "End" <+> text name <> text ".")
  coqShow (SentenceVariable name xs) = text "Variable" <+> text name <+> text ":" <+> coqShow xs <> text "."
  coqShow (SentenceRequireExport []) = empty
  coqShow (SentenceRequireExport names) = text "Require Export" <+> hsep (map coqShow names) <> text "."

instance CoqShow SubstTy where
  coqShow xs = hsep (map (\x -> case x of
                                    TermId s -> coqShow s
                                    TermSubst s -> coqShow s
                                    _ -> parens $ coqShow x) (substTerms xs))

coqShowParens :: Term -> Doc
coqShowParens (TermId s)    = coqShow s
coqShowParens (TermSubst s) = coqShow s
coqShowParens s             = parens $ coqShow s

instance CoqShow Term where
  coqShow (TermImp s) = text "@" <> coqShow s
  coqShow (Todo s)           = text ("Todo." ++ s)
  coqShow (TermApp s ts)     = coqShowParens s <+> hsep (map (\x -> case x of
                                                          TermId s -> coqShow s
                                                          TermSubst s -> coqShow s
                                                          _ -> parens $ coqShow x) ts)
  coqShow (TermId s)         = coqShow s
  coqShow (TermFunction s t) = coqShow s <+> text "->" <+> coqShow t
  coqShow (TermSort s)       = coqShow s
  coqShow TermUnderscore   = text "_"
  coqShow (TermForall bs t)  = text "forall" <+> hsep (map coqShow bs) <> text "," <+> coqShow t
  coqShow (TermAbs bs t)     = text "fun" <+> hsep (map coqShow bs) <+> text "=>" <+> coqShow t
  coqShow (TermLet s t u)    = text "let" <+> coqShow t <+> text ":=" <+> coqShow s <+> text "in" <+> coqShow u
  coqShow (Tuple s)          = cTupled (map coqShow s)
  coqShow (TupleTy s)        = encloseSep empty empty (text " * ") (map (parens . coqShow) s)
  coqShow (TermMatch m Nothing s) = text "match" <+> coqShow m <+> text "with" <$$> vcat (map coqShow s) <$$> text "end"
  coqShow (TermMatch m (Just ret) s) = text "match" <+> coqShow m <+> text "return" <+> coqShow ret <+> text "with" <$$> vcat (map coqShow s) <$$> text "end"
  coqShow (TermAnd s)  = encloseSep empty empty (text " /\\") (map (parens . coqShow) s)
  coqShow (TermEq s t) = coqShow s <+> text "=" <+> coqShow t
  coqShow (TermSubst s) = coqShow s
  coqShow (TermVar s) = coqShow s
  coqShow (TermConst c) = coqShow c

-- Printing for automation tactics
instance CoqShow Tactic where
  coqShow (TacticId t) = text t
  coqShow (TacticSeq ts) = hsep $ punctuate (text ";") (map coqShow ts)
  coqShow (TacticRewrite Nothing subst up lemmas) = (text "repeat first") <+> brackets (hsep
                                                    (punctuate (text "|") (map (\x -> text $ "progress rewrite ?" ++ x) lemmas ++
                                                    [text "progress" <+> parens (text "unfold" <+> hsep (punctuate comma (map text up))), text "progress" <+> parens (text "cbn" <+> brackets (hsep (map text subst))), text "fsimpl"]))) -- TODO : Syntax structure for LTAC.
  coqShow (TacticRewrite (Just s) subst up lemmas) = (text "repeat first") <+> brackets (hsep
                                                    (punctuate (text "|") (map (\x -> text $ "progress rewrite ?" ++ x ++ " " ++ s) lemmas ++
                                                    [text "progress" <+> parens (text "unfold" <+> hsep (punctuate comma (map text up)) <+> text s) , text "progress" <+> parens (text "cbn" <+> brackets (hsep (map text subst)) <+> text s), text "fsimpl in *"]))) -- TODO : Syntax structure for LTAC.
  coqShow (TacticRepeat t) = text "repeat" <+> coqShow t
  coqShow (TacticFold xs Nothing) = hsep (punctuate (text "; ") (map (\x -> text "try fold" <+> coqShow x) xs))
  coqShow (TacticUnfold xs Nothing) = text "unfold" <+> hsep (punctuate (text ", ") (map coqShow xs))
  coqShow (TacticFold xs (Just s)) = hsep (punctuate (text "; ") (map (\x -> text "try fold" <+> coqShow x <+> text s) xs))
  coqShow (TacticUnfold xs (Just s)) = text "unfold" <+> hsep (punctuate (text ", ") (map (\x -> coqShow x) xs)) <+> text s
