{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances  #-}
module Autosubst.PrintUnscoped where

-- Pretty Printing of Syntax to unscoped Coq code
import           Autosubst.Syntax
import           Text.PrettyPrint.Leijen

-- UCoqShow Class
class UCoqShow a where
  ucoqShow :: a -> Doc

instance UCoqShow String where
  ucoqShow = text

-- Generation of tuples accepted by UCoq, no parentheses if there is just one component.
cTupled ::  [Doc] -> Doc
cTupled []  = empty
cTupled [x] = x
cTupled xs  = encloseSep lparen rparen (comma <+> empty) xs

ucoqPreamble :: Bool -> Doc
ucoqPreamble b = ucoqShow (SentenceRequireExport (["unscoped"] ++ if b then ["header_extensible"] else []))  

ecoqPreamble :: Doc
ecoqPreamble = ucoqShow (SentenceRequireExport ["unscoped", "header_extensible"])

-- Printing of constants
instance UCoqShow Const where
  ucoqShow Some    = text "S"
  ucoqShow None    = text "0"
  ucoqShow Refl    = text "eq_refl"
  ucoqShow Sym     = text "eq_sym"
  ucoqShow Trans   = text "eq_trans"
  ucoqShow Nat     = text "nat"
  ucoqShow Suc     = text "S"
  ucoqShow Fin     = text "fin"
  ucoqShow Id      = text "id"
  ucoqShow Comp    = text "funcomp"
  ucoqShow Upren   = text "up_ren"
  ucoqShow Cons    = text "scons"
  ucoqShow VarZero = text "var_zero"
  ucoqShow Ap      = text "ap"
  ucoqShow Shift = text "shift"
  ucoqShow Fext = text "FunctionalExtensionality.functional_extensionality _ _ "

-- UCoq Primitives.
instance UCoqShow Sort where
  ucoqShow Prop = text "Prop"
  ucoqShow Set  = text "Set"
  ucoqShow Type = text "Type"

instance UCoqShow CBinder where
  ucoqShow (BinderName s) = ucoqShow s
  ucoqShow (BinderScopeNameType s t) = empty
  ucoqShow (BinderNameType s t) = parens $ hsep (map ucoqShow s) <+> text ":" <+> ucoqShow t
  ucoqShow (BinderImplicitName s) = text "{" <+> ucoqShow s <+> text "}"
  ucoqShow (BinderImplicitNameType s t) = text "{" <+> hsep (map ucoqShow s) <+> text ":" <+> ucoqShow t <+> text "}"
  ucoqShow (BinderImplicitScopeNameType s t) = empty

instance UCoqShow Definition where
  ucoqShow (Definition name bs mb s) = text "Definition" <+> ucoqShow name <+> hsep (map ucoqShow bs) <+> (text ":" <+> ucoqShow mb) <+> text ":="
                                        <$$> indent 2 (ucoqShow s) <> text "."

instance UCoqShow Equation where
  ucoqShow (Equation pat s) = text "|" <+> ucoqShow pat <+> text "=>" <+> ucoqShow s

instance UCoqShow Fixpoint where
  ucoqShow (Fixpoint r bs) =  (if r then text "Fixpoint" else text "Definition")
    <+> hcat (punctuate (line <> text " with ") (map (nest 2 . ucoqShow) bs)) <> dot

instance UCoqShow FixpointBody where
  ucoqShow (FixpointBody name bs ret s) = ucoqShow name <+> hsep (map ucoqShow bs) <+> text ":" <+> ucoqShow ret
                                            <+> text ":=" <$$> indent 2 (ucoqShow s)

instance UCoqShow Lemma where
  ucoqShow (Lemma name bs mb p) = text "Lemma" <+> ucoqShow name <+> hsep (map ucoqShow bs) <+> (text ":" <+> ucoqShow mb) <+> text "."
                                        <$$> text "Proof." <+> ucoqShow p <+> text "Qed."

instance UCoqShow Proof where
  ucoqShow (ProofExact tm) = text "exact" <+> parens (ucoqShow tm) <> text "."
  ucoqShow (ProofString s) = text s

instance UCoqShow Inductive where
  ucoqShow (Inductive bs) = text "Inductive"
    <+> hcat (punctuate (line <> text " with ") (map (nest 2 . ucoqShow ) bs)) <> dot

instance UCoqShow InductiveBody where
  ucoqShow (InductiveBody name bs s cs) = hang 2 (ucoqShow name </> hsep (map ucoqShow bs) </> colon <+> ucoqShow s <+> text ":=") <$$> vsep (map ucoqShow cs)

instance UCoqShow InductiveCtor where
  ucoqShow (InductiveCtor name mt) = text "| " <> text name </> colon <+> ucoqShow mt

instance UCoqShow MatchItem where
  ucoqShow (MatchItem s)  = ucoqShow s

instance UCoqShow a => UCoqShow (Maybe a) where
  ucoqShow Nothing  = text "_"
  ucoqShow (Just t) = ucoqShow t

instance UCoqShow Pattern where
  ucoqShow (PatternConstructor s ids) = ucoqShow s <+> hsep (map ucoqShow ids)
  ucoqShow (PatternUnderscore) = ucoqShow TermUnderscore

instance UCoqShow Command where
  ucoqShow (Arguments xs ts) = if (concatMap (show . ucoqShow) ts) == "" then text "" else  text "Arguments" <+> ucoqShow (xs) <+> hsep (map braces ( (map ucoqShow ts))) <> text "."

instance UCoqShow Sentence where
  ucoqShow (SentenceDefinition s) = ucoqShow s
  ucoqShow (SentenceInductive s)  = ucoqShow s
  ucoqShow (SentenceClass n bs xs) = text "Class" <+> text n <+> hsep (map ucoqShow bs) <+> text ":=" <+> hsep (map (\(x,y) -> text x <+> text ":" <+> ucoqShow y) xs) <> text "."
  ucoqShow (SentenceFixpoint s)   = ucoqShow s
  ucoqShow (SentenceLemma s)      = ucoqShow s
  ucoqShow (SentenceTactic name t) = text "Ltac" <+> text name <+> text ":=" <+> ucoqShow t <> text "."
  ucoqShow (SentenceTacticNotation name t) = text "Tactic Notation" <+> hsep (map text name) <+> text ":=" <+> ucoqShow t <> text "."
  ucoqShow (SentenceCommand z) = ucoqShow z
  ucoqShow (SentenceNotation x t y z) = text "Notation" <+> dquotes (text x) <+> text ":=" <+> parens (ucoqShow t) <+> parens (text y) <+> text ":" <+> text z <> text "."
  ucoqShow (SentenceInstance bs x s t) = text "Global Instance" <+> text x <+> hsep (map ucoqShow bs) <+> text ":" <+> ucoqShow s <+> text ":=" <+> ucoqShow t <+> text "."
  ucoqShow (SentenceId s) = text s
  ucoqShow (SentenceSection name xs) = (text "Section" <+> text name <> text ".") <$$> vsep (map  (\s -> ucoqShow s <$$> empty) xs) <$$> (text "End" <+> text name <> text ".")
  ucoqShow (SentenceVariable name xs) = text "Variable" <+> text name <+> text ":" <+> ucoqShow xs <> text "."
  ucoqShow (SentenceRequireExport []) = empty
  ucoqShow (SentenceRequireExport names) = text "Require Export" <+> hsep (map ucoqShow names) <> text "."

instance UCoqShow SubstTy where
  ucoqShow xs = hsep (map (\x -> case x of
                                    TermId s -> ucoqShow s
                                    TermVar s -> empty
                                    TermSubst s -> ucoqShow s
                                    _ -> parens $ ucoqShow x) (substTerms xs))

ucoqShowParens :: Term -> Doc
ucoqShowParens (TermId s)    = ucoqShow s
ucoqShowParens (TermSubst s) = ucoqShow s
ucoqShowParens s             = parens $ ucoqShow s


instance UCoqShow Term where
  ucoqShow (TermImp s) = text "@" <> ucoqShow s
  ucoqShow (Todo s)    = text ("Todo." ++ s)
  ucoqShow (TermApp (TermConst Fin) _) = ucoqShow (TermConst Fin)
  ucoqShow (TermApp (TermConst Suc) [s]) = ucoqShow s
  ucoqShow (TermApp s ts)     = ucoqShowParens s <+> hsep (map (\x -> case x of
                                                          TermId s -> ucoqShow s
                                                          TermSubst s -> ucoqShow s
                                                          TermVar s -> empty
                                                          _ -> parens $ ucoqShow x) ts)
  ucoqShow (TermId s)         = ucoqShow s
  ucoqShow (TermFunction s t) = text "(" <+> ucoqShow s <+> text ")" <+> text "->" <+> ucoqShow t
  ucoqShow (TermSort s)       = ucoqShow s
  ucoqShow TermUnderscore   = text "_"
  ucoqShow (TermForall bs t)  = text "forall" <+> hsep (map ucoqShow bs) <> text "," <+> ucoqShow t
  ucoqShow (TermAbs bs t)     = text "fun" <+> hsep (map ucoqShow bs) <+> text "=>" <+> ucoqShow t
  ucoqShow (TermLet s t u)    = text "let" <+> ucoqShow t <+> text ":=" <+> ucoqShow s <+> text "in" <+> ucoqShow u
  ucoqShow (Tuple s)          = cTupled (map ucoqShow s)
  ucoqShow (TupleTy s)        = encloseSep empty empty (text " * ") (map (parens . ucoqShow) s)
  ucoqShow (TermMatch m Nothing s) = text "match" <+> ucoqShow m <+> text "with" <$$> vcat (map ucoqShow s) <$$> text "end"
  ucoqShow (TermMatch m (Just ret) s) = text "match" <+> ucoqShow m <+> text "return" <+> ucoqShow ret <+> text "with" <$$> vcat (map ucoqShow s) <$$> text "end"
  ucoqShow (TermAnd s)  = encloseSep empty empty (text " /\\") (map (parens . ucoqShow) s)
  ucoqShow (TermEq s t) = ucoqShow s <+> text "=" <+> ucoqShow t
  ucoqShow (TermSubst s) = ucoqShow s
  ucoqShow (TermVar s) = empty
  ucoqShow (TermConst s) = ucoqShow s

-- Printing of tactics
instance UCoqShow Tactic where
  ucoqShow (TacticId t) = text t
  ucoqShow (TacticSeq ts) = hsep $ punctuate (text ";") (map ucoqShow ts)
  ucoqShow (TacticRewrite Nothing subst up lemmas) = (text "repeat first") <+> brackets (hsep
                                                    (punctuate (text "|") (map (\x -> text $ "progress rewrite ?" ++ x) lemmas ++
                                                    [text "progress" <+> parens (text "unfold" <+> hsep (punctuate comma (map text up))), text "progress" <+> parens (text "cbn" <+> brackets (hsep (map text subst))), text "fsimpl"]))) -- TODO : Syntax structure for LTAC.
  ucoqShow (TacticRewrite (Just s) subst up lemmas) = (text "repeat first") <+> brackets (hsep
                                                    (punctuate (text "|") (map (\x -> text $ "progress rewrite ?" ++ x ++ " " ++ s) lemmas ++
                                                    [text "progress" <+> parens (text "unfold" <+> hsep (punctuate comma (map text up)) <+> text s) , text "progress" <+> parens (text "cbn" <+> brackets (hsep (map text subst)) <+> text s), text "fsimpl in *"]))) -- TODO : Syntax structure for LTAC.
  ucoqShow (TacticRepeat t) = text "repeat" <+> ucoqShow t
  ucoqShow (TacticFold xs Nothing) = hsep (punctuate (text "; ") (map (\x -> text "try fold" <+> ucoqShow x) xs))
  ucoqShow (TacticUnfold xs Nothing) = text "unfold" <+> hsep (punctuate (text ", ") (map ucoqShow xs))
  ucoqShow (TacticFold xs (Just s)) = hsep (punctuate (text "; ") (map (\x -> text "try fold" <+> ucoqShow x <+> text s) xs))
  ucoqShow (TacticUnfold xs (Just s)) = text "unfold" <+> hsep (punctuate (text ", ") (map (\x -> ucoqShow x) xs)) <+> text s