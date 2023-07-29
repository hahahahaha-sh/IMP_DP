(*  Title:      HOL/Hoare/Hoare_Logic.thy
    Author:     Leonor Prensa Nieto & Tobias Nipkow
    Copyright   1998 TUM

Sugared semantic embedding of Hoare logic.
Strictly speaking a shallow embedding (as implemented by Norbert Galm
following Mike Gordon) would suffice. Maybe the datatype com comes in useful
later.
*)

theory Hoare_Logic
imports Main
begin

type_synonym 'a bexp = "'a set"
type_synonym 'a assn = "'a set"

datatype 'a com =
  Basic "'a ⇒ 'a"
| Seq "'a com" "'a com"               ("(_;/ _)"      [61,60] 60)
| Cond "'a bexp" "'a com" "'a com"    ("(1IF _/ THEN _ / ELSE _/ FI)"  [0,0,0] 61)
| While "'a bexp" "'a assn" "'a com"  ("(1WHILE _/ INV {_} //DO _ /OD)"  [0,0,0] 61)

abbreviation annskip ("SKIP") where "SKIP == Basic id"

type_synonym 'a sem = "'a => 'a => bool"

inductive Sem :: "'a com ⇒ 'a sem"
where
  "Sem (Basic f) s (f s)"
| "Sem c1 s s'' ⟹ Sem c2 s'' s' ⟹ Sem (c1;c2) s s'"
| "s ∈ b ⟹ Sem c1 s s' ⟹ Sem (IF b THEN c1 ELSE c2 FI) s s'"
| "s ∉ b ⟹ Sem c2 s s' ⟹ Sem (IF b THEN c1 ELSE c2 FI) s s'"
| "s ∉ b ⟹ Sem (While b x c) s s"
| "s ∈ b ⟹ Sem c s s'' ⟹ Sem (While b x c) s'' s' ⟹
   Sem (While b x c) s s'"

inductive_cases [elim!]:
  "Sem (Basic f) s s'" "Sem (c1;c2) s s'"
  "Sem (IF b THEN c1 ELSE c2 FI) s s'"

definition Valid :: "'a bexp ⇒ 'a com ⇒ 'a bexp ⇒ bool"
  where "Valid p c q ⟷ (∀s s'. Sem c s s' ⟶ s ∈ p ⟶ s' ∈ q)"


syntax
  "_assign" :: "idt => 'b => 'a com"  ("(2_ :=/ _)" [70, 65] 61)

syntax
 "_hoare_vars" :: "[idts, 'a assn,'a com,'a assn] => bool"
                 ("VARS _// {_} // _ // {_}" [0,0,55,0] 50)
syntax ("" output)
 "_hoare"      :: "['a assn,'a com,'a assn] => bool"
                 ("{_} // _ // {_}" [0,55,0] 50)

ML_file ‹hoare_syntax.ML›
parse_translation ‹[(\<^syntax_const>‹_hoare_vars›, K Hoare_Syntax.hoare_vars_tr)]›
print_translation ‹[(\<^const_syntax>‹Valid›, K (Hoare_Syntax.spec_tr' \<^syntax_const>‹_hoare›))]›


lemma SkipRule: "p ⊆ q ⟹ Valid p (Basic id) q"
by (auto simp:Valid_def)

lemma BasicRule: "p ⊆ {s. f s ∈ q} ⟹ Valid p (Basic f) q"
by (auto simp:Valid_def)

lemma SeqRule: "Valid P c1 Q ⟹ Valid Q c2 R ⟹ Valid P (c1;c2) R"
by (auto simp:Valid_def)

lemma CondRule:
 "p ⊆ {s. (s ∈ b ⟶ s ∈ w) ∧ (s ∉ b ⟶ s ∈ w')}
  ⟹ Valid w c1 q ⟹ Valid w' c2 q ⟹ Valid p (Cond b c1 c2) q"
by (auto simp:Valid_def)

lemma While_aux:
  assumes "Sem (WHILE b INV {i} DO c OD) s s'"
  shows "∀s s'. Sem c s s' ⟶ s ∈ I ∧ s ∈ b ⟶ s' ∈ I ⟹
    s ∈ I ⟹ s' ∈ I ∧ s' ∉ b"
  using assms
  by (induct "WHILE b INV {i} DO c OD" s s') auto

lemma WhileRule:
 "p ⊆ i ⟹ Valid (i ∩ b) c i ⟹ i ∩ (-b) ⊆ q ⟹ Valid p (While b i c) q"
apply (clarsimp simp:Valid_def)
apply(drule While_aux)
  apply assumption
 apply blast
apply blast
done


lemma Compl_Collect: "-(Collect b) = {x. ~(b x)}"
  by blast

lemmas AbortRule = SkipRule  ― ‹dummy version›
ML_file ‹hoare_tac.ML›

method_setup vcg = ‹
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (Hoare.hoare_tac ctxt (K all_tac)))›
  "verification condition generator"

method_setup vcg_simp = ‹
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD' (Hoare.hoare_tac ctxt (asm_full_simp_tac ctxt)))›
  "verification condition generator plus simplification"

end
