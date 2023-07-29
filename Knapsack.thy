subsection ‹The Knapsack Problem›

theory Knapsack
  imports
    "HOL-Library.Code_Target_Numeral"
    "../state_monad/State_Main" 
    "../heap_monad/Heap_Default"
    Example_Misc
begin

subsubsection ‹Definitions›

context (* Subset Sum *)
  fixes w :: "nat ⇒ nat"
begin

context (* Knapsack *)
  fixes v :: "nat ⇒ nat"
begin

fun knapsack :: "nat ⇒ nat ⇒ nat" where
  "knapsack 0 W = 0" |
  "knapsack (Suc i) W = (if W < w (Suc i)
    then knapsack i W
    else max (knapsack i W) (v (Suc i) + knapsack i (W - w (Suc i))))"

no_notation fun_app_lifted (infixl "." 999)

text ‹
  The correctness proof closely follows Kleinberg ‹&› Tardos: "Algorithm Design",
  chapter "Dynamic Programming" @{cite "Kleinberg-Tardos"}
›

definition
  "OPT n W = Max {∑ i ∈ S. v i | S. S ⊆ {1..n} ∧ (∑ i ∈ S. w i) ≤ W}"

lemma OPT_0:
  "OPT 0 W = 0"
  unfolding OPT_def by simp

subsubsection ‹Functional Correctness›

lemma Max_add_left:
  "(x :: nat) + Max S = Max (((+) x) ` S)" (is "?A = ?B") if "finite S" "S ≠ {}"
proof -
  have "?A ≤ ?B"
    using that by (force intro: Min.boundedI)
  moreover have "?B ≤ ?A"
    using that by (force intro: Min.boundedI)
  ultimately show ?thesis
    by simp
qed

lemma OPT_Suc:
  "OPT (Suc i) W = (
    if W < w (Suc i)
    then OPT i W
    else max(v (Suc i) + OPT i (W - w (Suc i))) (OPT i W)
  )" (is "?lhs = ?rhs")
proof -
  have OPT_in: "OPT n W ∈ {∑ i ∈ S. v i | S. S ⊆ {1..n} ∧ (∑ i ∈ S. w i) ≤ W}" for n W
    unfolding OPT_def by - (rule Max_in; force)
  from OPT_in[of "Suc i" W] obtain S where S:
    "S ⊆ {1..Suc i}" "sum w S ≤ W" and [simp]: "OPT (Suc i) W = sum v S"
    by auto

  have "OPT i W ≤ OPT (Suc i) W"
    unfolding OPT_def by (force intro: Max_mono)
  moreover have "v (Suc i) + OPT i (W - w (Suc i)) ≤ OPT (Suc i) W" if "w (Suc i) ≤ W"
  proof -
    have *: "
      v (Suc i) + sum v S = sum v (S ∪ {Suc i}) ∧ (S ∪ {Suc i}) ⊆ {1..Suc i}
      ∧ sum w (S ∪ {Suc i}) ≤ W" if "S ⊆ {1..i}" "sum w S ≤ W - w (Suc i)" for S
      using that ‹w (Suc i) ≤ W›
      by (subst sum.insert_if | auto intro: finite_subset[OF _ finite_atLeastAtMost])+
    show ?thesis
      unfolding OPT_def
      by (subst Max_add_left;
          fastforce intro: Max_mono finite_subset[OF _ finite_atLeastAtMost] dest: *
         )
  qed
  ultimately have "?lhs ≥ ?rhs"
    by auto

  from S have *: "sum v S ≤ OPT i W" if "Suc i ∉ S"
    using that unfolding OPT_def by (auto simp: atLeastAtMostSuc_conv intro!: Max_ge)

  have "sum v S ≤ OPT i W" if "W < w (Suc i)"
  proof (rule *, rule ccontr, simp)
    assume "Suc i ∈ S"
    then have "sum w S ≥ w (Suc i)"
      using S(1) by (subst sum.remove) (auto intro: finite_subset[OF _ finite_atLeastAtMost])
    with ‹W < _› ‹_ ≤ W› show False
      by simp
  qed
  moreover have
    "OPT (Suc i) W ≤ max(v (Suc i) + OPT i (W - w (Suc i))) (OPT i W)" if "w (Suc i) ≤ W"
  proof (cases "Suc i ∈ S")
    case True
    then have [simp]:
      "sum v S = v (Suc i) + sum v (S - {Suc i})" "sum w S = w (Suc i) + sum w (S - {Suc i})"
      using S(1) by (auto intro: finite_subset[OF _ finite_atLeastAtMost] sum.remove)
    have "OPT i (W - w (Suc i)) ≥ sum v (S - {Suc i})"
      unfolding OPT_def using S by (fastforce intro!: Max_ge)
    then show ?thesis
      by simp
  next
    case False
    then show ?thesis
      by (auto dest: *)
  qed
  ultimately have "?lhs ≤ ?rhs"
    by auto
  with ‹?lhs ≥ ?rhs› show ?thesis
    by simp
qed

theorem knapsack_correct:
  "OPT n W = knapsack n W"
  by (induction n arbitrary: W; auto simp: OPT_0 OPT_Suc)


subsubsection ‹Functional Memoization›

memoize_fun knapsack⇩m: knapsack with_memory dp_consistency_mapping monadifies (state) knapsack.simps

text ‹Generated Definitions›
context includes state_monad_syntax begin
thm knapsack⇩m'.simps knapsack⇩m_def
end

text ‹Correspondence Proof›
memoize_correct
  by memoize_prover
print_theorems
lemmas [code] = knapsack⇩m.memoized_correct

value "knapsack⇩m "
subsubsection ‹Imperative Memoization›

context fixes
  mem :: "nat option array"
  and n W :: nat
begin

memoize_fun knapsack⇩T: knapsack
  with_memory dp_consistency_heap_default where bound = "Bound (0, 0) (n, W)" and mem="mem"
  monadifies (heap) knapsack.simps

context includes heap_monad_syntax begin
thm knapsack⇩T'.simps knapsack⇩T_def
end

memoize_correct
  by memoize_prover

lemmas memoized_empty = knapsack⇩T.memoized_empty
value "knapsack⇩T "
end (* Fixed array *)

text ‹Adding Memory Initialization›
context
  includes heap_monad_syntax
  notes [simp del] = knapsack⇩T'.simps
begin

definition
  "knapsack⇩h ≡ λ i j. Heap_Monad.bind (mem_empty (i * j)) (λ mem. knapsack⇩T' mem i j i j)"

lemmas memoized_empty' = memoized_empty[
      of mem n W "λ m. λ(i,j). knapsack⇩T' m n W i j",
      OF knapsack⇩T.crel[of mem n W], of "(n, W)" for mem n W
    ]

lemma knapsack_heap:
  "knapsack n W = result_of (knapsack⇩h n W) Heap.empty"
  unfolding knapsack⇩h_def using memoized_empty'[of _ n W] by (simp add: index_size_defs)

end

end (* Knapsack *)

fun su :: "nat ⇒ nat ⇒ nat" where
  "su 0 W = 0" |
  "su (Suc i) W = (if W < w (Suc i)
    then su i W
    else max (su i W) (w (Suc i) + su i (W - w (Suc i))))"

lemma su_knapsack:
  "su n W = knapsack w n W"
  by (induction n arbitrary: W; simp)

lemma su_correct:
  "Max {∑ i ∈ S. w i | S. S ⊆ {1..n} ∧ (∑ i ∈ S. w i) ≤ W} = su n W"
  unfolding su_knapsack knapsack_correct[symmetric] OPT_def ..

subsubsection ‹Memoization›

memoize_fun su⇩m: su with_memory dp_consistency_mapping monadifies (state) su.simps

text ‹Generated Definitions›
context includes state_monad_syntax begin
thm su⇩m'.simps su⇩m_def
end

text ‹Correspondence Proof›
memoize_correct
  by memoize_prover
print_theorems
lemmas [code] = su⇩m.memoized_correct
value "su⇩m"
end (* Subset Sum *)


subsubsection ‹Regression Test›

definition
  "knapsack_test = (knapsack⇩h (λ i. [2,3,4] ! (i - 1)) (λ i. [2,3,4] ! (i - 1)) 3 8)"

code_reflect Test functions knapsack_test

ML ‹Test.knapsack_test ()›

end (* Theory *)
