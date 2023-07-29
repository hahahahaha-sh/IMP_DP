theory ks
  imports "Hoare_Logic" "Arith2" 
begin

definition list_list_update ::"nat list list ⇒ nat ⇒ nat⇒ nat ⇒ nat list list"
  where "list_list_update dlist i j value =list_update dlist i  (list_update (dlist!i) j value)"

fun knapsack :: "nat ⇒ nat ⇒ nat list ⇒ nat list ⇒ nat" where
  "knapsack 0 W w v= 0" |
  "knapsack (Suc i) W w v= (if W < w!(Suc i)
    then knapsack i W w v
    else max (knapsack i W w v) (v!(Suc i) + knapsack i (W - w!(Suc i)) w v))"

lemma  ks_DL3_1:"Suc 0 ≤ length m ∧
       (∀k<length m. length (m ! k) = length (m ! (k - Suc 0)) ∧ Suc 0 ≤ length (m ! k)) ∧
       (∀k<i. ∀j<length (m ! (k - Suc 0)). m ! k ! j = knapsack k j w v) ∧
       (∀k<j. m ! i ! k = knapsack i k w v) ∧ Suc 0 ≤ i ∧ i < length m ∧ j ≤ length (m ! (i - Suc 0)) ∧ j ≤ length (m ! i) - Suc 0 ⟹
       j < w ! i 
       ⟹ (m ! i)[j := m ! (i - Suc 0) ! j] ! j = knapsack i j w v"
  proof (induction i)
  case 0
  then show ?case by simp
 next
  case (Suc i')
  from Suc.prems have "i' < length m" by simp
  have "(m ! (Suc i'))[j := m ! i' ! j] ! j = (if j = j then m ! i' ! j else m ! (Suc i') ! j)"
    by (metis One_nat_def Suc.prems(1) diff_diff_cancel diff_is_0_eq' le_neq_implies_less less_Suc_eq_0_disj less_numeral_extra(4) nth_list_update_eq)
  also have "... = m ! i' ! j"
    by simp
  also have "... = knapsack i' j w v"
    by (metis Suc.prems(1) ‹i' < length m› diff_Suc_Suc diff_diff_cancel diff_is_0_eq' le_neq_implies_less lessI minus_nat.diff_0)
  finally show ?case
    using Suc.prems Suc.IH ‹i' < length m› One_nat_def diff_Suc_1 knapsack.simps(2) by presburger 
qed

lemma ks_DL3_2: " Suc 0 ≤ length m ∧
       (∀k<length m. length (m ! k) = length (m ! (k - Suc 0)) ∧ Suc 0 ≤ length (m ! k)) ∧
       (∀k<i. ∀j<length (m ! (k - Suc 0)). m ! k ! j = knapsack k j w v) ∧
       (∀k<j. m ! i ! k = knapsack i k w v) ∧ Suc 0 ≤ i ∧ i < length m ∧ j ≤ length (m ! (i - Suc 0)) ∧ j ≤ length (m ! i) - Suc 0 ⟹
       ¬ j < w ! i ⟹ (m ! i)[j := max (m ! (i - Suc 0) ! j) (m ! (i - Suc 0) ! (j - w ! i) + v ! i)] ! j = knapsack i j w v"
  proof (induction i)
  case 0
  then show ?case by simp
 next
  case (Suc i')
  from Suc.prems have "i' < length m" by simp
  have "(m ! (Suc i'))[j := m ! i' ! j] ! j = (if j = j then m ! i' ! j else m ! (Suc i') ! j)"
    by (metis One_nat_def Suc.prems(1) diff_diff_cancel diff_is_0_eq' le_neq_implies_less less_Suc_eq_0_disj less_numeral_extra(4) nth_list_update_eq)
  also have "... = m ! i' ! j"
    by simp
  also have "... = knapsack i' j w v"
    by (metis Suc.prems(1) ‹i' < length m› diff_Suc_Suc diff_diff_cancel diff_is_0_eq' le_neq_implies_less lessI minus_nat.diff_0)
  finally show ?case
    using Suc.prems Suc.IH ‹i' < length m› One_nat_def diff_Suc_1 knapsack.simps(2)
    by (smt add.commute add_diff_inverse_nat add_lessD1 diff_less nth_list_update_eq ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc zero_less_Suc) 
qed

 
lemma ks: "VARS m w v i j
 {length m ≥1}
i:=1;j:=0;m:=[ [0,0,0,0,0,0,0,0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0],
               [0,0,0,0,0,0,0,0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0],  
               [0,0,0,0,0,0,0,0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0]];
v:= [(0::nat),6,3,5,4,6]; w:= [(0::nat),2,2,6,5,4]; 
  WHILE i ≤ length m -1
  INV{ i≥1∧  i≤length m ∧  j≤length (m!(i-1)) ∧ j≥0
       ∧ (∀k. k < i ⟶ 
             ( ∀ j. j<length (m!(k-1))⟶
               m!k!j =knapsack k j w v  )  )
       ∧ length m ≥1  
       ∧(∀k .k<length m ⟶ length (m!k) = length (m!(k-1))  ∧  length (m!k)≥1 )
       }
   DO       
      j:=0;
      WHILE j ≤ length (m!i)-1
      INV{  i≥1∧   i<length m ∧  j≤length (m!(i-1)) ∧ j≥0 
           ∧ (∀k. k < i ⟶ 
             ( ∀ j. j<length (m!(k-1))⟶
                  m!k!j =knapsack k j w v )  )
           ∧ ( ∀ k. k < j⟶
                  m!i!k =knapsack i k w v )  
           ∧  length m ≥1
           ∧(∀k .k<length m ⟶ length (m!k) = length (m!(k-1))  ∧  length (m!k)≥1 )  }
       DO
          ( IF j<(w!(i)) THEN  m:=list_list_update m (i) j (m!(i-1)!j)
            ELSE m:=list_list_update m (i) j (max (m!(i-1)!j) ((m!(i-1)!(j-w!(i)))+v!(i)))FI);
              j:=j+1
       OD;  
        i:=i+1
    OD 
 {  (m!(i-1)!((length (m!(i-1)))-1)) =knapsack (i-1) ((length (m!(i-1)))-1) w v ∧  i=length m }"
  apply vcg
(*1  ks_DL1*)
  apply (simp add: nth_Cons' list_list_update_def)
(*2  ks_DL2*)
  apply (smt diff_diff_cancel diff_is_0_eq' le_neq_implies_less le_numeral_extra(3) le_trans not_less_zero not_one_le_zero)

(*3  ks_DL3*)
  apply (rule conjI)   apply rule    apply (simp add:list_list_update_def)
  apply rule
  apply (smt Suc_le_mono Suc_pred add_gr_0 diff_diff_cancel diff_is_0_eq' le_add_diff_inverse le_neq_implies_less lessI less_antisym list_update_same_conv nth_list_update)
  apply rule
  apply (simp add: All_less_Suc)
  using  ks_DL3_1 apply blast
  apply (smt length_list_update list_eq_iff_nth_eq nth_list_update nth_list_update_neq)
 


  apply rule     apply (simp add:list_list_update_def)
  apply rule 
  apply (metis Suc_leI diff_diff_cancel diff_is_0_eq' diff_self_eq_0 le_neq_implies_less n_not_Suc_n nth_list_update_neq)
  apply rule 
  apply (simp add: All_less_Suc)
  using ks_DL3_2 apply blast
  apply (smt add_lessD1 diff_diff_cancel diff_is_0_eq le0 le_add_diff_inverse2 le_neq_implies_less length_list_update max.absorb2 n_not_Suc_n nth_list_update zero_less_diff)
 
      

(*4   ks_DL4*)
  apply rule  apply simp 
  apply rule  apply simp 
  apply rule
  apply auto[1] 
  apply rule  apply simp
  apply (metis add_le_imp_le_diff add_le_imp_le_right discrete le_neq_implies_less)

(*5  ks_DL5*)
  by (metis One_nat_def Suc_le_lessD Suc_pred diff_less le_SucE less_numeral_extra(1))

end

