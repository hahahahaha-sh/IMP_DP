theory lcs
  imports "Hoare_Logic" "Arith2" 
begin

definition list_list_update ::"nat list list ⇒ nat ⇒ nat⇒ nat ⇒ nat list list"
  where "list_list_update dlist i j value =list_update dlist i  (list_update (dlist!i) j value)"

fun lcs :: "nat ⇒ nat ⇒ char list ⇒ char list ⇒ nat" where
  "lcs 0 _ A B = 0" |
  "lcs _ 0 A B = 0" |
  "lcs (Suc i) (Suc j) A B = (if A !(Suc i)  = B ! (Suc j) then 1 + lcs i j A B else max (lcs i (j + 1) A B) (lcs (i + 1) j A B))"

lemma lcs_incremental:
  assumes "i ≥ 1" "j ≥ 1" "A ! i = B ! j"
  shows "lcs i j A B = lcs (i - 1) (j - 1) A B + 1"
  by (metis add.commute assms(1) assms(2) assms(3) lcs.simps(3) ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc)

lemma lcs_DL3_1:
  assumes "Suc 0 ≤ length m"
    and "(∀k<length m. length (m ! k) = length (m ! (k - Suc 0)) ∧ Suc 0 ≤ length (m ! k))"
    and "(∀k<i. ∀j<length (m ! (k - Suc 0)). m ! k ! j = lcs k j A B)"
    and "(∀k<j. m ! i ! k = lcs i k A B)"
    and "Suc 0 ≤ i" "Suc 0 ≤ j" "i < length m" "j ≤ length (m ! (i - Suc 0))"
    and "j ≤ length (m ! i) - Suc 0" "A ! i = B ! j"
  shows "(m ! i)[j := Suc (m ! (i - Suc 0) ! (j - Suc 0))] ! j = lcs i j A B"
proof (cases "i = 0 ∨ j = 0")
  case True
  then show ?thesis
    using assms
    by blast 
next
  case False
  from assms False show ?thesis
  proof (cases "A ! i = B ! j")
    case True
    then have "lcs  i j A B = lcs (i-1) (j-1) A B +1"
      by (simp add: assms(10) assms(5) assms(6) assms(9) lcs_incremental)
     then have "m!(i-1)!(j-1) =  lcs (i - 1) (j - 1) A B"
      using assms(3)
      by (metis (no_types, lifting) One_nat_def Suc_le_lessD add_less_cancel_left assms(2) assms(5) assms(6) assms(7) assms(8) diff_less less_SucI less_numeral_extra(1) ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc)
      moreover from True have "(m ! i)[j := Suc (m ! (i - 1) ! (j - 1))] ! j = 1 + lcs (i - 1) (j - 1) A B"
      by (metis One_nat_def assms(9) assms(2) assms(7) calculation le_add_diff_inverse le_imp_less_Suc nth_list_update_eq plus_1_eq_Suc)
      ultimately show ?thesis
      by (simp add: ‹lcs i j A B = lcs (i - 1) (j - 1) A B + 1›)
  next
    case False
    then show ?thesis
    using assms
    by blast 
qed
qed


lemma lcs_DL3_2: 
  assumes "Suc 0 ≤ length m"
    and "(∀k<length m. length (m ! k) = length (m ! (k - Suc 0)) ∧ Suc 0 ≤ length (m ! k))"
    and "(∀k<i. ∀j<length (m ! (k - Suc 0)). m ! k ! j = lcs k j A B)"
    and "(∀k<j. m ! i ! k = lcs i k A B)"
    and "Suc 0 ≤ i" "Suc 0 ≤ j" "i < length m" "j ≤ length (m ! (i - Suc 0))"
    and "j ≤ length (m ! i) - Suc 0" "A ! i ≠ B ! j"
  shows "(m ! i)[j := max (lcs i (j - Suc 0) A B) (m ! (i - Suc 0) ! j)] ! j = lcs i j A B"
proof (cases "i = 0 ∨ j = 0")
  case True
  then show ?thesis
  using assms
  by blast 
next
  case False
  from assms False show ?thesis
  proof (cases "A ! i = B ! j")
    case True
    then show ?thesis
    using assms
    by blast 
  next
    case False  
    then have "lcs  i j A B =  max (lcs i (j - Suc 0) A B) (lcs (i-1) (j) A B)"
    by (metis (no_types, lifting) One_nat_def assms(5) assms(6) lcs.simps(3) le_add_diff_inverse le_add_diff_inverse2 max.commute plus_1_eq_Suc)
    then have "m!(i-1)!(j) =  lcs (i - 1) (j ) A B"
    by (metis (no_types, lifting) One_nat_def Suc_less_eq Suc_pred assms(9) assms(2) assms(3) assms(5) assms(7) diff_less le_imp_less_Suc less_SucI less_numeral_extra(1))   
    then show ?thesis
    by (metis One_nat_def ‹lcs i j A B = max (lcs i (j - Suc 0) A B) (lcs (i - 1) j A B)› assms(9) assms(2) assms(7) assms(8) diff_diff_cancel diff_is_0_eq' le_eq_less_or_eq not_one_le_zero nth_list_update_eq)
qed
qed

lemma lcs: "VARS m A B i j
 {length m ≥1}
j:=1;i:=1;m:=[[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],
         [0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0]];
A:=[CHR ''#'',CHR ''a'',CHR ''b'',CHR ''c'',CHR ''b'',CHR ''d'',CHR ''a'',CHR ''b''];
B:=[CHR ''#'',CHR ''b'',CHR ''d'',CHR ''c'',CHR ''a'',CHR ''b'',CHR ''a''];
  WHILE i ≤ length m -1
  INV{ length m ≥1 
       ∧(∀k .k<length m ⟶ length (m!k) = length (m!(k-1))  ∧  length (m!k)≥1 )
       ∧(∀k. k<length m ⟶ m!k!0=0)
       ∧ (∀k. k < i ⟶ 
             ( ∀ j. j<length (m!(k-1))⟶
               m!k!j =lcs k j A B  )  )
        ∧  i≥1∧   i≤length m ∧  j≤length (m!(i-1)) ∧ j≥1  
       }
   DO       
      j:=1;
      WHILE j ≤ length (m!i)-1
      INV{ length m ≥1
           ∧(∀k .k<length m ⟶ length (m!k) = length (m!(k-1))  ∧  length (m!k)≥1 )
           ∧(∀k. k<length m ⟶ m!k!0=0)
           ∧ (∀k. k < i ⟶ 
             ( ∀ j. j<length (m!(k-1))⟶
                  m!k!j =lcs k j A B ))
           ∧ ( ∀ k. k < j⟶
                  m!i!k =lcs i k A B  )  
              ∧  i≥1∧   i<length m ∧  j≤length (m!(i-1)) ∧ j≥1   }
       DO
            IF (A!(i))=(B!j) THEN  m:=list_list_update m (i) j (m!(i-1)!(j-1)+1) 
            ELSE  m:=list_list_update m (i) j (max (m!(i)!(j-1)) (m!(i-1)!j))  FI;
            j:=j+1
       OD;  
        i:=i+1
    OD 
 {  (m!(i-1)!((length (m!(i-1)))-1)) =lcs (i-1) ((length (m!(i-1)))-1) A B ∧  i=length m }"
  apply vcg
(*1  lcs_DL1*)
  apply (simp add: nth_Cons' list_list_update_def)
(*2  lcs_DL2*)
  apply (smt Suc_diff_1 diff_diff_cancel diff_is_0_eq' dual_order.order_iff_strict dual_order.trans lcs.simps(2) less_one zero_neq_one)
(*3  lcs_DL3*)
  apply rule   apply rule    apply (simp add:list_list_update_def)
  apply rule
  apply (smt length_list_update list_eq_iff_nth_eq nth_list_update nth_list_update_neq)
  apply rule
  apply (metis le_zero_eq not_less_eq_eq nth_list_update_eq nth_list_update_neq)
  apply (simp add: All_less_Suc)
  apply rule
  using lcs_DL3_1 apply blast
  apply (metis One_nat_def Suc_leI cancel_comm_monoid_add_class.diff_cancel diff_diff_cancel diff_is_0_eq' le_neq_implies_less nth_list_update_neq zero_neq_one)

  apply rule     apply (simp add:list_list_update_def)
  apply rule
  apply (metis length_list_update nth_list_update)   
  apply rule
  apply (smt add_lessD1 diff_diff_cancel diff_is_0_eq le0 le_add_diff_inverse2 le_neq_implies_less length_list_update max.absorb2 n_not_Suc_n nth_list_update zero_less_diff)
  apply (simp add: All_less_Suc)
  apply rule
  using lcs_DL3_2 apply blast
  apply (metis Suc_leI diff_diff_cancel diff_is_0_eq' diff_self_eq_0 le_neq_implies_less n_not_Suc_n nth_list_update_neq)
      

(*4  lcs_DL4*)
  apply rule  apply simp 
  apply rule
  apply blast
  apply rule    apply simp 
  apply (simp add: All_less_Suc)
  apply (metis Suc_pred le_SucE less_imp_Suc_add zero_less_Suc)

(*5  lcs_DL5*)
  by (metis One_nat_def Suc_le_lessD Suc_pred diff_less le_SucE less_numeral_extra(1))

end

