theory Iter_Reduction_Results
  imports Main Iter_Reduction_Lemmas CancelResults
begin

(*The following were the lemmas to be proven:*)

lemma reduced_iter_length: "reduced (iter (length xs) reduct xs)"
proof(induction xs)
  case Nil
then have "(iter (length []) reduct []) = []" by simp
  then show ?case by simp
next
  case (Cons a xs)
  have 2: "(((length (a#xs) div 2 + 1))* 2) \<ge> length (a#xs) " using mult_2_greater by auto
  have "length (a # xs) > 0" by simp
  then have 1:"length (a # xs) div 2 + 1 \<le> length (a#xs)" by (meson discrete div_less_dividend one_less_numeral_iff semiring_norm(76))
  then show ?case 
  proof(cases "\<not>reduced (iter (length (a # xs)) reduct (a # xs))")
    case True
  then have a: "\<not>reduced (iter (length (a # xs)) reduct (a # xs))" by simp
  then have cont:"\<not>reduced (iter (length (a # xs) div 2 + 1) reduct (a # xs))" using not_reduced_iter_suc 1 by blast
  then have "length (iter (length (a # xs) div 2 + 1) reduct (a # xs)) = length (a#xs) - (((length (a#xs) div 2 + 1))* 2)" using reduct_iter_minus by (metis mult.commute)
  then have "length (iter (length (a # xs) div 2 + 1) reduct (a # xs)) = 0" using subtract_greater[of "length (a#xs)" "(length (a # xs) div 2 + 1) * 2"] 2 by argo
  then have "(iter (length (a # xs) div 2 + 1) reduct (a # xs)) = []" by simp
  then have "reduced (iter (length (a # xs) div 2 + 1) reduct (a # xs))" by simp
   then show ?thesis using cont by blast
  next
    case False
    then show ?thesis by simp
  qed
qed

lemma assumes "iter (length xs) reduct xs = iter (length ys) reduct ys"
  shows "cancels_eq xs ys"
proof-
  have "cancels_to xs (iter (length xs) reduct xs)" using iter_cancels_to by auto
  then have a: "cancels_eq  xs (iter (length xs) reduct xs)" unfolding cancels_eq_def by blast
  have "cancels_to ys (iter (length ys) reduct ys)" using iter_cancels_to by auto
  then have b: "cancels_eq (iter (length ys) reduct ys) ys" unfolding cancels_eq_def by blast
  then show ?thesis using a b unfolding cancels_eq_def using assms by auto
qed

lemma assumes "cancels_eq xs ys"
  shows "iter (length xs) reduct xs = iter (length ys) reduct ys"
proof-
  have "cancels_to xs (iter (length xs) reduct xs)" using iter_cancels_to by auto
  then have "cancels_eq  (iter (length xs) reduct xs) xs" unfolding cancels_eq_def by blast
  then have a: "cancels_eq (iter (length xs) reduct xs) ys" using assms unfolding cancels_eq_def by auto
  have "cancels_to ys (iter (length ys) reduct ys)" using iter_cancels_to by auto
  then have b: "cancels_eq ys (iter (length ys) reduct ys)" unfolding cancels_eq_def by blast
  have rel: "cancels_eq (iter (length xs) reduct xs)  (iter (length ys) reduct ys)"  using a b unfolding cancels_eq_def by auto
  have x: "reduced (iter (length xs) reduct xs)" using reduced_iter_length by blast
  have y:  "reduced (iter (length ys) reduct ys)" using reduced_iter_length by blast
  then show ?thesis using rel x y reduced_cancel_eq by blast
qed

end