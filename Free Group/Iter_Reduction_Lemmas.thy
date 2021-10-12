theory Iter_Reduction_Lemmas
  imports Main iter Cancellation
begin

fun reduct :: "('a,'b) word \<Rightarrow> ('a,'b) word"
  where
"reduct [] = []"|
"reduct [x] = [x]"|
"reduct (g1#g2#wrd) = (if (g1 = inverse g2) 
                           then wrd 
                           else (g1#(reduct (g2#wrd))))"

lemma cons_reduct: 
  assumes "g1 \<noteq> inverse g2" 
  shows "reduct (g1#g2#wrd) = (g1#(reduct (g2#wrd)))"
  by (simp add: assms)

lemma cancel_at_cons:
  assumes "i\<ge>0" "(1+i) < length a" "cancel_at i a = b"
  shows "cancel_at (1 + i) (c#a) = (c#b)"
proof-
  have "c#(take i a) = take (1 + i) (c#a)" using assms(1) assms(2) by auto
  moreover have "drop (i+2) a = drop (1 + (i+2)) (c#a)"using assms(1) assms(2) by simp
  ultimately show ?thesis unfolding cancel_at_def by (metis (no_types, lifting) add.commute append_Cons assms(3) cancel_at_def group_cancel.add2)
qed

lemma cancels_to_1_at_cons:
  assumes "i\<ge>0" "(1+i) < length a" "cancels_to_1_at i a b"
  shows "cancels_to_1_at (1 + i) (c#a) (c#b)"
  unfolding cancels_to_1_at_def
proof-
  have 1:"0 \<le> (1 + i)" using assms(1) by simp
  moreover have 2: "1 + (1 + i) < length (c # a)" using assms(2) by auto
  have "(inverse (a ! i)) = (a ! (i+1))" using assms(3) by (metis add.commute cancels_to_1_at_def)
  moreover then have 3: "inverse ((c # a) ! (1 + i)) = (c # a) ! (1 + (1 + i))" by simp
  have "(b = cancel_at i a)" using assms(3)using cancels_to_1_at_def by auto
  moreover then have 4: "c # b = cancel_at (1 + i) (c # a)" using cancel_at_cons assms(1) assms(2) by metis
  ultimately show "0 \<le> 1 + i \<and>
    1 + (1 + i) < length (c # a) \<and>
    inverse ((c # a) ! (1 + i)) = (c # a) ! (1 + (1 + i)) \<and>
    c # b = cancel_at (1 + i) (c # a)" using "2" "3" by blast
qed

lemma cancels_to_1_cons:
  assumes "cancels_to_1 a b"
  shows "cancels_to_1 (c#a) (c#b)"
  using assms
  unfolding cancels_to_1_def
proof-
  obtain i where "cancels_to_1_at i a b" using assms cancels_to_1_def by auto
  then have "i\<ge>0 \<and> (1+i) < length a" using cancels_to_1_at_def by auto
  then have "cancels_to_1_at (1 + i) (c#a) (c#b)" using \<open>cancels_to_1_at i a b\<close> cancels_to_1_at_cons by blast
  then show "\<exists>i. cancels_to_1_at i (c # a) (c # b)" by auto
qed

lemma cons_cancel_at: "cancels_to xs ys \<longrightarrow> cancels_to (x#xs) (x#ys)"
  unfolding cancels_to_def
  apply(rule impI)
proof(induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl a b c)
  then have "cancels_to_1 b c" by simp
  then have "cancels_to_1 (x#b) (x#c)" by (simp add: cancels_to_1_cons)
  then show ?case using rtrancl_into_rtrancl.IH by auto 
qed

lemma cancels_to_reduct:"cancels_to xs (reduct xs)"
proof(induction xs rule: reduct.induct)
  case 1
  then have "cancels_to [] []"  unfolding cancels_to_def by simp
  then show ?case by simp
next
  case (2 x)
  then have "cancels_to [x] [x]"  unfolding cancels_to_def by simp
  then show ?case by simp
next
  case (3 g1 g2 wrd)
  then show ?case
  proof (cases "g1 = inverse g2")
    case True
    have a: "(reduct (g1 # g2 # wrd)) = wrd" using True by simp
    then have 1: "reduct (g1 # g2 # wrd) = cancel_at 0 (g1 # g2 # wrd)" by (simp add: cancel_at_def)
    have 2: "(inverse ((g1 # g2 # wrd) ! 0) = ((g1 # g2 # wrd) ! (1 + 0)))" using True by (metis inverse_of_inverse nth_Cons_0 nth_Cons_Suc plus_1_eq_Suc)
    have "cancels_to_1_at 0 (g1 # g2 # wrd) (reduct (g1 # g2 # wrd))" using cancels_to_1_at_def using "1" "2" by fastforce
    then have "cancels_to_1 (g1 # g2 # wrd) (reduct (g1 # g2 # wrd))" using cancels_to_1_def by blast
    then show ?thesis by (simp add: cancels_to_def)
next
  case False
  then have "cancels_to (g2 # wrd) (reduct (g2 # wrd))" by (simp add: "3.IH")
  then have "cancels_to (g1#g2#wrd) (g1#(reduct (g2 # wrd)))" by (simp add: cons_cancel_at)
    then show ?thesis using False by (simp add: cons_reduct)
    qed
  qed

lemma iter_cancels_to: "cancels_to xs (iter n reduct xs)"
proof(induction n)
  case 0
  have "(iter 0 reduct xs) = xs" by simp
  then show ?case unfolding cancels_to_def by simp
next
  case (Suc n)
  then have 1: "cancels_to xs (iter n reduct xs)" by auto
  have "(iter (Suc n) reduct xs) = reduct (iter  n reduct xs)" by simp
  moreover have "cancels_to (iter n reduct xs) (reduct (iter  n reduct xs))" using cancels_to_reduct by auto
  ultimately have "cancels_to (iter n reduct xs) (iter (Suc n) reduct xs)" by simp
  then show ?case using 1 unfolding cancels_to_def by auto
qed

lemma cons_reduced:
  assumes "g \<noteq> FreeGroupMain.inverse h"
  shows "reduced (h # wrd) \<Longrightarrow> reduced (g#h#wrd)"
  using assms
proof-
  assume a:  "reduced (h#wrd)"
  have "reduced (g#h#wrd) = reduced (h#wrd)" using assms by simp
  then show ?thesis by (simp add: a)
qed

lemma cons_not_reduced: assumes "g \<noteq> FreeGroupMain.inverse h"
  shows "\<not> reduced (g#h#wrd) \<Longrightarrow> \<not> reduced (h # wrd)"
  using assms
proof-
  assume a: "\<not> reduced (g#h#wrd)"
  have "reduced (h # wrd) \<Longrightarrow> reduced (g#h#wrd)" using assms cons_reduced by simp
  then show ?thesis using a by blast
qed

lemma reduct_minus: assumes "\<not> (reduced xs)"
  shows "length (reduct xs) = (length xs) - 2"
  using assms
proof(induction xs rule: reduct.induct)
  case 1
then show ?case by simp
next
  case (2 g)
  then have a: "\<not> reduced [g]" by blast
  have "reduced [g]" by auto
  then show ?case using a by blast
next
case (3 g h wrd)
  then show ?case
  proof(cases "g = inverse h")
    case True
    then have "reduct (g#h#wrd) = wrd" by simp
then show ?thesis by simp
next
  case False
  then have "\<not> reduced (h # wrd)" using cons_not_reduced "3.prems" by auto
  then have a: "length (reduct (h # wrd)) = length (h # wrd) - 2" using "3.IH" False by blast
  have b: "length (h # wrd)  = length (g # h # wrd) - 1" by auto
  have "reduct (g # h # wrd) = g#(reduct (h # wrd))" using False by simp
  moreover have "length (g#(reduct (h # wrd))) - 1 = length (reduct ( h # wrd))" by simp
  ultimately have c: "length (reduct ( h # wrd)) = length (reduct (g # h # wrd)) - 1" by simp
  then have " length (reduct (g # h # wrd)) - 1 = (length (g # h # wrd) - 1) - 2" using a b c by argo
  then have "length (reduct (g # h # wrd)) - 1 = length (g # h # wrd) - 2 - 1" by simp
  then show ?thesis by (smt (verit, ccfv_SIG) Suc_1 \<open>\<not> reduced (h # wrd)\<close> \<open>reduct (g # h # wrd) = g # reduct (h # wrd)\<close> diff_Suc_1 diff_Suc_eq_diff_pred length_Cons reduced.elims(3))
  qed
qed

lemma reduced_reduct: assumes "reduced xs"
  shows "reduct xs = xs"
  using assms
proof(induction xs rule: reduct.induct)
  case 1
  then have "reduct [] = []" by simp
then show ?case by simp 
next
  case (2 x)
  then have "reduct [x] = [x]" by simp
  then show ?case by simp
next
  case (3 g1 g2 wrd)
  then have 1: "g1 \<noteq> FreeGroupMain.inverse g2" by auto
  then moreover have "reduced (g2 # wrd)" using cons_reduced "3.prems" by simp
  ultimately have "reduct (g2 # wrd) = g2 # wrd" using "3.IH" by blast
  then have "g1#(reduct (g2 # wrd)) = g1#g2 # wrd" by simp
  moreover have "reduct (g1#g2 # wrd) = (g1#reduct (g2 # wrd))" using 1  by simp
  ultimately show ?case by simp
qed

lemma reduced_imp_reduct: "reduced xs \<Longrightarrow> reduced (reduct xs)"
proof-
  assume assms: "reduced xs"
  then have "reduct xs = xs" using reduced_reduct by auto
  then show ?thesis using assms by simp
qed

lemma length_reduct:
 "length (reduct wrd) \<le> length wrd"
proof(induction wrd rule: reduct.induct)
case 1
  then show ?case by simp
next
case (2 x)
  then show ?case by simp
next
  case (3 g1 g2 wrd)
  then show ?case 
  proof(cases "g1 = inverse g2")
    case True 
    then show ?thesis using 3 by force
  next
    case False
    then show ?thesis using 3 by auto 
 qed  
qed

lemma length_reduct_iter:  "length (iter n reduct xs) \<le> length xs"
proof(induction n)
  case 0
  then have "(iter 0 reduct xs) = xs" by simp
  then show ?case by simp
next
  case (Suc n)
  have "reduct (iter n reduct xs) = (iter (Suc n) reduct xs)" by simp
  moreover have "length (reduct (iter n reduct xs)) \<le> length (iter n reduct xs)" using length_reduct by fast
 ultimately have "length (reduct (iter n reduct xs)) \<le> length (iter n reduct xs)" by simp
  then show ?case using Suc.IH by simp
qed

lemma reduct_iter_minus: assumes "\<not> reduced (iter n reduct xs)"
  shows "length (iter n reduct xs) = length xs - (2*n)"
  using assms
proof(induction n)
  case 0
  have 1: "length xs - 2 * 0 = length xs" by simp
  have 2: "(iter 0 reduct xs) = xs" by simp
  then show ?case using 1 2 by simp
next
  case (Suc n)
  then have "\<not> reduced (iter (Suc n) reduct xs)" by simp
  moreover have b: "(iter (Suc n) reduct xs) = reduct (iter n reduct xs)" by simp
  ultimately have a: "\<not> reduced (iter n reduct xs)" using reduced_imp_reduct by auto
  then have " length (iter n reduct xs) = length xs - (2 * n)" using Suc.IH by auto
  then have c: "length (iter n reduct xs) - 2 = length xs - (2 * n) - 2" by simp
  have "length (iter n reduct xs) - 2 = length (iter (Suc n) reduct xs)" using a b reduct_minus by (simp add: reduct_minus)
  moreover have "length xs - (2 * n) - 2 = length xs - (2 * Suc n)" by simp
  ultimately show ?case using c  by presburger
qed

lemma assumes "\<not> reduced wrd"
  shows "length (reduct wrd) < length wrd"
  using assms
proof(induction wrd rule:reduct.induct)
  case 1
  then have "reduced []" by simp
  then show ?case using "1.prems" by simp
next
  case (2 x)
  then have "reduced [x]" by simp
  then show ?case using "2.prems" by simp
next
  case (3 g1 g2 wrd)
  have "length (g1 # g2 # wrd) > 0" by simp
  then show ?case using reduct_minus "3.prems" by force
qed

lemma not_reduced_iter: assumes  "reduced (iter n reduct xs)"
  shows "reduced (iter (n+1) reduct xs)"
  using assms
proof-
  have "(iter (n+1) reduct xs) = reduct (iter (n) reduct xs)" by simp
  then show ?thesis by (simp add: reduced_imp_reduct assms)
qed

lemma reduced_iter_suc: assumes "reduced (iter n reduct xs)"
  shows "reduced (iter (n+k) reduct xs)"
  using assms
proof(induction k)
case 0
then show ?case by simp
next
  case (Suc k)
  then have "reduced (iter (n + k) reduct xs)" by simp
  then show ?case using  reduced_imp_reduct by auto
qed

lemma not_reduced_iter_suc: assumes "\<not> reduced (iter n reduct xs)" "k \<le> n"
  shows "\<not> reduced (iter k reduct xs)"
proof-
  show ?thesis using reduced_iter_suc  using assms(1) assms(2) le_Suc_ex by blast
qed

lemma mult_2_greater:"((x::nat) div 2 + 1) * 2 \<ge> x"  by simp

lemma subtract_greater: assumes "(x::nat) \<ge> y"
  shows "y - x = 0"
  using assms 
  by simp

end

