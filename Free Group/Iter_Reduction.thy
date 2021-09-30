theory Iter_Reduction
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

lemma "cancels_to xs (reduct xs)"
proof(induction xs rule: reduction.induct)
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
  then have "cancels_to (g2 # wrd) (reduct (g2 # wrd))" by (simp add: "3.IH"(2))
  then have "cancels_to (g1#g2#wrd) (g1#(reduct (g2 # wrd)))" by (simp add: cons_cancel_at)
    then show ?thesis using False by (simp add: cons_reduct)
    qed
  qed

lemma assumes "iter (length xs) reduction xs = iter (length ys) reduction ys"
  shows "cancels_eq xs ys"
  sorry

lemma assumes "cancels_eq xs ys"
  shows "iter (length xs) reduction xs = iter (length ys) reduction ys"
  sorry

