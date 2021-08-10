theory Reduction
imports "FreeGroupMain" "HOL-Library.FuncSet" "HOL-Algebra.Group"
begin

(*Lemmas on reduction and reduced functions, and the reduction relation.*)

lemma length_reduction:
 "length (reduction wrd) \<le> length wrd"
proof(induction wrd rule: reduction.induct)
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
    then show ?thesis using 3 
    by auto 
 qed  
qed

lemma decreasing_length:
  assumes "reduction wrd \<noteq> wrd"
  shows "length (reduction wrd) < length wrd"
  using assms
proof(induction wrd rule: reduction.induct)
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
    then have red_inv:"reduction (g1#g2#wrd) = reduction wrd" by auto
    then show ?thesis 
    proof(cases "reduction wrd = wrd")
      case True
      then have "reduction (g1#g2#wrd) = wrd" using red_inv by auto
      then have "length (reduction (g1#g2#wrd)) = length wrd" by auto    
      then show ?thesis 
        by simp
    next
      case False
      then have "length (reduction wrd) < length wrd" using 3 True by argo
      then show ?thesis using red_inv by force
    qed
  next
    case False
    have prem:"reduction (g1#g2#wrd) \<noteq> (g1#g2#wrd)" using 3 by argo
    then have "reduction (g1#g2#wrd) = g1#reduction (g2#wrd)" using False by auto
    then have "reduction (g2#wrd) \<noteq> g2#wrd" using prem by fastforce
    then have "length (g2#wrd) > length (reduction (g2#wrd))" using 3 False by blast
    then have "length (g1#g2#wrd) > length (reduction (g1#g2#wrd))" using False by force
    then show ?thesis by fast
  qed  
qed

lemma if_length_reduction_eq:
  assumes "length (reduction (wrd)) = length wrd"
  shows "reduction wrd = wrd"
  using assms
proof(induction wrd rule: reduction.induct)
case 1
  then show ?case 
    by simp 
next
  case (2 x)
  then show ?case by simp
next
case (3 g1 g2 wrd)
  then show ?case
  proof(cases "g1 = inverse g2")
    case True
    then have "reduction (g1#g2#wrd) = reduction (wrd)" by simp     
    then have "length (reduction (g1#g2#wrd)) = length (reduction (wrd))" by auto
    moreover have "length (wrd) > length (reduction wrd)" using 3 by (metis \<open>reduction (g1 # g2 # wrd) = reduction wrd\<close> decreasing_length impossible_Cons le_cases)
    then show ?thesis using 3 by auto
  next
    case False
    then show ?thesis using "3.prems" decreasing_length nat_neq_iff by blast
  qed
qed

lemma reduction_fixpt:
  assumes "reduction wrd = wrd"
  shows "reduced wrd"
  using assms
proof(induction wrd rule:reduction.induct)
case 1
then show ?case by simp
next
case (2 x)
  then show ?case by simp
next
  case (3 g1 g2 wrd)
  then show ?case by (metis decreasing_length impossible_Cons length_Cons less_Suc_eq less_or_eq_imp_le list.inject reduced.simps(3) reduction.simps(3))
qed

lemma reduction_fixpt_conv:
  assumes "reduced wrd"
  shows "reduction wrd = wrd"
  using assms
proof(induction wrd rule: reduction.induct)
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
      then show ?thesis using 3 
        by force
    next
    case False
    have "reduced (g2#wrd)" using False 3 by force
      then show ?thesis using False 3 by force
    qed
  qed

lemma reduced_rightappend:
  assumes "reduced (xs@ys)"
  shows "reduced xs"
  using assms
proof (induction xs rule : reduction.induct)
case 1
then show ?case try
  by simp
next
  case (2 x)
  then show ?case try
    by simp
next
  case (3 g1 g2 wrd)
  then show ?case
  proof (cases "g1 =  inverse g2")
    case True    
then show ?thesis 
  using "3.prems" by force
next
  case False
  have "reduced ((g2 # wrd) @ ys)" 
    by (metis "3.prems" append_Cons reduced.simps(3))
  then have "reduced (g2#wrd)" 
    using "3.IH"(2) False by auto
  then show ?thesis by (simp add: False)
qed
qed

lemma reduced_leftappend:
  assumes "reduced (xs@ys)" 
  shows "reduced ys"
  sorry

lemma assumes "\<not>(reduced ys)"
  shows  "\<not>(reduced (xs@ys))"
proof-
  have 1: "reduced (xs@ys) \<longrightarrow> reduced ys" using reduced_leftappend[of xs ys] by simp
  then show ?thesis using not_mono [OF 1] assms by argo
qed

lemma inv_not_reduced:
  assumes "(i + 1) < length wrd"  "inverse (wrd ! i) = (wrd ! (i + 1))" 
  shows "\<not>(reduced wrd)"
  using assms
proof-
  have "inverse (wrd ! i) = wrd ! (i + 1)" using assms by auto
  have "i + 1 < length wrd" using  assms by blast
  then have 1: "wrd = (take i wrd) @ ((wrd ! i)#(wrd !(i + 1))#(drop (i + 2) wrd))" by (metis Cons_nth_drop_Suc Suc_1 Suc_eq_plus1 add_Suc_right add_lessD1 append_take_drop_id)
  then have "\<not>(reduced ((wrd ! i)#(wrd ! (i + 1))#(drop (i + 2) wrd)))" using assms by (metis inverse_of_inverse reduced.simps(3))
  then have "reduced wrd = False" using "1" by (metis reduced_leftappend) 
  then show ?thesis using assms by simp
qed

lemma reduced_no_inv:
  assumes "reduced wrd" "(i + 1) < length wrd"
  shows "\<not>(inverse (wrd ! i)) = (wrd ! (i + 1))"
proof- 
  have 1: "((inverse (wrd ! i)) = (wrd ! (i + 1))) \<longrightarrow> (\<not>(reduced wrd))" using inv_not_reduced assms(2) by auto
  then show ?thesis using not_mono [OF 1] assms by argo
qed

lemma inv_emptylist:
  assumes "h = inverse g"
  shows "[g, h] ~ []"
  using assms reln.base inverse.simps by simp

lemma relation: "(xs@ys) ~ xs@[g,inverse g]@ys"
  using reln.base reln.refl reln.mult
proof-
  have "(xs@[g, inverse g]) ~ xs" using reln.base reln.mult reln.refl by fastforce
  then show ?thesis using mult[of "xs@[g, inverse g]" "xs" "ys" "ys"] reln.refl reln.sym
    by auto
qed

lemma rel_to_reduction:"xs ~ reduction xs"
proof(induction xs rule:reduction.induct )
  case 1
  then show ?case 
    using reln.refl by auto
next
  case (2 x)
  then show ?case using reln.refl by auto
next
  case (3 g1 g2 wrd)
  then show ?case
  proof(cases "g1 = inverse g2")
    case True
    have "[g1,  g2] ~ []" using reln.base[of "g1"] inverse_of_inverse[of "g1" "g2"] True
      by blast
    then have 1:"([g1,g2]@wrd) ~ wrd" using reln.mult refl by fastforce
    with 3(1) have 2:"reduction ([g1,g2]@wrd) ~ wrd" using reln.trans True 
      using append_Cons append_Nil reduction.simps(3) reln.sym by auto
    then show ?thesis using 1 reln.sym reln.trans 
      by (metis append_Cons append_Nil)
next
  case False
  then have "([g1]@(g2#wrd)) ~ ([g1] @(reduction (g2#wrd)))" using 3(2) reln.mult reln.refl 
    by blast
  then have "([g1]@(g2#wrd)) ~ (reduction (g1#g2#wrd))" using False by simp
  then show ?thesis by simp
qed
qed


end
