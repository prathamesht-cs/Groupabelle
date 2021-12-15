theory CancelLemmas
imports "FreeGroupMain" "Cancellation" "Reduction" "HOL-Proofs-Lambda.Commutation"
begin

(*1. Cancellation append lemmas*)

lemma cancel_at_leftappend:
  assumes "i\<ge>0" "(1+i) < length a" "cancel_at i a = b"
  shows "cancel_at (length c + i) (c@a) = (c@b)"
proof-
  have "c@(take i a) = take (length c + i) (c@a)" using assms(1) assms(2) by auto
  moreover have "drop (i+2) a = drop (length c + (i+2)) (c@a)"using assms(1) assms(2) by simp
  ultimately show ?thesis unfolding cancel_at_def by (metis add.assoc add.commute append.assoc assms(3) cancel_at_def)
qed

lemma cancel_at_rightappend:
  assumes "i\<ge>0" "(1+i) < length a" "cancel_at i a = b"
  shows "cancel_at i (a@c) = (b@c)"
proof-
  have "take i (a@c) = take i a" using assms(1) assms (2) by simp
  moreover have "(drop (2 + i) a)@c = drop (2+i) (a@c)" using assms(1) assms(2) by simp
  ultimately show ?thesis unfolding cancel_at_def by (metis append.assoc assms(3) cancel_at_def)
qed

lemma cancels_to_1_at_leftappend:
  assumes "i\<ge>0" "(1+i) < length a" "cancels_to_1_at i a b"
  shows "cancels_to_1_at (length c + i) (c@a) (c@b)"
  unfolding cancels_to_1_at_def
proof-
  have 1:"0 \<le> (length c + i)" using assms(1) by simp
  moreover have 2: "1 + (length c + i) < length (c @ a)" using assms(2) by auto
  have "(inverse (a ! i)) = (a ! (i+1))" using assms(3) by (metis add.commute cancels_to_1_at_def)
  moreover then have 3: "inverse ((c @ a) ! (length c + i)) = (c @ a) ! (1 + (length c + i))" by (metis add.commute add.left_commute nth_append_length_plus)
  have "(b = cancel_at i a)" using assms(3)using cancels_to_1_at_def by auto
  moreover then have 4: "c @ b = cancel_at (length c + i) (c @ a)" using cancel_at_leftappend assms(1) assms(2) by metis
  ultimately show "0 \<le> length c + i \<and>
    1 + (length c + i) < length (c @ a) \<and>
    inverse ((c @ a) ! (length c + i)) = (c @ a) ! (1 + (length c + i)) \<and>
    c @ b = cancel_at (length c + i) (c @ a)" using "2" "3" by blast
qed

lemma cancels_to_1_at_rightappend:
  assumes "i\<ge>0" "(1+i) < length a" "cancels_to_1_at i a b"
  shows "cancels_to_1_at i (a@c) (b@c)"
  unfolding cancels_to_1_at_def
proof-
  have 1:"0 \<le> i" using assms(1) by simp
  moreover have 2: "1 + i < length (a@c)" using assms(2) by auto
  have "(inverse (a ! i)) = (a ! (i+1))" using assms(3) by (metis add.commute cancels_to_1_at_def)
  moreover then have 3: "inverse ((a @ c) ! i) = (a @ c) ! (1 + i)" by (metis Suc_eq_plus1 Suc_lessD add.commute assms(2) nth_append)
  have "(b = cancel_at i a)" using assms(3)using cancels_to_1_at_def by auto
  moreover then have 4: "b@c = cancel_at i (a@c)" using cancel_at_rightappend assms(1) assms(2) by metis
  ultimately show "0 \<le> i \<and>
    1 + i < length (a @ c) \<and> inverse ((a @ c) ! i) = (a @ c) ! (1 + i) \<and> b @ c = cancel_at i (a @ c)" using "2" "3" by blast
qed

lemma cancels_to_1_leftappend:
  assumes "cancels_to_1 a b"
  shows "cancels_to_1 (c@a) (c@b)"
  using assms
  unfolding cancels_to_1_def
proof-
  obtain i where "cancels_to_1_at i a b" using assms cancels_to_1_def by auto
  then have "i\<ge>0 \<and> (1+i) < length a" using cancels_to_1_at_def by auto
  then have "cancels_to_1_at (length c + i) (c@a) (c@b)" using \<open>cancels_to_1_at i a b\<close> cancels_to_1_at_leftappend by auto
  then show "\<exists>i. cancels_to_1_at i (c @ a) (c @ b)" by auto
qed

lemma cancels_to_1_rightappend:
  assumes "cancels_to_1 a b"
  shows "cancels_to_1 (a@c) (b@c)"
  using assms
  unfolding cancels_to_1_def
proof-
 obtain i where "cancels_to_1_at i a b" using assms cancels_to_1_def by auto
  then have "i\<ge>0 \<and> (1+i) < length a" using cancels_to_1_at_def by auto
  then have "cancels_to_1_at i (a@c) (b@c)" by (simp add: cancels_to_1_at_rightappend \<open>cancels_to_1_at i a b\<close>)
  then show "\<exists>i. cancels_to_1_at i (a @ c) (b @ c)" by auto
qed

lemma cancels_to_leftappend:
 "cancels_to a b \<longrightarrow> cancels_to (z@a) (z@b)"
  unfolding cancels_to_def
  apply(rule impI)
proof(induction rule:rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl a b c)
  then have 1:"cancels_to_1 (z@b) (z@c)"by (simp add: cancels_to_1_leftappend)
  have "cancels_to_1\<^sup>*\<^sup>* (z @ a) (z @ b)" by (simp add: rtrancl_into_rtrancl.IH)
  then show "cancels_to_1\<^sup>*\<^sup>* (z @ a) (z @ c)" using 1 by auto
qed

lemma cancels_to_rightappend:
 "cancels_to a b \<longrightarrow> cancels_to (a@z) (b@z)"
  unfolding cancels_to_def
  apply(rule impI)
proof(induction rule:rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl a b c)
  then have 1:"cancels_to_1 (b@z) (c@z)"by (simp add: cancels_to_1_rightappend)
  have "cancels_to_1\<^sup>*\<^sup>* (a@z) (b@z)" by (simp add: rtrancl_into_rtrancl.IH)
  then show "cancels_to_1\<^sup>*\<^sup>* (a@z) (c@z)" using 1 by auto
qed

lemma cancels_eq_leftappend:
"cancels_eq a b \<longrightarrow> cancels_eq (z@a) (z@b)"
  unfolding cancels_eq_def
  apply(rule impI)
proof(induction rule:rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl a b c)
  then have 1: "cancels_to (z@b) (z@c) \<or> cancels_to (z@c) (z@b)" using cancels_to_leftappend by blast
  have "(\<lambda> wrd1 wrd2. cancels_to wrd1 wrd2 \<or> cancels_to wrd2 wrd1)\<^sup>*\<^sup>* (z @ a) (z @ b)" by (simp add: rtrancl_into_rtrancl.IH)
  then show "(\<lambda> wrd1 wrd2. cancels_to wrd1 wrd2 \<or> cancels_to wrd2 wrd1)\<^sup>*\<^sup>* (z @ a) (z @ c)" unfolding cancels_eq_def using 1  by (metis (no_types, lifting) rtranclp.simps)
qed

lemma cancels_eq_rightappend:
"cancels_eq a b \<longrightarrow> cancels_eq (a@z) (b@z)"
  unfolding cancels_eq_def
  apply(rule impI)
proof(induction rule:rtranclp.induct)
case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl a b c)
  then have 1: "cancels_to (b@z) (c@z) \<or> cancels_to (c@z) (b@z)" using cancels_to_rightappend by auto
  have "(\<lambda> wrd1 wrd2. cancels_to wrd1 wrd2 \<or> cancels_to wrd2 wrd1)\<^sup>*\<^sup>* (a@z) (b@z)" by (simp add: rtrancl_into_rtrancl.IH)
  then show "(\<lambda> wrd1 wrd2. cancels_to wrd1 wrd2 \<or> cancels_to wrd2 wrd1)\<^sup>*\<^sup>* (a@z) (c@z)" unfolding cancels_eq_def using 1  by (metis (no_types, lifting) rtranclp.simps)
qed

(*2. Cancellation and Reduction relation.*)

lemma cancels_imp_rel: "cancels_to x y \<Longrightarrow> x ~ y"
  unfolding cancels_to_def
proof(induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by blast
next
  case (rtrancl_into_rtrancl a b c)
  then have "cancels_to_1 b c" by simp
  then obtain i where i:"cancels_to_1_at i b c" unfolding cancels_to_1_def by meson
  then have c_def:"(take i b)@(drop (i + 2) b) = c" unfolding cancels_to_1_at_def cancel_at_def
    by force
  moreover have "b!i = inverse (b!(i+1))" using i  unfolding cancels_to_1_at_def cancel_at_def
    using inverse_of_inverse 
    by (simp add: inverse_of_inverse add.commute)
  then have "[b!i, b!(i+1)] ~ []" 
    by (metis base inverse_of_inverse)
  then have "([b!i, b!(i+1)]@(drop (i+2) b)) ~ []@(drop (i+2) b)"
    using reln.refl reln.mult by fast
  then have "((take i b)@(([b!i, b!(i+1)]@(drop (i+2) b)))) ~ (take i b)@(drop (i+2) b)"
    using reln.refl reln.mult 
    by (simp add: mult reln.refl)
  then have "b ~ c" using c_def 
    by (metis Cons_nth_drop_Suc add.commute add_2_eq_Suc' append_Cons append_self_conv2 cancels_to_1_at_def i id_take_nth_drop linorder_not_less plus_1_eq_Suc trans_le_add2)
  then show ?case using reln.trans rtrancl_into_rtrancl(3) by fast
qed

lemma  "x ~ y \<Longrightarrow> cancels_eq x y"
proof(induction rule:reln.induct)
case (refl a)
then show ?case unfolding cancels_eq_def cancels_to_def by simp
next
  case (sym a b)
  then show ?case unfolding cancels_eq_def 
    by (metis (no_types, lifting) sympD sympI symp_rtranclp)
next
  case (trans a b c)
  then show ?case by (metis (no_types, lifting) cancels_eq_def rtranclp_trans)
next
  case (base g)
  then have "cancels_to_1_at 0 [g, inverse g] []" unfolding cancels_to_1_at_def cancel_at_def by auto
  then have "cancels_to [g, inverse g] []" unfolding cancels_to_def using cancels_to_1_def by auto
  then show ?case unfolding cancels_eq_def by (simp add: r_into_rtranclp)
next
  case (mult xs xs' ys ys')
  have "cancels_eq xs xs'" by (simp add: mult.IH(1))
  then have 1:"cancels_eq (xs@ys) (xs'@ys)"  by (simp add: cancels_eq_rightappend)
  have "cancels_eq ys ys'"  by (simp add: mult.IH(2))
  then have 2:"cancels_eq (xs'@ys) (xs'@ys')" by (simp add: cancels_eq_leftappend)
  then show "cancels_eq (xs@ys) (xs'@ys')" using 1 2  by (metis (no_types, lifting) cancels_eq_def rtranclp_trans)
qed

(*3. Cancellation on reduced words.*)

lemma reduced_no_cancels_to_1_at:
  assumes "reduced xs"
  shows "(\<nexists>i . cancels_to_1_at i xs ys)"
proof(rule ccontr)
  assume assm: "\<not>(\<nexists>i . cancels_to_1_at i xs ys)"
  hence "\<exists>i . cancels_to_1_at i xs ys" by auto
  then obtain i where "cancels_to_1_at i xs ys" by auto
  then have 1:"inverse (xs!i) = (xs!(i+1))" using cancels_to_1_at_def by (simp add: cancels_to_1_at_def)
  have 2: "i + 1 < length xs" by (metis \<open>cancels_to_1_at i xs ys\<close> add.commute cancels_to_1_at_def)
  then have "xs = (take i xs) @ ((xs!i)#(xs!(i+1))#(drop (i+2) xs))" by (metis Cons_nth_drop_Suc Suc_1 Suc_eq_plus1 add_Suc_right add_lessD1 append_take_drop_id)
  then have "reduced ((xs!i)#(xs!(i+1))#(drop (i+2) xs))" using assms reduced_leftappend by metis
  then show "False" using reduced.simps  by (simp add: "1" inverse_of_inverse)
qed

lemma cancels_to_1_red:
  assumes "reduced x"
  shows "\<forall>y. \<not>(cancels_to_1 x y)"
proof(rule ccontr)
  assume assm : "\<not>(\<forall>y. \<not>(cancels_to_1 x y))"
  then have "\<exists>y. cancels_to_1 x y" by simp
  then obtain y where y : "cancels_to_1 x y" by auto
  then have 1: " \<exists>i\<ge>0. cancels_to_1_at i x y" 
    unfolding cancels_to_1_def cancels_to_1_at_def by simp
  then have "reduced x = False" using "1" using reduced_no_cancels_to_1_at by auto
  then show "False" using assms by simp
qed

lemma reduced_normal:
  assumes "reduced x"
  shows "(\<not> Domainp cancels_to_1 x)"
proof-
  show ?thesis using assms cancels_to_1_red by (simp add: cancels_to_1_red Domainp.simps)
qed

(*Lemmas about cancels_eq*)

lemma eq_symp: "cancels_eq = (symclp cancels_to)^**"
  unfolding cancels_eq_def symclp_def
  by simp

lemma symp_sup:"(symclp cancels_to)^** = (sup cancels_to cancels_to^--1)^**"
proof-
  show ?thesis using symclp_pointfree[of "cancels_to"] by metis
qed

lemma sympstar:"(symclp cancels_to)^** = (symclp cancels_to_1)^**"
proof-
  have 1:"(symclp cancels_to)^** = (sup cancels_to cancels_to^--1)^**" using symp_sup by simp
  have 2: "... = (sup cancels_to_1^** (cancels_to_1^**)^--1)^**" using cancels_to_def by metis
  have 3: "... = (sup cancels_to_1 cancels_to_1^--1)^**" using rtranclp_sup_rtranclp rtranclp_conversep by metis
  have 4: "... = (symclp cancels_to_1)^**"  using symclp_pointfree[of "cancels_to_1"] by metis
  show ?thesis by(simp add: 1 2 3 4)
qed


(*Useful lemmas about order of cancellation.*)

lemma a1: 
  assumes"j \<ge> 0" "j + 2 < length x" 
  shows "take j x @ drop (2+j) x = take j x @ [nth x (2+j)] @  drop (2+(1+j)) x"
  using assms
proof(induction j)
case 0
  then show ?case by (metis Suc_1 add.left_neutral add.right_neutral add_2_eq_Suc append_Cons append_take_drop_id id_take_nth_drop same_append_eq self_append_conv2)
next
case (Suc j)
  then show ?case using Cons_nth_drop_Suc by fastforce
qed

lemma a2: 
  assumes"j \<ge> 0" "j + 2 < length x" 
  shows "take (j+1) x @ drop (2+(j+1)) x = take j x @ [nth x j] @  drop (2+(1+j)) x"
  using assms
proof(induction j)
case 0
  then show ?case by (metis Suc_1 Suc_inject add.commute add_2_eq_Suc' add_lessD1 append_Nil id_take_nth_drop plus_nat.add_0 take_Suc_Cons take_eq_Nil)
next
case (Suc j)
  then show ?case by (metis add.commute add_lessD1 append_assoc plus_1_eq_Suc take_Suc_conv_app_nth)
qed

lemma drop_assoc: assumes "i \<le> j"
  shows  "drop i ((take j xs)@(drop (j+2) xs)) =  (drop i (take j xs)) @(drop (j+2) xs)"
  using assms
proof(induction xs arbitrary: i j)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
  proof(cases "i = 0")
    case True
    then show ?thesis by simp
  next
    case False
    have i: "i > 0" using False by simp
    have j:"j \<ge> 1" using False Cons(2) by arith
    then have "take j (a#xs) = a#(take (j - 1) xs)" by (simp add: take_Cons')
    moreover have "drop (j + 2) (a#xs) = drop (j + 1) xs" using j by force
    ultimately have 1:"(take j (a#xs))@(drop (j + 1) xs) = a#(take (j-1) xs)@(drop (j + 1) xs)" by simp
    with False
    have 2: "drop i (a#(take (j-1) xs)@(drop (j + 1) xs)) = (drop (i-1) ((take (j-1) xs)@(drop (j + 1) xs)))"using  drop_Cons' by metis
    have 3: "drop i (a#(take (j-1) xs)@(drop (j + 1) xs)) = (drop (i-1) ((take (j-1) xs)@(drop ((j - 1) + 2) xs)))" using "2" j by auto
    then have 4: "... = (drop (i-1) (take (j-1) xs) @ drop ((j-1) + 2) xs)" using Cons(1)[of "i-1" "j-1"] Cons(2) i j by linarith
    then have 5: "... = drop i (a#(take (j-1) xs)) @ drop (j + 2) (a#xs)" by (metis (no_types, hide_lams) False \<open>drop (j + 2) (a # xs) = drop (j + 1) xs\<close> drop_Cons' drop_drop j le_add_diff_inverse2 nat_1_add_1)
    then have 6: "... = drop i (take j (a#xs)) @  drop (j + 2) (a#xs)"  using \<open>take j (a # xs) = a # take (j - 1) xs\<close> by presburger
    then show ?thesis by (metis "1" "3" "4" "5" \<open>drop (j + 2) (a # xs) = drop (j + 1) xs\<close>)
  qed
qed

lemma take_assoc:
  assumes "i \<le> j"
(*take i (cancel_at j xs) = take i xs*)
  shows  "take i ((take j xs)@(drop (j+2) xs)) = take i xs"
  using assms
proof(induction xs arbitrary: i j)
  case (Cons a xs)
  then show ?case
  proof(cases "i = 0")
    case True
    then show ?thesis by simp
  next
    case False
    hence j:"j \<ge> 1" using Cons(2) by arith
    then have "take j (a#xs) = a#(take (j - 1) xs)"  
      by (simp add: take_Cons')
    moreover have "drop (j + 2) (a#xs) = drop (j + 1) xs" using j by force
    ultimately have 1:"(take j (a#xs))@(drop (j + 1) xs) = a#(take (j-1) xs)@(drop (j + 1) xs)"
      by simp
    with take_Cons' False
    have 2:"take i  (a#(take (j-1) xs)@(drop (j + 1) xs)) = a#(take (i - 1) ((take (j-1) xs)@(drop (j + 1) xs)))"
      by metis
    then have 3:"... = a#(take (i - 1) xs)" using Cons(1)[of "i-1" "j-1"] Cons(2) using j by auto
    then have 4:"... = (take i (a#xs))" using False
      by (metis take_Cons')
    then show ?thesis
      by (metis "2" "3" Cons_eq_appendI \<open>drop (j + 2) (a # xs) = drop (j + 1) xs\<close> \<open>take j (a # xs) = a # take (j - 1) xs\<close>)
  qed
qed(auto)

lemma cancel_order: assumes "i +1 < j" "j + 1 < length xs"
  shows "cancel_at i (cancel_at j xs) = (cancel_at (j-2) (cancel_at i xs))"
  using assms
proof(induction xs arbitrary: i j)
  case Nil
  then show ?case unfolding cancel_at_def by force
next
  case (Cons a xs)
  then show ?case
  proof(cases "i \<le> 1")
    case True
    show ?thesis
    proof(cases "i = 0")
      case True
      have 1: "take i (take j (a # xs) @ drop (2 + j) (a # xs)) = []" using True by simp
      have 2: "take (j - 2) (take i (a # xs) @ drop (2 + i) (a # xs)) =  take (j - 2) (drop (2 + i) (a # xs))" using True by simp
      have 3: "drop (2 + (j - 2)) (take i (a # xs) @ drop (2 + i) (a # xs)) = drop (2 + (j - 2)) (drop (2 + i) (a # xs))" using True by simp
      then have 4: "... = drop (j + 2) (a#xs)" using True using Cons.prems(1) canonically_ordered_monoid_add_class.lessE by fastforce
      have ij: "2 + i \<le> j" using assms(1) using Cons.prems(1) by linarith
      have 5: "drop (2 + i) ((take j (a # xs)) @ drop (2 + j) (a # xs)) = (drop (2 + i) (take j (a # xs))) @ (drop (2 + j) (a # xs))" using drop_assoc[of "2+i" "j"] ij by (smt (z3) add.commute)
      have 6: "(drop (2 + i) (take j (a # xs))) = (drop 2 (take j (a # xs)))" using True by auto
      then have 7: "... =  take (j - 2) (drop (2 + i) (a # xs))" by (simp add: "6" True drop_take)
      then have 8: "... = take (j - 2) (drop (2 + i) (a # xs))" using True by blast
      show ?thesis unfolding cancel_at_def by (metis "1" "2" "3" "4" "5" "6" "7" add.commute append_self_conv2)
    next
      case False
      then have i1: "i = 1" using True by linarith
      have 1: "take i (take j (a # xs)) = take 1 (a#(take (j - 1) xs))" using i1 take_Cons' by (metis Cons.prems(1) less_nat_zero_code)
      then have 2: "... = (a#(take 0 (take (j - 1) xs)))" using take_Cons' by simp
      then have 3: "... = [a]" by simp
      have 4: "drop (2 + i) (take j (a # xs) @ drop (2 + j) (a # xs)) = (drop (2 + i) (take j (a # xs))) @ drop (2 + j) (a # xs)" using drop_assoc by (metis Cons.prems(1) add.commute discrete i1 nat_1_add_1)
      then have 5: "... =  (drop (1 + i) (take (j - 1) xs)) @ drop (1 + j) xs" using take_Cons' drop_Cons' by (simp add: "4" drop_Cons' take_Cons' Cons.prems(1) add.assoc add_diff_cancel_left' add_eq_0_iff_both_eq_0 gr_implies_not_zero less_one nat_1_add_1)
      have 6: "take (j - 2) (take i (a # xs) @ drop (2 + i) (a # xs)) = take (j - 2) (a#(drop (1 + i) xs))"  by (metis (no_types, lifting) True append_Cons append_eq_append_conv2 append_self_conv diff_add_inverse2 diff_is_0_eq' drop_Cons' i1 nat_1_add_1 numerals(1) take_0 take_Cons_numeral zero_le_one)
      then have 7: "... = (a#(take (j - 3) (drop (1 + i) xs)))" using take_Cons' by (metis Cons.prems(1) diff_diff_left i1 less_numeral_extra(3) nat_1_add_1 numeral_Bit1 numerals(1) zero_less_diff)
      then have 8: "... = [a] @ (take (j - 3) (drop (1 + i) xs))"  by simp
      have 9: "drop (2 + (j - 2)) (take i (a # xs) @ drop (2 + i) (a # xs)) = drop j (a#(drop (1 + i) xs))" using i1 drop_Cons' by (smt (z3) "7" "8" Cons.prems(1) Nat.diff_add_assoc add_diff_cancel_left' add_diff_cancel_right' append.assoc append_take_drop_id diff_diff_left diff_is_0_eq' le_numeral_extra(4) less_imp_le_nat list.distinct(1) nat_1_add_1 numeral_One numeral_plus_one semiring_norm(5) take0 take_0 take_Cons' take_Cons_numeral)
      then have 10: "... = drop (j - 1) (drop (1 + i) xs)" using drop_Cons' by (metis "1" "2" list.distinct(1) take_eq_Nil)
      then have 11: "... = drop (j - 1 + 1 + i) xs" by simp
      then have 12: "... = drop (j + 1) xs" using i1 Cons.prems(1) by force
      have 13: "(take (j - 3) (drop (1 + i) xs)) = (drop (1 + i) (take (j - 1) xs))" using drop_take by (simp add: drop_take i1 numeral_Bit1)
      then have 14: "[a] @ (take (j - 3) (drop (1 + i) xs)) = [a] @ (drop (1 + i) (take (j - 1) xs))" by blast
      then have 15: "take (j - 2) (take i (a # xs) @ drop (2 + i) (a # xs)) = take i (take j (a # xs)) @ (drop (1 + i) (take (j - 1) xs))" using "1" "2" "3" "6" "7" "8" by presburger
      have 16: "take i (take j (a # xs)) = take i (take j (a # xs) @ drop (2 + j) (a # xs))" using Cons.prems(1) i1 by auto
      then have 17: "take (j - 2) (take i (a # xs) @ drop (2 + i) (a # xs)) = take i (take j (a # xs) @ drop (2 + j) (a # xs)) @ (drop (1 + i) (take (j - 1) xs))" using 15 16  by presburger
      then have 18: "take (j - 2) (take i (a # xs) @ drop (2 + i) (a # xs)) @ drop (2 + (j - 2)) (take i (a # xs) @ drop (2 + i) (a # xs)) = take i (take j (a # xs) @ drop (2 + j) (a # xs)) @ (drop (1 + i) (take (j - 1) xs)) @ drop (j + 1) xs" by (metis "10" "11" "12" "9" append_assoc)
      then have 19: "take (j - 2) (take i (a # xs) @ drop (2 + i) (a # xs)) @ drop (2 + (j - 2)) (take i (a # xs) @ drop (2 + i) (a # xs)) = take i (take j (a # xs) @ drop (2 + j) (a # xs)) @ drop (2 + i) (take j (a # xs) @ drop (2 + j) (a # xs))" by (metis "4" "5" add.commute)
      then show ?thesis unfolding cancel_at_def by presburger
    qed
  next
    case False
    hence "i \<ge> 2" by simp
    with Cons(1)[of "i-1" "j-1"]
    have "cancel_at (i - 1) (cancel_at (j - 1) xs) =  cancel_at (j - 1 - 2) (cancel_at (i - 1) xs)" using Cons(2,3) by fastforce
    then have A: "take (i - 1) (take (j - 1) xs @ drop (2 + (j - 1)) xs) @
               drop (2 + (i - 1)) (take (j - 1) xs @ drop (2 + (j - 1)) xs) =
               take (j - 1 - 2) (take (i - 1) xs @ drop (2 + (i - 1)) xs) @
               drop (2 + (j - 1 - 2)) (take (i - 1) xs @ drop (2 + (i - 1)) xs)" unfolding cancel_at_def by blast
    have 1: "drop (2 + (j - 1)) xs = drop (2 + j) (a#xs)" using drop_Cons' Cons.prems(1) by auto
    have 2: "drop (2 + (i - 1)) xs = drop (2 + i) (a#xs)" using drop_Cons' False by auto
    have 3: "(a#(take (i - 1) (take (j - 1) xs @ drop (2 + (j - 1)) xs))) @
               drop (2 + (i - 1)) (take (j - 1) xs @ drop (2 + (j - 1)) xs) =
               (a#(take (j - 1 - 2) (take (i - 1) xs @ drop (2 + (i - 1)) xs))) @
               drop (2 + (j - 1 - 2)) (take (i - 1) xs @ drop (2 + (i - 1)) xs)" using A by (metis append_Cons)
    then have 4: "take i (a#(take (j - 1) xs @ drop (2 + (j - 1)) xs)) @
               drop (2 + (i - 1)) (take (j - 1) xs @ drop (2 + (j - 1)) xs) =
               take (j - 2) (a#(take (i - 1) xs @ drop (2 + (i - 1)) xs)) @
               drop (2 + (j - 1 - 2)) (take (i - 1) xs @ drop (2 + (i - 1)) xs)" using take_Cons' by (smt (verit) Cons.prems(1) False Nat.add_diff_assoc2 add_less_same_cancel2 diff_add_inverse2 diff_diff_left diff_is_0_eq less_diff_conv nat_1_add_1 nat_le_linear not_add_less2)
    then have 5: "take i (take j (a#xs) @ drop (2 + (j - 1)) xs) @
               drop (2 + (i - 1)) (take (j - 1) xs @ drop (2 + (j - 1)) xs) =
               take (j - 2) (take i (a#xs) @ drop (2 + (i - 1)) xs) @
               drop (2 + (j - 1 - 2)) (take (i - 1) xs @ drop (2 + (i - 1)) xs)" using take_Cons' by (smt (z3) Cons.prems(1) False Nat.add_diff_assoc2 add_is_0 append_Cons diff_add_inverse2 less_nat_zero_code nat_le_linear)
    have 6:  "drop (2 + (i - 1)) (take (j - 1) xs @ drop (2 + (j - 1)) xs) =  drop (2 + i) (a#(take (j - 1) xs @ drop (2 + (j - 1)) xs))" using drop_Cons' False by auto
    then have 7: "... =  drop (2 + i) (take j (a#xs) @ drop (2 + (j - 1)) xs)" using take_Cons' by (metis Cons.prems(1) Cons_eq_appendI gr_implies_not_zero)
    have 8: "drop (2 + (j - 1 - 2)) (take (i - 1) xs @ drop (2 + (i - 1)) xs) =  drop (2 + (j - 2)) (a#(take (i - 1) xs @ drop (2 + (i - 1)) xs))" using drop_Cons' False by (smt (z3) Cons.prems(1) Nat.add_diff_assoc \<open>2 \<le> i\<close> diff_add_inverse diff_le_self le_eq_less_or_eq le_trans less_diff_conv not_numeral_le_zero)
    then have 9: "... =  drop (2 + (j - 2)) (take i (a#xs) @ drop (2 + (i - 1)) xs)" using take_Cons' by (metis (no_types, hide_lams) False append_eq_Cons_conv zero_le_one)
    then show ?thesis unfolding cancel_at_def by (metis "1" "2" "5" "6" "7" "8")
  qed  
qed

lemma takenth: assumes  "take i x = take i y" "i \<ge> 0" "j < i"
  shows "(nth x j) = (nth y j)"
  by (metis assms(1) assms(3) nth_take)

lemma Con_nth: assumes "(nth x i) = (nth y j)" 
  shows "(nth (a#x) (i+1)) = (nth (a#y) (j+1))"
  by (simp add: assms)
 
lemma zero:"(a::nat) + 1 - 1 = a"
  by simp

lemma comm: assumes "a > 0"
  shows "(a::nat) - 1 + 1 = a + 1 - 1" 
  by (simp add: assms)

lemma cancel_atnth: assumes "j > i + 1" "j < length x"
  shows "(nth x j) = (nth (cancel_at i x) (j-2))"
  using assms
  unfolding cancel_at_def
  proof(induction x arbitrary: i j)
    case Nil
    have "j < 0" using Nil assms(2) by auto
    then show ?case by simp
next
  case (Cons a x)
  then show ?case
  proof(cases "i > 0")
    case True
  have i: "i > 0" using True by simp
  have a:"(j - 1) < length x" using Cons(3) Cons.prems(1) by auto
  have b: "(i - 1) + 1 < (j - 1)" using Cons True i by linarith
  have "(nth x (j - 1)) = nth (take (i - 1) x @ drop (2 + (i - 1)) x) ((j - 1) - 2)" using Cons(1)[of "i - 1" "j - 1"]  a b by metis
  then have c: "(nth (a#x) (j - 1 + 1)) = nth (a#(take (i - 1) x @ drop (2 + (i - 1)) x)) ((j - 1 - 2 + 1))" using Con_nth[of "x" "j - 1" "(take (i - 1) x @ drop (2 + (i - 1)) x)" "j - 1 - 2" "a"] by metis
  then have "(nth (a#x) j) = nth (a#(take (i - 1) x @ drop (2 + (i - 1)) x)) ((j - 2))" by (smt (z3) add_eq_0_iff_both_eq_0 b diff_diff_left less_diff_conv less_nat_zero_code nat_1_add_1 nth_Cons' zero)
  then have "(nth (a#x) j) = nth ((a#(take (i-1) x)) @ drop (2 + (i - 1)) x) ((j - 2))" by (smt (z3) append_Cons)
  then have "(nth (a#x) j) = nth ((take i (a#x)) @ drop (2 + (i - 1)) x) ((j - 2))" using take_Cons' i  by (smt (z3) not_gr_zero)
  then have "(nth (a#x) j) = nth ((take i (a#x)) @ drop (2 + i) (a#x)) (j - 2)" using drop_Cons' i  by (smt (z3) drop_drop gr_implies_not0)
  then show ?thesis by metis
  next
    case False
    then have i: "i = 0" by blast
    then have a:"nth ((take i (a#x)) @ drop (2 + i) (a#x)) (j - 2) = nth (drop (2 + i) (a#x)) (j - 2)" by simp
    have b:"... = nth (drop 2 (a#x)) (j - 2)" using i  by auto
    have c:"... = nth (drop 1 x) (j - 2)" using drop_Cons' by simp
    then have d: "... =  nth (tl x) (j - 2)" by (simp add: drop_Suc)
    then have e: "... = nth x (j - 1)" using nth_tl by (smt (verit, ccfv_threshold) Cons.prems(1) Cons.prems(2) Suc_1 Suc_diff_Suc add_cancel_right_left add_diff_inverse_nat diff_diff_left drop_Suc_Cons i length_drop length_tl not_less_eq zero_less_diff)
    have f: "(nth (a#x) j) = (nth x (j - 1))" by (metis Cons.prems(1) add_lessD1 i nth_Cons_pos)
    then show ?thesis using a b c d e by presburger
  qed 
qed

lemma length_Cons: "(length xs) + 1 = (length (a#xs))"
  by auto

lemma assoc_Cons: "(a#(b@c)) = ((a#b)@c)"
  by simp

lemma cancel_at_length: 
  assumes "0 \<le> i" "i + 1 < length x"
  shows "length (cancel_at i x) = (length x) - 2"
  using assms
  unfolding cancel_at_def
proof(induction x arbitrary: i)
case Nil
  then show ?case by auto
next
  case (Cons a x)
  then show ?case
  proof(cases "length x \<ge> 1")
    case True
    then have lx: "length x \<ge> 1" by simp
    then show ?thesis
  proof(cases "i > 0")
    case True 
    have a: "0 \<le> i - 1" using Cons.prems(1) by simp
  have b: "(i - 1) + 1 \<le> length x" using Cons.prems(2) True by fastforce
  have "length (take (i - 1) x @ drop (2 + (i - 1)) x) = length x - 2" using a b Cons(1)[of "i - 1"] by (metis Cons.prems(2) True length_Cons comm le_neq_implies_less less_not_refl3 zero)
  then have "(length (take (i - 1) x @ drop (2 + (i - 1)) x)) + 1 = (length x - 2) + 1" by presburger
  then have "(length (take (i - 1) x @ drop (2 + (i - 1)) x)) + 1 = (length x + 1) - 2" using lx Nat.add_diff_assoc2 Cons.prems(1) True  by (smt (z3) Cons.prems(2) length_Cons comm diff_add diff_diff_left diff_is_0_eq' less_diff_conv nat_1_add_1 nat_less_le zero_less_diff)
  then have "(length (take (i - 1) x @ drop (2 + (i - 1)) x)) + 1 = (length (a#x)) - 2" using length_Cons[of "x" "a"] by argo
  then have "(length (a#(take (i - 1) x @ drop (2 + (i - 1)) x))) = (length (a#x)) - 2" using length_Cons[of  "(take (i - 1) x @ drop (2 + (i - 1)) x)" "a"] by argo
  then have "(length ((a#take (i - 1) x) @ drop (2 + (i - 1)) x)) = (length (a#x)) - 2" using assoc_Cons[of "a" "take (i - 1) x" "drop (2 + (i - 1)) x"] by argo
  then have "length ((take i (a#x)) @ drop (2 + (i - 1)) x) = (length (a#x)) - 2" using True take_Cons' [of "i" "a" "x"] by presburger
  then have "length ((take i (a#x)) @ drop (2 + i) (a#x)) = (length (a#x)) - 2" using True drop_Cons' Cons.prems(1) by simp
  then show ?thesis  by blast
  next
    case False
    have i: "i = 0" using Cons.prems(1) False by auto
    then have 1: "length ((take i (a#x)) @ drop (2 + i) (a#x)) = length (drop (2 + i) (a#x))" by simp
    have 2: "... = length (drop 2 (a#x))"  using i by simp
    have 3: "... = length (drop 1 (a#x)) - 1"  by simp
    have 4: "... = length (drop 0 (a#x)) - 2" by simp
    have 5: "... = (length (a#x)) - 2" by auto
    then show ?thesis using "1" "2" "3" "4" by presburger
  qed
  next
    case False
    then have 1: "length x < 1" by linarith
    then have 2: "length x = 0"  by auto
    then have 3: "x = []" by auto
    then have 4: "(a#x) = [a]" by simp
    have "i + 1 \<ge> 1" using Cons.prems(2) by simp
    then have "i + 1 \<ge> length (a#x)" using 4 by simp
    then show ?thesis using Cons(3) by linarith
  qed
qed

lemma rtrancancel:
  assumes  "((\<exists>i. cancels_to_1_at i y u) \<or> y = u)"
  shows "cancels_to y u"
  by (metis assms cancels_to_1_def cancels_to_def rtranclp.simps)

(*Useful term-rewriting lemmas*)

theorem lconfluent_confluent:
  "\<lbrakk> wfP (R^--1); \<And>a b c. R a b \<Longrightarrow> R a c \<Longrightarrow> \<exists>d. R^** b d \<and> R^** c d  \<rbrakk> \<Longrightarrow> confluent R"
by(auto simp add: diamond_def commute_def square_def intro: newman)

lemma confluentD:
  "\<lbrakk> confluent R; R^** a b; R^** a c  \<rbrakk> \<Longrightarrow> \<exists>d. R^** b d \<and> R^** c d"
by(auto simp add: commute_def diamond_def square_def)

lemma tranclp_DomainP: "R^++ a b \<Longrightarrow> Domainp R a"
by(auto elim: converse_tranclpE)

lemma confluent_unique_normal_form:
  "\<lbrakk> confluent R; R^** a b; R^** a c; \<not> Domainp R b; \<not> Domainp R c  \<rbrakk> \<Longrightarrow> b = c"
  by(fastforce dest!: confluentD[of R a b c] dest: tranclp_DomainP rtranclpD[where a=b] rtranclpD[where a=c])

lemma Church_Rosser_unique_normal_form:
  assumes "Church_Rosser R" "(sup R (R\<inverse>\<inverse>))\<^sup>*\<^sup>* a b"  "\<not> Domainp R a" "\<not> Domainp R b"
  shows " a = b"
proof-
  have "\<exists>c. R^** a c \<and> R^** b c" using assms(1, 2) using Church_Rosser_def by fastforce
  then obtain c where "R^** a c \<and> R^** b c" by blast
  then have 1: "(a = c \<or> a \<noteq> c \<and> R\<^sup>+\<^sup>+ a c) \<and> (b = c \<or> b \<noteq> c \<and> R\<^sup>+\<^sup>+ b c)" by (simp add: rtranclpD)
  have a: "\<not> (R\<^sup>+\<^sup>+ a c)" using assms(3) tranclp_DomainP by metis
  have b: "\<not> (R\<^sup>+\<^sup>+ b c)" using assms(4) tranclp_DomainP by metis
  have "a = c \<and> b = c" using 1 a b by auto
  then show ?thesis by simp
qed

lemma canceling_terminates: "wfP (cancels_to_1^--1)"
proof-
  have "wf (measure length)" by auto
  moreover
  have "{(x, y). cancels_to_1 y x} \<subseteq> measure length"
    by (auto simp add: cancels_to_1_def cancel_at_def cancels_to_1_at_def)
  ultimately
  have "wf {(x, y). cancels_to_1 y x}"
    by(rule wf_subset)
  thus ?thesis by (simp add:wfP_def)
qed

end
