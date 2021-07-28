theory cancel_at_props
imports Main  "HOL-Library.FuncSet" "HOL-Algebra.Group" "HOL-Proofs-Lambda.Commutation"
begin

datatype ('a,'b) monoidgentype = C 'a  'b (infix "!" 63)

datatype ('a,'b) groupgentype = P "('a,'b) monoidgentype"
                               | N  "('a,'b) monoidgentype"

type_synonym ('a,'b) word = "(('a,'b) groupgentype) list"

primrec inverse::"('a,'b) groupgentype \<Rightarrow> ('a,'b) groupgentype"
  where
"inverse (P x) = (N x)"
|"inverse (N x) = (P x)"

primrec wordinverse::"('a,'b) word \<Rightarrow> ('a, 'b) word"
  where
"wordinverse [] = []"
|"wordinverse (x#xs) =  (wordinverse xs)@[inverse x]"

inductive_set spanset::"('a,'b) word set\<Rightarrow> ('a,'b) word set" ("\<langle>_\<rangle>")
  for S::"('a,'b) word set"
  where
"x \<in> S \<Longrightarrow> x \<in> \<langle>S\<rangle>"
|"x \<in> inver ` S \<Longrightarrow> x \<in> \<langle>S\<rangle>"
|"x \<in> S \<Longrightarrow> y \<in> \<langle>S\<rangle>\<Longrightarrow> x@y \<in> \<langle>S\<rangle>"
|"x \<in> inver ` S \<Longrightarrow> ys \<in> \<langle>S\<rangle> \<Longrightarrow> x@ys \<in> \<langle>S\<rangle>"

definition setlistcross::"'a set \<Rightarrow> 'a list \<Rightarrow> 'a list set"
 where
"setlistcross S xs = {[s]@xs | s. s \<in> S}"

value "setlistcross {(1::nat), 2, 3} [(4::nat), 5, 6]"

primrec lengthword::"nat \<Rightarrow> 'a set \<Rightarrow> 'a list set"
  where
"lengthword 0 S = {[s] | s. s \<in> S}"
|"lengthword (Suc n) S = \<Union> {setlistcross S xs | xs. xs \<in> (lengthword n S)}"

abbreviation "ngroupword \<equiv> \<lambda> n (S::('a,'b) word set). lengthword n (S \<union> (wordinverse ` S))" 

datatype char = G | H

value "ngroupword 1 {[P (C G (1::nat))], [N (C G (2::nat))], [P (C H (3::nat))]}" 

(*reduction removes cancellations next to each other*)
fun reduction:: "('a,'b) word \<Rightarrow> ('a,'b) word"
 where
"reduction [] = []"
|"reduction [x] = [x]"
|"reduction (g1#g2#wrd) = (if (g1 = inverse g2) 
                             then reduction wrd 
                             else (g1#(reduction (g2#wrd))))"

value "reduction [P (C G (3::nat)), N (C G (3::nat)), (N (C G (2::nat)))]"

fun reduced::"('a,'b) word \<Rightarrow> bool"
  where
"reduced [] = True"
|"reduced [g] = True"
|"reduced (g#h#wrd) = (if (g \<noteq> inverse h) then reduced (h#wrd) else False)"

primrec iter::"nat \<Rightarrow>('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)"
  where
"iter 0 f = (\<lambda> x. x)"
|"iter (Suc n) f = (\<lambda> x. f ((iter n f) x))"

(*Prove the following*)
lemma fixedpt_iteration:
  assumes "f x = x"
  shows "iter (n+1) f x = x"
  using assms
proof(induction n)
  case 0
  then show ?case by simp 
next
  case (Suc n)
  then show ?case by simp
qed

lemma iterative_fixed_pt:
  assumes "iter (n+1) f x = iter n f x" 
  shows "iter (k+(n+1)) f x = iter (k+n) f x"
  using assms
proof(induction k)
  case 0
  then show ?case 
    by force
next
  case (Suc m)
  have "iter (m + (n + 1)) f x = iter (Suc m + n) f x" by simp
  then show ?case using Suc.IH Suc.prems by fastforce
qed

(*prove converse of the following too*)
lemma assumes "reduced wrd"
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

(*Show that length decreases if and only the word after reduction is not the same as the original word*)

(*show that if after reduction of a word it does not change, that subsequent reductions will be ineffective*)

(*use the word length argument decrement argument to show that the reduced word is finally reduced*)


value "reduced  [P (C G (1::nat)), N (C G (2::nat)), P (C G (1::nat))]" 

inductive reln::"('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool" (infixr "~" 65)
  where
refl[intro!]: "a ~ a" |
sym: "a ~ b \<Longrightarrow> b ~ a" |
trans: "a ~ b \<Longrightarrow> b ~ c \<Longrightarrow> a ~ c" |
base: "[g, inverse g] ~ []" |
mult: "xs ~ xs' \<Longrightarrow> ys ~ ys' \<Longrightarrow> (xs@ys) ~ (xs'@ys')"
  

lemma assumes "h = inverse g"
  shows "[g, h] ~ []"
  using assms reln.base inverse.simps by simp

lemma relation: "(xs@ys) ~ xs@[g,inverse g]@ys"
  using reln.base reln.refl reln.mult
proof-
  have "(xs@[g, inverse g]) ~ xs" using reln.base reln.mult reln.refl by fastforce
  then show ?thesis using mult[of "xs@[g, inverse g]" "xs" "ys" "ys"] reln.refl reln.sym
    by auto
qed

lemma inverse_of_inverse:
  assumes "g = inverse h"
  shows "h = inverse g"
  using assms inverse.simps 
  by (metis groupgentype.exhaust)

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
  then have "([g1]@(g2#wrd)) ~ ([g1]@(reduction (g2#wrd)))" using 3(2) reln.mult reln.refl 
    by blast
  then have "([g1]@(g2#wrd)) ~ (reduction (g1#g2#wrd))" using False by simp
  then show ?thesis by simp
qed
qed

definition wordeq::"('a,'b) word \<Rightarrow> ('a,'b) word set" ("[[_]]")
  where
"wordeq wrd = {wrds. wrd ~ wrds}"


(*This is approach for normal form using newsmans lemma*)

definition cancel_at :: "nat \<Rightarrow> ('a,'b) word \<Rightarrow> ('a,'b) word"
  where "cancel_at i l = take i l @ drop (2+i) l"

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
  moreover have "(drop (2+i) a)@c = drop (2+i) (a@c)" using assms(1) assms(2) by simp
  ultimately show ?thesis unfolding cancel_at_def by (metis append.assoc assms(3) cancel_at_def)
qed

definition cancels_to_1_at ::  "nat \<Rightarrow> ('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool"
where "cancels_to_1_at i l1 l2 = (0\<le>i \<and> (1+i) < length l1
                              \<and> (inverse (l1 ! i) = (l1 ! (1+i)))
                              \<and> (l2 = cancel_at i l1))"

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

definition cancels_to_1 :: "('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool"
  where "cancels_to_1 l1 l2 = (\<exists>i. cancels_to_1_at i l1 l2)"

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

definition cancels_to  :: "('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool"
  where "cancels_to = (cancels_to_1)^**"

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

lemma "cancels_to x y \<Longrightarrow> x ~ y"
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

definition cancels_eq::"('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool"
  where
"cancels_eq = (\<lambda> wrd1 wrd2. cancels_to wrd1 wrd2 \<or> cancels_to wrd2 wrd1)^**"

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

lemma cancels_to_iter:
"cancels_to wrd (iter n reduction wrd)"
  unfolding cancels_to_def cancels_to_1_def
proof (induction wrd)
  case Nil
  have "iter n reduction [] = []" sorry
  then show ?case sorry
next
case (Cons a wrd)
then show ?case sorry
qed

lemma reduced_right_append:
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

  
lemma reduced_append:
  assumes "reduced (ys@xs)"
  shows "reduced xs"
  using assms
  sorry


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
  then have "reduced ((xs!i)#(xs!(i+1))#(drop (i+2) xs))" using assms reduced_append by metis
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
  then have "\<exists>i. inverse (x ! i) = x ! (i + 1)" using cancels_to_1_at_def by auto
  then have "i + 1 < length x" using "1"  assms reduced_no_cancels_to_1_at by blast
  then have "x = (take i x) @ ((x!i)#(x!(i+1))#(drop (i+2) x))" by (metis Cons_nth_drop_Suc Suc_1 Suc_eq_plus1 add_Suc_right add_lessD1 append_take_drop_id)
  then have "reduced ((x!i)#(x!(i+1))#(drop (i+2) x))" by (metis assms reduced_append)
  then have "reduced x = False" using "1" using reduced_no_cancels_to_1_at by auto
  then show "False" using assms by simp
qed


lemma assumes "\<not>(reduced xs)"
  shows  "\<not>(reduced (ys@xs))"
proof-
  have 1: "reduced (ys@xs) \<longrightarrow> reduced xs" using reduced_append by auto
  then show ?thesis using not_mono [OF 1] assms by argo
qed


lemma inv_not_reduced:
  assumes "(i + 1) < length wrd"  "inverse (wrd ! i) = (wrd ! (i + 1))" 
  shows "\<not>(reduced wrd)"
  using assms
proof-
  have "inverse (wrd ! i) = wrd ! (i + 1)" using assms by auto
  have "i + 1 < length wrd" using  assms reduced_no_cancels_to_1_at by blast
  then have 1: "wrd = (take i wrd) @ ((wrd ! i)#(wrd !(i + 1))#(drop (i + 2) wrd))" by (metis Cons_nth_drop_Suc Suc_1 Suc_eq_plus1 add_Suc_right add_lessD1 append_take_drop_id)
  then have "\<not>(reduced ((wrd ! i)#(wrd ! (i + 1))#(drop (i + 2) wrd)))" using assms by (metis inverse_of_inverse reduced.simps(3))
  then have "reduced wrd = False" using "1" by (metis reduced_append) 
  then show ?thesis using assms by simp
qed

(*proof(induction wrd arbitrary : i)
  case Nil
  then show ?case by simp
next
  case (Cons a wrd)
  then show ?case 
  proof (cases "i = 0")
case True
  then have "inverse((a # wrd) ! 0)  = (a # wrd) ! 1" using Cons reduced.simps by simp
    then have "(a # wrd) ! 0 = inverse((a # wrd) ! 1)" using inverse_of_inverse by metis
    then show ?thesis using True by (smt (z3) Cons.prems(1) One_nat_def add_cancel_right_left canonically_ordered_monoid_add_class.lessE diff_Suc_1 less_numeral_extra(1) list.discI list.size(3) list.size(4) nth_Cons_0 nth_Cons_pos plus_1_eq_Suc reduced.elims(2))
next
  case False
  have "i \<ge> 1" using False by linarith
  have "(i + 1) < length (a # wrd)" using  local.Cons(2) by simp
  then have "(i + 1) \<le> length wrd" by simp
  have "inverse ((a # wrd) ! i) = (a # wrd) ! (i + 1)" using local.Cons(3) by auto
  then show ?thesis sorry
qed
*)

lemma takei_cancelatj:
  assumes "i < j"  (*take i (cancel_at j xs) = take i xs*)
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
    hence j:"j > 1" using Cons(2) by arith
    then have "take j (a#xs) = a#(take (j - 1) xs)"  
      by (simp add: take_Cons')
    moreover have "drop (j + 2) (a#xs) = drop (j + 1) xs" using j by force
    ultimately have 1:"(take j (a#xs))@(drop (j + 1) xs) = a#(take (j-1) xs)@(drop (j + 1) xs)"
      by simp
    with take_Cons' False
    have 2:"take i  (a#(take (j-1) xs)@(drop (j + 1) xs)) = a#(take (i - 1) ((take (j-1) xs)@(drop (j + 1) xs)))"
      by metis
    then have 3:"... = a#(take (i - 1) xs)" using Cons(1)[of "i-1" "j-1"] Cons(2) by force
    then have 4:"... = (take i (a#xs))" using False
      by (metis take_Cons')
    then show ?thesis
      by (metis "2" "3" Cons_eq_appendI \<open>drop (j + 2) (a # xs) = drop (j + 1) xs\<close> \<open>take j (a # xs) = a # take (j - 1) xs\<close>)
  qed
qed(auto)

lemma assumes "i < j"
  shows  "drop i ((take j xs)@(drop (j+2) xs)) =  ((drop i (take j xs))) @(drop (j+2) xs)"
  using assms
proof(induction xs arbitrary: i j)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)  
  then show ?case
  proof (cases "i = 0")
case True
  then show ?thesis by simp
next
  case False
  have a: "i > 0" using False by auto
  have b : "j > 1" using Cons.prems False by auto
  then have c : "take j (a#xs) = a # (take (j - 1)) xs" by (metis gr_implies_not0 take_Cons')
  have d : "drop (j + 2) (a # xs) = drop (j + 1) xs" by simp
  then have 1: "take j (a#xs)@drop (j + 1) xs = a # (take (j - 1)) xs@drop (j + 1) xs" by (simp add: c)
  
  then show ?thesis sorry
qed
   
qed

lemma cancels_to_reduced :
  assumes "i\<ge>0" "(1+i)<length x" "cancels_to x y"  "cancels_to x z" "reduced y" "reduced z" 
  shows "y = z"
  unfolding cancels_to_1_def
proof-
  have "cancels_to_1 \<^sup>*\<^sup>* x y" by (metis assms(3) cancels_to_def)
  moreover have "cancels_to_1 \<^sup>*\<^sup>* x z" by (metis assms(4) cancels_to_def)
  moreover have "\<forall>h. \<not>(cancels_to_1 y h)" using cancels_to_1_red assms (5) by auto 
  moreover have "\<forall>h. \<not>(cancels_to_1 z h)" using cancels_to_1_red assms(6) by auto
  ultimately show "y = z"  sorry  
  
qed
 
lemma "cancels_eq x y \<Longrightarrow> reduced x \<Longrightarrow> reduced y \<Longrightarrow> x = y" sorry 

(*  define overlapping where
    "overlapping \<equiv> \<lambda> m (n :: nat). m \<in> {n, n + 1} \<or> n \<in> {m, m + 1}"
*)


lemma novl : assumes "i \<ge> 0" "i + 1 < j" "(1 + j) < length wrd"
  shows "cancel_at (j-2) (cancel_at i wrd) = cancel_at i (cancel_at j wrd)"
proof-
  have "(cancel_at i wrd) = take i wrd @ (drop (2 + i) wrd)" unfolding cancel_at_def by simp
  then show "cancel_at (j-2) (cancel_at i wrd) = cancel_at i (cancel_at j wrd)" sorry 
qed

lemma "diamond (\<lambda> x y. (cancels_to_1 x y) \<or> x = y)"
  unfolding  diamond_def cancels_to_1_def commute_def square_def 
  apply (rule allI, rule allI, rule impI, rule allI, rule impI)
proof-
  fix x y z :: "('a,'b) word"
  assume 1:"(\<exists>i. cancels_to_1_at i x y) \<or> x = y"
  assume 2:"(\<exists>i. cancels_to_1_at i x z) \<or> x = z"
  show "\<exists>u. ((\<exists>i. cancels_to_1_at i y u) \<or> y = u) \<and> ((\<exists>i. cancels_to_1_at i z u) \<or> z = u)"
  proof (cases "x = y \<or> x = z")
  case True
  have "(\<exists>i. cancels_to_1_at i y z) \<or> (\<exists>i. cancels_to_1_at i z y) \<or> z = y" using "1" "2" True by auto
  then show ?thesis by auto
  next
  case False
  then have "x \<noteq> y" "x \<noteq> z" by auto
  then show ?thesis
  proof (cases "y = z")
case True
  then show ?thesis by auto
next
  case False
  then have asm1:"(\<exists>i. cancels_to_1_at i x y)" using "1" False  \<open>x \<noteq> y\<close> by auto
  then obtain i where i: "cancels_to_1_at i x y" by auto
  have asm2 :"(\<exists>i. cancels_to_1_at i x z)" using "2" False  \<open>x \<noteq> z\<close> by auto
  then obtain j where j: "cancels_to_1_at j x z" by auto
  define overlapping where "overlapping \<equiv> \<lambda> m (n :: nat). m \<in> {n, n + 1} \<or> n \<in> {m, m + 1}" 
  then show ?thesis 
      proof (cases "overlapping i j")
      case True
      then have ovl:"i \<in> {j, j + 1} \<or> j \<in> {i, i + 1}" using overlapping_def by auto
      then show ?thesis 
        proof (cases "i = j")
        case True
        then have "y = z" using i j cancels_to_1_at_def by metis
        then show ?thesis by auto
        next
        case False
        then have "(i > j) \<or> (i < j)" by auto 
        then have "i = j + 1 \<or> j = i + 1" using ovl by blast 
        then show ?thesis 
        proof (cases "j = i + 1")
        case True
        then have "((nth x (i + 2)) = (nth x i))" using j i inverse_of_inverse sorry
        then have "cancel_at i x = cancel_at (i + 1) x" using "1" cancels_to_1_at cancel_at_def sorry
        then have y: "y = z" using  cancels_to_1_at_def by (metis True i j)
        then show ?thesis sorry
        next
        case False
        then have "i = j + 1" using \<open>i = j + 1 \<or> j = i + 1\<close> by blast
        then show ?thesis sorry
        qed
       qed
      next
      case False
      then have novl1:"\<not>(i \<in> {j, j + 1})" by (simp add: overlapping_def)
      have novl2: "\<not>(j \<in> {i, i + 1})" using False by (simp add: overlapping_def)
      then show ?thesis 
        proof (cases "i<j")
        case True
        then have a:"(i + 1) < j" using i j True overlapping_def by (metis Nat.add_0_right add_Suc_right insertCI linorder_neqE_nat nat_1 nat_one_as_int not_less_eq novl2)
        have "cancels_to_1_at j x z" using j by auto
        then have b: "(j + 1) < length x" using cancels_to_1_at_def by auto
        have "cancels_to_1_at i x y" using i by auto
        then have c: "i \<ge> 0" by simp
        then have  "cancel_at i (cancel_at j x) = cancel_at (j - 2) (cancel_at i x)" using a b novl[of i j x] by simp
        then have "cancel_at (j - 2) y = cancel_at i z" using cancels_to_1_at_def by (metis i j)
        then have "(nth x i) = (nth z i)" sorry
        then show ?thesis using i j sorry
        next
        case False
        then have "i \<noteq> j" using novl1 by auto
        then have "i > j" using False by auto
        then have a:"(j + 1) < i" using i j overlapping_def using novl1 by force
        have "cancels_to_1_at i x y" using i by auto
        then have b: "(i + 1) < length x" using cancels_to_1_at_def by auto
        have "cancels_to_1_at j x z" using j by auto
        then have c: "j \<ge> 0" by simp
        then have  "cancel_at j (cancel_at i x) = cancel_at (i - 2) (cancel_at j x)" using a b novl[of j i x] by simp
        then have "cancel_at (i - 2) z = cancel_at j y" using cancels_to_1_at_def by (metis i j)
        then have "(nth x j) = (nth z j)" sorry
        then show ?thesis using i j sorry 
       qed
      qed
    qed
  qed  
 qed
qed


