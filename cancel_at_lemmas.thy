theory cancel_at_lemmas
imports Main  "HOL-Library.FuncSet" "HOL-Algebra.Group"
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
|"x \<in> S \<Longrightarrow> y \<in> \<langle>S\<rangle> \<Longrightarrow> x@y \<in> \<langle>S\<rangle>"
|"x \<in> inver ` S \<Longrightarrow> ys \<in> \<langle>S\<rangle> \<Longrightarrow> x@y \<in> \<langle>S\<rangle>"



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

(*"reduction-reduced lemma"*)
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

definition cancels_eq::"('a,'b) word \<Rightarrow> ('a,'b)  word \<Rightarrow> bool"
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
  have "(\<lambda>wrd1 wrd2. cancels_to wrd1 wrd2 \<or> cancels_to wrd2 wrd1)\<^sup>*\<^sup>* (z @ a) (z @ b)" by (simp add: rtrancl_into_rtrancl.IH)
  then show "(\<lambda>wrd1 wrd2. cancels_to wrd1 wrd2 \<or> cancels_to wrd2 wrd1)\<^sup>*\<^sup>* (z @ a) (z @ c)" unfolding cancels_eq_def using 1  by (metis (no_types, lifting) rtranclp.simps)
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
  have "(\<lambda>wrd1 wrd2. cancels_to wrd1 wrd2 \<or> cancels_to wrd2 wrd1)\<^sup>*\<^sup>* (a@z) (b@z)" by (simp add: rtrancl_into_rtrancl.IH)
  then show "(\<lambda>wrd1 wrd2. cancels_to wrd1 wrd2 \<or> cancels_to wrd2 wrd1)\<^sup>*\<^sup>* (a@z) (c@z)" unfolding cancels_eq_def using 1  by (metis (no_types, lifting) rtranclp.simps)
qed

(*Try proving this*)
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

definition
  square :: "['a => 'a => bool, 'a => 'a => bool, 'a => 'a => bool, 'a => 'a => bool] => bool" where
  "square R S T U =
    (\<forall>x y. R x y --> (\<forall>z. S x z --> (\<exists>u. T y u \<and> U z u)))"

definition
  commute :: "['a => 'a => bool, 'a => 'a => bool] => bool" where
  "commute R S = square R S S R"

definition
  diamond :: "('a => 'a => bool) => bool" where
  "diamond R = commute R R"

definition
  Church_Rosser :: "('a => 'a => bool) => bool" where
  "Church_Rosser R =
    (\<forall>x y. (sup R (R^--1))^** x y --> (\<exists>z. R^** x z \<and> R^** y z))"

abbreviation
  confluent :: "('a => 'a => bool) => bool" where
  "confluent R == diamond (R^**)"

lemma a1: assumes"j \<ge> 0" "j + 2 < length x" 
  shows "take j x @ drop (2+j) x = take j x @ [nth x (2+j)] @  drop (2+(1+j)) x"
  using assms
proof(induction j)
case 0
  then show ?case by (metis Suc_1 add.left_neutral add.right_neutral add_2_eq_Suc append_Cons append_take_drop_id id_take_nth_drop same_append_eq self_append_conv2)
next
case (Suc j)
  then show ?case using Cons_nth_drop_Suc by fastforce
qed

lemma a2: assumes"j \<ge> 0" "j + 2 < length x" 
  shows "take (j+1) x @ drop (2+(j+1)) x = take j x @ [nth x j] @  drop (2+(1+j)) x"
  using assms
proof(induction j)
case 0
  then show ?case by (metis Suc_1 Suc_inject add.commute add_2_eq_Suc' add_lessD1 append_Nil id_take_nth_drop plus_nat.add_0 take_Suc_Cons take_eq_Nil)
next
case (Suc j)
  then show ?case by (metis add.commute add_lessD1 append_assoc plus_1_eq_Suc take_Suc_conv_app_nth)
qed

lemma assumes "j\<le>0" "j + 2 < Suc i" "Suc i + 1 \<le> length x"
  shows "cancel_at j (cancel_at (Suc i) x) = take (i - 2) (cancel_at j (cancel_at i x)) @ [(nth x i)] @ drop (i - 1) (cancel_at j (cancel_at i x))"
  unfolding cancel_at_def
  using assms
proof(induction j arbitrary: i)
case 0
  then show ?case sorry
next
  case (Suc j)
then show ?case sorry
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

lemma diamond_cancel:
  shows "diamond (\<lambda> x y . (cancels_to_1 x y) \<or> x = y)"
  unfolding diamond_def cancels_to_1_def commute_def square_def
  apply(rule allI)
  apply(rule allI)
  apply(rule impI)
  apply(rule allI)
  apply(rule impI)
proof-
  fix x y z :: "('a, 'b) word"
  assume 1: "(\<exists>i. cancels_to_1_at i x y) \<or> x = y"
  assume 2: "(\<exists>i. cancels_to_1_at i x z) \<or> x = z"
  show "\<exists>u. ((\<exists>i. cancels_to_1_at i y u) \<or> y = u) \<and> ((\<exists>i. cancels_to_1_at i z u) \<or> z = u)"
  proof(cases "x = y \<or> x = z")
    case True
    then have "(\<exists>i. cancels_to_1_at i y z) \<or> (\<exists>i. cancels_to_1_at i z y) \<or> y = z " using 1 2 by blast
  then show ?thesis by blast
  next
    case False
    have 3: "(\<exists>i. cancels_to_1_at i x y) \<and> (\<exists>j. cancels_to_1_at j x z)" using 1 2 False by blast
    obtain i where "cancels_to_1_at i x y" using 3 by auto
    obtain j where "cancels_to_1_at j x z" using 3 by auto
  then show ?thesis 
    proof(cases "y = z")
      case True
    then show ?thesis by auto
    next
      case False
      then show ?thesis
      proof(cases "i \<in> {j, j + 1} \<or> j \<in> {i, i+1}")
        case True
        have a: "y \<noteq> z"  by (simp add: False)
      then show ?thesis
        proof(cases "i = j")
          case True
          have y: "y = cancel_at i x" using cancels_to_1_at_def using \<open>cancels_to_1_at i x y\<close> by auto
          have z: "z = cancel_at i x" using cancels_to_1_at_def True using \<open>cancels_to_1_at j x z\<close> by auto
          have cont: "y = z" using y z by simp
        then show ?thesis using a by auto 
        next
          case False
          then have ij: "i = j + 1 \<or> j = i + 1" using True by blast
          have xi: "inverse (x!i) = (x!(1+i))" using cancels_to_1_at_def \<open>cancels_to_1_at i x y\<close> by auto
          have xj: "inverse (x!j) = (x!(1+j))" using cancels_to_1_at_def \<open>cancels_to_1_at j x z\<close> by auto
        then show ?thesis
          proof(cases "i = 1 + j")
            case True
            have xij: "((nth x j) = (nth x (2+j)))" using True xi xj inverse_of_inverse by (metis add_2_eq_Suc plus_1_eq_Suc)
            have y1: "y = cancel_at (j+1) x" by (metis True \<open>cancels_to_1_at i x y\<close> add.commute cancels_to_1_at_def)
            have z1: "z = cancel_at j x" using cancels_to_1_at_def \<open>cancels_to_1_at j x z\<close> by (simp add: cancels_to_1_at_def)
            have contr1: "y = z" using y1 z1 a1 z1 xij by (smt (z3) True \<open>cancels_to_1_at i x y\<close> a2 add.commute cancel_at_def cancels_to_1_at_def group_cancel.add1 nat_1_add_1 zero_le)
          show ?thesis using a contr1 by auto
          next
            case False
            have "j = i + 1" using False ij by auto
            then have xji: "((nth x i) = (nth x (2+i)))" by (metis Suc_1 add.commute add_Suc_right inverse_of_inverse plus_1_eq_Suc xi xj)
            have y2: "y = cancel_at i x" using cancels_to_1_at_def \<open>cancels_to_1_at i x y\<close> by auto
            have z2: "z = cancel_at (i+1) x" using xji cancels_to_1_at_def \<open>cancels_to_1_at j x z\<close> by (simp add: cancels_to_1_at_def \<open>j = i + 1\<close>)
            have contr2: "y = z" using y2 z2 a2 z2 xji  by (smt (verit) \<open>cancels_to_1_at j x z\<close> \<open>j = i + 1\<close> a1 add.left_commute cancel_at_def cancels_to_1_at_def le_add2 le_add_same_cancel2 nat_1_add_1)
          then show ?thesis using a contr2 by auto
          qed
        qed
      next
        case False
        have xi: "inverse (x!i) = (x!(1+i))" using cancels_to_1_at_def \<open>cancels_to_1_at i x y\<close> by auto
        have xj: "inverse (x!j) = (x!(1+j))" using cancels_to_1_at_def \<open>cancels_to_1_at j x z\<close> by auto
        then show ?thesis
        proof(cases "i \<le> j")
          case True
          then have l: "i < j + 1"  by linarith
          have m: "1 + j  < length x" using \<open>cancels_to_1_at j x z\<close> cancels_to_1_at_def by (simp add: cancels_to_1_at_def)
          then have n: "cancel_at i (cancel_at j x) = cancel_at (j-2) (cancel_at i x)" using cancel_order l m by (metis False True add.commute discrete insert_iff le_neq_implies_less)
          then have "cancel_at i z = cancel_at (j-2) y" using \<open>cancels_to_1_at j x z\<close> \<open>cancels_to_1_at i x y\<close> cancels_to_1_at_def by (simp add: cancels_to_1_at_def)
          have "take i z = take i x" using take_assoc cancel_at_def l m by (metis True \<open>cancels_to_1_at j x z\<close> add.commute cancels_to_1_at_def)
          then have o: "(nth (take i z) i) = (nth (take i x) i)" by simp
          moreover have "z = take i z @ drop i z" by simp
          moreover have "x = take i x @ drop i x" by simp
          ultimately have "(nth z i) = (nth x i)" using o l m sorry
          (*Show that inverse (z!i) = (z!(i+1)) and inverse (y!(j-2)) = (y!(j-2 + 1))*)
          then show ?thesis sorry
        next
          case False
          then show ?thesis sorry
        qed
      qed
    qed
  qed
qed

lemma assumes "reduced xs" "reduced ys" "inverse (last xs) \<noteq> (hd ys)"
  shows "reduced (xs@ys)"
proof(induction xs arbitrary: ys)
case Nil
  then show ?case sorry
next
  case (Cons a xs)
  then show ?case sorry
qed

lemma assumes "reduced (xs@ys)"
  shows "reduced xs"
  using assms
proof (induction xs rule : reduction.induct)
case 1
then show ?case by simp
next
  case (2 x)
  then show ?case by simp
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

lemma reduced_append: assumes "reduced (xs@ys)"
  shows "reduced ys"
  using assms
proof (induction ys arbitrary: xs rule : reduction.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 g1 g2 wrd)
  then show ?case
  proof (cases "g1 =  inverse g2")
    case True
    then show ?thesis sorry
  next
    case False
    then show ?thesis sorry
  qed
qed

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

lemma assumes "cancels_to xs ys" "cancels_to xs zs" "reduced ys" "reduced zs" 
  shows "ys = zs"
  sorry