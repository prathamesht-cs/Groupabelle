theory Generators
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


(*Prove the following:
  (1) if xs and ys can be reduced to same element, they are related. 
  (2) if xs and ys are related, they have the same final reduction. 
  (3) If xs is a related to a reduced word, the reduced word is unique. 
  (4) Every element is related to its reduced form. 
*)

(*
(1) Every element is related to the reduced word obtained by applying 
   the iter algorithm. 
(2) If two elements reduce to the same word obtained by the iter algorithm, they are related. 
(3) Reduced word obtained by our (iter application) algorithm is unique in the equivalence
class.
(4) If two elements have the same reduced word (obtained by applying the iter
algorithm), the two elements are related. 
*)


lemma reln_of_iter:"xs ~ iter n (reduction) xs"
proof(induction n)
  case 0
  then show ?case using reln.refl[of "xs"] unfolding iter.simps .
next
  case (Suc n)
  have loc:"iter n (reduction) xs ~ iter (Suc n) reduction xs" unfolding iter.simps(2) 
    using rel_to_reduction[of "iter n (reduction) xs "] .
  show ?case using reln.trans[OF "Suc" loc] .
qed

lemma iter_eq_implies_reln:
  assumes "iter n reduction xs = iter m reduction ys"
  shows "xs ~ ys"
proof-
  have "xs ~ iter n reduction xs" using reln_of_iter[of "xs" "n"] .
  moreover have "ys ~ iter m reduction ys" using reln_of_iter[of "ys" "m"] .
  ultimately show ?thesis using assms reln.refl reln.trans 
    by (metis reln.sym)
qed



 

lemma   "wrd1 ~ wrd2 \<Longrightarrow> reduced wrd1 \<Longrightarrow> reduced wrd2 \<Longrightarrow> wrd1 = wrd2"
proof(induction rule: reln.induct)
  case (refl a)
  then show ?case by fast
next
  case (sym a b)
  then show ?case by simp
next
  case (trans a b c)
  then show ?case sorry
next
  case (base g)
  then show ?case using reduced.simps 
    by (metis inverse_of_inverse)
next
  case (mult xs xs' ys ys')
  then show ?case sorry
  (*use the result that if (xs@ys) is reduced, xs and ys are reduced *)
qed

quotient_type ('a,'b) wordclass = "('a,'b) word"/"reln"
  using reln.refl reln.sym reln.trans  equivpI reflpI sympI transpI
  by metis

lift_definition mult::"('a,'b) wordclass \<Rightarrow> ('a,'b) wordclass \<Rightarrow> ('a,'b) wordclass" (infixr "*" 65)
 is List.append
  by (simp add: mult)

(*Prove the following: Product of Abs of two wordclasses is the Abs of the product*)

(*Look up the difference between Abs_wordclasss and abs_wordclass, by experiment or reading. 
Same for Rep_wordclass and rep_wordclass*)

lemma "abs_wordclass (wrd) * abs_wordclass (wrd') = abs_wordclass (wrd@wrd')"
  by (simp add: mult.abs_eq)


lemma "Rep_wordclass (Abs_wordclass wrdset) = wrdset"

(*Try to finish this lemma along with the lemmas above*)
lemma "rep_wordclass (abs_wordclass wrd) = wrd"
  unfolding wordeq_def sorry
qed