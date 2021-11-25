theory Conjugacy
imports "FreeGroupMain" "Iter_Reduction_Results"
begin

(*To prove: conj_rel xs ys \<Longleftrightarrow> cyclicp (cyclic_reduct xs) (cyclic_reduct ys)
Lemmas required:
(A. Every word is conjugate to a cyclically reduced word, namely its cyclic reduction.)
1. "cyclic_reduced (cyclic_reduct xs)" [DONE]
2. "conj_rel xs (cyclic_reduct xs)"

(B. If x and y are two cyclically reduced words that are conjugate, then x is a cyclic presentation of y.)
3. "cyclic_reduced x" "cyclic_reduced y \<Longleftrightarrow> conj_rel x y" shows "cyclip x y" 

C. Any two cyclically reduced words that are conjugate are of the same length.
D. A word is cyclically reduced if and only if it is of the minimum length in its conjugacy class.
*)

(* Other lemmas required:
1. Conjugacy relation is sym, refl, tran [Current]
2. Every word is conjugate to its cyclic presentations
*)

fun uncyclic :: "('a,'b) word \<Rightarrow> bool"
  where
"uncyclic [] = True" |
"uncyclic [x] = True" |
"uncyclic (x#xs) =  (x \<noteq> inverse (last xs))"

definition cyclic_reduced :: "('a,'b) word \<Rightarrow> bool"
  where "cyclic_reduced xs = (reduced xs \<and> uncyclic xs)"

fun uncycle :: "('a,'b) word \<Rightarrow> ('a,'b) word"
  where
"uncycle [] = []"|
"uncycle [x] = [x]"|
"uncycle (x#xs) = (if (x = inverse (last xs)) then uncycle (take (length xs - 1) xs)
                   else (x#xs))"

definition cyclic_reduct :: "('a,'b) word \<Rightarrow> ('a,'b) word"
  where "cyclic_reduct xs =  uncycle (iter (length xs) reduct xs)"

lemma take_last:
  assumes "xs \<noteq> []"
  shows  "xs = (take (length xs - 1) xs) @ [last xs]"
  using assms
proof(induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
  proof(cases "xs = []")
    case True
    then have 1: "(a#xs) = [a]" by simp
    have 2: "(take (length (a#xs) - 1) (a#xs)) = []" using True by simp
    have 3: "[last (a#xs)] = [a]" using True by simp
then show ?thesis using 1 2 3  by simp
next
  case False
  then have 1: "xs = take (length xs - 1) xs @ [last xs]" using Cons.IH by auto
  then have "(a#xs) = (a#( take (length xs - 1) xs @ [last xs]))" by simp
  then have "(a#xs) = (take (length (a#xs) - 1)(a#xs) @ [last xs])" using False by (metis Cons.prems butlast_conv_take last_ConsR snoc_eq_iff_butlast)
  then have "(a#xs) = (take (length (a#xs) - 1)(a#xs) @ [last (a#xs)])" using False by auto
  then show ?thesis by simp
qed
qed

lemma reduced_take_last: assumes "reduced (x#xs)"
  shows "reduced (take (length xs - 1) xs)"
proof(cases "xs = []")
  case True
  then show ?thesis by simp
next
  case False
  have "(x#xs) = [x] @ xs"  by simp
  then have a: "reduced xs" using assms reduced_leftappend by metis
  moreover have "xs = (take (length xs - 1) xs) @ [last xs]"using False take_last by blast
  ultimately show ?thesis using reduced_rightappend by metis
qed



lemma reduced_uncycle: assumes "reduced xs"
  shows "reduced (uncycle xs)"
  using assms
proof(induction xs rule: uncycle.induct)
  case 1
  then have "uncycle [] = []" by simp
  then show ?case by simp 
next
  case (2 x)
 then have "uncycle [x] = [x]" by simp
  then show ?case by simp 
next
  case (3 x v va)
  then show ?case 
  proof(cases "x \<noteq> inverse (last (v#va))")
    case True
    then have "uncycle (x#v#va) = (x#v#va)" by auto
then show ?thesis using 3 by metis
next
  case False
  have "reduced (v#va)" using 3 by (metis reduced.simps(3))
  then have " reduced (take (length (v # va) - 1) (v # va))" using reduced_take_last "3.prems" by blast
  then have "reduced (uncycle (take (length (v # va) - 1) (v # va)))" using 3 False by blast
  moreover have "uncycle (x#v#va) = uncycle (take (length (v # va) - 1) (v # va))" using False by auto
  ultimately show ?thesis by presburger
qed
qed

lemma reduced_cyclic_reduct:"reduced (cyclic_reduct xs)"
proof(induction xs rule: reduced.induct)
  case 1
  have "(iter (length []) reduct []) = []" by simp
  moreover have "uncycle [] = []" by simp
  ultimately have a: "cyclic_reduct [] = []" by (simp add: cyclic_reduct_def)
  have 1: "reduced []" by simp
  show ?case using 1 by (simp add: a cyclic_reduced_def)
next
  case (2 x)
  have "(iter (length [x]) reduct [x]) = [x]" by simp
  moreover have "uncycle [x] = [x]" by simp
  ultimately have a: "cyclic_reduct [x] = [x]" by (simp add: cyclic_reduct_def)
  have 1: "reduced [x]" by simp
  show ?case using 1 by (simp add: a cyclic_reduced_def)
next
  case (3 g h wrd)
  have "cyclic_reduct xs = uncycle (iter (length xs) reduct xs)"  by (simp add: cyclic_reduct_def)
  then show ?case using reduced_uncycle 3 
    by (metis cyclic_reduct_def reduced_iter_length)
qed

lemma uncylic_uncycle: "uncyclic (uncycle xs)"
proof(induction xs rule: uncycle.induct)
  case 1
  then have "uncycle [] = []" by simp
  then show ?case by simp
next
  case (2 x)
   then have "uncycle [x] = [x]" by simp
  then show ?case by simp
next
  case (3 x v va)
  then show ?case
proof(cases "x = inverse(last (v#va))")
  case True
  then have "uncyclic (uncycle (take (length (v # va) - 1) (v # va)))"  using "3.IH" by blast
  moreover have "uncycle (x#v#va) = uncycle (take (length (v # va) - 1) (v # va))" using True by simp
  ultimately show ?thesis by presburger
next
  case False
  then show ?thesis using False by auto
qed
qed

lemma uncyclic_cyclic_reduct : "uncyclic (cyclic_reduct xs)"
  by (simp add: cyclic_reduct_def uncylic_uncycle)

lemma cyclic_reduced_cyclic_reduct: "cyclic_reduced (cyclic_reduct xs)"
proof-
  have "reduced (cyclic_reduct xs)" by (simp add: reduced_cyclic_reduct)
  moreover have "uncyclic (cyclic_reduct xs)" by (simp add: uncyclic_cyclic_reduct)
  ultimately show ?thesis by (simp add: cyclic_reduced_def)
qed

inductive_set group_spanset::"('a,'b) groupgentype set \<Rightarrow> ('a,'b) word set" ("\<llangle>_\<rrangle>")
  for S::"('a,'b) groupgentype set"
  where
"[] \<in> \<llangle>S\<rrangle>"
|"x \<in> S \<Longrightarrow> [x] \<in> \<llangle>S\<rrangle>"
|"y \<in> inverse ` S \<Longrightarrow> [y] \<in> \<llangle>S\<rrangle>"
|"xs \<in> \<llangle>S\<rrangle> \<Longrightarrow> ys \<in> \<llangle>S\<rrangle> \<Longrightarrow> xs@ys \<in> \<llangle>S\<rrangle>"

lemma wordinverse_inverse: "(xs @ (wordinverse xs)) ~ []"
proof(induction xs)
  case Nil
  have "[] = []" by simp
  then show ?case by (simp add: reln.refl)
next
  case (Cons a xs)
  have "wordinverse (a#xs) = (wordinverse xs) @ [inverse a]"  by simp
  moreover have "(a#xs) = [a] @ xs" by simp
  ultimately have 1: "((a # xs) @ wordinverse (a # xs)) = [a] @ xs @ (wordinverse xs) @  [inverse a]" by (metis append_assoc)
  have "([a] @ xs @ (wordinverse xs)) ~ [a] @ []"  using Cons.IH mult by blast
  then have "([a] @ xs @ (wordinverse xs)) ~ [a]"  by auto
  moreover have "[inverse a] ~ [inverse a]" by (simp add: reln.refl)
  ultimately have "([a] @ xs @ (wordinverse xs) @  [inverse a]) ~ [a] @ [inverse a]" using mult by (metis append_assoc)
  then have "([a] @ xs @ (wordinverse xs) @  [inverse a]) ~ []" by (simp add: base reln.trans)
  then show ?case using 1  by auto
qed


definition conj_rel :: "('a,'b) groupgentype set \<Rightarrow> ('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool"
  where "conj_rel S x y = ( x \<in> \<llangle>S\<rrangle> \<and> y \<in> \<llangle>S\<rrangle> \<and> (\<exists>a\<in>\<llangle>S\<rrangle> . (a @ x @ (wordinverse a)) ~ y))" 

(*We are assuming, for example, (ab)^-1 = b^-1 a^-1*)

lemma conj_rel_sym: assumes "conj_rel S x y"
  shows "conj_rel S y x"
  using assms
proof(induction x)
  case Nil
  then obtain a where "(a @ [] @ (wordinverse a)) ~ y" using assms conj_rel_def by blast
  then have "y ~ (a @ [] @ (wordinverse a))" using reln.sym by auto
  moreover have "(a @ [] @ (wordinverse a)) = (a @ (wordinverse a))"  by simp
  ultimately have "y ~ (a @ (wordinverse a))" by simp
  then have "y ~ []" using wordinverse_inverse reln.trans by auto
  then have "([] @ y  @ (wordinverse [])) ~ []" by simp
  then show ?case using Nil unfolding conj_rel_def by blast
next
  case (Cons a x)
  then show ?case sorry
qed

                           
definition conj_class ::"('a,'b) groupgentype set \<Rightarrow> ('a,'b) word \<Rightarrow> ('a,'b) word set"
  where "conj_class S x = {y. conj_rel S x y}"


definition cyclic_at_i :: "('a,'b) word \<Rightarrow> nat \<Rightarrow> ('a,'b) word"
  where
"cyclic_at_i x i = (drop i x)@(take i x)"

definition cyclicp_at_i :: "('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> nat \<Rightarrow> bool"
  where "cyclicp_at_i x y i = (cyclic_at_i x i = y)"

definition cyclicp :: "('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool"
  where "cyclicp x y = (\<exists>i. cyclicp_at_i x y i)"








