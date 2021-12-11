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
1. Conjugacy relation is sym, refl, tran [Done]]
2. Every word is conjugate to its cyclic presentations [Done]
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

(*
lemma vonj_rel xs (iter ... xs)
lemma conj_rel xs (unclycle xs) 
*)

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
empty:"[] \<in> \<llangle>S\<rrangle>"
|gen:"x \<in> S \<Longrightarrow> xs \<in> \<llangle>S\<rrangle> \<Longrightarrow> (x#xs) \<in> \<llangle>S\<rrangle>"
|invgen: "y \<in> inverse ` S \<Longrightarrow> ys \<in> \<llangle>S\<rrangle> \<Longrightarrow> (y#ys) \<in> \<llangle>S\<rrangle>"

(*
inductive_set group_spanset::"('a,'b) groupgentype set \<Rightarrow> ('a,'b) word set" ("\<llangle>_\<rrangle>")
  for S::"('a,'b) groupgentype set"
  where
empty:"[] \<in> \<llangle>S\<rrangle>"
|gen:"x \<in> S \<Longrightarrow>  [x] \<in> \<llangle>S\<rrangle>"
|invgen: "y \<in> inverse ` S \<Longrightarrow> [y] \<in> \<llangle>S\<rrangle>"
|app: "xs \<in> \<llangle>S\<rrangle> \<Longrightarrow> ys \<in> \<llangle>S\<rrangle> \<Longrightarrow> (xs@ys) \<in> \<llangle>S\<rrangle>"
*)

lemma cons_span: assumes "(x#xs) \<in> \<llangle>S\<rrangle>" shows "[x] \<in> \<llangle>S\<rrangle>"
proof(induction xs)
  case Nil
  then show ?case using assms group_spanset.cases group_spanset.empty group_spanset.gen group_spanset.invgen
    by (metis list.distinct(1) list.sel(1))
next
  case (Cons y xs)
  then show ?case  by auto
qed

lemma span_append:assumes "a \<in> \<llangle>S\<rrangle>" "b \<in> \<llangle>S\<rrangle>" shows "(a@b) \<in> \<llangle>S\<rrangle>"
  using assms
proof(induction a)
  case empty
  then show ?case by simp
next
  case (gen x)
  then show ?case using  group_spanset.gen  by (metis Cons_eq_appendI)
next
  case (invgen y)
  then show ?case using  group_spanset.invgen  by (metis Cons_eq_appendI)
qed

lemma span_cons: assumes "(x#xs) \<in> \<llangle>S\<rrangle>" shows "xs \<in> \<llangle>S\<rrangle>"
  using assms
proof(induction xs)
  case Nil
  then show ?case  by (simp add: group_spanset.empty)
next
  case (Cons a xs)
  then show ?case  using group_spanset.cases  group_spanset.gen group_spanset.invgen by blast
qed

lemma leftappend_span: assumes "(a@b) \<in>  \<llangle>S\<rrangle>" shows "a \<in>  \<llangle>S\<rrangle>"
  using assms
proof(induction a)
  case Nil
  then show ?case using group_spanset.empty by simp
next
  case (Cons a1 a2)
  then have 1: "(a1#(a2 @ b)) \<in> \<llangle>S\<rrangle>" by auto
  then have 2:"[a1] \<in> \<llangle>S\<rrangle>" using cons_span by blast
  have "(a2 @ b) \<in> \<llangle>S\<rrangle>" using span_cons Cons 1 by blast
  then have "a2 \<in> \<llangle>S\<rrangle>" using Cons by simp
  moreover have "(a1#a2)  = [a1] @ a2" by simp
  ultimately show ?case using 1 2 span_append  by metis 
qed

lemma rightappend_span: assumes "(a@b) \<in>  \<llangle>S\<rrangle>" shows "b \<in>  \<llangle>S\<rrangle>"
  using assms
proof(induction a)
case Nil
  then show ?case using empty by simp
next
  case (Cons a1 a2)
 then have 1: "(a1#(a2 @ b)) \<in> \<llangle>S\<rrangle>" by auto
  then have 2:"[a1] \<in> \<llangle>S\<rrangle>" using cons_span by blast
  have "(a2 @ b) \<in> \<llangle>S\<rrangle>" using span_cons Cons 1 by blast
  then show ?case using Cons by blast
qed

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

lemma wordinverse_append: "(wordinverse x) @ (wordinverse y) = (wordinverse (y@x))"
proof(induction y)
  case Nil
  have "wordinverse [] = []" by simp
  then show ?case by simp
next
  case (Cons a y)
  have "(wordinverse x) @ (wordinverse (a # y)) = (wordinverse x) @ (wordinverse y) @ [inverse a]" by simp
  moreover have "(wordinverse ((a#y)@x)) = (wordinverse (y@x)) @ [inverse a]" by simp
  ultimately show ?case using "Cons.IH" by simp
qed

lemma wordinverse_of_wordinverse:  "wordinverse (wordinverse xs) = xs"
proof(induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  have 1: "wordinverse (a#xs) = (wordinverse xs) @ [inverse a]" by auto
  have "wordinverse [inverse a] = [a]" using inverse_of_inverse  by (metis append.left_neutral wordinverse.simps(1) wordinverse.simps(2))
  then have 2:"wordinverse ((wordinverse xs) @ [inverse a]) = [a] @ wordinverse (wordinverse xs)" using wordinverse_append by metis
  then have "[a] @ wordinverse (wordinverse xs) = [a] @ xs" using Cons by auto
  moreover have "[a] @ xs = (a#xs)" by simp
  ultimately show ?case using 1 2 by simp
qed

lemma wordinverse_symm :assumes "wordinverse xs = ys" shows "xs = wordinverse ys"
proof-
  have "wordinverse (wordinverse xs) = wordinverse ys"  using assms by auto
  then show ?thesis using wordinverse_of_wordinverse by metis
qed

lemma inverse_wordinverse: "((wordinverse xs) @  xs) ~ []"
proof-
  let ?ys = "wordinverse xs"
  have "(wordinverse ?ys = xs)" by (simp add: wordinverse_of_wordinverse)
  moreover have "(?ys @ wordinverse ?ys) ~ []" using wordinverse_inverse by blast
  ultimately show ?thesis using wordinverse_of_wordinverse by simp
qed

lemma span_wordinverse: assumes "xs \<in> \<llangle>S\<rrangle>" shows "wordinverse xs \<in> \<llangle>S\<rrangle>"
  using assms
proof(induction xs)
  case empty
  then show ?case by (simp add: group_spanset.empty)
next
  case (gen x xs)
  then have "inverse x \<in> inverse ` S" by simp
  then have "[inverse x] \<in> \<llangle>S\<rrangle>" using group_spanset.empty group_spanset.invgen by blast
  then have "wordinverse xs @ [inverse x] \<in> \<llangle>S\<rrangle>" using gen using span_append by auto
  moreover have "wordinverse (x#xs) = wordinverse xs @ [inverse x]" by simp
  ultimately show ?case  by simp
next
  case (invgen y ys)
  then have "inverse y \<in>  S" using inverse_of_inverse by (metis image_iff)
  then have "[inverse y] \<in> \<llangle>S\<rrangle>" by (simp add: group_spanset.empty group_spanset.gen)
  then have "wordinverse ys @ [inverse y] \<in> \<llangle>S\<rrangle>" using invgen using span_append by auto
  moreover have "wordinverse (y#ys) = wordinverse ys @ [inverse y]" by simp
  ultimately show ?case  by simp
qed

definition conj_rel :: "('a,'b) groupgentype set \<Rightarrow> ('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool"
  where "conj_rel S x y = ( x \<in> \<llangle>S\<rrangle> \<and> y \<in> \<llangle>S\<rrangle> \<and> (\<exists>a\<in>\<llangle>S\<rrangle> . (a @ x @ (wordinverse a)) ~ y))" 

lemma conj_rel_refl:
  assumes "x \<in> \<llangle>S\<rrangle>"
  shows "conj_rel S x x"
  using assms
proof-
  have 1: "[] \<in> \<llangle>S\<rrangle>" by (simp add: group_spanset.empty)
  have "[] @ x @ [] = x" by simp
  moreover then have "x ~ x" by auto
  ultimately then have "([] @ x @ []) ~ x" by simp
  then show ?thesis using assms conj_rel_def 1 by force
qed
 
lemma conj_rel_symm:
  assumes "conj_rel S x y" 
  shows "conj_rel S y x"
  using assms
proof-
  have "conj_rel S x y" using assms by simp
  then obtain a where 1: "a \<in> \<llangle>S\<rrangle> \<and> ((a @ x @ (wordinverse a)) ~ y)" using assms conj_rel_def by blast
  then have "y ~ (a @ x @ (wordinverse a))" using reln.sym by auto
  then have "((wordinverse a) @ y) ~ (wordinverse a @ a @ x @ (wordinverse a))" by (simp add: mult reln.refl)
  then have "((wordinverse a) @ y @ a) ~ (wordinverse a @ a @ x @ (wordinverse a) @ a)" using mult by fastforce
  have "((wordinverse a) @ a) ~ []" by (metis wordinverse_of_wordinverse wordinverse_inverse)
  then have "((wordinverse a) @ y @ a) ~ ([] @ x @ [])" using 1 by (metis (no_types, hide_lams) append.assoc mult reln.refl reln.trans)
  then have "((wordinverse a) @ y @ a) ~ x" by simp
  then have "((wordinverse a) @ y @ wordinverse(wordinverse a)) ~ x" by (metis wordinverse_of_wordinverse)
  then obtain b where "(b = wordinverse a) \<and> (b @ y @ (wordinverse b)) ~ x" by auto
  moreover then have "b \<in> \<llangle>S\<rrangle>" by (simp add: ‹a \<in> \<llangle>S\<rrangle> ∧ (a @ x @ wordinverse a) ~ y› span_wordinverse)
  ultimately show ?thesis using assms conj_rel_def by blast
qed 

lemma conj_rel_trans: assumes "conj_rel S x y" "conj_rel S y z"
  shows "conj_rel S x z"
  using assms
proof-
  obtain a where 1: "a \<in> \<llangle>S\<rrangle> \<and> (a @ x @ (wordinverse a)) ~ y" using assms(1) conj_rel_def by blast
  obtain b where 2: "b \<in> \<llangle>S\<rrangle> \<and>(b @ y @ (wordinverse b)) ~ z" using assms(2) conj_rel_def by blast
  have "(b @ (a @ x @ (wordinverse a))) ~ (b @ y)"  by (simp add: 1 mult reln.refl)
  then have  "(b @ a @ x @ (wordinverse a) @ wordinverse b)~ (b @ y @ wordinverse b)"  using mult by fastforce
  then have "(b @ a @ x @ (wordinverse a) @ wordinverse b) ~ z" using 2 using reln.trans by blast
  then have "((b @ a) @ x @ (wordinverse (b @ a))) ~ z" by (simp add: wordinverse_append)
  moreover have "(b@a) \<in>  \<llangle>S\<rrangle>" using "2" "1"  using span_append  by blast
  ultimately show ?thesis using assms unfolding conj_rel_def by blast
qed
                           
definition conj_class ::"('a,'b) groupgentype set \<Rightarrow> ('a,'b) word \<Rightarrow> ('a,'b) word set"
  where "conj_class S x = {y. conj_rel S x y}"

definition cycle_at_i :: "('a,'b) word \<Rightarrow> nat \<Rightarrow> ('a,'b) word"
  where
"cycle_at_i x i = (drop i x)@(take i x)"

definition cyclicp_at_i :: "('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> nat \<Rightarrow> bool"
  where "cyclicp_at_i x y i = (cycle_at_i x i = y)"

definition cyclicp :: "('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool"
  where "cyclicp x y = (\<exists>i. cyclicp_at_i x y i)"

lemma assumes "xs \<in>  \<llangle>S\<rrangle>" shows "conj_rel S xs (cycle_at_i xs i)"
proof-
  have 1: "xs = (take i xs) @ (drop i xs)" by simp
  have d: "(drop i xs) \<in>  \<llangle>S\<rrangle>" using 1 rightappend_span assms by metis
  have t: "(take i xs) \<in>  \<llangle>S\<rrangle>" using 1 leftappend_span assms by metis
  let ?as = "wordinverse (take i xs)"
  have a: "?as \<in>  \<llangle>S\<rrangle>" using t by (simp add: span_wordinverse)
  have "(wordinverse (take i xs) @ (take i xs)) ~ []" using inverse_wordinverse by fast
  then have "(wordinverse (take i xs) @ (take i xs) @ (drop i xs)) ~ (drop i xs)" using mult reln.refl by (metis append.left_neutral append_assoc)
  then have "(wordinverse (take i xs) @ (take i xs) @ (drop i xs) @ (take i xs)) ~ (drop i xs) @ (take i xs)" using mult reln.refl by (metis append.assoc)
  then have "(wordinverse (take i xs) @ xs @ (take i xs)) ~ (drop i xs) @ (take i xs)" using 1 by (metis append.assoc)
  then have "(?as @ xs @ wordinverse ?as) ~ (drop i xs) @ (take i xs)" by (simp add: wordinverse_of_wordinverse)
  then have "(?as @ xs @ wordinverse ?as) ~ (cycle_at_i xs i)"by (simp add: cycle_at_i_def)
  moreover have "(cycle_at_i xs i) \<in>  \<llangle>S\<rrangle>" unfolding cycle_at_i_def using d t span_append by blast
  ultimately show ?thesis unfolding conj_rel_def using assms a by blast
qed

lemma "conj_rel S xs (cyclic_reduct xs)"
proof(induction xs)
  case Nil
  have "length [] = 0" by simp
  moreover have "iter 0 reduct [] = []" by simp
  ultimately have "uncycle [] = []" by simp
  then have 1: "cyclic_reduct [] = []"  by (simp add: cyclic_reduct_def)  
  have "[] @ [] @ [] = []" by simp
  moreover then have "[] ~ []" by (simp add: reln.refl)
  ultimately have "([] @ [] @ []) ~ []" by simp
  then show ?case using 1 by (smt (verit, ccfv_SIG) conj_rel_def group_spanset.empty wordinverse.simps(1))
next
  case (Cons a xs)
  then show ?case sorry
qed


 






