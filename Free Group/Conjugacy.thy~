theory Conjugacy
imports "FreeGroupMain" "Iter_Reduction_Results"
begin


(*To prove: conj_rel S xs ys \<Longleftrightarrow> cyclicp (cyclic_reduct xs) (cyclic_reduct ys) [DONE]

Lemmas required:
(A. Every word is conjugate to a cyclically reduced word, namely its cyclic reduction.)
1. "cyclic_reduced S (cyclic_reduct xs)" [DONE]
2. "conj_rel S xs (cyclic_reduct xs)" [DONE]

(B. If x and y are two cyclically reduced words that are conjugate, then x is a cyclic presentation of y.)
3. "cyclic_reduced x" "cyclic_reduced y" "conj_rel S x y" \<Rightarrow> "cyclip x y" [DONE]
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
  ultimately  have "([] @ x @ []) ~ x" by simp
  then show ?thesis using assms conj_rel_def 1 by force
qed
 
lemma conj_rel_symm:
  assumes "conj_rel S x y" 
  shows "conj_rel S y x"
  using assms
proof-
  obtain a where 1: "a \<in> \<llangle>S\<rrangle> \<and> (a @ x @ (wordinverse a)) ~ y" using assms(1) conj_rel_def by blast
  let ?b = "wordinverse a"
  have inv: "wordinverse ?b = a" by (simp add: wordinverse_of_wordinverse)
  have b: "?b \<in> \<llangle>S\<rrangle>" by (simp add: 1 span_wordinverse)
  have "(?b@a@ x @ (wordinverse a)) ~ (?b@y)" by (simp add: 1 mult reln.refl)
  moreover have "([] @ x @ (wordinverse a)) ~ (?b@a@ x @ (wordinverse a)) " using inverse_wordinverse append_assoc mult reln.refl reln.sym by metis
  ultimately have "([] @ x @ (wordinverse a)) ~ (?b@y)" using  reln.trans by blast
  then have "(x @ (wordinverse a) @ a) ~ (?b@y@(wordinverse ?b))" using inv mult by fastforce
  moreover have "(x @ []) ~ (x @ (wordinverse a) @ a)" using wordinverse_inverse reln.refl inv mult reln.sym by metis
  ultimately have "x ~ (?b@y@(wordinverse ?b))" using reln.trans by auto
  then show ?thesis  using b assms reln.sym unfolding conj_rel_def  by blast
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

lemma cycle_at_conj: assumes "xs \<in>  \<llangle>S\<rrangle>" shows "conj_rel S xs (cycle_at_i xs i)"
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

lemma conj_cyclcip: assumes "xs \<in>  \<llangle>S\<rrangle>" "ys \<in>  \<llangle>S\<rrangle>" "cyclicp xs ys" shows "conj_rel S xs ys"
proof-
  obtain i where "ys = cycle_at_i xs i" by (metis assms(3) cyclicp_at_i_def cyclicp_def)
  then have "conj_rel S xs ys" by (simp add: assms(1) cycle_at_conj)
  then show ?thesis by simp
qed

lemma reduct_span: assumes "xs \<in>  \<llangle>S\<rrangle>" shows "reduct xs \<in>  \<llangle>S\<rrangle>"
  using assms
proof(induction xs rule:reduct.induct)
  case 1
  then have "reduct [] = []" by simp
  then show ?case using 1  by simp
next
  case (2 x)
  then have "reduct [x] = [x]" by simp
  then show ?case using 2  by simp
next
  case (3 g1 g2 wrd)
  then show ?case
  proof(cases "g1 = inverse g2")
    case True
    then have "reduct (g1#g2#wrd) = wrd" by simp
    moreover have "wrd \<in> \<llangle>S\<rrangle>" using 3 span_cons by blast
    ultimately show ?thesis  by simp
next
  case False
  then have 1: "reduct (g1#g2#wrd) = (g1#(reduct (g2#wrd)))" by simp
  have "g2 # wrd \<in> \<llangle>S\<rrangle>" using 3 span_cons by blast
  then have "reduct (g2#wrd) \<in> \<llangle>S\<rrangle>" using 3 False by simp
  moreover have "[g1] \<in> \<llangle>S\<rrangle>" using False using 3 cons_span by blast
  ultimately show ?thesis using 1 span_append by fastforce
qed
qed

lemma iter_reduct_span : assumes "xs \<in>  \<llangle>S\<rrangle>" shows "(iter n reduct xs) \<in>  \<llangle>S\<rrangle>"
  using assms
proof(induction n)
  case 0
  then have "iter 0 reduct xs = xs" by simp
  then show ?case by (simp add: assms)
next
  case (Suc n)
  then have "iter n reduct xs \<in> \<llangle>S\<rrangle>" by simp
  then have "reduct (iter n reduct xs) \<in> \<llangle>S\<rrangle>" using reduct_span by auto
then show ?case by simp
qed

lemma conj_iter :assumes "xs \<in>  \<llangle>S\<rrangle>" shows "conj_rel S (iter (length xs) reduct xs) xs"
  using assms
proof-
  have "cancels_to xs (iter (length xs) reduct xs)" using iter_cancels_to  by auto
  then have "xs ~  (iter (length xs) reduct xs)" using cancels_imp_rel  by blast
  then have "([] @ (iter (length xs) reduct xs) @ (wordinverse [])) ~ xs" by (simp add: reln.sym)
  moreover have "(iter (length xs) reduct xs) \<in>  \<llangle>S\<rrangle>" using assms iter_reduct_span by blast
  ultimately show ?thesis unfolding conj_rel_def using assms group_spanset.empty by blast
qed

lemma conj_uncycle: assumes "xs \<in>  \<llangle>S\<rrangle>" shows "conj_rel S (uncycle xs) xs"
  using assms
proof(induction xs rule: uncycle.induct)
  case 1
  then have "uncycle [] = []" by simp
  moreover have "([] @ [] @ wordinverse [])~[]" by auto
  ultimately show ?case unfolding conj_rel_def using 1 group_spanset.empty by force
next
  case (2 x)
then have "uncycle [x] = [x]" by simp
  moreover have "([] @ [x] @ wordinverse [])~[x]" by auto
  ultimately show ?case unfolding conj_rel_def using 2 group_spanset.empty by force
next
case (3 x v va)
  then show ?case
  proof(cases "x = inverse (last (v#va))")
    case True
    have b:"(x#v # va)\<in>  \<llangle>S\<rrangle>" using 3 by simp
    then have "(v # va)\<in>  \<llangle>S\<rrangle>" using span_cons by blast
    then have "take (length (v # va) - 1) (v # va) \<in> \<llangle>S\<rrangle>" by (metis append_take_drop_id leftappend_span)
    then have 1: "conj_rel S (uncycle (take (length (v # va) - 1) (v # va))) (take (length (v # va) - 1) (v # va))" using 3 True  by blast
    have a: "uncycle (x # v # va) = uncycle (take (length (v # va) - 1) (v # va))" using True by simp
    then have "([] @ uncycle (x # v # va) @ wordinverse []) ~ uncycle (take (length (v # va) - 1) (v # va))" by (simp add: reln.refl)
    moreover have "uncycle (take (length (v # va) - 1) (v # va)) \<in>  \<llangle>S\<rrangle>" using 1 unfolding conj_rel_def by simp
    ultimately have 2: "conj_rel S (uncycle (x # v # va)) (uncycle (take (length (v # va) - 1) (v # va)))" unfolding conj_rel_def using a empty by metis
    have x: "[x] \<in>  \<llangle>S\<rrangle>" using b cons_span  by blast
    have "(last (v#va)) = inverse x" using True inverse_of_inverse by blast
    then have "[x] @ (take (length (v # va) - 1) (v # va)) @ wordinverse [x] = (x # v # va)" using take_last wordinverse.simps by (metis (no_types, lifting) Cons_eq_append_conv list.distinct(1))
    moreover have "(take (length (v # va) - 1) (v # va)) \<in>  \<llangle>S\<rrangle>" using 1 unfolding conj_rel_def by simp
    ultimately  have "conj_rel S (take (length (v # va) - 1) (v # va)) (x # v # va)" unfolding conj_rel_def using  b x reln.refl by metis
    then have "conj_rel S (uncycle (take (length (v # va) - 1) (v # va))) (x # v # va)" using 1 conj_rel_trans  by blast
then show ?thesis using 2 conj_rel_trans by fast
next
  case False
  then have "uncycle (x#v#va) = (x#v#va)" by simp
  moreover then have "([] @ uncycle (x#v#va) @ wordinverse []) ~ (x#v#va)" using reln.refl by auto
  ultimately show ?thesis unfolding conj_rel_def using 3 empty by force
qed
qed



lemma conj_cyclicreduct:assumes "xs \<in>  \<llangle>S\<rrangle>" shows "conj_rel S (cyclic_reduct xs) xs"
proof-
  have "conj_rel S (iter (length xs) reduct xs) xs" using assms by (simp add: conj_iter)
  moreover have "conj_rel S (uncycle (iter (length xs) reduct xs)) (iter (length xs) reduct xs)" using assms iter_reduct_span conj_uncycle by fast
  ultimately show ?thesis  unfolding cyclic_reduct_def  using conj_rel_trans by blast
qed

(*----------------------------------------------------------------*)

lemma wordinverse_redef1: "wordinverse xs = rev (map inverse xs)"
proof(induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have 1:"wordinverse (a#xs) = wordinverse xs @ [inverse a]" by auto
  have "rev (map inverse (a#xs)) = rev((inverse a#( map inverse xs)))" by simp
  then have 2: "rev (map inverse (a#xs)) = rev (map inverse (xs)) @ [inverse a]" by simp
  then show ?case using 1 2 Cons.IH by simp
qed

lemma wordinverse_redef2: "wordinverse xs = map inverse (rev xs)"
proof(induction xs)
case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have 1:"wordinverse (a#xs) = wordinverse xs @ [inverse a]" by auto
  have "map inverse (rev (a#xs)) = map inverse (rev xs @ [a])"  by simp
  then have 2: "map inverse (rev (a#xs)) = map inverse (rev xs) @ [inverse a]"  by simp
  then show ?case using 1 2 Cons.IH by auto
qed

(*
lemma shows "(wordinverse xs) ~ (wordinverse ((iter (length xs) reduct) xs))"
proof-
  have "(xs @ (wordinverse xs)) ~ []" by (simp add: wordinverse_inverse)
  moreover have "(((iter (length xs) reduct) xs) @ (wordinverse ((iter (length xs) reduct) xs))) ~ []" by (simp add: wordinverse_inverse)
  ultimately have "(xs @ (wordinverse xs)) ~ (((iter (length xs) reduct) xs) @ (wordinverse ((iter (length xs) reduct) xs)))" using reln.sym reln.trans by blast
  moreover have "xs  ~ ((iter (length xs) reduct) xs)" by (simp add: cancels_imp_rel iter_cancels_to)
  ultimately show ?thesis sorry
qed
*)

lemma reduced_iter_eq: assumes "reduced xs" shows "((iter n reduct) xs) = xs"
  by (metis assms iter.iter.simps(1) iter_cancels_to le0 not_reduced_iter_suc unique_reduced_cancel)

lemma hd_last_wordinverse: assumes "length xs > 0" shows "hd xs = inverse (last (wordinverse xs))"
  using assms
proof(induction xs)
  case Nil
  then have False by auto
  then show ?case by simp
next
  case (Cons a xs)
  have 1:"hd (a#xs) = a" by simp
  have " wordinverse (a#xs) = wordinverse xs @ [inverse a]" by simp 
  then have "last (wordinverse (a#xs)) = inverse a" by simp
  then have "inverse (last (wordinverse (a#xs))) = inverse (inverse a)" by simp
  then have "inverse (last (wordinverse (a#xs))) = a"  by (metis inverse_of_inverse)
  then show ?case using 1  by simp
qed


lemma cancels_to_1_at_not_reduced:
  assumes  "reduced xs" 
  shows "(\<nexists>i. i<(length xs - 1) \<and> xs!i = inverse (xs!(i+1)))"
  using assms
proof(induction xs)
  case Nil
  then show ?case  by auto
next
  case (Cons a xs)
  then have xs:"reduced xs" by (metis (mono_tags, lifting) reduced.elims(3) reduced.simps(3))
  then show ?case
  proof(cases "xs = []")
    case True
    then have "(a#xs) = [a]" by simp
    then have "length (a#xs) = 1" by simp
    then show ?thesis using Cons by auto
  next
    case False
    then have gnil: "xs \<noteq> []"  by auto
    then show ?thesis
    proof(cases "length xs = 1")
      case True
      then obtain b where "xs = [b]"  using length_Cons reduced.elims(2) xs by fastforce 
      then have 1:"(a#xs) = (a#[b])" by simp
      then have 2:"length (a#xs) = 2" by auto
      then show ?thesis
      proof(cases "a = inverse b")
        case True
        then have "\<not> reduced (a#xs)" using 1 by auto
  then show ?thesis using Cons by blast
next
  case False
  then have "(a # xs) ! 0 \<noteq> FreeGroupMain.inverse ((a # xs) ! (0 + 1))" using 1  by simp
  then show ?thesis using 2  by force
qed
next
  case False
  then have "1 < length xs" using gnil  nat_neq_iff by auto
  then have ix:"\<not> (\<exists>i<length xs - 1. xs ! i = FreeGroupMain.inverse (xs ! (i + 1)))" using xs Cons by blast
  let ?x = "hd xs"
  show ?thesis
  proof(cases "a = inverse ?x")
    case True
    then have "\<not> reduced (a#xs)"  by (metis gnil list.exhaust_sel reduced.simps(3)) 
then show ?thesis using Cons by blast
next
  case False
  then show ?thesis using ix by (metis Cons.prems(1) inv_not_reduced inverse_of_inverse less_diff_conv)
qed
qed
  qed
qed

lemma not_reduced_cancels_to_1_at:
  assumes "\<not> reduced xs"
  shows "(\<exists>i .i<(length xs - 1)\<and> xs!i = inverse (xs!(i+1)))"
proof(rule ccontr)
  assume assm: "\<not>(\<exists>i .i<(length xs - 1)\<and>  xs!i = inverse (xs!(i+1)))"
  then have  "(\<nexists>i .i<(length xs - 1)\<and> xs!i = inverse (xs!(i+1)))" by simp
  then have "reduced xs"
  proof(induction xs rule:reduced.induct)
    case 1
    then show ?case by simp
  next
    case (2 g)
    then show ?case by simp
  next
    case (3 g h wrd)
    then have 1: "g \<noteq> inverse h"  by force
    moreover have " \<not> (\<exists>i<length (h # wrd) - 1. (h # wrd) ! i = FreeGroupMain.inverse ((h # wrd) ! (i + 1)))" using 3  using BNF_Greatest_Fixpoint.length_Cons add.commute add_diff_cancel_left' by auto
    ultimately have "reduced (h # wrd)" using 3 by simp
    then show ?case using 1 by simp
  qed
  then show False using assms by blast
qed

lemma reduced_rev: assumes "reduced xs" shows "reduced (rev xs)"
proof(rule ccontr)
  assume "\<not> reduced (rev xs)"
  then obtain i where ixs:"i<length (rev xs)-1 \<and>(rev xs)!i = inverse ((rev xs)!(i+1))" using not_reduced_cancels_to_1_at by blast
  then have "(rev xs)!i = xs!((length xs - 1)- i)"  by (metis add_lessD1 diff_Suc_eq_diff_pred length_rev less_diff_conv rev_nth)
  moreover have "((rev xs)!(i+1)) = xs!((length xs - 1)- (i+1))" by (metis diff_diff_left ixs length_rev less_diff_conv plus_1_eq_Suc rev_nth)
  ultimately have "xs!((length xs - 1)- i) = inverse (xs!((length xs - 1)- (i+1)))" using ixs by presburger
  then have j:"(xs!((length xs - 1)- (i+1))) = inverse (xs!((length xs - 1)- i))" using inverse_of_inverse by blast
  let ?j = "((length xs - 1)- (i+1))"
   have "?j + 1 = ((length xs - 1)- i)"by (metis Suc_diff_Suc add.commute ixs length_rev plus_1_eq_Suc)
   moreover have "?j <length xs-1" using calculation by linarith
   ultimately have "(?j <length xs-1) \<and> (xs!?j = inverse (xs!(?j+1)))" using j by presburger
   then have "\<not> reduced xs" using cancels_to_1_at_not_reduced by blast
   then show False using assms by simp
 qed

lemma reduced_inverse: assumes "reduced xs" shows "reduced (map inverse xs)"
proof(rule ccontr)
  assume "\<not> reduced (map inverse xs)"
  then obtain i where ixs:"i<length (map inverse xs)-1 \<and>(map inverse xs)!i = inverse ((map inverse xs)!(i+1))" using not_reduced_cancels_to_1_at by blast
  then have "xs!i = inverse (xs!(i+1))"  by (metis add_lessD1 inverse_of_inverse length_map less_diff_conv nth_map)
  moreover have "i<length  xs-1" using ixs by auto
  ultimately have "\<not> reduced xs" using cancels_to_1_at_not_reduced by blast
 then show False using assms by simp
 qed

lemma reduced_wordinverse: assumes "reduced xs" shows "reduced (wordinverse xs)"
proof-
  have "reduced (rev xs)" using assms by (simp add: reduced_rev)
  then have "reduced (map inverse (rev xs))" by (simp add: reduced_inverse)
  then show ?thesis by (simp add: wordinverse_redef2)
qed

lemma append_notreduced: assumes "reduced a" "reduced b" "a\<noteq>[]" "b\<noteq>[]" shows "last a = inverse (hd b) \<Longrightarrow> \<not>(reduced (a@b))"
  using assms
proof(induction a rule: reduced.induct)
  case 1
  then show ?case  by blast
next
  case (2 g)
  then show ?case by (metis append_Cons append_self_conv2 last_ConsL list.exhaust_sel reduced.simps(3))
next
  case (3 g h wrd)
then have 1: "g \<noteq> inverse h" by auto
  moreover have  "last (h # wrd) = FreeGroupMain.inverse (hd b)" using 3 by auto
  ultimately have "\<not> reduced ((h # wrd) @ b)" using 3 assms reduced_rightappend by blast
  then show ?case by auto
qed

lemma append_reduced: assumes "reduced a" "reduced b" shows "last a \<noteq> inverse (hd b) \<Longrightarrow> (reduced (a@b))"
  using assms
proof(induction a rule:reduced.induct)
  case 1
  then show ?case by simp
next
  case (2 g)
  then show ?case using reduced.elims(3) by fastforce
next
  case (3 g h wrd)
  then have 1: "g \<noteq> inverse h" by auto
  moreover have  "last (h # wrd) \<noteq> FreeGroupMain.inverse (hd b)" using 3 by auto
  ultimately have "reduced ((h # wrd) @ b)" using 3  by auto
  then show ?case using 1 by auto
qed

(*Show 0.2*)
lemma onesidecancel: assumes "reduced a" "reduced b" "reduced c" "b\<noteq>[]" "\<not> reduced (a@b@c)" shows "(\<not> reduced (a@b)) \<or> (\<not> reduced (b@c))"
proof(rule ccontr)
  assume "\<not>((\<not> reduced (a@b)) \<or> (\<not> reduced (b@c)))"
  then have assm: "( reduced (a@b) \<and>   reduced (b@c))"  by simp
  have "reduced (a@b@c)"
  proof(rule ccontr)
    assume assmassm:"\<not> reduced (a @ b @ c)"
    then show False
    proof(cases "a = []")
      case True
      then have "\<not> reduced (b @ c)" using assmassm by auto
      then show ?thesis using assm by simp
    next
      case False
      have "last a = inverse (hd (b@c))" using append_reduced assm assms by blast
      then have "last a = inverse (hd b)" using assms by simp
      then have "\<not> reduced (a @ b)" using append_notreduced using False assms by blast
      then show ?thesis using assm by blast
    qed
  qed
  then show False using assms  by simp
qed

lemma tlempty: assumes "length xs > 1" shows "tl xs \<noteq> []"
proof(rule ccontr)
  assume "\<not> tl xs \<noteq> []" 
  then have tl: "tl xs = []" by auto
  then have "xs = [hd xs] @ tl xs" using assms by (metis append_Nil2 hd_Cons_tl list.size(3) not_one_less_zero)
  then have "xs = [hd xs]" using tl by simp
  then have "length xs = 1" by (metis BNF_Greatest_Fixpoint.length_Cons One_nat_def list.size(3))
  then show False using assms by simp
qed

lemma not_uncyclic:assumes "length xs > 1" "hd xs = inverse (last xs)" shows "\<not> uncyclic xs"
proof-
  let ?x = "hd xs"
  let ?s = "tl xs"
  have 1:"?s \<noteq> []" using assms tlempty by blast
  have xs:"xs = (?x#?s)" using assms by (metis hd_Cons_tl list.size(3) not_one_less_zero)
  then have "?x = inverse (last ?s)" using assms  by (metis last_ConsR length_tl less_numeral_extra(3) list.size(3) zero_less_diff)
  then show ?thesis using 1 uncyclic.elims(2) by fastforce
qed

lemma inverse_not_refl: assumes "a = b" shows "a \<noteq> inverse b"
proof-
  show ?thesis using assms  inverse.elims by blast
qed

(*Show 0.1*)
lemma onesidenotcancel:assumes "reduced a" "cyclic_reduced xs" shows "(reduced (a@xs) \<or> reduced (xs@ wordinverse a))"
proof(rule ccontr)
  have xs:"reduced xs" using assms(2) using cyclic_reduced_def by auto
  assume "\<not>(reduced (a@xs) \<or> reduced (xs@ wordinverse a))"
  then have assm:"(\<not> reduced (a@xs)) \<and> (\<not> reduced (xs@ wordinverse a))" by simp
  then show False
  proof(cases "length xs > 1") 
  case True
  then have 1:"last a = inverse (hd xs)" using append_reduced assm assms(1) xs  by auto
  have 2:"last xs = inverse (hd (wordinverse a))" using append_reduced assms(1) xs assm reduced_wordinverse by auto
  have "last a = inverse (hd (wordinverse a))" by (metis append_Nil2 assm last_snoc list.exhaust list.sel(1) wordinverse.simps(2) wordinverse_symm xs)
  then have "hd xs = inverse (last xs)" using 1 2 inverse_of_inverse by metis
  then have "\<not> uncyclic xs" using True not_uncyclic by auto
  then show ?thesis using assms(2) cyclic_reduced_def by auto
next
  case False
  then have F:"length xs \<le> 1" by simp
  show ?thesis
  proof(cases "xs = []")
    case True
    then have "reduced (a@xs)" using assms(1) by simp
then show ?thesis using assm  by simp
next
  case False
  then have "length xs = 1" using F by (metis One_nat_def append_eq_conv_conj div_by_Suc_0 div_less nat_less_le take0)
  then obtain b where b:"xs = [b]" using reduced.elims(2) xs by fastforce
  then have "last a = inverse b" using assm xs append_reduced assms(1) by (metis list.sel(1))
  moreover have "b = inverse (hd (wordinverse a))" using assms(1)  reduced_wordinverse xs assm b append_reduced by (metis last.simps)
  ultimately have "last a = (hd (wordinverse a))" by (metis inverse_of_inverse)
  moreover have "last a = inverse (hd (wordinverse a))" using assm wordinverse.simps(1) wordinverse_redef2  wordinverse_of_wordinverse xs by (metis append_Nil2 calculation hd_map hd_rev rev.simps(1))
  ultimately show ?thesis using inverse_not_refl by blast
qed
qed
qed

lemma middleterm: assumes "(a@b) = (c@a)" shows "(\<exists>x y. (y@x@y) = (a@b) \<and> (y@x@y) = (c@a))"
  by (metis append_eq_append_conv2 append_self_conv assms)

lemma overlapleftexist:assumes "(a@b) = (y@x)" "length y > length a" shows "(\<exists>z.(a@z) = y)"
proof-
let ?v = "take (length y) (a@b)"
  have "?v = y" by (simp add: assms(1))
  moreover then have "take ( length a) ?v = a" by (metis append_eq_append_conv_if assms(1) assms(2) less_imp_le_nat)
  ultimately have " a @ (drop (length a) ?v)= y" by (metis append_take_drop_id)
  then show ?thesis  by blast
qed

lemma overlaprightexist:assumes "(b@a) = (x@y)" "length y > length a" shows "(\<exists>z.(z@a) = y)"
proof-
let ?v = "drop (length x) (b@a)"
  have "?v = y" by (simp add: assms(1))
  moreover then have "drop (length ?v - length a) ?v = a" using  append_eq_append_conv_if assms(2) by fastforce
  ultimately have "(take (length ?v - length a) ?v) @ a = y" by (metis append_take_drop_id)
  then show ?thesis  by blast
qed

lemma append_cyclicp: assumes "xs = a@b" "ys = b@a" shows "cyclicp xs ys"
proof-
  have "take (length a) xs = a" using assms(1) by simp
  moreover have "drop (length a) xs = b" using assms(1) by simp
  ultimately have "ys = (drop (length a) xs) @ (take (length a) xs)" using assms(2) by simp
  then show ?thesis unfolding cyclicp_def cyclicp_at_i_def cycle_at_i_def by blast
qed

primrec  power :: "('a, 'b) word \<Rightarrow> nat \<Rightarrow> ('a, 'b) word"
  where
"power xs 0 = []"|
"power xs (Suc n) = (xs@(power xs n))"

lemma powerrightappend:assumes "n>0" shows "(power b (n - 1))@b = power b n"
  using assms
proof(induction n)
  case 0
  then show ?case by blast
next
  case (Suc n)
  then show ?case
  proof(cases "0<n")
    case True
    then have "(power b (n - 1))@b = power b n" using Suc.IH  by auto
    then have "b@(power b (n - 1))@b = b@power b n" by simp
  then show ?thesis  by (metis Conjugacy.power.simps(2) Suc_pred True append_assoc diff_Suc_1)
next
  case False
  then have n: "n=0" by simp
  moreover have "(power b 0)@b = power b 1" by simp
  ultimately show ?thesis by simp
qed
qed

lemma divassm: assumes "(a::nat) = (b * n) + k" "a<b" shows "n=0"
  by (metis Euclidean_Division.div_eq_0_iff assms(1) assms(2) div_mult_self4 less_nat_zero_code zero_eq_add_iff_both_eq_0)

(*Show 3.1*)
lemma overlappower:  assumes "(b@a) = (a@c)"  "length a \<ge>  length b" "length a = ((length b) * n) + k   \<and> k<(length b)"shows  "take ((length b) * n) a = power b n"
  using assms
proof( induction n arbitrary: a b c)
  case 0 
  then show ?case by simp
next
  case (Suc n)
  let ?x = "drop (length b) a"
  have ba:"b@?x = a" by (metis Suc.prems(1) Suc.prems(2) append_eq_append_conv_if append_take_drop_id)
  have "length ?x = length b * Suc n + k - (length b)   \<and> k < (length b)" by (simp add: Suc.prems(3))
  then have 1: "length ?x = length b * n + k  \<and>k < (length b)" by simp
  then show ?case
  proof(cases "length ?x < length b")
    case True
    then have 0: "n = 0" using "1" divassm by blast
    have "take (length b) a = b"  by (metis append_eq_conv_conj ba)
    moreover have "power b 1 = b" by simp
    ultimately show ?thesis using 0 by simp
next
  case False
  then have "length ?x \<ge> length b" by simp
  moreover have "b@?x = ?x@c" by (metis Suc.prems(1) Suc.prems(2) append.right_neutral append_eq_append_conv_if)
  ultimately have "take (length b * n) ?x = power b n" using "1" Suc.IH by blast
  then have "b@take (length b * n) ?x = b@power b n" by simp
  then have "take (length b * Suc n) a = b@power b n" using ba by (metis append_eq_conv_conj mult_Suc_right take_add)
  then show ?thesis by simp
qed
qed

definition divmod_nat_rel :: "nat => nat => nat \<times> nat => bool" where
  "divmod_nat_rel m n qr \<longleftrightarrow>
    m = fst qr * n + snd qr \<and>
      (if n = 0 then fst qr = 0  else if n > 0 then 0 \<le> snd qr \<and> snd qr < n \<and> fst qr \<ge> 0 else n < snd qr \<and> snd qr \<le> 0)"

lemma divmod_nat_rel_ex:
  obtains q r where "divmod_nat_rel m n (q, r)"
proof (cases "n = 0")
  case True  with that show thesis
    by (auto simp add: divmod_nat_rel_def)
next
  case False
  have "\<exists>q r. m = q * n + r \<and> r < n"
  proof (induct m)
    case 0 with `n \<noteq> 0`
    have "(0::nat) = 0 * n + 0 \<and> 0 < n" by simp
    then show ?case by blast
  next
    case (Suc m) then obtain q' r'
      where m: "m = q' * n + r'" and n: "r' < n" by auto
    then show ?case proof (cases "Suc r' < n")
      case True
      from m n have "Suc m = q' * n + Suc r'" by simp
      with True show ?thesis by blast
    next
      case False then have "n \<le> Suc r'" by auto
      moreover from n have "Suc r' \<le> n" by auto
      ultimately have "n = Suc r'" by auto
      with m have "Suc m = Suc q' * n + 0" by simp
      with `n \<noteq> 0` show ?thesis by blast
    qed
  qed
  with that show thesis
    using `n \<noteq> 0` by (auto simp add: divmod_nat_rel_def)
qed

lemma unfolddiv: assumes "(a::nat) \<ge>(b::nat)" "b>0" shows "\<exists>n k . a = (b * n)+k  \<and> k<b"
proof-
  obtain n k  where 1:"divmod_nat_rel a b (n, k)" using divmod_nat_rel_ex by blast
  then have "a = (n*b)+k" using divmod_nat_rel_def by simp
  moreover have "0 \<le> k \<and> k < b \<and> 0 \<le> n" using divmod_nat_rel_def assms(2)using "1" by auto
  ultimately show ?thesis by (metis mult.commute)
qed

(*Show 3*)
lemma obtainpoweroverlap: assumes "(b@a) = (a@c)"  "length a \<ge>  length b" "length b>0" shows "\<exists>x n . ((power b n)@x) = a \<and> (length x < length b)"
proof-
 obtain m k where length:  "length a = ((length b) * m) + k \<and> k<(length b)" using unfolddiv assms(2)assms(3) by blast
  then have "take ((length b) * m) a = power b m"using overlappower assms(1) assms(2) by blast
  then have "a = power b m@ drop ((length b) * m) a" by (metis append_take_drop_id)
  moreover have "length (drop ((length b) * m) a) < (length b)" using length by simp 
  ultimately show ?thesis by metis
qed



(*Show 2.2*)
lemma centrelength: assumes "(b@a) = (a@c)"  "length a >  length b"  shows "cyclicp c b"
proof-
  have leq:"length b = length c" by (metis add_left_imp_eq assms(1) length_append length_rotate rotate_append)
  have eq: "(b@a) = (a@c)" using assms(1) by simp
  have length: "length a >  length b" using assms(2) by simp
  then obtain x where bx:"(b@x) = a" using eq overlapleftexist by blast
   have "length a >  length b"  using length by auto
   then have xc: "(x@c) = a"  using bx eq by fastforce
   then show ?thesis
   proof(cases "length x < length c")
     case True
     then obtain y where "y@x = c" by (metis bx overlaprightexist xc)
     moreover then have "x@y = b" using bx xc by auto
     ultimately show ?thesis using append_cyclicp by blast
next
  case False
  then have "length x \<ge> length c" by simp
  then have F1:"length x \<ge> length b" by (simp add: leq)
  have eq2: "b@x = x@c" by (simp add: bx xc)
  then show ?thesis
  proof(cases "length b > 0")
    case True
    then obtain z n where A:"power b n @ z = x \<and> length z < length b" using F1 eq2 obtainpoweroverlap[of "b" "x" "c"] by auto
    then show ?thesis
    proof(cases "n\<le>0")
      case True
      then have "n=0" by simp
      then have xz: "x=z" using A by auto
      then obtain u1 where c:"c = u1@z" using A xc bx False leq by auto
      obtain u2 where "b = z@u2"  using A xc bx False leq   xz by auto
      moreover have "u1 = u2" using xc bx  A False leq xz by auto
      ultimately have "b = z@u1" by simp
      then show ?thesis using c by (simp add: append_cyclicp)
    next
      case False
      then have n: "n>0" by auto
      then have "x = (power b (n - 1))@b@z" using A powerrightappend by (metis append_assoc)
      then have o:"b@(power b (n - 1))@b@z = (power b (n - 1))@b@z@c" using eq2 by auto
      have "b@(power b (n - 1)) = (power b n)" by (metis Conjugacy.power.simps(2) One_nat_def Suc_pred n)
      moreover have "(power b (n - 1))@b = (power b n)" using n powerrightappend by auto
      ultimately have  "(power b n)@b@z = (power b n)@z@c" by (metis append.assoc o)
      then have o2: "b@z = z@c" by simp
      then obtain u1 where c:"c = u1@z" by (metis A leq overlaprightexist)
      obtain u2 where "b = z@u2"   by (metis A o2 overlapleftexist)
      moreover then have "u1 = u2" using c o2 by auto
      ultimately have "b = z@u1" by simp
      then show ?thesis using c by (simp add: append_cyclicp)
qed
  next
    case False
    then have "b=[]" by simp
    moreover then have "c=[]" using leq by simp
    ultimately show ?thesis by (simp add: append_cyclicp)
  qed
qed
qed

lemma cyclicsym: assumes "cyclicp c b" shows "cyclicp b c"
proof-
  obtain i where i: "drop i c @ take i c = b" using assms  unfolding cyclicp_def cyclicp_at_i_def cycle_at_i_def by blast
  then have "take (length(drop i c)) b = drop i c" by (metis append_eq_conv_conj)
  moreover have "drop (length(drop i c)) b = take i c" using i  by (metis append_eq_conv_conj)
  ultimately have "drop (length(drop i c)) b @ take (length(drop i c)) b = c" by simp
  then show ?thesis   unfolding cyclicp_def cyclicp_at_i_def cycle_at_i_def by blast
qed

lemma middleexist: assumes "(a@b) = (c@a)" "length a \<le> length c" shows "\<exists>z . (a@z@a) = (a@b)"
proof-
  obtain z where "c = a@z" using assms by (metis append_Nil2 append_eq_append_conv le_eq_less_or_eq overlapleftexist)
  then show ?thesis  by (simp add: assms(1))
qed

(* Show 2.1*)
lemma middletermcycle:  assumes "(a@b) = (c@a)" shows "cyclicp c b"
proof-
  obtain x y where A:"(y@x@y) = (a@b) \<and> (y@x@y) = (c@a)" using assms middleterm[of "a" "b" "c"] by blast
  then show ?thesis
  proof(cases "length y > length a")
    case True
    then obtain z1 where z1:"a@z1 = y" using A  by (metis append_eq_append_conv2 length_append not_add_less1) 
    moreover obtain z2 where z2: "z2@a = y" using A True  by (metis append.assoc overlaprightexist)
    ultimately have b:"(a@b) = a@z1@x@z2@a" using A by auto
    then have c:"(c@a) = a@z1@x@z2@a" using A by auto
    have "b = (z1@x@z2)@a" using b by auto
    moreover have "c = a@(z1@x@z2)" using c by auto
    ultimately show ?thesis by (simp add: append_cyclicp)
next
  case False
  then obtain z1 where z1:"y@z1 = a" using A overlapleftexist  by (metis append_eq_append_conv append_eq_append_conv2 nat_neq_iff)
  moreover obtain z2 where z2: "z2@y = a" using A False overlaprightexist by (metis (no_types, hide_lams) append_eq_append_conv append_eq_append_conv2 nat_neq_iff)
  have z12:"length z1 = length z2" by (metis diff_add_inverse diff_add_inverse2 length_append z1 z2)
  have bc:"length b = length c"  by (metis assms diff_add_inverse diff_add_inverse2 length_append)
    show ?thesis
  proof(cases "\<exists>z . (a@z@a) = (a@b)")
    case True
    then obtain z where z: "(a@z@a) = (a@b)" by blast
    then have "b = (z@a)" by simp
    moreover have "c = (a@z)" using z assms by simp
    ultimately show ?thesis by (simp add: append_cyclicp)
  next
    case False
    then have "length a > length c" using middleexist  assms not_le by blast
    then show ?thesis using centrelength by (metis assms cyclicsym)
  qed
qed
qed

(*Show 1*)
lemma largestcancel: assumes "reduced (xs)" "reduced (ys)" shows "(\<exists> (a)(b)(c) . (a@b) = xs \<and> ((wordinverse b)@c) = ys \<and> reduced(a@c))"
  using assms
proof(induction xs  rule:reduced.induct)
  case 1
  have "reduced ys" using assms(2) by simp
  then show ?case by simp
next
  case (2 g)
  then show ?case
  proof(cases "ys = []")
    case True
    then show ?thesis by force
  next
    case False
    then show ?thesis
proof(cases "g = inverse (hd ys)")
    case True
    then have 1:"[(hd ys)] = wordinverse [g]" by (simp add: inverse_of_inverse)
    then have 2:"([hd ys] @ (tl ys)) = ys" using False hd_Cons_tl by fastforce
    have "reduced (tl ys)" using assms(2) 2 reduced_leftappend by metis
    then show ?thesis using 1 2 by force
  next
    case False
    then have "reduced ([g] @ ys)" using assms(2) append_reduced by (metis last_ConsL reduced.simps(2))
then show ?thesis using wordinverse.simps(1) by blast
qed
  qed
next
  case (3 g h wrd)
  then have rdh:"reduced (h#wrd)" by (metis reduced.simps(3))
  moreover have gh:"g \<noteq> inverse h" using 3 by auto
  ultimately have "\<exists>a b c. a @ b = h # wrd \<and> wordinverse b @ c = ys \<and> reduced (a @ c)" using assms(2) "3.IH" by blast
  then obtain a b c  where i:" a @ b = h # wrd \<and> wordinverse b @ c = ys \<and> reduced (a @ c)"  by auto
  then have ga:"((g#a)@b) = g#h#wrd" by simp
  then show ?case
  proof(cases "a = []")
    case True
    then have a: "a = []" by simp
    then have gb: "[g] @ b = g#h#wrd" using ga by auto
    then have b:"b = h#wrd"  by simp
    then have ib:"wordinverse b = (wordinverse wrd)@[inverse h]"  by simp 
    have rc :"reduced c" using a i by auto
    then show ?thesis
    proof(cases "c = []")
case True
  then show ?thesis using a i ga by (metis  append_Nil2 ga reduced.simps(2))
next
  case False
  then have c:"c \<noteq> []" by simp
  then have "inverse h \<noteq> inverse (hd c)" using b rdh a  append_notreduced assms(2) i ib reduced_wordinverse  by (metis append.left_neutral snoc_eq_iff_butlast)
  then show ?thesis
  proof(cases "g = inverse (hd c)")
    case True
    have cc:"[(hd c)] @ (tl c) = c" using c by simp
      moreover have "wordinverse (g#h#wrd) = (wordinverse wrd)@[inverse h]@[inverse g]" using True by auto
      ultimately have "wordinverse (g#h#wrd) @ (tl c) = ys" using i cc True ib inverse_of_inverse by (metis append.assoc)
      moreover have "reduced([]@(tl c))" using rc  assms(2) calculation reduced_leftappend by (metis append.left_neutral)
      ultimately show ?thesis  by blast
  next
    case False
    then have "reduced ([g]@c)" using rc  append_reduced by (metis last_ConsL reduced.simps(2))
    then show ?thesis using gb i by blast
  qed
qed
next
  case False
  then have "g \<noteq> inverse (hd a)" using  gh  i  by (metis hd_append2 list.sel(1))
  then have "reduced ([g]@a@c)" using False append_reduced i by (metis  hd_append2 last_ConsL reduced.simps(2))
  then have "reduced ((g#a)@c)" by auto
  then show ?thesis using i ga by blast
qed
qed

lemma wordinverseiterrel: "wordinverse (iter (length a) reduct a) ~ wordinverse a"
proof-
  let ?b = "(iter (length a) reduct a)"
  have 1:"a ~ ?b" by (simp add: cancels_imp_rel iter_cancels_to)
  have a: "(a @wordinverse a) ~ []" by (simp add: wordinverse_inverse)
  have b:"(?b@wordinverse?b) ~ []" by (simp add: wordinverse_inverse)
  have "(?b@wordinverse?b) ~ (a@wordinverse?b)" using 1 mult reln.sym by blast
  then have 1: "(wordinverse a@?b@wordinverse?b) ~ (wordinverse a@a@wordinverse?b)"  by (simp add: mult reln.refl)
  then have "(wordinverse a@?b@wordinverse?b) ~ (wordinverse a)" by (metis append.right_neutral b mult reln.refl)
  moreover have "(wordinverse a@a@wordinverse?b) ~ (wordinverse?b)" using inverse_wordinverse mult by fastforce
  ultimately show ?thesis using 1 reln.sym reln.trans by blast
qed

lemma conj_red: assumes "conj_rel S xs ys" "cyclic_reduced xs" "cyclic_reduced ys" shows "cyclicp xs ys"
proof-
  have uxs: "uncyclic xs" using assms(2) cyclic_reduced_def by auto
  have rxs: "reduced xs" using assms(2) cyclic_reduced_def by auto
  have uys: "uncyclic ys" using assms(3) cyclic_reduced_def by auto
  have rys: "reduced ys" using assms(3) cyclic_reduced_def by auto
  obtain a where 1: "a \<in>  \<llangle>S\<rrangle> \<and> (a @ xs @ (wordinverse a)) ~ ys" using assms(1) unfolding conj_rel_def by auto
  let ?b = "(iter (length a) reduct) a"
  have rb:"reduced ?b" by (simp add: reduced_iter_length)
  have sb:"?b \<in>  \<llangle>S\<rrangle>" using 1 iter_reduct_span by blast
  have "?b ~ a" by (simp add: cancels_imp_rel iter_cancels_to reln.sym)
  moreover have "(wordinverse ?b) ~ wordinverse a" using wordinverseiterrel by (simp add: wordinverseiterrel)
  ultimately have brela: "(?b @ xs @ (wordinverse ?b)) ~ (a @ xs @ (wordinverse a))" by (simp add: mult reln.refl)
  then have A: "(?b @ xs @ (wordinverse ?b)) ~ ys" using 1 using reln.trans by auto
  let ?x = "(?b @ xs @ (wordinverse ?b))"
  have rx:"reduced ((iter (length ?x) reduct) ?x)"  using reduced_iter_length by blast
  have "((iter (length ?x) reduct) ?x) ~ ys" using A using cancels_imp_rel iter_cancels_to reln.sym reln.trans by blast
  then have "cancels_eq ((iter (length ?x) reduct) ?x)  ys" by (simp add: reln_imp_cancels)
  then  have B:"((iter (length ?x) reduct) ?x) = ys" using reduced_cancel_eq rys rx  by auto
  then show ?thesis
  proof(cases "reduced ?x")
  (*reduced b@x@-b*)
    case True
    then have "((iter (length ?x) reduct) ?x) = ?x" by (simp add: reduced_iter_eq)
    then have 1:"?x = ys" using B by auto
    then show ?thesis
    proof(cases "?b = []")
   (*ys = []@xs@-[], cyclicp*)
      case True
      then have "?x = xs" by simp
      then have "xs = ys" using 1 by simp
      then have "cycle_at_i xs 0 = ys" unfolding cycle_at_i_def by auto
  then show ?thesis unfolding cyclicp_def cyclicp_at_i_def by blast
next
  (*ys = b@x@-b, contradiction*)
      case False
      then have F: "?b \<noteq> []" by simp
      then show ?thesis
      proof(cases "length ?b = 1")
        case True
        then obtain ba where "?b = [ba]" using False  by (metis append_Nil le_numeral_extra(4) subtract_greater take_eq_Nil take_last)
        then have "?x = ([ba] @ xs @ [inverse ba])" by simp
        then have "ys = ([ba] @ xs @ [inverse ba])" using 1 by auto
        then have "ys = (ba#(xs @ [inverse ba]))" by simp
        moreover have "ba = inverse (last (xs @ [inverse ba]))" by (simp add: inverse_of_inverse)
        ultimately have False using  uys  uncyclic.simps(3) by (metis neq_Nil_conv snoc_eq_iff_butlast)
then show ?thesis  by simp
next
  case False
  then have ln: "length ?b > 1" using F  using nat_neq_iff by auto
  let ?ba = "hd ?b"
  have contr:"?ba = inverse ( last (wordinverse ?b))" using  ln F  hd_last_wordinverse by simp
  have ys:"ys = (?b @ xs @ wordinverse ?b)" using 1 by simp
  then have hd:"hd ys = ?ba" using F by auto
  moreover have "last ys = last (wordinverse ?b)" using ys F by (metis Nil_is_append_conv last_appendR wordinverse.simps(1) wordinverse_of_wordinverse)
  ultimately have contrr:"hd ys = inverse (last ys)" using contr by simp
  moreover have ls:"last ys = last (hd (tl ys)#(tl(tl ys)))" using hd ys F wordinverse.simps(2)  contrr by (metis Nil_is_append_conv last_ConsL last_tl list.collapse tl_append2)
  ultimately have "hd ys = inverse (last (hd (tl ys)#(tl(tl ys))))" by simp
  moreover then have "ys = (hd ys#hd (tl ys)#(tl(tl ys)))" using ys ln ls hd wordinverse.simps(2) by (metis F Nil_is_append_conv hd_Cons_tl last_ConsL tl_append2)
  ultimately have False using uys uncyclic.simps(3) by metis
  then show ?thesis by simp
qed
qed
next
  case False
(*unreduced b@xs@-b*)
  then have nredx: "\<not> reduced ?x" by blast
  then have red: "(reduced (?b@xs)) \<or> (reduced (xs@(wordinverse ?b)))" using rb assms(2) onesidenotcancel by (simp add: onesidenotcancel)
  then show ?thesis
  proof(cases "xs = []")
(*ys = b@-b = [] = xs*, cyclicp*)
    case True
    then have "?x = ?b @ wordinverse ?b" by simp
    then have "?x ~ []"  by (simp add: wordinverse_inverse)
    then have "(iter (length ?x) reduct) ?x = []" using 1 B True  reduced.simps(1) reduced_cancel_eq reln.sym reln.trans reln_imp_cancels rys wordinverse_inverse by (metis append.left_neutral)
    then have "ys = xs" using B True by auto
    then have "cycle_at_i xs 0 = ys" using cycle_at_i_def by (simp add: cycle_at_i_def)
    then show ?thesis  unfolding cyclicp_def cyclicp_at_i_def by blast
next
  case False
  then have xsnnil:"xs \<noteq> []" by simp
  then have nred:"(\<not> reduced (?b@xs)) \<or> (\<not> reduced (xs@wordinverse?b))" using reduced_wordinverse rb rxs   nredx onesidecancel[of "?b" "xs" "wordinverse ?b"]  by blast
(*cancellation on the left or cancellation on the right*)
  then show ?thesis
  proof(cases "?b = []")
(*xs = ys, cyclicp*)
    case True
    then have "?x = xs" by simp
    then show ?thesis using nredx  rxs by auto
  next
    case False
    then have bnnil: "?b \<noteq> []" by simp
    then have ibnnil: "wordinverse ?b \<noteq> []"  by (metis wordinverse.simps(1) wordinverse_of_wordinverse)
    show ?thesis
    proof(cases "\<not> reduced (?b@xs)")
(*cancellation on the left*)
      case True
      then have "reduced (xs@wordinverse ?b)" using red by auto
(*no cancellation on the right*)
      then have lsxs:"last xs \<noteq> inverse (hd (wordinverse ?b))" using rxs append_notreduced rb reduced_wordinverse False xsnnil by (metis wordinverse.simps(1) wordinverse_symm)
      obtain x y z where ob:"(x@y) = ?b \<and> ((wordinverse y)@z) = xs \<and> reduced(x@z)" using largestcancel[of "?b" "xs"] rxs rb by auto
(*b@xs = (x@y@-y@z), x@z = ys*)
      then have xsb:"?b@xs = (x@y@wordinverse y@z)" by simp
      have "(y@wordinverse y) ~ []" by (simp add: wordinverse_inverse)
      then have "(x@y@wordinverse y) ~ x"  by (metis append_Nil2 mult reln.refl)
      then have "(x@y@wordinverse y@z) ~ (x@z)"  using mult by fastforce
      then have xsbrel:"(?b@xs) ~ (x@z)" using xsb by simp
      then have "((?b@xs)@(wordinverse ?b)) ~ (x@z)@(wordinverse ?b)"using mult by blast
      moreover have "ys ~ (?b@xs)@(wordinverse ?b)"  by (simp add: A reln.sym)
      ultimately have ysrel: "ys ~ (x@z)@(wordinverse ?b)" using reln.trans by blast
      show ?thesis 
      proof(cases "z \<noteq> []")
(*xs is not completely cancelled out*)
        case True
        then have "last z  \<noteq> inverse (hd (wordinverse ?b))" using ob lsxs by auto
        then have "last (x@z) \<noteq> inverse (hd (wordinverse ?b))" using True by simp
        then have "reduced (x@z@(wordinverse ?b))" using ob rb append_reduced[of "(x@z)" "wordinverse ?b"] by (simp add: reduced_wordinverse)
        then have nys:"ys = (x@z@(wordinverse ?b))" using rys ysrel using reduced_cancel_eq reln_imp_cancels by auto
        then show ?thesis
        proof(cases "x\<noteq>[]")
(*xs is not completely cancelled out,b is not completely canceled out, contradiction*)
          case True
          then have "hd ?b = hd x" using bnnil ob by (metis hd_append)
          then have "(hd x) = inverse (last (wordinverse ?b))" using hd_last_wordinverse[of "?b"] bnnil by simp
          then have "(hd ys) = inverse (last ys)" using nys by (simp add: True ibnnil)
          moreover have "length ys > 1" using True ibnnil nys by (metis (no_types, hide_lams) Nil_is_append_conv append_self_conv diff_add_0 hd_append length_0_conv length_append length_tl less_one linorder_neqE_nat list.exhaust_sel)
          ultimately have "\<not> uncyclic ys" using not_uncyclic  by blast
            then show ?thesis using uys by auto
        next
          case False
(*xs is not completely cancelled out,b is completely canceled out, cyclicp*)
          then have "x = []" by simp
          then have "?b = y" using ob  by auto
          then have "wordinverse ?b = wordinverse y"  by simp
          then have "ys = z@(wordinverse y)" using nys using False by auto
          moreover have "xs = (wordinverse y)@z" using ob by simp
          ultimately show ?thesis  by (simp add: append_cyclicp) 
        qed
      next
        case False
(*xs is completely cancelled out*)
        then have znil:"z = []" by simp
        then show ?thesis
        proof(cases "x = []")
(*xs is completely cancelled out, b is completely cancelled out, xs = ys*)
          case True
          then have "ys ~ wordinverse ?b" using ysrel znil  by auto
          then have 1: "ys = wordinverse ?b" using rb reduced_wordinverse[of "?b"]reduced_cancel_eq reln_imp_cancels rys by auto
          have "?b = y" using True ob by simp
          then have "wordinverse ?b = wordinverse y"  by simp
          then have "xs = wordinverse ?b" using ob znil by simp
          then have "xs = ys" using 1 by simp
          then have "cycle_at_i xs 0 = ys" using cycle_at_i_def by (simp add: cycle_at_i_def)
          then show ?thesis  unfolding cyclicp_def cyclicp_at_i_def by blast
        next
          case False
(*xs is completely cancelled out, b is not completely cancelled out, xs *)
          then have xnnil: "x \<noteq> []" by simp
          then have ysxb:"ys ~ x@wordinverse ?b" using znil ysrel by auto
          have xsy:"xs = wordinverse y" using znil ob by auto
          have lxb:"length x < length ?b" by (metis append_Nil2 append_eq_append_conv le_add1 length_append nat_less_le ob wordinverse_append xsnnil znil)
          obtain d e f where ob2:"(d@e) = x \<and> ((wordinverse e)@f) = wordinverse ?b \<and> reduced(d@f)" using largestcancel[of "x" "wordinverse ?b"] rb reduced_wordinverse[of "?b"] ob znil by auto
(*remaining b@-b = d@e@-e@f, ys = d@f*)
          then have fnnil:"f \<noteq> []" using lxb by (metis add_less_same_cancel2 append_Nil2 length_append less_nat_zero_code wordinverse_of_wordinverse)
          have xf:"hd x = inverse (last f)"  by (metis bnnil fnnil hd_append2 hd_last_wordinverse last_appendR length_greater_0_conv ob ob2 xnnil)
          have "(d@e @ (wordinverse e)) ~ d" by (metis append.right_neutral mult reln.refl wordinverse_inverse)
          then have "(d@e @ (wordinverse e)@f) ~ (d@f)"using mult by fastforce
          moreover have "ys ~ (d@e) @ ((wordinverse e)@f)" using ob2 ysxb by simp
          ultimately have "ys ~ (d@f)" using reln.trans by auto
          then have ysdf:"ys = (d@f)" using rys ob2  by (simp add: reduced_cancel_eq reln_imp_cancels)
          show ?thesis
          proof(cases "d\<noteq>[]")
(*ys = some remaining b@some end of -b, contradiction*)
            case True
            have "length d > 0" using True by simp
            moreover have "length f > 0" using fnnil by simp
            ultimately have lys:"length ys > 1" using ysdf by (metis append_eq_append_conv fnnil le_iff_add length_append less_one linorder_neqE_nat self_append_conv verit_comp_simplify1(3))
            have "hd d = hd x" using ob2 True  by force
            then have "hd d = inverse (last f)" using xf by simp
            then have "hd ys = inverse (last ys)" using ysdf True fnnil by auto
            then have "\<not> uncyclic ys"  using lys not_uncyclic by auto
            then show ?thesis using uys by blast
          next
            case False
(*All of the remaining b cancels with -b*)
            then have "?b = (e@y)" using ob ob2  by auto
            then have "wordinverse ?b = (wordinverse y) @ (wordinverse e)"by (simp add: wordinverse_append)
            moreover have "wordinverse ?b = (wordinverse e) @ f" by (simp add: ob2)
            ultimately have "cyclicp (wordinverse y) f " by (metis cyclicsym middletermcycle)
(*xs = -y, ys = f*)
            then show ?thesis using False xsy ysdf by force
          qed
        qed
qed
next
  case False
 then have "reduced (?b@xs)" using red by auto
      then have lsxs:"last ?b \<noteq> inverse (hd (xs))" using rxs append_notreduced rb False xsnnil bnnil by auto
      obtain x y z where ob:"(x@y) = xs \<and> ((wordinverse y)@z) = wordinverse ?b \<and> reduced(x@z)" using largestcancel[of "xs" "wordinverse ?b"] rxs rb reduced_wordinverse by blast
      then have xsb:"xs@wordinverse ?b = (x@y@wordinverse y@z)" by simp
      have "(y@wordinverse y) ~ []" by (simp add: wordinverse_inverse)
      then have "(x@y@wordinverse y) ~ x"  by (metis append_Nil2 mult reln.refl)
      then have "(x@y@wordinverse y@z) ~ (x@z)"  using mult by fastforce
      then have xsbrel:"(xs@wordinverse ?b) ~ (x@z)" using xsb by simp
      then have "((?b@xs@wordinverse ?b)) ~ ?b@(x@z)"using mult by blast
      moreover have "ys ~ (?b@xs@wordinverse ?b)"  by (simp add: A reln.sym)
      ultimately have ysrel: "ys ~ ?b@(x@z)" using reln.trans by blast
      show ?thesis 
proof(cases "x \<noteq> []")
  case True
  then have xnnil: "x\<noteq>[]" by simp
        then have "hd x  \<noteq> inverse (last ?b)" by (metis hd_append2 inverse_of_inverse lsxs ob)
        then have "hd (x@z) \<noteq> inverse (last ?b)" using True by simp
        then have "reduced (?b@x@z)" using ob rb append_reduced[of "?b" "wordinverse (x@z)"] by (metis False True append.assoc onesidecancel reduced_leftappend reduced_rightappend)
        then have nys:"ys = (?b@x@z)" using rys ysrel using reduced_cancel_eq reln_imp_cancels by auto
        then show ?thesis
proof(cases "z\<noteq>[]")
          case True
          then have "last (wordinverse ?b) = last z" using bnnil ob by (metis last_append)
          then have "(hd ?b) = inverse (last z)" by (simp add: bnnil hd_last_wordinverse)
          then have "(hd ys) = inverse (last ys)" by (simp add: True bnnil nys)
          moreover have "length ys > 1" using bnnil True xnnil nys by (metis Nil_is_append_conv cancel_comm_monoid_add_class.diff_cancel length_greater_0_conv length_tl less_irrefl_nat less_one linorder_neqE_nat tl_append2)
          ultimately have "\<not> uncyclic ys" using not_uncyclic  by blast
            then show ?thesis using uys by auto
        next
          case False
          then have "z = []" by simp
          then have "wordinverse ?b = wordinverse y" using ob  by auto
          then have "?b =  y"  by (metis wordinverse_symm)
          then have "ys = y@x" using nys using False by auto
          moreover have "xs = x@y" using ob by simp
          ultimately show ?thesis  by (simp add: append_cyclicp) 
        qed
      next
        case False
        then have znil:"x = []" by simp
        then show ?thesis
        proof(cases "z = []")
          case True
          then have "ys ~ ?b" using ysrel znil  by auto
          then have 1: "ys =  ?b" using rb reduced_cancel_eq reln_imp_cancels rys by auto
          have "wordinverse ?b = wordinverse y" using True ob by simp
          then have "?b = y"   by (metis wordinverse_symm)
          then have "xs =  ?b" using ob znil by simp
          then have "xs = ys" using 1 by simp
          then have "cycle_at_i xs 0 = ys" using cycle_at_i_def by (simp add: cycle_at_i_def)
          then show ?thesis  unfolding cyclicp_def cyclicp_at_i_def by blast
        next
          case False
          then have xnnil: "z \<noteq> []" by simp
          then have ysxb:"ys ~ ?b@z" using znil ysrel by auto
          have xsy:"xs = y" using znil ob by auto
          have lxb:"length x < length ?b" by (simp add: bnnil znil)
          obtain d e f where ob2:"(d@e) = ?b \<and> ((wordinverse e)@f) = z \<and> reduced(d@f)" using largestcancel[of "?b" "z"] rb  ob znil by auto
          then have fnnil:"d \<noteq> []" using lxb by (metis append_self_conv2 length_append length_greater_0_conv less_add_same_cancel1 not_add_less2 ob wordinverse_append wordinverse_of_wordinverse xsnnil xsy)
          have xf:"hd d = inverse (last z)"  by (metis bnnil fnnil hd_append2 hd_last_wordinverse last_appendR length_greater_0_conv ob ob2 xnnil)
          have "(d@e @ (wordinverse e)) ~ d" by (metis append.right_neutral mult reln.refl wordinverse_inverse)
          then have "(d@e @ (wordinverse e)@f) ~ (d@f)"using mult by fastforce
          moreover have "ys ~ (d@e) @ ((wordinverse e)@f)" using ob2 ysxb by simp
          ultimately have "ys ~ (d@f)" using reln.trans by auto
          then have ysdf:"ys = (d@f)" using rys ob2  by (simp add: reduced_cancel_eq reln_imp_cancels)
          show ?thesis
          proof(cases "f\<noteq>[]")
            case True
            have "length f > 0" using True by simp
            moreover have "length d > 0" using fnnil by simp
            ultimately have lys:"length ys > 1" using ysdf by (smt (verit, ccfv_SIG) int_ops(2) length_append of_nat_0_less_iff of_nat_add of_nat_less_imp_less)
            then have "hd d = inverse (last z)" using xf by simp
            then have "hd d = inverse (last f)" using ob2 True by (metis last_appendR)
            then have "hd ys = inverse (last ys)" using ysdf True fnnil by auto
            then have "\<not> uncyclic ys"  using lys not_uncyclic by auto
            then show ?thesis using uys by blast
          next
            case False
            then have "wordinverse ?b = (wordinverse y@wordinverse e)" using ob ob2 by auto
            then have " ?b = e @ y"using wordinverse_append  wordinverse_of_wordinverse  by (metis)
            moreover have " ?b = d@e" by (simp add: ob2)
            ultimately have "cyclicp d y" by (metis middletermcycle) 
            then show ?thesis using False cyclicsym xsy ysdf by auto
          qed
        qed
qed
qed
  qed

qed
qed
qed


(*assuming cyclic_reduced x and y are conjugate, we need to that show x is a cyclic presentation of y

proof-
obtain a: a x -a ~ y
obtain b: wrd = b x -b ~ y, b is reduced
iter wrd = y

case 1(wrd is reduced)

iter wrd = wrd
\<Longrightarrow> wrd = y

cases:
(b is []) \<Longrightarrow> x = y
(otherwise), y = c z -c, contradiction
_______________________________________________________
case 2(wrd is not reduced)

can only cancel on one side (need to prove)

A. b is not longer than x
1. b is completely canceled \<Longrightarrow> cyclip  
2. not completely cancelled \<Longrightarrow> contradiction

B. b is longer than or equal to x
1. x is not completely cancelled \<Longrightarrow> contradiction 
2. x is exactly cancelled \<Longrightarrow> x = y 
3. x is completely cancelled and some of b remains 
a) remaining b doesn't completely  cancel out \<Longrightarrow> contradiction
b) remaining b completely cancels out, cyclicp

Lemmas to be done:
1. can only cancel on one side
2. a. xs~ys then wordinverse xs ~ wordinverse ys
   OR
   b. wordinverse xs ~ wordinverse ("iter" xs)
*)

lemma assumes  "conj_rel S xs ys" shows "cyclicp (cyclic_reduct xs) (cyclic_reduct ys)"
proof-
   have xs: "xs\<in>\<llangle>S\<rrangle>" using assms conj_rel_def by blast
   then have cxs:"conj_rel S xs (cyclic_reduct xs)" by (simp add: conj_cyclicreduct conj_rel_symm)
   have ys: "ys\<in>\<llangle>S\<rrangle>" using assms conj_rel_def by blast
   then have cys:"conj_rel S ys (cyclic_reduct ys)" by (simp add: conj_cyclicreduct conj_rel_symm)
   have "conj_rel S (cyclic_reduct xs) (cyclic_reduct ys)" using assms conj_cyclicreduct conj_rel_trans cys xs by blast
   moreover have "cyclic_reduced (cyclic_reduct xs) \<and> cyclic_reduced (cyclic_reduct ys)" by (simp add: cyclic_reduced_cyclic_reduct)
   ultimately show ?thesis using conj_red by blast
 qed

lemma assumes "xs\<in>\<llangle>S\<rrangle>" "ys\<in>\<llangle>S\<rrangle>"  "cyclicp (cyclic_reduct xs) (cyclic_reduct ys)" shows "conj_rel S xs ys"
proof-
  have cxs:"conj_rel S xs (cyclic_reduct xs)" using assms(1) by (simp add: conj_cyclicreduct conj_rel_symm)
  have cys:"conj_rel S ys (cyclic_reduct ys)" using assms(2) by (simp add: conj_cyclicreduct conj_rel_symm)
  have "conj_rel S (cyclic_reduct xs) (cyclic_reduct ys)" using assms(3) conj_cyclcip conj_rel_def cxs cys by blast
  then show ?thesis using conj_rel_symm conj_rel_trans cxs cys by blast
qed



