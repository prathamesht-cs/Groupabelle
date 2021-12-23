theory ConjugacyCyclic
imports "FreeGroupMain" "Iter_Reduction_Results"
begin


(*To prove: conj_rel xs ys \<Longleftrightarrow> cyclicp (cyclic_reduct xs) (cyclic_reduct ys)
Lemmas required:
(A. Every word is conjugate to a cyclically reduced word, namely its cyclic reduction.)
1. "cyclic_reduced S (cyclic_reduct xs)" [DONE]
2. "conj_rel S xs (cyclic_reduct xs)" [DONE]

(B. If x and y are two cyclically reduced words that are conjugate, then x is a cyclic presentation of y.)
3. "cyclic_reduced x" "cyclic_reduced y" "conj_rel S x y" \<Rightarrow> "cyclip x y" 

To prove 3:
C. Any two words that are of the same length and are conjugate are cyclic presentations of each other.
D. Any two cyclically reduced words that are conjugate are of the same length.
D'. A word is cyclically reduced if and only if it is of the minimum length in its conjugacy class.
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



lemma assumes "xs \<in>  \<llangle>S\<rrangle>" shows "conj_rel S (cyclic_reduct xs) xs"
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

lemma hd_last_wordinverse: assumes "length xs > 1" shows "hd xs = inverse (last (wordinverse xs))"
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

lemma assumes "reduced xs" shows "reduced (wordinverse xs)"
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


lemma assumes "reduced a" "reduced b" "reduced c" "b\<noteq>[]" "\<not> reduced (a@b@c)" shows "(\<not> reduced (a@b)) \<or> (\<not> reduced (b@c))"
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

(*
lemma assumes "cyclic_reduced xs" "xs \<in> \<llangle>S\<rrangle>" shows "(\<nexists> ys. (conj_rel S ys xs) \<and> (length ys) < length xs)"
proof(rule ccontr)
  have 1:"reduced xs" using assms cyclic_reduced_def by blast
  have 2:"uncyclic xs"  using assms cyclic_reduced_def by blast
  assume "\<not> (\<nexists>ys. conj_rel S ys xs \<and> length ys < length xs)"
  then have "(\<exists>ys. conj_rel S ys xs \<and> length ys < length xs)" by simp
  then obtain y where contr:"conj_rel S y xs \<and> length y < length xs" by auto
  then obtain a where "(a @ y @ wordinverse a) ~ xs" using conj_rel_def by blast
  then show False
  proof(induction a)
    case Nil
    then have "y ~ xs" by simp
    have "length xs \<le> length y" using 1 sledgehammer
  then show ?case sorry
next
  case (Cons a1 a2)
  then show ?case sorry
qed
*)
lemma assumes "conj_rel S xs ys" "cyclic_reduced xs" "cyclic_reduced ys" shows "cyclicp xs ys"
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
  moreover have "(wordinverse ?b) ~ wordinverse a" sorry
  ultimately have brela: "(?b @ xs @ (wordinverse ?b)) ~ (a @ xs @ (wordinverse a))" by (simp add: mult reln.refl)
  then have A: "(?b @ xs @ (wordinverse ?b)) ~ ys" using 1 using reln.trans by auto
  let ?x = "(?b @ xs @ (wordinverse ?b))"
  have rx:"reduced ((iter (length ?x) reduct) ?x)"  using reduced_iter_length by blast
  have "((iter (length ?x) reduct) ?x) ~ ys" using A using cancels_imp_rel iter_cancels_to reln.sym reln.trans by blast
  then have "cancels_eq ((iter (length ?x) reduct) ?x)  ys" by (simp add: reln_imp_cancels)
  then  have B:"((iter (length ?x) reduct) ?x) = ys" using reduced_cancel_eq rys rx  by auto
  then show ?thesis
  proof(cases "reduced ?x")
    case True
    then have "((iter (length ?x) reduct) ?x) = ?x" by (simp add: reduced_iter_eq)
    then have 1:"?x = ys" using B by auto
    then show ?thesis
    proof(cases "?b = []")
      case True
      then have "?x = xs" by simp
      then have "xs = ys" using 1 by simp
      then have "cycle_at_i xs 0 = ys" unfolding cycle_at_i_def by auto
  then show ?thesis unfolding cyclicp_def cyclicp_at_i_def by blast
    next
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
  have contr:"?ba = inverse ( last (wordinverse ?b))" using  ln  hd_last_wordinverse by auto
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

