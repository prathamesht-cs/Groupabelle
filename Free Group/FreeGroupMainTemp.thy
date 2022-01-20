theory FreeGroupMainTemp
imports Main "HOL-Algebra.Group"
begin

type_synonym ('a,'b) monoidgentype = "'a \<times> 'b"

type_synonym ('a,'b) groupgentype = "('a,'b) monoidgentype \<times> bool"

type_synonym ('a,'b) word = "(('a,'b) groupgentype) list"

fun inverse::"('a,'b) groupgentype \<Rightarrow> ('a,'b) groupgentype"
  where
"inverse (x, True) = (x, False)"
|"inverse (x, False) = (x, True)"

lemma inverse_of_inverse:
  assumes "g = inverse h"
  shows "h = inverse g"
  using assms inverse.simps 
  by (metis inverse.elims)

primrec wordinverse::"('a,'b) word \<Rightarrow> ('a, 'b) word"
  where
"wordinverse [] = []"
|"wordinverse (x#xs) =  (wordinverse xs)@[inverse x]"

definition invgen ::  "('a,'b) monoidgentype set \<Rightarrow> ('a,'b) groupgentype set"
  where
"invgen S = S \<times> {True,False}"

inductive_set group_spanset::"('a,'b) groupgentype set \<Rightarrow> ('a,'b) word set" ("\<llangle>_\<rrangle>")
  for S::"('a,'b) groupgentype set"
  where
empty:"[] \<in> \<llangle>S\<rrangle>"
|gen:"x \<in> S \<Longrightarrow> xs \<in> \<llangle>S\<rrangle> \<Longrightarrow> (x#xs) \<in> \<llangle>S\<rrangle>"
|invgen: "y \<in> inverse ` S \<Longrightarrow> ys \<in> \<llangle>S\<rrangle> \<Longrightarrow> (y#ys) \<in> \<llangle>S\<rrangle>"

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

definition spanset::"('a,'b) monoidgentype set \<Rightarrow> ('a,'b) word set" ("\<langle>_\<rangle>")
  where
"spanset S = group_spanset (invgen S)"

definition setlistcross::"'a set \<Rightarrow> 'a list \<Rightarrow> 'a list set"
 where
"setlistcross S xs = {[s]@xs | s. s \<in> S}"

value "setlistcross {(1::nat), 2, 3} [(4::nat), 5, 6]"

primrec lengthword::"nat \<Rightarrow> 'a set \<Rightarrow> 'a list set"
  where
"lengthword 0 S = {[s] | s. s \<in> S}"
|"lengthword (Suc n) S = \<Union> {setlistcross S xs | xs. xs \<in> (lengthword n S)}"

abbreviation "ngroupword \<equiv> \<lambda> n (S::('a,'b) word set). lengthword n (S \<union> (wordinverse ` S))" 

fun reduction:: "('a,'b) word \<Rightarrow> ('a,'b) word"
 where
"reduction [] = []"
|"reduction [x] = [x]"
|"reduction (g1#g2#wrd) = (if (g1 = inverse g2) 
                             then reduction wrd 
                             else (g1#(reduction (g2#wrd))))"

fun reduced::"('a,'b) word \<Rightarrow> bool"
  where
"reduced [] = True"
|"reduced [g] = True"
|"reduced (g#h#wrd) = (if (g \<noteq> inverse h) then reduced (h#wrd) else False)"

inductive reln::"('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool" (infixr "~" 65)
  where
refl[intro!]: "a ~ a" |
sym: "a ~ b \<Longrightarrow> b ~ a" |
trans: "a ~ b \<Longrightarrow> b ~ c \<Longrightarrow> a ~ c" |
base: "[g, inverse g] ~ []" |
mult: "xs ~ xs' \<Longrightarrow> ys ~ ys' \<Longrightarrow> (xs@ys) ~ (xs'@ys')"

definition reln_set :: "(('a,'b) word) set \<Rightarrow>(('a,'b) word \<times> ('a,'b) word) set"
  where
"reln_set S = {(x,y).x~y \<and> x \<in> S \<and> y \<in> S}" 


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





lemma reflp_reln: "reflp (reln)"
  unfolding reflp_def by (simp add: reln.refl)

lemma symp_reln: "symp (reln)"
  unfolding symp_def by (simp add: reln.sym)

lemma transp_reln: "transp (reln)"
  unfolding transp_def by (simp add: reln.trans)

quotient_type ('a, 'b) wordclass = "('a, 'b) word"/"reln"
  by(rule equivpI, simp add: reflp_reln, simp add: symp_reln, simp add: transp_reln)

quotient_definition "liftappend :: ('a, 'b) wordclass \<Rightarrow> ('a, 'b) wordclass \<Rightarrow> ('a, 'b) wordclass" 
  is
"append :: ('a, 'b) word  \<Rightarrow> ('a, 'b) word  \<Rightarrow> ('a, 'b) word"
  by (simp add: mult)

quotient_definition "NilLift :: ('a, 'b) wordclass" 
  is
"Nil :: ('a, 'b) word"
  done


definition wordeq::"(('a, 'b) word) set \<Rightarrow>('a,'b) word \<Rightarrow> ('a,'b) word set" ("[[_]]")
  where
"wordeq  S wrd = {wrds. wrd ~ wrds \<and> wrds \<in> S}"

definition lift_append1 :: " (('a,'b) word) set \<Rightarrow> (('a,'b) word) set \<Rightarrow> (('a,'b) word) set \<Rightarrow>(('a, 'b) word) set"
  where
"lift_append1 S a b = {x \<in> Rep_wordclass (liftappend (Abs_wordclass a) (Abs_wordclass b)). x \<in> S}"

definition Congruent2 :: "('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool"
  where
"Congruent2 r f \<longleftrightarrow> (\<forall> y1 z1 y2 z2. (y1, z1) \<in> r \<and> (y2, z2) \<in> r \<longrightarrow> (f y1 y2, f z1 z2)  \<in> r)"


lemma append_congruent: "Congruent2 (reln_set \<langle>S\<rangle>) (@)"
proof-
  have "\<And>y1 z1 y2 z2 .\<lbrakk> (y1, z1) \<in> reln_set \<langle>S\<rangle> ; (y2, z2) \<in> reln_set \<langle>S\<rangle>\<rbrakk> \<Longrightarrow> (y1 @ y2, z1 @ z2) \<in> reln_set \<langle>S\<rangle>"
  proof-
    fix y1 z1 y2 z2 assume 1:"(y1, z1) \<in> (reln_set \<langle>S\<rangle>)" "(y2, z2) \<in> (reln_set \<langle>S\<rangle>)"
  have "y1 \<in>  \<langle>S\<rangle> \<and> z1 \<in> \<langle>S\<rangle>" using 1 reln_set_def by auto
  moreover have "y2 \<in>  \<langle>S\<rangle> \<and> z2 \<in> \<langle>S\<rangle>" using 1 reln_set_def by auto
  ultimately have A:"(y1@y2) \<in>  \<langle>S\<rangle> \<and> (z1@z2) \<in> \<langle>S\<rangle>" unfolding spanset_def by (simp add: span_append)
  have "y1 ~ z1" using 1 reln_set_def by auto
  moreover have "y2 ~ z2" using 1 reln_set_def by auto
  ultimately have "(y1@y2) ~ (z1@z2)" using mult by auto
  then show "((y1@y2) , (z1@z2)) \<in> (reln_set \<langle>S\<rangle>)" using A reln_set_def by auto
qed
  thus ?thesis  using Congruent2_def by blast
qed



definition ProjFun2 :: "'a set \<Rightarrow> ('a\<times>'a) set \<Rightarrow> ('a\<Rightarrow>'a \<Rightarrow>'a) \<Rightarrow> ('a set \<Rightarrow> 'a set \<Rightarrow> 'a set) " where
"ProjFun2 A r f =  (\<lambda>p q. (\<Union>x\<in>(p\<times>q) .r `` {f (fst x) (snd x)}))"

definition lift_append ::  " (('a,'b) word) set \<Rightarrow> (('a,'b) word) set \<Rightarrow> (('a,'b) word) set \<Rightarrow> (('a,'b) word) set"
  where
"lift_append S a b =  (ProjFun2 S (reln_set S) append) a b"


definition freegroup :: "('a,'b) monoidgentype set \<Rightarrow> (('a,'b) word set) monoid"
  where
"freegroup S \<equiv> \<lparr>
     carrier =  quotient \<langle>S\<rangle> (reln_set \<langle>S\<rangle>),
     mult = lift_append \<langle>S\<rangle>,
     one = (reln_set \<langle>S\<rangle>) `` {[]}
  \<rparr>"


lemma reln_refl: "refl_on \<langle>S\<rangle> (reln_set \<langle>S\<rangle>)"
proof-
  have "(\<And>x. x \<in> (reln_set \<langle>S\<rangle>) \<Longrightarrow> x \<in> \<langle>S\<rangle> \<times> \<langle>S\<rangle>)"
  proof-
    fix x assume 1: "x \<in> (reln_set \<langle>S\<rangle>)"
    let ?a = "(fst x)"
    let ?b = "(snd x)"
    have "(?a, ?b) \<in> (reln_set \<langle>S\<rangle>)" by (simp add: "1")
    then have "(?a, ?b) \<in> \<langle>S\<rangle> \<times> \<langle>S\<rangle>" using reln_set_def by (metis (no_types, lifting) Product_Type.Collect_case_prodD SigmaI prod.collapse)
    then show "x \<in> \<langle>S\<rangle> \<times> \<langle>S\<rangle>" by simp
  qed
  then have A:"reln_set \<langle>S\<rangle> \<subseteq> \<langle>S\<rangle> \<times> \<langle>S\<rangle>" by (simp add: subsetI)
  have "(\<And>x. x\<in>\<langle>S\<rangle> \<Longrightarrow> (x, x) \<in> reln_set \<langle>S\<rangle>)"
  proof-
    fix x assume "x\<in>\<langle>S\<rangle>"
    moreover have "x ~ x" by (simp add: reln.refl)
    ultimately show "(x, x) \<in> reln_set \<langle>S\<rangle>" by (simp add: reln_set_def)
  qed
  then have "(\<forall>x\<in>\<langle>S\<rangle>. (x, x) \<in> reln_set \<langle>S\<rangle>)" by simp
  then show ?thesis using A unfolding refl_on_def  by simp
qed

lemma reln_sym: "sym  (reln_set \<langle>S\<rangle>)"
proof-
  have "(\<And>x y. (x, y) \<in> (reln_set \<langle>S\<rangle>) \<Longrightarrow> (y, x) \<in> (reln_set \<langle>S\<rangle>))"
  proof-
    fix x y assume 1:"(x,y)\<in>(reln_set \<langle>S\<rangle>)"
    then have 2:"x ~ y" using reln_set_def 1 by (metis (no_types, lifting) case_prodD mem_Collect_eq)
    then have "y ~ x" by (simp add: 2 reln.sym)
    then show "(y, x) \<in> reln_set \<langle>S\<rangle>" using 1 by (simp add: reln_set_def)
  qed
  then have "(\<forall>x y . (x, y) \<in> (reln_set \<langle>S\<rangle>) \<longrightarrow> (y, x) \<in> (reln_set \<langle>S\<rangle>))" by simp
  then show ?thesis unfolding sym_def  by simp
qed

lemma reln_trans: "trans  (reln_set \<langle>S\<rangle>)"
proof-
  have "(\<And>x y z. (x, y) \<in> (reln_set \<langle>S\<rangle>) \<Longrightarrow> (y, z) \<in> (reln_set \<langle>S\<rangle>) \<Longrightarrow> (x, z) \<in> (reln_set \<langle>S\<rangle>))"
  proof-
    fix x y z assume 1:"(x,y)\<in>(reln_set \<langle>S\<rangle>)" assume 2: "(y, z) \<in> (reln_set \<langle>S\<rangle>)"
    have "x ~ y" using reln_set_def 1 by (metis (no_types, lifting) case_prodD mem_Collect_eq)
    moreover have "y ~ z" using reln_set_def 2 by (metis (no_types, lifting) case_prodD mem_Collect_eq)
    ultimately have "x ~ z" using reln.trans by auto
    then show "(x, z) \<in> reln_set \<langle>S\<rangle>" using 1 2 by (simp add: reln_set_def)
  qed
  then have "(\<forall>x y z. (x, y) \<in> (reln_set \<langle>S\<rangle>) \<longrightarrow> (y, z) \<in> (reln_set \<langle>S\<rangle>) \<longrightarrow> (x, z) \<in> (reln_set \<langle>S\<rangle>))" by simp
  then show ?thesis unfolding trans_def  by simp
qed

lemma reln_equiv: "equiv \<langle>S\<rangle> (reln_set \<langle>S\<rangle>)"
  by (simp add: equivI reln_refl reln_sym reln_trans)

lemma equiv_2f_con: assumes "equiv A r"  "Congruent2 r f" "C1\<in>A//r" "C2\<in>A//r"  "y1\<in>C1"  "z1\<in>C1" "y2 \<in>C2" "z2\<in>C2"
  shows  "r `` {(f y1 y2)} = r `` {(f z1 z2)}"
proof-
  have "(y1, z1) \<in> r" by (meson assms(1) assms(3) assms(5) assms(6) quotient_eq_iff)
  moreover have "(y2, z2) \<in> r" by (meson assms(1) assms(4) assms(7) assms(8) quotient_eq_iff)
  ultimately have "((f y1 y2),(f z1 z2)) \<in> r"  using Congruent2_def assms(2) by fastforce
  then show ?thesis  by (meson assms(1) equiv_class_eq)
qed

lemma equiv_2f_clos: assumes "equiv A r"  "Congruent2 r f" "C1\<in>A//r"  "C2\<in>A//r"  "y1\<in>C1"  "y2\<in>C2"
  shows  "(f y1 y2) \<in> A"
proof-
  have y:"y1 \<in> A" using Union_quotient assms(1) assms(3) assms(5) by auto
  have z:"y2 \<in> A" using Union_quotient assms(1) assms(4) assms(6) by auto
  have yy: "(y1,y1) \<in> r" by (metis assms(1) assms(3) assms(5) quotient_eq_iff)
  have zz:  "(y2,y2) \<in> r" by (metis assms(1) assms(4) assms(6) quotient_eq_iff)
  have "(f y1 y2, f y1 y2) \<in> r" using yy zz using Congruent2_def assms(2) by fastforce
  then show ?thesis by (metis assms(1) equiv_class_eq_iff)
qed



lemma union_eq_2f_in:
  assumes "C1\<times>C2\<noteq>{}"  "\<forall>x\<in>C1\<times>C2. r``{ (b (fst x) (snd x))}\<in>A//r"  "\<forall>x y. x\<in>C1\<times>C2\<and>y\<in>C1\<times>C2\<longrightarrow> r``{(b (fst x) (snd x))}= r``{(b (fst y) (snd y))}" shows  "(\<Union>x\<in>C1\<times>C2. r``{(b (fst x) (snd x))} )\<in>A//r"
proof-
  obtain x where A:"x\<in>C1\<times>C2" using assms(1) by auto
  then have "\<forall>y\<in>C1\<times>C2. r``{(b (fst x) (snd x))}= r``{(b (fst y) (snd y))}" using assms(3) by blast
  then have "(\<Union>y\<in>C1\<times>C2. r``{(b (fst y) (snd y))}) = r``{(b (fst x) (snd x))}"  using assms(1) by blast
    then show ?thesis using A  by (simp add: assms(2))
  qed

lemma proj2fun_clos:assumes "equiv A r"  "Congruent2 r f" "C1\<in>A//r" "C2\<in>A//r"shows "((ProjFun2 A r f) C1 C2) \<in> A//r"
proof-
  have "\<And>z. z\<in>C1\<times>C2 \<Longrightarrow> f (fst z) (snd z)\<in>A" 
  proof-
    fix z assume z: "z\<in>C1\<times>C2"
    show "f (fst z) (snd z) \<in> A" using equiv_2f_clos using assms(1) assms(2) assms(3) assms(4) z by fastforce
  qed
  then have "\<forall>z\<in>C1\<times>C2. f (fst z) (snd z)\<in>A" by simp
  then have "\<forall>z\<in>C1\<times>C2. r``{f (fst z) (snd z)}\<in>A//r" by (simp add: quotientI)
  moreover have "\<forall>z1 z2. z1\<in>C1\<times>C2\<and>z2\<in>C1\<times>C2\<longrightarrow>  r ``{f (fst(z1)) (snd(z1))} = r `` {f (fst(z2)) (snd(z2))}"
  proof-
    have "\<And>z1 z2. z1\<in>C1\<times>C2\<and>z2\<in>C1\<times>C2 \<Longrightarrow>  r ``{f (fst(z1)) (snd(z1))} = r `` {f (fst(z2)) (snd(z2))}"
    proof-
      fix z1 z2 assume 1:"z1\<in>C1\<times>C2\<and>z2\<in>C1\<times>C2"
      have 2:"(fst(z1)) \<in>C1" using 1 by auto
      have 3:"(fst(z2)) \<in>C1" using 1 by auto
      have 4:"(snd(z1)) \<in>C2" using 1 by auto
      have 5:"(snd(z2)) \<in>C2" using 1 by auto
      show " r ``{f (fst(z1)) (snd(z1))} = r `` {f (fst(z2)) (snd(z2))}" using equiv_2f_con[of "A" "r" "f" "C1" "C2" "(fst(z1))" "(fst(z2))" "(snd(z1))" "(snd(z2))"]   1 2 3 4 5  assms(1) assms(2) assms(3) assms(4) by simp
    qed
    then show ?thesis by simp
  qed
  moreover have "C1\<times>C2\<noteq>{}"  using assms(1) assms(3) assms(4) in_quotient_imp_non_empty by auto
  ultimately have "(\<Union>x\<in>C1\<times>C2. r``{(f (fst x) (snd x))} )\<in>A//r" using union_eq_2f_in[of "C1" "C2" "r" "f" "A"] by fastforce
  then show ?thesis unfolding ProjFun2_def by auto
qed

lemma lift_append_clos: assumes "C1\<in> quotient \<langle>S\<rangle> (reln_set \<langle>S\<rangle>)" "C2\<in> quotient \<langle>S\<rangle> (reln_set \<langle>S\<rangle>)"shows "(lift_append \<langle>S\<rangle> C1 C2) \<in>  (quotient \<langle>S\<rangle> (reln_set \<langle>S\<rangle>))"
proof-
  show ?thesis using assms(1) assms(2) reln_equiv[of "S"] append_congruent[of "S"] proj2fun_clos[of "\<langle>S\<rangle>" "(reln_set \<langle>S\<rangle>)" "append" "C1" "C2"] unfolding lift_append_def by fastforce
qed

lemma union_eq_2f_eq: assumes "C1\<times>C2\<noteq>{}"  "\<forall>x\<in>C1\<times>C2. r``{ (b (fst x) (snd x))} = X" shows  "(\<Union>y\<in>C1\<times>C2 .r``{ (b (fst y) (snd y))})=X"
    by (metis (no_types, lifting) SUP_eq_const assms(1) assms(2))

lemma equiv_2f_wd:assumes "equiv A r" "Congruent2 r f"  "x\<in>A"  "y\<in>A"shows "(ProjFun2 A r f) (r``{x}) (r``{y}) = r ``{(f x y)}"
proof-
  have "(r``{x})\<times> (r``{y}) \<noteq> {}"  by (metis Sigma_empty_iff assms(1) assms(3) assms(4) equals0D equiv_class_self)
  moreover have "\<forall>z\<in>r``{x}\<times>r``{y}. r ``{f (fst z) (snd z)}=r ``{f x y}"
  proof-
    have "\<And>z. z \<in> r``{x}\<times>r``{y} \<Longrightarrow> r ``{f (fst z) (snd z)}=r ``{f x y}"
    proof-
      fix z assume 1:"z \<in> r``{x}\<times>r``{y}"
      have "(fst z) \<in> r``{x}" using 1 by auto
      moreover have  "(snd z) \<in> r``{y}" using 1 by auto
      moreover have "r``{x}\<in>A//r" by (simp add: assms(3) quotientI)
      moreover have "r``{y}\<in>A//r" by (simp add: assms(4) quotientI)
      moreover have "x\<in>r``{x}" using assms(1) assms(3) equiv_class_self by force
     moreover have "y \<in>r``{y}" using assms(1) assms(4) equiv_class_self by force
     ultimately show "r ``{f (fst z) (snd z)}=r ``{f x y}" using assms(1) assms(2)  equiv_2f_con[of "A" "r" "f" "r `` {x}" "r `` {y}" "(fst z)" "x" "(snd z)" "y"]   by fastforce
   qed
   then show ?thesis by simp
 qed
  ultimately have "(\<Union>z\<in>r``{x}\<times>r``{y}. r``{(f (fst z) (snd z))} ) = r ``{f x y}" using union_eq_2f_eq by simp
  then show ?thesis unfolding ProjFun2_def by simp
qed

lemma lift_append_wd: assumes "x \<in> \<langle>S\<rangle>" "y \<in> \<langle>S\<rangle>" shows "(lift_append \<langle>S\<rangle> ((reln_set \<langle>S\<rangle>)``{x}) ((reln_set \<langle>S\<rangle>)``{y})) = (reln_set \<langle>S\<rangle>) `` {append x y}"
proof-
  show ?thesis using reln_equiv[of "S"] append_congruent[of "S"] assms equiv_2f_wd[of "\<langle>S\<rangle>" "(reln_set \<langle>S\<rangle>)" "append" "x" "y"] unfolding lift_append_def  by simp
qed

lemma projfun2_assoc:assumes "equiv A r" and "Congruent2 r f" and "\<forall>x \<in> A. \<forall> y \<in> A. \<forall> z \<in> A. f x (f y z) = f (f x y) z" "C1\<in>A//r" "C2\<in>A//r" "C3\<in>A//r" "g=(ProjFun2 A r f)" shows "(g (g C1 C2) C3) = (g C1 (g C2 C3))"
proof-
  obtain x y z where A:"C1=r``{x} \<and> C2=r``{y} \<and>  C3=r``{z} \<and>  x\<in>A \<and>  y\<in>A \<and>  z\<in>A" by (meson assms(4) assms(5) assms(6) quotientE)
  moreover then have B: "(f x y) \<in> A \<and> (f y z)  \<in> A"  using assms(1) assms(2) assms(4) assms(5) assms(6) equiv_2f_clos equiv_class_self by fastforce
  ultimately have "g (g C1 C2) C3 = r``{f (f x y) z}"  by (simp add: assms(1) assms(2) assms(7) equiv_2f_wd)
  moreover have "... = r``{f  x (f y z)}" by (simp add: A assms(3))
  moreover have "... = g  C1 (g C2 C3)" by (simp add: A B assms(1) assms(2) assms(7) equiv_2f_wd)
  ultimately show ?thesis by simp
qed

lemma append_assoc2: "\<forall>x \<in> A. \<forall> y \<in> A. \<forall> z \<in> A. append x (append y z) = append (append x y) z"
  by simp

lemma lift_append_assoc: assumes  "C1\<in>quotient \<langle>S\<rangle> (reln_set \<langle>S\<rangle>)" "C2\<in>quotient \<langle>S\<rangle> (reln_set \<langle>S\<rangle>)" "C3\<in>quotient \<langle>S\<rangle> (reln_set \<langle>S\<rangle>)" shows "(lift_append \<langle>S\<rangle> C1 (lift_append \<langle>S\<rangle> C2 C3)) = (lift_append \<langle>S\<rangle> (lift_append \<langle>S\<rangle> C1 C2) C3)"
proof-
  show ?thesis using assms reln_equiv[of "S"] append_congruent[of "S"] append_assoc2[of "\<langle>S\<rangle>"] projfun2_assoc[of "\<langle>S\<rangle>" "(reln_set \<langle>S\<rangle>)" "append" "C1" "C2" "C3"] unfolding lift_append_def by simp
qed

lemma freegroup_is_group: "group (freegroup S)"
proof
  fix x y
  assume "x \<in> carrier (freegroup S)" hence x: "x \<in>(quotient \<langle>S\<rangle> (reln_set \<langle>S\<rangle>))" by(auto simp add:freegroup_def) 
  assume "y \<in> carrier (freegroup S)" hence y: "y \<in> (quotient \<langle>S\<rangle> (reln_set \<langle>S\<rangle>))" by(auto simp add:freegroup_def)
  from x and y
  have "x \<otimes>\<^bsub>freegroup S\<^esub> y \<in> (quotient \<langle>S\<rangle> (reln_set \<langle>S\<rangle>))" by (simp add: freegroup_def lift_append_clos)
  thus "x \<otimes>\<^bsub>freegroup S\<^esub> y \<in> carrier (freegroup S)"
    by (auto simp add:freegroup_def)
next
  fix x y z assume x:"x \<in> carrier (freegroup S)" assume y: "y \<in> carrier (freegroup S)" assume z: "z \<in> carrier (freegroup S)"
  from x and y and z
  show  "x \<otimes>\<^bsub>freegroup S\<^esub> y \<otimes>\<^bsub>freegroup S\<^esub> z = x \<otimes>\<^bsub>freegroup S\<^esub> (y \<otimes>\<^bsub>freegroup S\<^esub> z)" by (simp add: freegroup_def lift_append_assoc)
next
  have "[] \<in> \<langle>S\<rangle>" unfolding spanset_def using empty by auto
  then have "(reln_set \<langle>S\<rangle>) `` {[]} \<in> quotient \<langle>S\<rangle> (reln_set \<langle>S\<rangle>)" by (simp add: quotientI)
  then show "\<one>\<^bsub>freegroup S\<^esub> \<in> carrier (freegroup S)"  by (auto simp add:freegroup_def)
next
  fix x assume "x \<in> carrier (freegroup S)"
  moreover then obtain x1 where x:"(reln_set \<langle>S\<rangle>)``{x1} = x" by (metis freegroup_def partial_object.select_convs(1) quotientE)
  ultimately have "x1 \<in> \<langle>S\<rangle>"   by (metis freegroup_def partial_object.select_convs(1) proj_def proj_in_iff reln_equiv)
  moreover have "[] \<in> \<langle>S\<rangle>" using empty spanset_def by auto
  ultimately have "lift_append \<langle>S\<rangle> ((reln_set \<langle>S\<rangle>) `` {[]}) ((reln_set \<langle>S\<rangle>)``{x1}) = ((reln_set \<langle>S\<rangle>)``{x1})" by (simp add: lift_append_wd)
  then show "\<one>\<^bsub>freegroup S\<^esub> \<otimes>\<^bsub>freegroup S\<^esub> x = x" using x by (simp add: freegroup_def)
next
 fix x assume "x \<in> carrier (freegroup S)"
  moreover then obtain x1 where x:"(reln_set \<langle>S\<rangle>)``{x1} = x" by (metis freegroup_def partial_object.select_convs(1) quotientE)
  ultimately have "x1 \<in> \<langle>S\<rangle>"   by (metis freegroup_def partial_object.select_convs(1) proj_def proj_in_iff reln_equiv)
  moreover have "[] \<in> \<langle>S\<rangle>" using empty spanset_def by auto
  ultimately have "lift_append \<langle>S\<rangle>  ((reln_set \<langle>S\<rangle>)``{x1}) ((reln_set \<langle>S\<rangle>) `` {[]}) = ((reln_set \<langle>S\<rangle>)``{x1})" by (simp add: lift_append_wd)
  then show "x \<otimes>\<^bsub>freegroup S\<^esub> \<one>\<^bsub>freegroup S\<^esub> = x" using x by (simp add: freegroup_def)
next
  show "carrier (freegroup S) \<subseteq> Units (freegroup S)"
  proof (simp add:freegroup_def Units_def, rule subsetI)
    fix x assume 1:"x \<in> \<langle>S\<rangle> // reln_set \<langle>S\<rangle>"
    moreover then obtain x1 where x:"(reln_set \<langle>S\<rangle>)``{x1} = x" by (metis quotientE)
    ultimately have x1:"x1 \<in> \<langle>S\<rangle>"  by (metis  proj_def proj_in_iff reln_equiv)
    then have ix1:"wordinverse x1 \<in> \<langle>S\<rangle>" by (simp add: span_wordinverse spanset_def)
    then have 2:"(reln_set \<langle>S\<rangle>)``{wordinverse x1} \<in> \<langle>S\<rangle> // reln_set \<langle>S\<rangle>" by (simp add: quotientI)
    have nil: "[] \<in> \<langle>S\<rangle>" using empty spanset_def by auto
    have "lift_append \<langle>S\<rangle> ((reln_set \<langle>S\<rangle>)``{x1}) ((reln_set \<langle>S\<rangle>)``{wordinverse x1}) = reln_set \<langle>S\<rangle> `` {x1@(wordinverse x1)}"  by (simp add: ix1 lift_append_wd x1)
    moreover have "x1@(wordinverse x1) \<in> \<langle>S\<rangle>" using ix1 span_append spanset_def x1 by blast
    moreover then have "((x1@(wordinverse x1)), []) \<in> reln_set \<langle>S\<rangle>" using nil wordinverse_inverse reln_set_def by auto
    moreover then have "reln_set \<langle>S\<rangle> `` {x1@(wordinverse x1)} = reln_set \<langle>S\<rangle> `` {[]}" by (metis equiv_class_eq reln_equiv)
    ultimately have 3:"lift_append \<langle>S\<rangle> ((reln_set \<langle>S\<rangle>)``{x1}) ((reln_set \<langle>S\<rangle>)``{wordinverse x1}) = reln_set \<langle>S\<rangle> `` {[]}" by simp
    have "lift_append \<langle>S\<rangle>  ((reln_set \<langle>S\<rangle>)``{wordinverse x1}) ((reln_set \<langle>S\<rangle>)``{x1}) = reln_set \<langle>S\<rangle> `` {(wordinverse x1)@x1}"  by (simp add: ix1 lift_append_wd x1)
    moreover have "(wordinverse x1)@x1 \<in> \<langle>S\<rangle>" using ix1 span_append spanset_def x1 by blast
    moreover then have "(((wordinverse x1)@x1), []) \<in> reln_set \<langle>S\<rangle>" using nil inverse_wordinverse reln_set_def by auto
    moreover then have "reln_set \<langle>S\<rangle> `` {(wordinverse x1)@x1} = reln_set \<langle>S\<rangle> `` {[]}" by (metis equiv_class_eq reln_equiv)
    ultimately have 4:"lift_append \<langle>S\<rangle> ((reln_set \<langle>S\<rangle>)``{wordinverse x1}) ((reln_set \<langle>S\<rangle>)``{x1}) = reln_set \<langle>S\<rangle> `` {[]}" by simp
    show "x \<in> {y \<in> \<langle>S\<rangle> // reln_set \<langle>S\<rangle>.\<exists>x\<in>\<langle>S\<rangle> // reln_set \<langle>S\<rangle>.lift_append \<langle>S\<rangle> x y = reln_set \<langle>S\<rangle> `` {[]} \<and> lift_append \<langle>S\<rangle> y x = reln_set \<langle>S\<rangle> `` {[]}}"  using 1 2 3 4 x by auto
  qed
qed


(*
lemma quotient_in_carrier: 
  assumes "x \<in> carrier (freegroup S)"
  shows "x \<in> quotient \<langle>S\<rangle> reln_set"
proof-
  have "carrier (freegroup S) =  quotient \<langle>S\<rangle> reln_set"  by (simp add: freegroup_def)
  moreover have "x \<in>  carrier (freegroup S)" using assms by simp
  ultimately show ?thesis  by auto
qed

*)

  
end