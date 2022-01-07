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
"Congruent2 r f = (\<forall>(y1, z1) \<in> r. \<forall>(y2, z2) \<in> r. (f y1 y2, f z1 z2)  \<in> r)"

(*
lemma append_congruent: "Congruent2 (reln_set \<llangle>S\<rrangle>) append"
proof-
  assume 1:"(y1, z1) \<in> (reln_set \<llangle>S\<rrangle>)"
  assume 2:"(y2, z2) \<in> (reln_set \<llangle>S\<rrangle>)"
  then have "y1 \<in>  \<llangle>S\<rrangle> \<and> z1 \<in> \<llangle>S\<rrangle>" using 1 reln_set_def by auto
  moreover have "y2 \<in>  \<llangle>S\<rrangle> \<and> z2 \<in> \<llangle>S\<rrangle>" using 2 reln_set_def by auto
  ultimately have A:"(y1@y2) \<in>  \<llangle>S\<rrangle> \<and> (z1@z2) \<in> \<llangle>S\<rrangle>" by (simp add: span_append)
  have "y1 ~ z1" using 1 reln_set_def by auto
  moreover have "y2 ~ z2" using 2 reln_set_def by auto
  ultimately have "(y1@y2) ~ (z1@z2)" using mult by auto
  then have "((y1@y2) , (z1@z2)) \<in> (reln_set \<llangle>S\<rrangle>)" using A reln_set_def by auto
  then have "(\<forall>(y1, z1) \<in> (reln_set \<llangle>S\<rrangle>). \<forall>(y2, z2) \<in> (reln_set \<llangle>S\<rrangle>). ( y1 @y2, z1@ z2)  \<in> (reln_set \<llangle>S\<rrangle>))" using A 1 2 sledgehammer sorry
qed
*)

definition ProjFun2 :: "'a set \<Rightarrow> ('a\<times>'a) set \<Rightarrow> ('a\<Rightarrow>'a \<Rightarrow>'a) \<Rightarrow> ('a set \<Rightarrow> 'a set \<Rightarrow> 'a set) " where
"ProjFun2 A r f =  (\<lambda>p\<in>(A//r). \<lambda>q\<in>(A//r). (\<Union>z\<in>p\<times>q .r `` {f (fst z) (snd z)}))"

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