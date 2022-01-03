theory Aabid_Relation
imports Main
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


inductive_set spanset::"('a,'b) word set\<Rightarrow> ('a,'b) word set"
  for S::"('a,'b) word set"
  where
"x \<in> S \<Longrightarrow> x \<in> spanset S"
|"x \<in> inver ` S \<Longrightarrow> x \<in> spanset S"
|"x \<in> S \<Longrightarrow> y \<in> spanset S \<Longrightarrow> x@y \<in> spanset S"
|"x \<in> inver ` S \<Longrightarrow> ys \<in> spanset S \<Longrightarrow> x@y \<in> spanset S"

definition setlistcross::"'a set \<Rightarrow> 'a list \<Rightarrow> 'a list set"
 where
"setlistcross S xs = {[s]@xs | s. s \<in> S}"

value "setlistcross {(1::nat), 2, 3} [(4::nat), 5, 6]"

primrec lengthword::"nat \<Rightarrow> 'a set \<Rightarrow> 'a list set"
  where
"lengthword 0 S = {[s] | s. s \<in> S}"
|"lengthword (Suc n) S = \<Union> {setlistcross S xs | xs. xs \<in> (lengthword n S)}"


abbreviation "ngroupword \<equiv> \<lambda> n (S::('a,'b) word set). lengthword n (S \<union> (wordinverse ` S))" 

inductive redrel :: "('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool" where
refl: "redrel a a"|
cancel: "redrel [x, inverse x] []"|
symm: "redrel a b \<Longrightarrow> redrel b a"|
welldefined: "redrel a b \<Longrightarrow> redrel c d \<Longrightarrow> redrel (a@c) (b@d)"|
trans: "redrel a b \<Longrightarrow> redrel b c \<Longrightarrow> redrel a c"

lemma reflp_redrel: "reflp (redrel)"
  unfolding reflp_def by (simp add: redrel.refl)

lemma symp_redrel: "symp (redrel)"
  unfolding symp_def by (simp add: redrel.symm)

lemma transp_redrel: "transp (redrel)"
  unfolding transp_def by (simp add: redrel.trans)

quotient_type ('a, 'b) wordclass = "('a, 'b) word"/"redrel"
  by(rule equivpI, simp add: reflp_redrel, simp add: symp_redrel, simp add: transp_redrel)

quotient_definition "f :: ('a, 'b) wordclass \<Rightarrow> ('a, 'b) wordclass \<Rightarrow> ('a, 'b) wordclass" 
  is
"append :: ('a, 'b) word  \<Rightarrow> ('a, 'b) word  \<Rightarrow> ('a, 'b) word"
  by (simp add: welldefined)

quotient_definition "NilLift :: ('a, 'b) wordclass" 
  is
"Nil :: ('a, 'b) word"
  done

class semigroup =
  fixes S :: "'a set"
  and mult :: "'a \<Rightarrow> 'a  \<Rightarrow> 'a" (infixl "\<otimes>" 70)
  assumes assoc: "(x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"

class monoidl = semigroup +
  fixes neutral :: 'a ("e")
  assumes neutl: "e \<otimes> x = x"

class monoid = monoidl +
  assumes neutr: "x \<otimes> e = x"

class group = monoid +
fixes inverse ::"'a \<Rightarrow> 'a" ("inv")
assumes invl: "(inv x) \<otimes> x = e"

(*interpretation a: semigroup "?" "f"*)