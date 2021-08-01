theory FreeGroupMain
imports Main 
begin

type_synonym ('a,'b) monoidgentype = "'a \<times> 'b"

type_synonym ('a,'b) groupgentype = "('a,'b) monoidgentype \<times> bool"

type_synonym ('a,'b) word = "(('a,'b) groupgentype) list"

fun inverse::"('a,'b) groupgentype \<Rightarrow> ('a, 'b) groupgentype"
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

(*reduction removes cancellations next to each other*)
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

definition wordeq::"('a,'b) word \<Rightarrow> ('a,'b) word set" ("[[_]]")
  where
"wordeq wrd = {wrds. wrd ~ wrds}"

  
end
