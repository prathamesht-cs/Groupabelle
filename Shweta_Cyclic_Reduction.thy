theory Cyclic_Reduction
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

fun cyclic_reduction :: "('a,'b) word \<Rightarrow> ('a, 'b) word"
  where
"cyclic_reduction [] = []"
|"cyclic_reduction [x] = [x]"
|"cyclic_reduction ([x,y]) = (if reduced [x,y] then [x,y] else [])"
|"cyclic_reduction ([x]@xs@[y]) = (if reduced (xs@[y]@[x]) then ([x]@xs@[y]) 
                                   else cyclic_reduction xs)"

(*[-1,-2,3,2,1] \<rightarrow> [-2,3,2,1,-1] \<rightarrow> not reduced \<rightarrow> cyclic_reduction [-2,3,2] \<rightarrow> [3,-2,2] \<rightarrow> nr \<rightarrow> c_r [3] \<rightarrow> [3]*)

fun conj_set :: "('a,'b) groupgentype set  \<Rightarrow> ('a, 'b) word \<Rightarrow> ('a, 'b) word set"
  where
"conj_set S [] = {}"
|"conj_set S [x] = {([s]@[x]@[inverse s]) |s \<in> S}"
|"conj_set S ([x]@xs@[y]) = {([s]@(cyclic_reduction ([x]@xs@[y]))@[inverse s]) |s \<in> S}"

(*fun conj_bool :: "('a,'b) word set\<Rightarrow> ('a, 'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool"
  where
"conj_bool S ([x]@xs@[y]) ([z]@zs@[w]) = (if (\<exists> k \<in> (conj_set S ([x]@xs@[y]))|(k = (cyclic_reduction ([z]@[zs]@[w])))) then True else False)"
*)
