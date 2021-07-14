theory Aabid_Iter_Reduce
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

primrec lengthword::"nat \<Rightarrow> 'a set \<Rightarrow> 'a list set"
  where
"lengthword 0 S = {[s] | s. s \<in> S}"
|"lengthword (Suc n) S = \<Union> {setlistcross S xs | xs. xs \<in> (lengthword n S)}"

abbreviation "ngroupword \<equiv> \<lambda> n (S::('a,'b) word set). lengthword n (S \<union> (wordinverse ` S))" 

datatype char = G | H

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

lemma assumes "f x = x"
  shows "iter (n+1) f x = x"
  using assms
proof(induction n)
  case 0
  then show ?case by simp 
next
  case (Suc n)
  then show ?case by simp
qed

(*"iter lemma"*)
lemma assumes "iter (n+1) f x = iter n f x" 
  shows "iter (k+(n+1)) f x = iter (k+n) f x"
  using assms
proof(induction k)
  case 0
  then show ?case 
    by force
next
  case (Suc m)
  have "iter (m + (n + 1)) f x = iter (Suc m + n) f x" by simp
  then show ?case using Suc.IH Suc.prems by auto
qed

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

lemma "length (reduction wrd) \<le> length wrd"
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

lemma assumes "g = inverse h"
  shows "length (reduction (g#h#wrd)) < length (g#h#wrd)"
  using assms
proof(induction "length wrd")
  case 0
  then show ?case by auto
next
  case (Suc x)
  then show ?case
    by (metis decreasing_length length_Cons lessI less_SucI reduction.simps(3))
qed

lemma assumes "length (reduction (wrd)) = length wrd"
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
lemma assumes "reduction wrd = wrd"
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

definition iter_reduce ::  "('a,'b) word \<Rightarrow> ('a,'b) word"
  where "iter_reduce wrd = (iter (length wrd + 1) reduction) wrd"

lemma  "length ((iter (length xs) reduction) xs) \<le> length ((iter (length xs + 1) reduction) xs)"
proof(induction xs rule: reduction.induct)
case 1
then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 g1 g2 wrd)
  then show ?case sorry
qed


lemma "(iter (length xs) reduction) xs = (iter (length xs + 1) reduction) xs"
proof(induction xs rule: reduction.induct)
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
  then show ?thesis sorry
next
  case False
  then show ?thesis sorry
qed
qed

lemma "\<exists>x \<le> length xs . (iter x reduction) xs = (iter (x+1) reduction) xs"
proof(induction xs rule: reduction.induct)
case 1
then show ?case by simp
next
  case (2 x)
  then show ?case by auto
next
  case (3 g1 g2 wrd)
  then show ?case sorry
qed

lemma correctness: "reduced (iter_reduce xs)"
proof-
(*
\<exists>x \<le> length xs . (iter x reduction) xs = (iter x+1 reductio)n xs <-- NEED TO PROVE
\<Rightarrow> (iter (length xs) reduction) xs = (iter (lenght xs + 1) reduction) xs (by iter lemma, already proved)
\<Rightarrow> reduction ((iter (length xs - 1) reduction) xs) =  (iter (length xs + 1) reduction) xs
\<Rightarrow> reduced ((iter (length xs + 1) reduction) xs) (by reduction-reduced lemma, already proved)
\<Rightarrow> reduced (iter_reduce xs)
*)
