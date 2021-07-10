theory Free_Group
imports Main 
begin

datatype 'a gentype = C 'a | InvG 'a 

primrec inverse :: " 'a gentype \<Rightarrow> 'a gentype"
  where
"inverse (C x) = InvG x"
|"inverse (InvG x) = C x"

primrec ngenset :: "nat \<Rightarrow> ('a gentype) set"
  where
"ngenset 0 = {C 0}"
|"ngenset (Suc n) = (ngenset(n+1)) \<union> {C (n-1)}"

type_synonym 'a word = "('a gentype) list"

inductive_set spanset :: "nat \<Rightarrow> ('a gentype \<Rightarrow> 'a gentype \<Rightarrow> 'a gentype) \<Rightarrow> ('a gentype) set"
  for n :: "nat" and f :: "('a gentype\<Rightarrow> 'a gentype\<Rightarrow> 'a gentype)"
  where
"x \<in> ngenset n \<Longrightarrow> x \<in> spanset n f"
|"x \<in> spanset n f \<Longrightarrow> y \<in> spanset n f \<Longrightarrow> (f x y) \<in> spanset n f"

fun is_inverse :: "'a word \<Rightarrow> bool"
  where
"is_inverse [] = False"
|"is_inverse (x#[]) = False"
|"is_inverse (x#[y]) = (if x = inverse y then True else False)"

fun reduce :: "'a word \<Rightarrow> 'a word"
  where
"reduce [] = []"
|"reduce (x#[]) = (x#[])"
|"reduce (x#(y#xys)) = (if is_inverse (x#[y]) then reduce xys else reduce(x#(reduce(y#xys)))"

fun is_reduced :: "'a word \<Rightarrow> bool"
  where
"is_reduced [] = True"
|"is_reduced (x#[]) = True"
|"is_reduced (x#(y#xys)) = (if is_inverse (x#[y]) then False else is_reduced (y#xys))"

(*lemma spanset_prop:
  assumes "x \<in> spanset n f " 
  shows "(\<exists> ls. length ls = n) "
proof-
  using assms by (solve_direct: List.Ex_list_of_length)
qed 

lemma spanset_prop1:
  assumes "x \<in> spanset n f " 
  shows "\<exists> ls. ls = x"
proof -
  using assms by (solve_direct :  SMT.smt_arith_simplify(45))
qed 

*)


  
 


  

