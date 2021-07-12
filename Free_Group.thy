theory Free_Group
imports Main 
begin

datatype 'a gentype = C 'a | InvG 'a

primrec inverse :: " 'a gentype ⇒ 'a gentype"
  where
"inverse (C x) = InvG x"
|"inverse (InvG x) = C x"

primrec genset :: "('a gentype) list ⇒ ('a gentype) list"
  where
"genset [] = []"
|"genset (x#xs) = (x#[inverse x]) @ (genset xs)"

type_synonym 'a word = "('a gentype) list"

inductive_set spanset :: "('a gentype list) ⇒('a gentype ⇒ 'a gentype ⇒ 'a gentype) ⇒ ('a gentype) list"
  for S :: "('a gentype) list" and f :: "('a gentype⇒ 'a gentype⇒ 'a gentype)" 
  where
"x ∈ genset S ⟹ x ∈ spanset S f"
|"x ∈ spanset S f ⟹ y ∈ spanset S f ⟹ (f x y) ∈ spanset S f"

fun is_inverse :: "'a word ⇒ bool"
  where
"is_inverse [] = False"
|"is_inverse (x#[]) = False"
|"is_inverse (x#[y]) = (if x = inverse y then True else False)"


fun reduce :: "'a word ⇒ 'a word"
  where
"reduce [] = []"
|"reduce (x#[]) = (x#[])"
|"reduce (x#(y#xys)) = (if is_inverse (x#[y]) then reduce xys else x#(reduce(y#xys)))"

fun is_reduced :: "'a word ⇒ bool"
  where
"is_reduced [] = True"
|"is_reduced (x#[]) = True"
|"is_reduced (x#(y#xys)) = (if is_inverse (x#[y]) then False else is_reduced (y#xys))"

(*define reduced:: "'a gentype set" as a spanset S where ∄ x ∈ S. (y = inverse x) ∈ S"
 and prove lemma empty_list_is_reduced and set with one element is reduced.*)

(*lemma spanset_prop:
  assumes "x ∈ spanset n f " 
  shows "(∃ ls. length ls = n) "
proof-
  using assms by (solve_direct: List.Ex_list_of_length)
qed 

lemma spanset_prop1:
  assumes "x ∈ spanset n f " 
  shows "∃ ls. ls = x"
proof -
  using assms by (solve_direct :  SMT.smt_arith_simplify(45))
qed 

*)


  
 


  

