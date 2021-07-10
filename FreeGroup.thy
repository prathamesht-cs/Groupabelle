theory FreeGroup
  imports Main
begin

(*Words are formalized as lists*)

inductive_set Words :: "'a set \<Rightarrow> ('a list) set" 
  for S::"'a set"
  where
base: "[] \<in> Words S"|
step: "xs \<in> Words S \<Longrightarrow> x \<in> S \<Longrightarrow> [x]@xs \<in> Words S"

datatype 'a inverted = G 'a | InvG 'a

inductive_set invertedset :: "'a set \<Rightarrow> ('a inverted) set"
for S::"'a set"
where
"x \<in> S \<Longrightarrow> G x \<in> invertedset S"|
"G x \<in> invertedset S \<Longrightarrow> InvG x \<in> invertedset S"

primrec invert :: "('a inverted) \<Rightarrow> ('a inverted)" where
"invert (G x) = InvG x"|
"invert (InvG x) = G x"

(*Function to reduce a word:*)
(*Method 1:*)

function reduce1 :: "('a inverted) list \<Rightarrow> ('a inverted) list" where
"reduce1 [] = []"|
"reduce1 (x#[]) = (x#[])"|
"reduce1 (x#(y#xys)) = (if y = invert x then reduce1 xys else (reduce1 (x#(reduce1 (y#xys)))))"
  by (auto, metis list.exhaust)

(*Method 2:*)

fun singlereduction ::  "('a inverted) list \<Rightarrow> ('a inverted) list" where
"singlereduction [] = []"|
"singlereduction (x#[]) = (x#[])"|
"singlereduction (x#(y#xys)) = (if y = invert x then singlereduction xys else x#(singlereduction (y#xys)))"

fun checkreduced :: "('a inverted) list \<Rightarrow> bool" where
"checkreduced [] = True"|
"checkreduced (x#[]) = True"|
"checkreduced (x#(y#xys)) = (if y = invert x then False else checkreduced (y#xys))"

function reduce2 :: "('a inverted) list \<Rightarrow> ('a inverted) list" where
"reduce2 xs = (if (checkreduced xs) then xs else reduce2 (singlereduction xs))"
  by (auto)

(*Method 3 (defining a set as the set of reduced words)*)
inductive_set ReducedWords :: "('a inverted) set \<Rightarrow> (('a inverted) list) set" 
  for S::"('a inverted) set"
  where
base: "[] \<in> ReducedWords S"|
single: "x \<in> S \<Longrightarrow> [x] \<in> ReducedWords S"|
step: "xs \<in> Words S \<Longrightarrow> x \<in> S \<and> x \<noteq> invert(last xs) \<Longrightarrow> xs@[x] \<in> ReducedWords S"
