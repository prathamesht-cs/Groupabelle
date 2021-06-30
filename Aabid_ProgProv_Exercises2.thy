theory Aabid_ProgProv_Exercises2
imports Main
begin

(*2.1*)
value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

(*2.2*)
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

lemma add_assoc: "add (add a b) c = add a (add b c)"
  by (induction a, auto)

lemma add_zeroright: "add a 0 = a"
  by (induction a, auto)

lemma add_Suceq: "Suc(add a b) = add a (Suc b)"
  by (induction a, auto)

lemma add_comm: "add a b = add b a"
  by (induction a, simp add: add_zeroright, simp add: add_Suceq)

primrec double :: "nat \<Rightarrow>  nat" where
"double 0  = 0"|
"double (Suc n) = Suc (Suc (double n))"

lemma double_add: "double m = add m m"
  by (induction m, auto, simp add: add_Suceq)

(*2.3*)
primrec count :: "int  \<Rightarrow> int list \<Rightarrow> nat" where
"count a [] = 0"|
"count a (y#ys) = (if a = y then (Suc(count a ys)) else (count a ys))"

lemma count_length: "count x xs \<le> length xs"
  by (induction xs, auto)

(*2.4*)
primrec snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] a  = (a#[])"|
"snoc (x#xs) a = x#(snoc xs a)"

primrec reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []"|
"reverse (x#xs) = snoc (reverse xs) x"

lemma app_assoc: "(xs @ ys) @ zs = xs @ (ys @ zs)" 
  by (induction xs, auto)

lemma snoc_app: "snoc xs x = xs @ [x]"
  by (induction xs, auto)

lemma reverse_app_distr: "reverse (xs @ ys) = (reverse ys) @ reverse(xs)"
  by (induction xs, simp add: snoc_app, auto, simp add: snoc_app)

lemma reverse_reverse : "reverse (reverse xs) = xs"
  by (induction xs, auto, simp add: snoc_app, simp add: reverse_app_distr)

(*2.5*)
primrec sum_upto  :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0"|
"sum_upto (Suc n) = (n + (sum_upto n)) + 1"

lemma sum_upto_formula: "sum_upto n = n * (n + 1) div 2"
  by (induction n, auto)

(*2.6*)
datatype 'a tree = Tip | Node "'a tree" 'a " 'a tree"

primrec contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []"|
"contents (Node l a r) = a#((contents l) @ (contents r))"

primrec sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0"|
"sum_tree (Node l a r) = a + (sum_tree l) +  (sum_tree r)"

lemma sumtree_sumlist: "sum_tree t = sum_list (contents t)"
  by (induction t, auto)

(*2.7*)
(* primrec mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l a r ) = Node (mirror r ) a (mirror l)"

primrec pre_order :: "'a tree \<Rightarrow> 'a list" where
"pre_order Tip = []"|
"pre_order (Node l a r) = a#((pre_order l) @ (pre_order r))"

primrec post_order :: "'a tree \<Rightarrow> 'a list" where
"post_order Tip = []"|
"post_order (Node l a r) = ((pre_order l) @ (pre_order r)) @ (a#[])" *)

(*2.8*)
primrec intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a [] = []"|
"intersperse a (x#xs) = (x#(a#(intersperse a xs)))"

lemma map_intersperse: "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  by (induction xs, auto)

(*2.9*)
fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 m  = m"|
"itadd (Suc 0) m = Suc m"|
"itadd (Suc n) m = itadd (Suc 0) (itadd n m)"

lemma itadd_add: "itadd n m = add n m"
  by(induction n m rule: itadd.induct, auto)

(*2.10*)
datatype tree0 = Tip0 | Node0 "tree0" "tree0"

primrec nodes :: "tree0 \<Rightarrow> nat" where
"nodes Tip0 = 1"|
"nodes (Node0 l r) = 1 + nodes l + nodes r"

primrec explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where 
"explode 0 t = t"|
"explode (Suc n) t = explode n (Node0 t t)"

lemma nodes_explode_formula: "nodes (explode n t) = ((2^n) * (nodes t)) + ((2^n) - 1)"
  by(induction n arbitrary: t, auto simp add: algebra_simps)

(*2.11*)
datatype exp = Var | Const int | Add exp exp | Mult exp exp

primrec eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x"|
"eval (Const c) x = c"|
"eval (Add a b) x = (eval a x) + (eval b x)"|
"eval (Mult a b) x = (eval a x) * (eval b x)"

primrec evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] c = 0"|
"evalp (x#xs) c  = x + (c * (evalp xs c))"