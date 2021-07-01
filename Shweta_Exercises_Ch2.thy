theory Shweta_Exercises
imports Main
begin

(*2.2 :Addition and properties*)

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 n = n" 
| "add (Suc m) n = Suc(add m n)"

lemma add_Assoc: "add (add m n) p = add m (add n p)"
  by (induction m, auto)

lemma add_Zero: "add m 0 = m"
  by (induction m, auto)

lemma add_Suc: "Suc(add m n) = add m (Suc n)"
  by (induction m, auto)

lemma add_Comm: "add m n = add m n"
  by (induction m, simp add: add_Zero, simp add: add_Suc)

primrec double :: "nat \<Rightarrow>  nat" where
  "double 0  = 0"
| "double (Suc m) = Suc (Suc (double m))"

lemma add_double: "double m = add m m"
  by (induction m, auto, simp add: add_Suc)

(*2.3: No. of occurences of element in a list*)

primrec count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count a [] = 0"
| "count a (x#xs) = (if (x=a) then Suc (count a xs) else count a xs)"

lemma length: "count x xs \<le> length xs"
  by (induction xs, auto)

(*2.4*)
primrec snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] a  = (a#[])"
| "snoc (x#xs) a = x#(snoc xs a)"

primrec reverse :: "'a list \<Rightarrow> 'a list" where
 "reverse [] = []"
|"reverse (x#xs) = snoc (reverse xs) x"

primrec app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
 "app [] ys = ys" 
|"app (x#xs) ys = x # (app xs ys)"

lemma app_Assoc: "(xs @  ys) @ zs = xs @ (ys @ zs)" 
  by (induction xs, auto)

lemma append_snoc: "snoc xs x = xs @ [x]"
  by (induction xs, auto)

(*lemma reverse_reverse : "reverse (reverse xs) = xs"
  by (induction xs, auto, simp add:append_snoc)*)

(*2.5:Function sum_upto*)

primrec sum_upto  :: "nat \<Rightarrow> nat" where
 "sum_upto 0 = 0"
|"sum_upto (Suc n) = (n + (sum_upto n)) + 1"

lemma sum_upto_law: "sum_upto n = n * (n + 1) div 2"
  by (induction n, auto)

(*2.6*)
(*Contents  collects all values in a tree in a list,
in any order, without removing duplicates*)

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

primrec contents :: "'a tree \<Rightarrow> 'a list" where
 "contents Tip = []"
|"contents (Node l a r) = a#((contents l) @ (contents r))"

(*sum_tree sums up all values in a tree of natural numbers*)

primrec sum_tree :: "nat tree\<Rightarrow> nat" where
 "sum_tree Tip = 0"
|"sum_tree (Node l a r) = a + (sum_tree l) + (sum_tree r)"

(*sum_list is pre-defined*)

lemma sum_tree_list: "sum_tree t = sum_list (contents t)"
  by (induction t, auto)

(*2.7*)
(*pre and post_order traverse a tree and collect all stored values in the
respective order in a list*)

primrec pre_order :: "'a tree \<Rightarrow> 'a list" where
 "pre_order Tip = []"
|"pre_order (Node l a r) =[a]@((pre_order l)@(pre_order r))"

primrec post_order :: "'a tree \<Rightarrow> 'a list" where
 "post_order Tip = []"
|"post_order (Node l a r) = ((post_order l)@(post_order r))@[a]"

primrec mirror :: "'a tree \<Rightarrow>'a tree" where
 "mirror Tip = Tip" 
|"mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma pre_mirror_post :"pre_order (mirror t) = rev (post_order t)"
  by (induct_tac t, auto) 

(*2.8: intersperse a [x 1 , ..., x n ] = [x 1 , a, x 2 , a, ..., a, x n ]*)

primrec intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
 "intersperse a [] = []"
|"intersperse a (x#xs) = (x#(a#(intersperse a xs)))"

lemma mapintersperse: "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  by (induction xs, auto)

(*2.9:tail-recursive variant of add*)
fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
 "itadd 0 n  = n"
|"itadd (Suc 0) n = Suc n"
|"itadd (Suc m) n = itadd (Suc 0) (itadd m n)"

(*lemma itadd_add: "itadd n m = add n m", not proven*)

(*2.10:tree0 are binary tree skeletons which do not
store any information, nodes counts no of nodes*)

datatype tree0 = Tip' | Node' "tree0" "tree0"

primrec nodes :: "tree0 \<Rightarrow> nat" where
 "nodes Tip' = 1"
|"nodes (Node' l r) = 1 + nodes l + nodes r"

primrec explode :: "nat\<Rightarrow> tree0 \<Rightarrow> tree0" where 
 "explode 0 t = t"
|"explode (Suc n) t = explode n (Node' t t)"

(* equation expressing the size of a tree after exploding it not proven.*)

(*Not excercises*)
primrec pow :: "nat => nat => nat" where
  "pow x 0       = Suc 0"
| "pow x (Suc n) = x * pow x n"

lemma pow_add: "pow x (y + z) = pow x y * pow x z"
  by (induct z, auto)
   
theorem pow_mult: "pow x (m * n) = pow (pow x m) n"
  by (induct n, auto simp add: pow_add)

primrec sum :: "nat list => nat" where
  "sum []     = 0"
| "sum (x#xs) = x + sum xs"

lemma sum_append: "sum (xs @ ys) = sum xs + sum ys"
  by (induct xs, auto)
  
primrec rev :: "'a list \<Rightarrow> 'a list" where
 "rev [] = []" 
|"rev (x # xs) = rev xs @ [x]"

theorem sum_rev: "sum (rev xs) = sum xs"
  by (induct xs,auto simp add: sum_append)

   





