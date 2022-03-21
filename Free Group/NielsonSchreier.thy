theory NielsonSchreier
imports "UniversalProperty"
begin

definition equal_equiv where "equal_equiv S x y = (equiv_red S x = equiv_red S y)"

definition inv_equiv where "inv_equiv S x y = (x = equivinv S y)"

fun nielson_reln :: "('a, 'b) monoidgentype set \<Rightarrow> ('a, 'b) word set \<Rightarrow> ('a, 'b) word set \<Rightarrow> bool"
  where
"nielson_reln S x y = (equal_equiv S x y \<or> inv_equiv S x y)"

definition nielson_set :: "('a, 'b) monoidgentype set \<Rightarrow>(('a,'b) word  \<times> ('a,'b) word) set"
  where
"nielson_set S = {(w,z). \<exists>x y . x \<in> (\<langle>S\<rangle> // (reln_set \<langle>S\<rangle>)) \<and> w = equiv_red S x \<and> y \<in> (\<langle>S\<rangle> // (reln_set \<langle>S\<rangle>)) \<and> z = equiv_red S y \<and> nielson_reln S x y}"

lemma refl_nielson : "\<forall> x. nielson_reln S x x"
  using nielson_reln.simps equal_equiv_def by blast

lemma sym_nielson : "\<forall> x y. nielson_reln S x y \<Longrightarrow> nielson_reln S y x"
  using nielson_reln.simps equal_equiv_def by blast

lemma trans_nielson : "\<forall> x y z. nielson_reln S x y \<Longrightarrow> nielson_reln S y z \<Longrightarrow> nielson_reln S x z"
  using nielson_reln.simps equal_equiv_def by blast

fun compare :: "((('a,'b) groupgentype \<times> ('a,'b) groupgentype)) set \<Rightarrow>('a, 'b) word \<Rightarrow> ('a, 'b) word \<Rightarrow> bool"
  where
"compare r x y = (if x = [] \<or> (hd x, hd y) \<in> r  
                     then True else compare r (tl x) (tl y))"

fun lex :: "((('a,'b) groupgentype \<times> ('a,'b) groupgentype)) set \<Rightarrow> ('a, 'b) word \<Rightarrow> ('a, 'b) word \<Rightarrow> bool"
  where
"lex r x y = (if length x < length y then True else compare r x y)"

definition lex_set where "lex_set A r = {(x, y). x \<in> A \<and> y \<in> A \<and> lex r x y}"

fun lex_lift :: "('a,'b) monoidgentype set \<Rightarrow> ((('a,'b) groupgentype \<times> ('a,'b) groupgentype)) set \<Rightarrow> ('a, 'b) word set \<Rightarrow> ('a,'b) word set \<Rightarrow> bool"
  where
"lex_lift S r a b = (lex r (equiv_red S a) (equiv_red S b ))"

definition lexlift_set :: "('a,'b) monoidgentype set \<Rightarrow> (('a,'b) word set) set \<Rightarrow> (('a,'b) groupgentype \<times> ('a,'b) groupgentype) set \<Rightarrow> ((('a,'b) word set \<times> ('a,'b) word set)) set"
  where "lexlift_set S A r = {(a,b). a \<in> A \<and> b \<in> A \<and> lex_lift S r a b}"

lemma well_order_words :
  assumes "well_order_on A r"
  shows "well_order_on \<llangle>A\<rrangle> (lex_set \<llangle>A\<rrangle> r)"
  unfolding well_order_on_def
sorry



