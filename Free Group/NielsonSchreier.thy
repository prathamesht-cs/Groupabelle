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



