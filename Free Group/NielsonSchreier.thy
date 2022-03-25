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
"compare r x y = (if x = [] \<or> ((hd x \<noteq> hd y) \<and> (hd x, hd y) \<in> r) 
                     then True else compare r (tl x) (tl y))"

definition compare_set 
  where "compare_set A r = {(x, y). x \<in> \<langle>A\<rangle> \<and> y \<in> \<langle>A\<rangle> \<and> compare r x y }"

lemma refl_compare : 
  assumes "well_order_on (invgen A) r"
  shows "\<forall> x \<in> \<langle>A\<rangle>. compare r x x"
proof
  fix x 
  assume "x \<in> \<langle>A\<rangle>"
  then show "compare r x x" 
  proof (induction x)
    case Nil
    then show ?case by simp
  next
    case (Cons a x)
    have "x \<in> \<langle>A\<rangle>" using Cons.prems span_cons spanset_def by blast
    then have "compare r (tl (a # x)) (tl (a # x))" using compare.simps using Cons.IH \<open>x \<in> \<langle>A\<rangle>\<close> by auto
    then show ?case by simp
  qed
qed

lemma antisym_compare :
  assumes "well_order_on (invgen A) r"
  shows "(\<forall>x y. (length x = length y) \<longrightarrow>(x, y) \<in> compare_set A r \<longrightarrow> (y, x) \<in> compare_set A r \<longrightarrow> x = y)"
  apply (rule allI)+ 
  apply (rule impI)+
proof-
  fix x y
  assume l: "length x = length y" and xy: "(x, y) \<in> compare_set A r" 
                                  and yx: "(y, x) \<in> compare_set A r"
  then show "x = y"
  proof (induct x y rule : compare.induct)
    case (1 r x y)
    then show ?case 
    proof (cases "x = []")
      case True
      have "y = []" using "1.prems"(1) True by auto
      then show ?thesis using True by simp
    next
      case False
      then show ?thesis 
      proof (cases "hd x = hd y")
        case True
        have a: "x \<noteq> []" using False by simp
        then have b: "y \<noteq> []" using 1 by auto
        then have c:" \<not> (x = [] \<or> hd x \<noteq> hd y \<and> (hd x, hd y) \<in> r)" using a by (simp add: True)
        have "length x = length y" using 1 by auto
        then have "length (tl x) = length (tl y)" using a b by fastforce
        then have "(tl x) = (tl y)" using 1 c try
      next
        case False
        then show ?thesis sorry
      qed
    qed
  qed
    
fun lex :: "((('a,'b) groupgentype \<times> ('a,'b) groupgentype)) set \<Rightarrow> ('a, 'b) word \<Rightarrow> ('a, 'b) word \<Rightarrow> bool"
  where
"lex r x y = (if length x < length y then True else compare r x y)"

definition lex_set where "lex_set A r = {(x, y). x \<in> A \<and> y \<in> A \<and> lex r x y}"

fun lex_lift :: "('a,'b) monoidgentype set \<Rightarrow> ((('a,'b) groupgentype \<times> ('a,'b) groupgentype)) set \<Rightarrow> ('a, 'b) word set \<Rightarrow> ('a,'b) word set \<Rightarrow> bool"
  where
"lex_lift S r a b = (lex r (equiv_red S a) (equiv_red S b))"

definition lexlift_set :: "('a,'b) monoidgentype set \<Rightarrow> (('a,'b) word set) set \<Rightarrow> (('a,'b) groupgentype \<times> ('a,'b) groupgentype) set \<Rightarrow> ((('a,'b) word set \<times> ('a,'b) word set)) set"
  where "lexlift_set S A r = {(a,b). a \<in> A \<and> b \<in> A \<and> lex_lift S r a b}"

lemma well_order_words :
  assumes "well_order_on A r"
  shows "well_order_on \<llangle>A\<rrangle> (lex_set \<llangle>A\<rrangle> r)"
  unfolding well_order_on_def
  sorry



