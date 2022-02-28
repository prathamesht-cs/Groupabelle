theory UniversalProperty
  imports "FreeGroupMainTemp" "CancelResults" "Iter_Reduction_Results"
begin

definition (in group) genmap
  where "genmap f g = (if snd g then f (fst g) else inv (f (fst g)))"

lemma (in group) genmap_closed:
  assumes cl: "f \<in> gens \<rightarrow> carrier G"
      and "fst g \<in> gens"
    shows "genmap f g \<in> carrier G"
proof-
  show ?thesis using assms by (auto simp add:genmap_def)
qed

fun (in group) genmapext
  where "genmapext f [] = \<one>"|
"genmapext f (x#xs) = (genmap f x) \<otimes> (genmapext f xs)"


lemma gen_spanset: assumes "xs \<in> \<llangle>S\<rrangle>" "xs \<noteq> []" shows "hd xs \<in> S"
  using assms
proof(induction xs)
  case empty
  then show ?case by simp
next
  case (gen x xs)
  then show ?case by simp
qed

lemma (in group) genmapext_closed:
  assumes "f \<in> gens \<rightarrow> carrier G"
      and "x \<in> FreeGroupMainTemp.spanset gens"
    shows "genmapext f x \<in> carrier G"
  using assms
proof(induction x)
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  have a:"genmapext f (a # x) = genmap f a \<otimes>  (genmapext f x)" by simp
  have "a \<in> gens \<times> {True, False}"  using FreeGroupMainTemp.spanset_def gen_spanset invgen_def Cons by (metis list.distinct(1) list.sel(1))
  then have "fst a \<in> gens" by force
  then have " genmap f a \<in> carrier G" using genmap_closed Cons.prems(1) by blast
  moreover have "x \<in> \<langle>gens\<rangle>" using Cons FreeGroupMainTemp.spanset_def span_cons by blast
  ultimately show ?case using a by (simp add: Cons.IH assms(1))
qed

lemma (in group) genmapext_append:
  assumes "f \<in> gens \<rightarrow> carrier G"
      and "x \<in> FreeGroupMainTemp.spanset gens"
      and "y \<in> FreeGroupMainTemp.spanset gens"
    shows "genmapext f (x @ y) = genmapext f x \<otimes> genmapext f y"
  using assms
proof(induction x)
  case Nil
  have "genmapext f [] = \<one>" by simp
  moreover have "genmapext f y \<in> carrier G" using genmapext_closed assms by auto
  then have "genmapext f [] \<otimes> genmapext f y = genmapext f y" using r_one by simp
  then show ?case by simp
next
  case (Cons a x)
  have "a \<in> gens \<times> {True, False}" using FreeGroupMainTemp.spanset_def gen_spanset invgen_def Cons by (metis list.distinct(1) list.sel(1))
  then have a:"fst a \<in> gens" by force
  have x:"x \<in> \<langle>gens\<rangle>" using Cons using FreeGroupMainTemp.spanset_def span_cons by blast
  have "genmapext f (a # x) \<otimes> genmapext f y = genmap f a \<otimes> genmapext f x \<otimes> genmapext f y" by simp
  then have 1: "genmapext f (a # x) \<otimes> genmapext f y = genmap f a \<otimes> genmapext f (x @ y)" using Cons x a genmap_closed genmapext_closed by (metis m_assoc)
  have "genmapext f ((a #x) @ y) = genmapext f (a# (x  @ y))" by auto
  then have "genmapext f ((a #x) @ y) = genmap f a \<otimes> genmapext f (x @ y)" by simp
  then show ?case using 1 by auto
qed


lemma cancels_to_1_unfold:
  assumes "cancels_to_1 x y"
  obtains xs1 x1 x2 xs2
  where "x = xs1 @ x1 # x2 # xs2"
    and "y = xs1 @ xs2"
    and "inverse x1 = x2"
proof-
  assume a: "(\<And>xs1 x1 x2 xs2. \<lbrakk>x = xs1 @ x1 # x2 # xs2; y = xs1 @ xs2; inverse x1 =  x2\<rbrakk> \<Longrightarrow> thesis)"
  from assms
  obtain i where "cancels_to_1_at i x y"
    unfolding cancels_to_1_def by auto
  hence "inverse (x ! i) =  (x ! Suc i)"
    and "y = (take i x) @ (drop (Suc (Suc i)) x)"
    and "x = (take i x) @ x ! i # x ! Suc i # (drop (Suc (Suc i)) x)"
    unfolding cancel_at_def and cancels_to_1_at_def by (auto simp add: Cons_nth_drop_Suc)
  with a show thesis by blast
qed

lemma cancels_to_1_preserves:
  assumes "cancels_to_1 x y"
      and "x \<in> FreeGroupMainTemp.spanset gens"
    shows "y \<in> FreeGroupMainTemp.spanset gens"
proof-
  obtain xs1 x1 x2 xs2
  where x:"x = xs1 @ x1 # x2 # xs2"
    and y:"y = xs1 @ xs2"
    using assms cancels_to_1_unfold by metis
  have "xs1 \<in> FreeGroupMainTemp.spanset gens" using x leftappend_span FreeGroupMainTemp.spanset_def assms(2) by blast
  moreover have "xs2 \<in> FreeGroupMainTemp.spanset gens" using x rightappend_span FreeGroupMainTemp.spanset_def assms(2) span_cons by blast
  ultimately show ?thesis using y by (simp add: span_append FreeGroupMainTemp.spanset_def)
qed

lemma cancels_to_preserves:
  assumes "cancels_to x y"
      and "x \<in> FreeGroupMainTemp.spanset gens"
    shows "y \<in> FreeGroupMainTemp.spanset gens"
  using assms unfolding cancels_to_def
proof(induct rule:rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl a b c)
  then show ?case using cancels_to_1_preserves by auto
qed


lemma (in group) inverse_ext:
  assumes  "inverse x1 = x2"
  and "[x1] \<in> FreeGroupMainTemp.spanset gens"
  and "[x2] \<in> FreeGroupMainTemp.spanset gens"
  and "f \<in> gens \<rightarrow> carrier G"
  shows "(genmapext f [x1] \<otimes> genmapext f [x2]) = \<one>"
proof-
  have "genmapext f [x1] = genmap f x1 \<otimes> \<one>" by simp
  have x1:"x1 \<in> gens \<times> {True, False}" using  invgen_def gen_spanset FreeGroupMainTemp.spanset_def assms(2)  by (metis list.distinct(1) list.sel(1))
  then have  "fst x1 \<in> gens" by auto
  then have g1:"genmap f x1 \<in> carrier G" using genmap_closed assms(4) by blast
  moreover have "genmapext f [x1] = genmap f x1 \<otimes> \<one>" by simp
  ultimately have 1:"genmapext f [x1] = genmap f x1" by simp
  have "genmapext f [x2] = genmap f x2 \<otimes> \<one>" by simp
  have "x2 \<in> gens \<times> {True, False}" using  invgen_def gen_spanset FreeGroupMainTemp.spanset_def assms(3)  by (metis list.distinct(1) list.sel(1))
  then have "fst x2 \<in> gens" by auto
  then have g2:"genmap f x2 \<in> carrier G" using genmap_closed assms(4) by blast
  moreover have "genmapext f [x2] = genmap f x2 \<otimes> \<one>" by simp
  ultimately have 2:"genmapext f [x2] = genmap f x2" by simp
  let ?g = "fst x1"
   show ?thesis
  proof (cases "snd x1 = False")
    case True
    have t1:"x1 = (?g, False)" using True by (metis prod.collapse)
    then have t2:"x2 = (?g, True)" using assms(1)  by (metis FreeGroupMain.inverse.simps(2))
    have "genmap f x1 = inv f ?g" using t1 by (metis genmap_def snd_conv)
    moreover have "genmap f x2 = f ?g" using t2 by (simp add: genmap_def)
    ultimately show ?thesis  using 1 2 Units_eq Units_l_inv g1 g2 by presburger
next
  case False
    have t1:"x1 = (?g, True)" using False by (metis prod.collapse)
    then have t2:"x2 = (?g, False)" using assms(1) by (metis FreeGroupMain.inverse.simps(1))
    have "genmap f x1 =  f ?g" using t1 by (metis genmap_def snd_conv)
    moreover have "genmap f x2 = inv f ?g" using t2 by (simp add: genmap_def)
    ultimately show ?thesis  using 1 2 Units_eq Units_r_inv g1 g2 by presburger
  qed
qed


lemma (in group) genmapext_cancels_to:
  assumes "cancels_to x y"
      and "x \<in> FreeGroupMainTemp.spanset gens"
      and "y \<in> FreeGroupMainTemp.spanset gens"
      and  "f \<in> gens \<rightarrow> carrier G"
  shows "genmapext f x = genmapext f y"
using assms
unfolding cancels_to_def
proof(induct rule:rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by auto
  case (rtrancl_into_rtrancl a b c)
obtain c1 x1 x2 c2
      where b: "b = c1 @ x1 # x2 # c2"
      and c: "c = c1 @ c2"
      and i: "inverse x1 = x2"
  using cancels_to_1_unfold rtrancl_into_rtrancl.hyps(3) by blast
  have bin: "b \<in> FreeGroupMainTemp.spanset gens" using cancels_to_preserves  cancels_to_def rtrancl_into_rtrancl.prems(1) rtrancl_into_rtrancl.hyps(1)  by metis
  have c1:"c1 \<in> FreeGroupMainTemp.spanset gens" using b bin  FreeGroupMainTemp.spanset_def leftappend_span by blast
  moreover have fx1:"([x1] @ [x2] @ c2)\<in> FreeGroupMainTemp.spanset gens" using b bin  FreeGroupMainTemp.spanset_def rightappend_span by fastforce
  moreover then have x1:"[x1] \<in> FreeGroupMainTemp.spanset gens" using fx1  FreeGroupMainTemp.spanset_def leftappend_span by blast
  moreover  have fx2: "([x2] @ c2) \<in> FreeGroupMainTemp.spanset gens" using fx1  FreeGroupMainTemp.spanset_def rightappend_span by fastforce
  moreover then have x2:"[x2] \<in> FreeGroupMainTemp.spanset gens" using  FreeGroupMainTemp.spanset_def leftappend_span by blast
  moreover  have c2: "c2 \<in> FreeGroupMainTemp.spanset gens" using fx2  FreeGroupMainTemp.spanset_def rightappend_span by fastforce
  ultimately have 2: "genmapext f (c1 @ [x1] @ [x2] @ c2) = genmapext f c1  \<otimes> (genmapext f [x1] \<otimes> genmapext f [x2]) \<otimes> genmapext f c2" using genmapext_append rtrancl_refl.prems(3) by (smt (z3) genmapext_closed m_assoc m_closed)
  then have "genmapext f (c1 @ [x1] @ [x2] @ c2) = genmapext f c1  \<otimes> \<one> \<otimes> genmapext f c2" using inverse_ext i x1 x2 assms(4) by metis
  then have "genmapext f (c1 @ [x1] @ [x2] @ c2) = genmapext f c1  \<otimes>  genmapext f c2" using c1 c2 assms(4) genmapext_closed by (metis l_cancel_one' one_closed)
  then have "genmapext f (c1 @ [x1] @ [x2] @ c2) = genmapext f (c1@c2)" using genmapext_append c1 c2 assms(4) by metis
  then have "genmapext f b = genmapext f c" using b c by simp
  then show ?case using rtrancl_into_rtrancl by (simp add: bin)
qed
