theory UniversalProperty
  imports "FreeGroupMain" "CancelResults" "Iter_Reduction_Results"
begin

definition (in group) genmap
  where "genmap S f g = (if g \<in> S then f g else inv (f (wordinverse g)))"

definition freeg :: "_  \<Rightarrow> bool"
  where "freeg G  = ((group G) \<and> (\<exists>X \<subseteq> carrier G . \<forall>group H .(\<forall>f \<in> X \<rightarrow> carrier H . (\<exists>g \<in> hom G H . (\<forall>x \<in> X . f x = g x) \<and> (\<forall>h \<in> hom G H. \<forall>y \<in> carrier G. g y = h y)))))"

definition inclusion ("\<iota>")
  where "\<iota> g = [(g, True)]"

lemma (in group) genmap_closed:
  assumes cl: "f \<in> (\<iota> ` (gens ::('a, 'b) monoidgentype set)) \<rightarrow> carrier G"
      and "g \<in> (\<iota> ` gens) \<union> (wordinverse ` (\<iota> ` gens))"
    shows "genmap (\<iota> ` gens) f g \<in> carrier G"
proof-
  have 1:"g \<in> (\<iota> ` gens) \<or> g \<in> (wordinverse ` (\<iota> ` gens))" using assms(2) by blast
  then show ?thesis
  proof(cases "g \<in> (\<iota> ` gens)")
    case True
    then show ?thesis using assms by (metis Pi_mem genmap_def)
  next
    case False
    then have 2: "g \<in> (wordinverse ` (\<iota> ` gens))" using 1 by simp
    then have "genmap (\<iota> ` gens) f g =  inv (f (wordinverse g))" by (simp add: False genmap_def)
    moreover have "wordinverse g  \<in> (\<iota> ` gens)" by (metis 1 False image_iff wordinverse_symm)
    ultimately show ?thesis using assms by (metis Pi_mem Units_eq Units_inv_Units)
  qed
qed


fun (in group) genmapext
  where "genmapext S f [] = \<one>"|
"genmapext S f (x#xs) = (genmap S f [x]) \<otimes> (genmapext S f xs)"


lemma gen_spanset: assumes "xs \<in> \<llangle>S\<rrangle>" "xs \<noteq> []" shows "hd xs \<in> S"
  using assms
proof(induction xs)
  case empty
  then show ?case by simp
next
  case (gen x xs)
  then show ?case by simp
qed

lemma inclusion_union:
  assumes "a \<in> (gens ::('a, 'b) monoidgentype set) \<times> {True, False}"
  shows "[a] \<in> (\<iota> ` gens) \<union> (wordinverse ` (\<iota> ` gens))"
proof(cases "snd a = True")
  case True
  have "fst a \<in> gens" using assms by auto
  then show ?thesis by (metis (mono_tags, lifting) True UnI1 inclusion_def rev_image_eqI surjective_pairing)
next
  case False
  have 1:"fst a \<in> gens" using assms by auto
  moreover have "snd a = False" using assms False by simp
  ultimately have "inverse a = (fst a, True)" by (metis inverse.simps(2) prod.collapse)
  then have "wordinverse [a] \<in> (\<iota> ` gens)" by (simp add: 1 inclusion_def)
  then show ?thesis  by (metis UnCI imageI wordinverse_of_wordinverse)
qed

lemma (in group) genmapext_closed:
  assumes "f \<in> (\<iota> ` (gens ::('a, 'b) monoidgentype set)) \<rightarrow> carrier G"
      and "x \<in> FreeGroupMain.spanset  gens"
    shows "genmapext (\<iota> ` gens) f x \<in> carrier G"
  using assms
proof(induction x)
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  have a:"genmapext (\<iota> ` gens) f (a # x) = genmap (\<iota> ` gens) f [a] \<otimes>  (genmapext (\<iota> ` gens)  f x)" by simp
  have "a \<in> gens \<times> {True, False}"  using FreeGroupMain.spanset_def gen_spanset invgen_def Cons by (metis list.distinct(1) list.sel(1))
  then have "[a] \<in> (\<iota> ` gens) \<union> (wordinverse ` (\<iota> ` gens))" using inclusion_union  by blast
  then have " genmap (\<iota> ` gens) f [a] \<in> carrier G" using genmap_closed Cons.prems(1) by meson
  moreover have "x \<in> \<langle>gens\<rangle>" using Cons.prems(2) FreeGroupMain.spanset_def span_cons by blast
  ultimately show ?case using a by (simp add: Cons.IH assms(1))
qed

lemma (in group) genmapext_append:
  assumes "f \<in> (\<iota> ` (gens ::('a, 'b) monoidgentype set)) \<rightarrow> carrier G"
      and "x \<in> FreeGroupMain.spanset gens"
      and "y \<in> FreeGroupMain.spanset gens"
    shows "genmapext (\<iota> ` gens)  f (x @ y) = genmapext (\<iota> ` gens) f x \<otimes> genmapext (\<iota> ` gens) f y"
  using assms
proof(induction x)
  case Nil
  have "genmapext (\<iota> ` gens) f [] = \<one>" by simp
  moreover have "genmapext (\<iota> ` gens) f y \<in> carrier G" using genmapext_closed assms by auto
  then have "genmapext (\<iota> ` gens) f [] \<otimes> genmapext (\<iota> ` gens)  f y = genmapext (\<iota> ` gens) f y" using r_one by simp
  then show ?case by simp
next
  case (Cons a x)
  have "a \<in> gens \<times> {True, False}" using FreeGroupMain.spanset_def gen_spanset invgen_def Cons by (metis list.distinct(1) list.sel(1))
  then have a:"[a] \<in> (\<iota> ` gens) \<union> (wordinverse ` (\<iota> ` gens))" using inclusion_union  by blast
  have x:"x \<in> \<langle>gens\<rangle>" using Cons.prems(2) FreeGroupMain.spanset_def span_cons by blast
  have "genmapext (\<iota> ` gens) f (a # x) \<otimes> genmapext (\<iota> ` gens) f y = genmap (\<iota> ` gens) f [a] \<otimes> genmapext (\<iota> ` gens) f x \<otimes> genmapext (\<iota> ` gens) f y" by simp
  then have 1: "genmapext (\<iota> ` gens) f (a # x) \<otimes> genmapext (\<iota> ` gens) f y = genmap (\<iota> ` gens) f [a] \<otimes> genmapext (\<iota> ` gens) f (x @ y)" using Cons.IH Cons.prems(1) Cons.prems(3)  a genmap_closed genmapext_closed m_assoc x by presburger
  have "genmapext  (\<iota> ` gens) f ((a # x) @ y) = genmapext (\<iota> ` gens) f (a # (x  @ y))" by auto
  then have "genmapext (\<iota> ` gens) f ((a #x) @ y) = genmap (\<iota> ` gens) f [a] \<otimes> genmapext (\<iota> ` gens) f (x @ y)" by simp
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
      and "x \<in> FreeGroupMain.spanset gens"
    shows "y \<in> FreeGroupMain.spanset gens"
proof-
  obtain xs1 x1 x2 xs2
  where x:"x = xs1 @ x1 # x2 # xs2"
    and y:"y = xs1 @ xs2"
    using assms cancels_to_1_unfold by metis
  have "xs1 \<in> FreeGroupMain.spanset gens" using x leftappend_span FreeGroupMain.spanset_def assms(2) by blast
  moreover have "xs2 \<in> FreeGroupMain.spanset gens" using x rightappend_span FreeGroupMain.spanset_def assms(2) span_cons by blast
  ultimately show ?thesis using y by (simp add: span_append FreeGroupMain.spanset_def)
qed

lemma cancels_to_preserves:
  assumes "cancels_to x y"
      and "x \<in> FreeGroupMain.spanset gens"
    shows "y \<in> FreeGroupMain.spanset gens"
  using assms unfolding cancels_to_def
proof(induct rule:rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl a b c)
  then show ?case using cancels_to_1_preserves by auto
qed

lemma inclusion_snd:
  assumes "[x] \<in> (\<iota> ` gens)"
  shows "snd x = True"
proof-
  show ?thesis using assms  by (metis image_iff inclusion_def last.simps old.prod.inject prod.collapse)
qed

lemma (in group) inverse_ext:
  assumes  "inverse x1 = x2"
  and "[x1] \<in> FreeGroupMain.spanset (gens ::('a, 'b) monoidgentype set)"
  and "[x2] \<in> FreeGroupMain.spanset gens"
  and "f \<in> (\<iota> ` gens) \<rightarrow> carrier G"
  shows "(genmapext (\<iota> ` gens) f [x1] \<otimes> genmapext (\<iota> ` gens) f [x2]) = \<one>"
proof-
  have "genmapext (\<iota> ` gens) f [x1] = genmap (\<iota> ` gens) f [x1] \<otimes> \<one>" by simp
  have x1:"x1 \<in> gens \<times> {True, False}" using  invgen_def gen_spanset FreeGroupMain.spanset_def assms(2)  by (metis list.distinct(1) list.sel(1))
  then have "[x1] \<in> (\<iota> ` gens) \<union> (wordinverse ` (\<iota> ` gens))" using inclusion_union  by blast
  then have g1:"genmap (\<iota> ` gens) f [x1] \<in> carrier G" using genmap_closed[of "f" "gens" "[x1]"] assms(4) by fast
  moreover have "genmapext (\<iota> ` gens) f [x1] = genmap (\<iota> ` gens) f [x1] \<otimes> \<one>" by simp
  ultimately have 1:"genmapext (\<iota> ` gens) f [x1] = genmap (\<iota> ` gens) f [x1]" by simp
  have "genmapext (\<iota> ` gens) f [x2] = genmap (\<iota> ` gens) f [x2] \<otimes> \<one>" by simp
  have x2:"x2 \<in> gens \<times> {True, False}" using  invgen_def gen_spanset FreeGroupMain.spanset_def assms(3)  by (metis list.distinct(1) list.sel(1))
  then have "[x2] \<in> (\<iota> ` gens) \<union> (wordinverse ` (\<iota> ` gens))" using inclusion_union  by blast
  then have g2:"genmap (\<iota> ` gens) f [x2] \<in> carrier G" using genmap_closed assms(4) by blast
  moreover have "genmapext (\<iota> ` gens) f [x2] = genmap (\<iota> ` gens) f [x2] \<otimes> \<one>" by simp
  ultimately have 2:"genmapext (\<iota> ` gens) f [x2] = genmap (\<iota> ` gens) f [x2]" by simp
  have fx1:"fst x1 \<in> gens" using x1 by auto
  have fx2:"fst x2 \<in> gens" using x2 by auto
  then show ?thesis
  proof (cases "snd x1 = False")
    case True
    then have "snd x2 = True" using assms(1) by (metis inverse.simps(2) snd_eqD surjective_pairing)
    then have "[x2] \<in> (\<iota> ` gens)" using fx2 by (metis inclusion_def rev_image_eqI surjective_pairing)
    then have a:"genmap (\<iota> ` gens) f [x2] = f [x2]" by (simp add: genmap_def)
    have "[x1] \<notin> (\<iota> ` gens)" using inclusion_snd True  by metis
    moreover have "wordinverse [x1] = [x2]" by (simp add: assms(1))
    ultimately have "genmap (\<iota> ` gens) f [x1] = inv (f [x2])" by (simp add: genmap_def)
    then show ?thesis  using 1 2 a  Units_eq Units_l_inv g2 by presburger
next
  case False
    then have T:"snd x1 = True" using assms(1) by (metis inverse.simps(2) snd_eqD surjective_pairing)
    then have "[x1] \<in> (\<iota> ` gens)" using fx1 by (metis inclusion_def rev_image_eqI surjective_pairing)
    then have a:"genmap (\<iota> ` gens) f [x1] = f [x1]" by (simp add: genmap_def)
    have "snd x2 = False" using T assms(1) by (metis eq_snd_iff inverse.simps(1))
    then have "[x2] \<notin> (\<iota> ` gens)" using inclusion_snd  by metis
    moreover have "wordinverse [x2] = [x1]"  by (metis append_self_conv2 assms(1) inverse_of_inverse wordinverse.simps(1) wordinverse.simps(2))
    ultimately have "genmap (\<iota> ` gens) f [x2] = inv (f [x1])" by (simp add: genmap_def)
    then show ?thesis  using 1 2 a Units_eq Units_r_inv g1 by presburger
  qed
qed


lemma (in group) genmapext_cancels_to:
  assumes "cancels_to x y"
      and "x \<in> FreeGroupMain.spanset (gens ::('a, 'b) monoidgentype set)"
      and "y \<in> FreeGroupMain.spanset gens"
      and  "f \<in> (\<iota> ` gens) \<rightarrow> carrier G"
  shows "genmapext (\<iota> ` gens) f x = genmapext (\<iota> ` gens) f y"
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
  have bin: "b \<in> FreeGroupMain.spanset gens" using cancels_to_preserves  cancels_to_def rtrancl_into_rtrancl.prems(1) rtrancl_into_rtrancl.hyps(1)  by metis
  have c1:"c1 \<in> FreeGroupMain.spanset gens" using b bin  FreeGroupMain.spanset_def leftappend_span by blast
  moreover have fx1:"([x1] @ [x2] @ c2)\<in> FreeGroupMain.spanset gens" using b bin  FreeGroupMain.spanset_def rightappend_span by fastforce
  moreover then have x1:"[x1] \<in> FreeGroupMain.spanset gens" using fx1  FreeGroupMain.spanset_def leftappend_span by blast
  moreover  have fx2: "([x2] @ c2) \<in> FreeGroupMain.spanset gens" using fx1  FreeGroupMain.spanset_def rightappend_span by fastforce
  moreover then have x2:"[x2] \<in> FreeGroupMain.spanset gens" using  FreeGroupMain.spanset_def leftappend_span by blast
  moreover  have c2: "c2 \<in> FreeGroupMain.spanset gens" using fx2  FreeGroupMain.spanset_def rightappend_span by fastforce
  ultimately have 2: "genmapext (\<iota> ` gens) f (c1 @ [x1] @ [x2] @ c2) = genmapext (\<iota> ` gens) f c1  \<otimes> (genmapext (\<iota> ` gens) f [x1] \<otimes> genmapext (\<iota> ` gens) f [x2]) \<otimes> genmapext (\<iota> ` gens) f c2" using genmapext_append rtrancl_refl.prems(3) by (smt (z3) genmapext_closed m_assoc m_closed)
  then have "genmapext (\<iota> ` gens) f (c1 @ [x1] @ [x2] @ c2) = genmapext (\<iota> ` gens) f c1  \<otimes> \<one> \<otimes> genmapext (\<iota> ` gens) f c2" using inverse_ext i x1 x2 assms(4) by metis
  then have "genmapext (\<iota> ` gens) f (c1 @ [x1] @ [x2] @ c2) = genmapext (\<iota> ` gens) f c1  \<otimes>  genmapext (\<iota> ` gens) f c2" using c1 c2 assms(4) genmapext_closed by (metis l_cancel_one' one_closed)
  then have "genmapext (\<iota> ` gens) f (c1 @ [x1] @ [x2] @ c2) = genmapext (\<iota> ` gens) f (c1@c2)" using genmapext_append c1 c2 assms(4) by metis
  then have "genmapext (\<iota> ` gens) f b = genmapext (\<iota> ` gens) f c" using b c by simp
  then show ?case using rtrancl_into_rtrancl by (simp add: bin)
qed

lemma (in group) genmapext_reln_set:
  assumes "(x,y) \<in> (reln_set (FreeGroupMain.spanset (gens ::('a, 'b) monoidgentype set)))"
      and "x \<in> FreeGroupMain.spanset gens"
      and "y \<in> FreeGroupMain.spanset gens"
      and  "f \<in> (\<iota> ` gens) \<rightarrow> carrier G"
  shows "genmapext (\<iota> ` gens) f x = genmapext (\<iota> ` gens) f y"
proof-
  let ?rx = "iter (length x) reduct x"
  let ?ry = "iter (length y) reduct y"
  have "cancels_to x ?rx" by (simp add: iter_cancels_to)
  moreover then have "?rx  \<in> FreeGroupMain.spanset gens" using assms cancels_to_preserves by blast
  ultimately have x:"genmapext (\<iota> ` gens) f x = genmapext (\<iota> ` gens) f ?rx"  using genmapext_cancels_to[of "x" "?rx" "gens" "f"] assms(2) assms(4) by auto 
  have  "cancels_to y ?ry" by (simp add: iter_cancels_to)
  moreover then have ryg:"?ry  \<in> FreeGroupMain.spanset gens" using assms cancels_to_preserves by blast
  ultimately have y:"genmapext (\<iota> ` gens) f y = genmapext (\<iota> ` gens) f ?ry"  using genmapext_cancels_to[of "y" "?ry" "gens" "f"] assms(3) assms(4) by auto
  have "FreeGroupMain.reln x y" using assms(1) reln_set_def assms by (metis (no_types, lifting) case_prodD mem_Collect_eq)
  then have "cancels_eq x y" using reln_imp_cancels by blast
  then have "?rx = ?ry" using cancels_imp_iter by blast
  then show ?thesis using x y by simp
qed

(*
  then have 1:"(symclp cancels_to_1)^** x y" using  eq_symp sympstar by metis
  show ?thesis using 1 assms
  proof(induct rule:rtranclp.induct)
case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl a b c)
  then show ?case
    proof(cases "cancels_to b c")
      case True
      then have b:"b \<in> FreeGroupMain.spanset gens" using rtrancl_into_rtrancl.prems(1)  reln_set_def  sledgehammer
      ultimately have "genmapext f c = genmapext f b"  using genmapext_cancels_to rtrancl_into_rtrancl.prems by blast
      moreover have "genmapext f a = genmapext f b" using b  genmapext_cancels_to rtrancl_into_rtrancl by blast
      ultimately show ?thesis by simp 
    next
      case False
      then have "cancels_to c b" using rtrancl_into_rtrancl.hyps(3) cancels_to_1_def by (metis rtrancancel symclp_def)
      moreover then have b:"b \<in> FreeGroupMain.spanset gens" using cancels_to_preserves rtrancl_into_rtrancl.prems(2) by blast
      ultimately have "genmapext f c = genmapext f b"  using genmapext_cancels_to rtrancl_into_rtrancl.prems by blast
      moreover have "genmapext f a = genmapext f b" using b  genmapext_cancels_to rtrancl_into_rtrancl by blast
      ultimately show ?thesis by simp
    qed
next
  case False
  show ?thesis sorry
    qed
qed
qed *)



lemma (in group) congruentlift: assumes "f \<in> (\<iota> ` (S::('a,'b) monoidgentype set)) \<rightarrow> carrier G" shows "congruent (reln_set (FreeGroupMain.spanset S)) (genmapext (\<iota> ` S) f)"
  unfolding congruent_def
proof-
  have "(\<And>x y. (x, y) \<in> (reln_set \<langle>S\<rangle>) \<Longrightarrow> (genmapext (\<iota> ` S) f x) = (genmapext (\<iota> ` S) f y))"
  proof-
    fix x y assume assm: "(x, y) \<in> (reln_set \<langle>S\<rangle>)"
    moreover then have "x \<in> \<langle>S\<rangle>" using reln_set_def by auto
    moreover have "y \<in> \<langle>S\<rangle>" using reln_set_def assm  by auto
    ultimately show "(genmapext (\<iota> ` S) f x) = (genmapext (\<iota> ` S) f y)" using genmapext_reln_set assms by blast
  qed
  then show "\<forall>(y, z)\<in>reln_set \<langle>S\<rangle>. genmapext (\<iota> ` S) f y = genmapext (\<iota> ` S)  f z" by blast
qed

definition (in group) genmapext_proj where "genmapext_proj S f a = (\<Union>x \<in> a. {genmapext S f x})"

lemma (in group) genmapext_proj_wd:
  assumes " A \<in> quotient \<langle>(S::('a,'b) monoidgentype set)\<rangle> (reln_set \<langle>S\<rangle>)" 
          "a \<in> A" 
          "f \<in> (\<iota> ` S) \<rightarrow> carrier G" 
          shows "genmapext_proj (\<iota> ` S) f A = {genmapext (\<iota> ` S) f a}"
proof-
  have "\<forall> x \<in> A . ({genmapext (\<iota> ` S) f x} = {genmapext (\<iota> ` S) f a})"
  proof-
    have "(\<And>x. x \<in> A \<Longrightarrow> ({genmapext (\<iota> ` S) f x} = {genmapext (\<iota> ` S) f a}))"
    proof-
      fix x  assume assm: "x \<in> A"
      then have "(x, a)\<in>reln_set \<langle>S\<rangle>" by (meson assms(1) assms(2) quotient_eq_iff reln_equiv)
      then have "genmapext (\<iota> ` S) f x = genmapext (\<iota> ` S) f a" using assms(3) congruentlift unfolding congruent_def by blast
      then show "{genmapext (\<iota> ` S) f x} = {genmapext (\<iota> ` S) f a}" by simp
    qed
    then show "\<forall> x \<in> A . ({genmapext (\<iota> ` S) f x} = {genmapext (\<iota> ` S) f a})" by simp
  qed
  then show ?thesis unfolding genmapext_proj_def using assms(2) by blast
qed

definition (in group) genmapext_lift where "genmapext_lift S f a = (THE x. x \<in> genmapext_proj S f a)"

lemma (in group) genmapext_lift_wd:
assumes " A \<in> quotient \<langle>(S::('a,'b) monoidgentype set)\<rangle> (reln_set \<langle>S\<rangle>)" 
          "a \<in> A" 
          "f \<in> (\<iota> ` S) \<rightarrow> carrier G" 
        shows "genmapext_lift (\<iota> ` S) f A = genmapext (\<iota> ` S) f a"
  unfolding genmapext_lift_def
proof-
  have "genmapext_proj (\<iota> ` S) f A = {genmapext (\<iota> ` S) f a}" using assms genmapext_proj_wd by blast
  then show "(THE x. x \<in> genmapext_proj (\<iota> ` S) f A) = genmapext (\<iota> ` S) f a"  by simp
qed

lemma (in group) genmapext_lift_hom:
  assumes "f \<in> (\<iota> ` S) \<rightarrow> carrier G"
  shows "genmapext_lift (\<iota> ` S) f \<in> hom (freegroup S) G"
  sorry



