theory UP
imports UniversalProperty Homomorphism_Eq
begin    

lemma 
  assumes "h \<in> A \<rightarrow> B"
  shows "\<exists>h1. \<forall>x \<in> A. h1 x = h x"
  using assms by blast


fun hom_ext::"(_ \<Rightarrow> _) \<Rightarrow> ('c, 'd) monoid_scheme
        \<Rightarrow> ('a,'b) monoidgentype list \<Rightarrow> 'c"
  where
"hom_ext h G [] = \<one>\<^bsub>G\<^esub> "
|"hom_ext h G (x#xs) = (h x) \<otimes>\<^bsub>G\<^esub> (hom_ext h G xs)"


lemma "carrier (freegroup S) = \<langle>liftgen S\<rangle>\<^bsub>(freegroup S)\<^esub>"
  by (meson freegroup_is_group group.liftgen_span group.span_liftgen subset_antisym)



theorem (in group) exists_hom:
  assumes "group G"
      and "f  \<in>  (S::('c,'d) monoidgentype set) \<rightarrow> carrier G"
    shows "\<exists>h \<in> hom (freegroup S) G. \<forall> x \<in> S. f x = h (reln_tuple \<langle>S\<rangle> `` {\<iota>  x})"
proof-
  have "inj_on \<iota> S" unfolding inclusion_def 
    by (meson Pair_inject inj_onI list.inject)
  hence bij_step:"bij_betw \<iota> S (\<iota> ` S)" unfolding inclusion_def 
    by (meson \<open>inj_on \<iota> S\<close> bij_betw_imageI inclusion_def inj_on_cong)
  then have inv:"\<forall>x \<in>  S. (the_inv_into S \<iota>) (\<iota> x) = x" unfolding the_inv_into_def bij_betw_def
       inj_on_def by auto
  define f' where "f' = f \<circ> (the_inv_into S \<iota>)" 
  have "f' \<in> (\<iota> ` S) \<rightarrow> carrier G" using bij_step inv unfolding f'_def using assms(2) by force
  then have step1:"genmapext_lift (\<iota> ` S) f' \<in> hom (freegroup S) G" using genmapext_lift_hom
    by (simp add: \<open>\<And>f S. f \<in> \<iota> ` S \<rightarrow> carrier G \<Longrightarrow> genmapext_lift (\<iota> ` S) f \<in> hom F\<^bsub>S\<^esub> G\<close>)
  define h where "h = genmapext_lift (\<iota> ` S) f'"
  {fix x
   assume "x \<in> \<iota> ` S"
   hence ext_eq:"genmapext_lift (\<iota> ` S) f' (reln_tuple \<langle>S\<rangle> `` {x}) =  genmapext (\<iota> ` S) f' x"
     using genmapext_lift_wd 
     by (smt (verit, best) Set.set_insert \<open>f' \<in> \<iota> ` S \<rightarrow> carrier G\<close> equiv_class_self inclusion_subset_spanset insert_subset quotientI reln_equiv)
  hence "h (reln_tuple \<langle>S\<rangle> `` {x}) =  genmapext (\<iota> ` S) f' x" unfolding h_def by simp}
  moreover then have "\<forall>x \<in> S. f x = genmapext (\<iota> ` S) f' (\<iota> x)" unfolding f'_def 
    by (smt (z3) PiE assms(2) genmap_def genmapext.simps(1) genmapext.simps(2) image_eqI inclusion_def inv o_apply r_one)
  moreover then have "\<forall> x \<in> S. f x = f' (\<iota> x)" unfolding f'_def using inv by force
  ultimately have "\<forall> x \<in> S. f x = h (reln_tuple \<langle>S\<rangle> `` {\<iota> x})" by simp
  then show ?thesis using step1 h_def by fast
qed

theorem (in group)
  assumes "group G"
     and "f  \<in>  (S::('c,'d) monoidgentype set) \<rightarrow> carrier G"
     and "h \<in> hom (freegroup S) G" "g \<in> hom (freegroup S) G"
     and "\<forall> x \<in> S. f x = h (reln_tuple \<langle>S\<rangle> `` {\<iota>  x})"
     and "\<forall> x \<in> S. f x = g (reln_tuple \<langle>S\<rangle> `` {\<iota>  x})"
   shows "\<forall> x \<in> carrier (freegroup S).  h x  = g x"
proof-    
  have "liftgen S \<subseteq> carrier (freegroup S)" 
    by (meson gen_span.gen_gens span_liftgen subset_iff) 
  hence h_in:"h \<in> (liftgen S) \<rightarrow> carrier G" using assms(3) span_liftgen 
    using hom_in_carrier by fastforce
  hence h_eq:"\<forall>y\<in>carrier (freegroup S). genmapext_lift (\<iota> ` S) (unlift h S (liftgen S)) y = h y"
    using assms genmapext_unlift_uni by blast
  moreover have liftgen_inv:"\<forall>x \<in> (liftgen S). \<exists>y \<in> S. x = (reln_tuple \<langle>S\<rangle> `` {\<iota>  y})"
  proof
    fix x
    assume x:"x \<in> liftgen S"
    then obtain  y' where y':"y' \<in> \<iota> ` S" "x = reln_tuple \<langle>S\<rangle> ``{y'}" unfolding liftgen_def by blast
    then obtain y where "y \<in> S" "y' = \<iota> y" by auto
    thus "\<exists>y\<in>S. x = reln_tuple \<langle>S\<rangle> `` {\<iota> y}" using y' by auto
  qed
  {fix x
   assume asm:"x \<in> (liftgen S)"
   then obtain y where y:"y \<in> S" "x = (reln_tuple \<langle>S\<rangle> `` {\<iota>  y})" using liftgen_inv by meson
   then have "f y = h x" using assms by auto
   moreover have "f y =g x" using assms y by auto 
   ultimately have "h x = g x" by auto}
  then have "\<forall>x \<in> (liftgen S). h x = g x" by auto
  then have "\<forall>y\<in>carrier (freegroup S). genmapext_lift (\<iota> ` S) (unlift h S (liftgen S)) y = g y"
    using h_in genmapext_unlift_uni 
    using assms(4) by blast
  with h_eq have "\<forall>y\<in>carrier (freegroup S). h y = g y" by fastforce
  then show ?thesis by blast
qed

lemma  inv_extn_to_carrier:
 assumes "group G" 
 and "(\<langle>S\<rangle>\<^bsub>G\<^esub>) = carrier G"
 and  "h \<in> hom G (freegroup S')"
 and  "g \<in> hom (freegroup S') G"
 and "\<forall> x \<in> S. g (h x) = x"
 shows "\<forall> x \<in> carrier G. g (h x) = x"
proof
  fix x
  assume "x \<in> carrier G"
  hence x_in:"x \<in> (\<langle>S\<rangle>\<^bsub>G\<^esub>)" using assms by auto
  have comp_hom:"g \<circ> h \<in> hom G G" using assms 
    using Group.hom_compose by blast
  have "g (h x) = x" using x_in
  proof(induction rule:gen_span.induct)
    case gen_one
    then show ?case using x_in comp_hom hom_one[OF comp_hom assms(1) assms(1)] by force
  next
    case (gen_gens x)
    then show ?case using assms(5) by metis 
  next
    case (gen_inv x)
    show ?case using assms(1,2,3,4) gen_inv 
      by (metis comp_def comp_hom group.int_pow_1 group.int_pow_neg hom_int_pow)
  next
    case (gen_mult x y)
    then show ?case  using assms gen_mult.IH(1) gen_mult.IH(2) gen_mult.hyps(1) gen_mult.hyps(2) hom_mult comp_hom
      by (smt (verit, ccfv_SIG) hom_in_carrier)     
  qed
  then show "g (h x) = x" by blast
qed

(*push this in another file*)
lemma surj_gen_implies_epi:
  assumes "h \<in> hom G H"
   and "carrier H = \<langle>gens\<rangle>\<^bsub>H\<^esub>"
   and "group G"
   and "group H"
   and "gens \<subseteq> h ` (carrier G)"
 shows "h \<in> epi G H" 
proof-
  {fix x
  assume x_in:"x \<in> carrier H"
  hence "x \<in> h ` (carrier G)" unfolding assms(2)
  proof(induction x rule:gen_span.induct)
    case gen_one
    then show ?case using assms 
      by (smt (verit, ccfv_SIG) antisym_conv gen_span.gen_one group.gen_span_closed group_hom.hom_span group_hom.intro group_hom_axioms.intro hom_carrier subset_image_iff)  
  next
    case (gen_gens x)
    then show ?case using assms(5) by blast
  next
    case (gen_inv x)
    then show ?case 
      by (smt (verit) assms(1) assms(3) assms(4) group.inv_equality group.l_inv_ex group_hom.hom_inv group_hom.intro group_hom_axioms.intro image_iff)  
  next
    case (gen_mult x y)
    then show ?case  
      by (smt (verit, ccfv_SIG) antisym_conv assms(1) assms(2) assms(3) assms(4) assms(5) group.gen_span_closed group.surj_const_mult group_hom.hom_span group_hom.intro group_hom_axioms.intro hom_carrier image_eqI subset_image_iff)  
  qed}
  hence "h ` carrier G = carrier H" using assms(1) 
    by (simp add: hom_carrier subsetI subset_antisym)
  thus ?thesis using assms(1) unfolding epi_def by blast 
qed

(*universal property: sufficient condition- restricted in terms of type*)
lemma (in group) exist_of_hom_implies_freegroup: fixes S::"'a set"
  assumes "group G"
    and "(\<langle>S\<rangle>\<^bsub>G\<^esub>) = carrier G"
    and "\<And>(H::((unit \<times> 'a) \<times> bool) list set monoid).\<And>f.(group H) \<and> (f  \<in> S \<rightarrow> (carrier H)) \<longrightarrow> (\<exists>h \<in> hom G H. (\<forall> x \<in> S. h x = f x))"
  shows "\<exists>(S_H::(unit \<times> 'a) set). G \<cong> (freegroup S_H)" using assms
proof-
  define S_H where "(S_H::(unit, 'a) monoidgentype set) = ({()::unit}) \<times> S"
  define f' where "f' = (\<lambda>(x::'a). ((()::unit), x))"
  define f where "f = (\<lambda> (x::'a). (reln_tuple \<langle>S_H\<rangle> `` {\<iota>  (f' x)}))"
  hence bij:"bij_betw f' S S_H" unfolding bij_betw_def inj_on_def S_H_def f'_def by blast
  define Gs where "Gs = freegroup S_H"
  hence group_G:"group Gs" 
    by (simp add: freegroup_is_group)
  moreover have f_to_carrier:"f \<in> S \<rightarrow> carrier Gs"
    unfolding f_def S_H_def Gs_def f'_def
  proof
    fix x
    assume "x \<in> S"
    hence "f' x \<in> S_H" using bij 
      using bij_betwE by auto
    thus " reln_tuple \<langle>{()} \<times> S\<rangle> `` {\<iota> ((), x)} \<in> carrier F\<^bsub>{()} \<times> S\<^esub> " unfolding f'_def S_H_def 
      by (metis (no_types, lifting) freegroup_def inclusion_subset_spanset insert_image insert_subset partial_object.simps(1) quotientI)
  qed
  then obtain h where h:"h \<in> hom G Gs" "\<forall>x \<in> S. h x = f x" using assms(3)[of Gs] 
    by (metis group_G)  
  have mod_assms2: "carrier G = \<langle>S\<rangle>\<^bsub>G\<^esub>" using assms by blast
  have h_epi:"h \<in> epi G Gs" 
  proof-
   have carr_eq:"carrier Gs = \<langle>liftgen S_H\<rangle>\<^bsub>(freegroup S_H)\<^esub>" using Gs_def 
         by (simp add: liftgen_span span_liftgen subset_antisym)
   moreover have "f ` S = liftgen S_H" unfolding liftgen_def S_H_def f_def f'_def
         by blast
   moreover have "f ` S = h ` S" using h(2) by simp
   ultimately have "(liftgen S_H) \<subseteq> h ` (carrier G)" using assms 
         by (metis gen_span.gen_gens subsetI subset_image_iff)
   hence "h \<in> epi G Gs"  using surj_gen_implies_epi[OF h(1) ] unfolding Gs_def
         using  carr_eq freegroup_is_group assms(1) 
         by (metis Gs_def)
   thus ?thesis unfolding epi_def by blast
  qed
  have inv_exists:"(inv_into S f') \<in> S_H \<rightarrow> carrier G" using  f_def f_to_carrier bij_betw_inv_into[OF bij] 
    by (metis (no_types, lifting) Pi_I assms(2) bij_betw_imp_funcset funcset_mem gen_span.gen_gens)
  then obtain g where g:"g \<in> hom Gs G" "\<forall> x \<in> S_H. (inv_into S f') x = g (reln_tuple \<langle>S_H\<rangle> `` {\<iota>  x})" 
    using bij exists_hom[OF assms(1) inv_exists]  Gs_def by auto
  then have "\<forall> x \<in> S. g (h x) = x" using h 
    by (metis bij bij_betw_apply bij_betw_inv_into_left f_def) 
  then have "\<forall>x \<in> carrier G. g (h x) = x" using inv_extn_to_carrier[OF assms(1,2)] h(1) g(1)
    unfolding Gs_def by fast
  hence "g \<circ> h \<in> iso G G" by auto
  hence "h \<in> Group.iso G Gs \<and> g \<in> Group.iso Gs G" using epi_iso_compose_rev[OF h_epi g(1)] 
       iso_def by blast
  thus ?thesis using is_isoI unfolding Gs_def by blast
qed

(*now push the final proof*)

lemma assumes "reduce w = w" "w \<noteq> []"
  shows "\<not> (w ~ [])" using assms 
  by (metis CancelLemmas.length_Cons fixedpt_iteration neq_Nil_conv reduced.simps(1) reduced_cancel_eq reduced_iter_length reln_imp_cancels)
(*proof-
  have "iter (length w) (reduce) w = w"
    using assms apply(induction w) apply blast 
    by (metis CancelLemmas.length_Cons fixedpt_iteration)
  hence "reduced w" 
    by (metis reduced_iter_length)
  thus ?thesis 
    by (meson assms
(2) reduced.simps(1) reduced_cancel_eq reln_imp_cancels)
qed*)

(*Show that if gens generators G and minimally so, and if G is isomorpghic to freegroup S via \phi, then 
\phi gens generates freegroup S*)


definition is_freegroup::"_ \<Rightarrow> bool"
  where
"is_freegroup (G::('a,'b) monoid_scheme) \<equiv> (\<exists>(S::(unit \<times> 'a) set). G \<cong> (freegroup S))"

definition fg_with_basis
  where
"fg_with_basis (G::('a,'b) monoid_scheme) X \<equiv> (\<exists>(S::(unit \<times> 'a) set) \<phi>. (\<phi> \<in> iso G (freegroup S)) \<and> (\<langle>X\<rangle>\<^bsub>G\<^esub> = carrier G) \<and>(\<phi> ` X \<subseteq> (liftgen S)))"


lemma fixes G 
  fixes X
  assumes "(fg_with_basis G X)"
  shows "is_freegroup G" using assms unfolding fg_with_basis_def is_iso_def is_freegroup_def by auto


lemma m_concat_in_span:
  assumes "group G"
  and  "\<forall>x \<in> set l. x \<in> gens"
shows "monoid.m_concat G l \<in> \<langle>gens\<rangle>\<^bsub>G\<^esub>" using assms
proof(induction l)
  case (Cons a l)
  have "monoid.m_concat G (a#l) = a \<otimes>\<^bsub>G\<^esub> (monoid.m_concat G l)" by auto
  hence "(monoid.m_concat G l) \<in> \<langle>gens\<rangle>\<^bsub>G\<^esub>" using Cons by force
  moreover have "a \<in> \<langle>gens\<rangle>\<^bsub>G\<^esub>" using Cons(3) 
    by (simp add: gen_span.gen_gens)
  thus ?case 
    by (simp add: calculation gen_span.gen_mult)  
qed (simp)


value "[(1::nat), 2, 3]!2"
definition non_reducible::"('a,'b) monoid_scheme \<Rightarrow> 'a set => 'a \<Rightarrow> bool"
  where
"non_reducible G X w \<equiv> (\<exists>l. w = monoid.m_concat G l \<and> (\<forall>x \<in> set l. x \<in> X ) \<and> (\<forall>i \<le> (length l)-2 . l!i \<noteq> inv\<^bsub>G\<^esub> (l!(i+1))))"

lemma assume " X \<inter> (m_inv (freegroup A) ` X) = {}"

(* consider two intermediaries for the following result,
group generated by X and
free group X*)
(*
theorem 
  assumes "group G"
       and 
       and "G0 = gen\<^bsub>G\<^esub> X"
       and "h \<in> hom G H"
          
     shows "ex
theorem 
  assumes "group G"
    and "X \<subseteq> carrier G"
    and "\<forall>H. ((group H) \<and> (f \<in> X \<rightarrow> carrier H)) \<longrightarrow> (\<exists>!h \<in> hom G H. \<forall> x \<in> carrier G. f x = h x)"
   shows "is_iso G (freegroup X)"
  sorry

theorem 
  assumes "group G"


(*proof outline-
1) define the extension*)



theorem

  assumes "group G"
  and "f  \<in> liftgen (S::('a,'b) monoidgentype set) \<rightarrow> carrier G"
shows "\<exists>!h \<in> hom (freegroup S) G. \<forall> x \<in> (liftgen S) . f x = h x"
proof
*)
end