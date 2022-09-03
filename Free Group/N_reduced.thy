theory N_reduced
imports NielsonSchreier Minimal Main UP
begin   


definition N_reduced ("N")
  where
"N_reduced S A = ((\<forall>x \<in> (red_rep A) ` (union_inv S A). N0 x) \<and>
                  (\<forall>x \<in> (red_rep A) ` (union_inv S A). \<forall>y \<in> (red_rep A) ` (union_inv S A). N1 x y) \<and> 
                  (\<forall>x \<in> (red_rep A) ` (union_inv S A). 
                      \<forall>y \<in> (red_rep A) ` (union_inv S A). 
                          \<forall> z \<in> (red_rep A) ` (union_inv S A).
                                         N2 x y z))"


lemma N_reduced_X: assumes "H \<le> freegroup A"
  shows "N_reduced (X (SG (freegroup A) H) A) A"
proof-
  have N0: "((\<forall>x \<in> (red_rep A) ` (union_inv  (X (SG (freegroup A) H) A) A). N0 x))"
    using assms N0 by blast
  moreover have N1: "\<forall>x \<in> (red_rep A) ` (union_inv (X (SG (freegroup A) H) A) A). \<forall>y \<in> (red_rep A) ` (union_inv (X (SG (freegroup A) H) A) A). N1 x y"
    using assms N1 by blast
  moreover have "\<forall>x \<in> (red_rep A) ` (union_inv (X (SG (freegroup A) H) A) A). \<forall>y \<in> (red_rep A) ` (union_inv (X (SG (freegroup A) H) A) A). \<forall>z \<in> (red_rep A) ` (union_inv (X (SG (freegroup A) H) A) A). N2 x y z"
    using N0 N1 N2 assms by blast
  ultimately show ?thesis unfolding N_reduced_def by blast
qed


definition minimal_set
  where
"minimal_set S A = (SOME X. X \<subseteq> S \<and>  X \<inter> (m_inv (freegroup A) ` X) = {} \<and> union_inv S A = union_inv X A)"


lemma min_set_exists:
  assumes "H \<le> (freegroup A)"
  shows "\<exists>S. S = minimal_set (X (SG (freegroup A) H) A) A"
  by simp

lemma union_inv_eq_minimal: 
  assumes "H \<le> (freegroup A)"
  shows "union_inv (X (SG (freegroup A) H) A) A = union_inv (minimal_set (X (SG (freegroup A) H) A) A) A"
proof-
  let ?Q =  "\<lambda> Y . (Y \<subseteq>   (X (SG (freegroup A) H) A) 
        \<and>  Y \<inter> (m_inv (freegroup A) ` Y) = {} 
        \<and> union_inv Y A = union_inv (X (SG (freegroup A) H) A)  A)" 
  obtain S where S:" S \<subseteq>  (X (SG (freegroup A) H) A) " "S \<inter> (m_inv (freegroup A) ` S) = {}"
          "union_inv (X (SG (freegroup A) H) A) A  = union_inv S A"
    using group.existence_of_minimal[OF freegroup_is_group] 
    by (smt (verit, del_insts) G_def UnCI X_def assms dual_order.trans gen_span.intros(1) mem_Collect_eq one_SG subgroup.mem_carrier subset_eq union_inv_def union_inv_sub_H) 
  hence Q_S:"?Q S" by argo
  hence "?Q (minimal_set (X (SG (freegroup A) H) A) A)" unfolding minimal_set_def using someI
    by (metis (mono_tags, lifting))
  then show ?thesis by argo
qed

lemma minimal_set_empty_intersection: 
  assumes "H \<le> (freegroup A)"
  shows "(minimal_set (X (SG (freegroup A) H) A) A)
      \<inter>(m_inv (freegroup A) ` (minimal_set (X (SG (freegroup A) H) A) A)) = {}"
proof-
  let ?Q =  "\<lambda> Y . (Y \<subseteq>   (X (SG (freegroup A) H) A) 
        \<and>  Y \<inter> (m_inv (freegroup A) ` Y) = {} 
        \<and> union_inv Y A = union_inv (X (SG (freegroup A) H) A)  A)" 
  obtain S where S:" S \<subseteq>  (X (SG (freegroup A) H) A) " "S \<inter> (m_inv (freegroup A) ` S) = {}"
          "union_inv (X (SG (freegroup A) H) A) A  = union_inv S A"
    using group.existence_of_minimal[OF freegroup_is_group] 
    by (smt (verit, del_insts) G_def UnCI X_def assms dual_order.trans gen_span.intros(1) 
          mem_Collect_eq one_SG subgroup.mem_carrier subset_eq union_inv_def union_inv_sub_H) 
  hence Q_S:"?Q S" by argo
  hence "?Q (minimal_set (X (SG (freegroup A) H) A) A)" unfolding minimal_set_def using someI
    by (metis (mono_tags, lifting))
  then show ?thesis by argo
qed

lemma minimal_set_in_carrier: 
  assumes "H \<le> (freegroup A)"
  shows "(minimal_set (X (SG (freegroup A) H) A) A) \<subseteq> carrier (freegroup A)"
proof-
  let ?Q =  "\<lambda> Y . (Y \<subseteq>   (X (SG (freegroup A) H) A) 
        \<and>  Y \<inter> (m_inv (freegroup A) ` Y) = {} 
        \<and> union_inv Y A = union_inv (X (SG (freegroup A) H) A)  A)" 
  obtain S where S:" S \<subseteq>  (X (SG (freegroup A) H) A)" "S \<inter> (m_inv (freegroup A) ` S) = {}"
          "union_inv (X (SG (freegroup A) H) A) A  = union_inv S A"
    using group.existence_of_minimal[OF freegroup_is_group] 
    by (smt (verit, del_insts) G_def UnCI X_def assms dual_order.trans gen_span.intros(1) 
          mem_Collect_eq one_SG subgroup.mem_carrier subset_eq union_inv_def union_inv_sub_H) 
  hence Q_S:"?Q S" by argo
  hence "?Q (minimal_set (X (SG (freegroup A) H) A) A)" unfolding minimal_set_def using someI
    by (metis (mono_tags, lifting))
  hence "(minimal_set (X (SG (freegroup A) H) A) A) \<subseteq>  (X (SG (freegroup A) H) A)" by argo
  thus ?thesis using assms unfolding X_def SG_def 
    using subgroup.subset by fastforce
qed

lemma N_reduced_minimal:
  assumes "H \<le> (freegroup A)"
  shows "N_reduced (minimal_set (X (SG (freegroup A) H) A) A) A" 
  using union_inv_eq_minimal  unfolding N_reduced_def 
    using N_reduced.N_reduced_X N_reduced.N_reduced_def assms by blast 

lemma union_inv_eq_span:
  assumes "union_inv S A = union_inv Y A"
  shows "\<langle>S\<rangle>\<^bsub>freegroup A\<^esub> =  \<langle>Y\<rangle>\<^bsub>freegroup A\<^esub>"
proof(rule equalityI)
  show " \<langle>S\<rangle>\<^bsub>freegroup A\<^esub> \<subseteq> \<langle>Y\<rangle>\<^bsub>freegroup A\<^esub>" unfolding union_inv_def
  proof
    fix x
    assume x:"x \<in> \<langle>S\<rangle>\<^bsub>freegroup A\<^esub>"
    show "x \<in>  \<langle>Y\<rangle>\<^bsub>freegroup A\<^esub>" using x
    proof(induction rule:gen_span.induct)
      case gen_one
      then show ?case by auto 
    next
      case (gen_gens x)
      then show ?case using assms unfolding union_inv_def 
        by (metis (mono_tags, hide_lams) UnCI UnE gen_span.gen_gens gen_span.intros(3) imageE)
    next
      case (gen_inv x)
      then show ?case 
        by (simp add: gen_span.gen_inv)
    next
      case (gen_mult x y)
      then show ?case 
        by (simp add: gen_span.gen_mult) 
    qed
  qed
next
 show " \<langle>Y\<rangle>\<^bsub>freegroup A\<^esub> \<subseteq> \<langle>S\<rangle>\<^bsub>freegroup A\<^esub>" unfolding union_inv_def
  proof
    fix x
    assume x:"x \<in> \<langle>Y\<rangle>\<^bsub>freegroup A\<^esub>"
    show "x \<in>  \<langle>S\<rangle>\<^bsub>freegroup A\<^esub>" using x
    proof(induction rule:gen_span.induct)
      case gen_one
      then show ?case by auto 
    next
      case (gen_gens x)
      then show ?case using assms unfolding union_inv_def 
        by (metis (mono_tags, hide_lams) UnCI UnE gen_span.gen_gens gen_span.intros(3) imageE)
    next
      case (gen_inv x)
      then show ?case 
        by (simp add: gen_span.gen_inv)
    next
      case (gen_mult x y)
      then show ?case 
        by (simp add: gen_span.gen_mult) 
    qed
  qed
qed

lemma min_set_eq_span:
  assumes "H \<le> (freegroup A)"
  shows "\<langle>(minimal_set (X (SG (freegroup A) H) A) A)\<rangle>\<^bsub>(freegroup A)\<^esub> 
    =  \<langle>(X (SG (freegroup A) H) A)\<rangle>\<^bsub>(freegroup A)\<^esub>"
  using N_reduced_minimal union_inv_eq_span union_inv_eq_minimal 
  using assms by blast
 
lemma (in group) carrier_eq_minimal:
  assumes "H \<le> freegroup A"
  shows "\<langle>(minimal_set (X (SG (freegroup A) H) A) A)\<rangle>\<^bsub>freegroup A\<^esub> = H"
proof-
  let ?Y = "(X (SG (freegroup A) H) A)"
  have 1:"\<langle>?Y\<rangle>\<^bsub>(SG (freegroup A) H)\<^esub> = carrier (SG (freegroup A) H)"
    using span_X_SG_eq_SG assms 
    by (simp add: span_X_SG_eq_SG assms)  
   have carr:"carrier (SG (freegroup A) H) = H" unfolding SG_def 
      by simp
   have 2:"\<langle>?Y\<rangle>\<^bsub>(SG (freegroup A) H)\<^esub> = \<langle>?Y\<rangle>\<^bsub>(freegroup A)\<^esub>"
(*    using assms unfolding SG_def using group.gen_span_closed freegroup_is_group *)
  proof
      show  "\<langle>?Y\<rangle>\<^bsub>(SG (freegroup A) H)\<^esub> \<subseteq> \<langle>?Y\<rangle> \<^bsub>(freegroup A)\<^esub>" 
      proof(rule subsetI)
        fix x
        assume x:"x \<in> \<langle>X (SG F\<^bsub>A\<^esub> H) A\<rangle>\<^bsub>SG F\<^bsub>A\<^esub> H\<^esub>"
        show "x \<in> \<langle>X (SG F\<^bsub>A\<^esub> H) A\<rangle>\<^bsub>F\<^bsub>A\<^esub>\<^esub>" using x
        proof(induction x rule:gen_span.induct)
          case gen_one
          then show ?case 
            by (metis gen_span.gen_one one_SG)  
        next
          case (gen_gens x)
          then show ?case 
            by (simp add: gen_span.gen_gens)  
        next
          case (gen_inv x)
          then show ?case 
            by (metis "1" assms carr freegroup_is_group gen_span.gen_inv inv_SG)  
        next
          case (gen_mult x y)
          then show ?case 
            by (metis gen_span.gen_mult mult_SG) 
        qed
      qed
    next
      show  "\<langle>?Y\<rangle>\<^bsub>(freegroup A)\<^esub> \<subseteq> \<langle>?Y\<rangle>\<^bsub>(SG (freegroup A) H)\<^esub>" 
      proof
        fix x
        assume "x \<in> \<langle>?Y\<rangle>\<^bsub>(freegroup A)\<^esub>"
        thus "x \<in> \<langle>?Y\<rangle>\<^bsub>(SG (freegroup A) H)\<^esub>"
        proof(induction x rule:gen_span.induct)
          case gen_one
          then show ?case using assms
            unfolding SG_def X_def 
            by (metis (mono_tags, lifting) SG_def gen_span.gen_one one_SG)
        next
          case (gen_gens x)
          then show ?case 
            by (simp add: gen_span.gen_gens)  
        next
          case (gen_inv x)
          then show ?case using  gen_span.gen_inv[OF gen_inv(2)]  
                group.m_inv_consistent[OF "freegroup_is_group" assms] carr unfolding X_def 
            by (metis (mono_tags, lifting) SG_def 1 gen_inv.IH)
        next
          case (gen_mult x y)
          then show ?case using gen_span.gen_mult[OF gen_mult(3,4)] 
             group.subgroup_mult_equality[OF "freegroup_is_group" assms] carr unfolding X_def SG_def
            by simp
        qed 
      qed
    qed
  show ?thesis using 1  HOL.sym[OF 2] min_set_eq_span[OF assms] carr by argo
qed


lemma(in group) subgp_of_freegroup_is_fg_with_basis:
  assumes "H \<le> (freegroup A)"
  shows "fg_with_basis (SG (freegroup A) H) (minimal_set (X (SG (freegroup A) H) A) A)"
proof-
  define Y where  "Y = (minimal_set (X (SG (freegroup A) H) A) A)"
  hence 1:"Y \<inter> (m_inv (freegroup A) ` Y) = {}" using minimal_set_empty_intersection[OF assms] by auto
  moreover have 2:"Y \<subseteq> carrier (freegroup A)" using minimal_set_in_carrier[OF assms] unfolding Y_def
    by auto
  moreover have 3:"\<forall>w \<in> \<langle>Y\<rangle>\<^bsub>freegroup A\<^esub>.  non_reducible (freegroup A) Y w \<longrightarrow> w \<noteq> \<one>\<^bsub>freegroup A\<^esub>"
    sorry
  show "fg_with_basis (SG (freegroup A) H) (minimal_set (X (SG (freegroup A) H) A) A)"
   using group.one_point_nine[OF freegroup_is_group[of "A"] 1 2  freegroup_is_group[of "A"]]
         unfolding Y_def using carrier_eq_minimal[OF assms] unfolding SG_def 
         by (simp add: SG_def Y_def \<open>\<forall>w\<in>\<langle>Y\<rangle>\<^bsub>F\<^bsub>A\<^esub>\<^esub>. non_reducible F\<^bsub>A\<^esub> Y w \<longrightarrow> w \<noteq> \<one>\<^bsub>F\<^bsub>A\<^esub>\<^esub>\<close>)
qed

lemma(in group) Nielson_Schrier:
  assumes "H \<le> (freegroup A)"
  shows "is_freegroup ((freegroup A)\<lparr>carrier := H\<rparr>)"
  using subgp_of_freegroup_is_fg_with_basis[OF assms] fg_with_basis_is_free unfolding SG_def 
  by blast
(*
definition fg_with_basis
  where
"fg_with_basis (G::('a,'b) monoid_scheme) X 
    \<equiv> (\<exists>(S::(unit \<times> 'a) set) \<phi>. (\<phi> \<in> iso G (freegroup S)) 
              \<and> (\<langle>X\<rangle>\<^bsub>G\<^esub> = carrier G) \<and>(\<phi> ` X = (liftgen S)))"*)

(*definition non_reducible::"('a,'b) monoid_scheme \<Rightarrow> 'a set => 'a \<Rightarrow> bool"
  where
"non_reducible G X w \<equiv> (\<exists>l. w = monoid.m_concat G l \<and> (l \<noteq> []) 
                          \<and> (\<forall>x \<in> set l. x \<in> X \<union> m_inv G ` X) 
                          \<and> ((length l = 1) \<or> (\<forall>i \<le> (length l)-2 . l!i \<noteq> inv\<^bsub>G\<^esub> (l!(i+1)))))"


*)
(*
\<langle>X (SG (freegroup A) H) A\<rangle>\<^bsub>(SG (freegroup A) H)\<^esub> = carrier (SG (freegroup A) H)"
  using span_X_SG_eq_SG*)
(*show the following*)
(*proof sketch*)
(*the minimal set is N-reduced*)(*Done*)

(*span of the minimal set is the same as the original set (X (SG (freegroup A) H) A)*)(*has been shown*)

(*the original set spans the subgroup H - search term in the other file- desired result4*)

(*for all elements in   (X (SG (freegroup A) H) A) [or minimal set of it], 
irreducible word implies non identity*)
(*n_reduced_cancel*)

(*for last step, need to look at red_rep. The claimed process is as follows*)
(*if an element belongs to minimal, then it can be reduced to m_concat of its red_rep*)
(*red_rep elements are irreducible*)
(*Further these elements satisfy N0, N1 and N2, thus they cannot be identity*)
(*thus mapping them back, we find that they are not identity*)

(*union inv implies equal span. done!*)
(*question- why SG?*)