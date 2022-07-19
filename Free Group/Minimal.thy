theory Minimal
imports FreeGroupMain Distinct_Inverse
begin

definition union_inv
  where
"union_inv S A \<equiv> S \<union> (m_inv (freegroup A) ` S)"

lemma inv_inv_G:
  assumes "group G" "x \<in> carrier G"
   shows "inv\<^bsub>G\<^esub> (inv\<^bsub>G\<^esub> x) = x"
  using assms 
  by simp

lemma inv_in_S:
  assumes "x \<in> (m_inv G ` S)" "x \<in> carrier G" "S \<subseteq> carrier G" "group G"
  shows "inv\<^bsub>G\<^esub> x \<in> S"
proof-
 obtain y where y:"x = m_inv G y" "y \<in> S" using assms(1) by force
 have "y = m_inv  G x" using inv_inv_G assms(2,4) unfolding y 
   by (metis assms(3) in_mono y(2))
  then show ?thesis using y(2) by blast
qed

lemma intersection_lemma:
  assumes "A \<inter> (f ` A) = {}"
      and "x \<notin> A"
      and "f x \<notin> A"
      and "x \<notin> f ` A"
      and "x \<noteq> f x"
    shows "(A \<union> {x}) \<inter> (f ` (A \<union> { x})) = {}"
  using assms 
proof-
  have "(A \<union> {x}) \<inter> (f ` (A \<union> { x})) = (A \<union> {x}) \<inter> ((f  ` A) \<union> {f x})"
    by force
  moreover then have "... =  (A  \<inter> ((f  ` A) \<union> {f x})) \<union> ({x} \<inter> ((f  ` A) \<union> {f x}))"
    by blast
  moreover then have "... = (A  \<inter> (f  ` A)) \<union> (A  \<inter> {f x})  \<union> ({x} \<inter> ((f  ` A)) \<union> ({x} \<inter> {f x}))" 
    by fast
  moreover then have "... =  ({x} \<inter> ((f  ` A)) \<union> ({x} \<inter> {f x}))" 
    using assms by simp
  moreover then have "... = {}" using assms by blast
  ultimately show ?thesis by simp
qed

definition minimal_set
  where
"minimal_set S A = (SOME X. X \<subseteq> S \<and>  X \<inter> (m_inv (freegroup A) ` X) = {} 
                       \<and> union_inv S A = union_inv X A)"
(*
lemma assumes "x \<in> carrier (freegroup A)" "x \<noteq> one (freegroup A)"
  shows "x \<noteq> m_inv (freegroup A) x"
proof(rule ccontr)
  assume "\<not> x \<noteq> inv\<^bsub>freegroup A\<^esub> x"
  then have "x = inv\<^bsub>freegroup A\<^esub> x" by argo
  then obtain w where "w \<in> \<langle>A\<rangle>" "x = A(w)" *)

lemma (in group) one_not_in_inv:
assumes "S \<subseteq> carrier (freegroup A)"
          "\<one>\<^bsub>freegroup A\<^esub> \<notin> S"
shows  "\<one>\<^bsub>freegroup A\<^esub> \<notin>  m_inv (freegroup A) `S"
proof(rule ccontr)
  assume asm:"\<not> \<one>\<^bsub>F\<^bsub>A\<^esub>\<^esub> \<notin> m_inv F\<^bsub>A\<^esub> ` S"
  then have "\<one>\<^bsub>F\<^bsub>A\<^esub>\<^esub> \<in> m_inv F\<^bsub>A\<^esub> ` S" by auto
  then obtain x where x:"\<one>\<^bsub>F\<^bsub>A\<^esub>\<^esub> \<otimes>\<^bsub>F\<^bsub>A\<^esub>\<^esub> x = \<one>\<^bsub>F\<^bsub>A\<^esub>\<^esub>" "x \<in> S"
    unfolding m_inv_def image_def apply simp 
    by (meson \<open>\<one>\<^bsub>F\<^bsub>A\<^esub>\<^esub> \<in> m_inv F\<^bsub>A\<^esub> ` S\<close> assms(1) freegroup_is_group group.r_inv group.subgroup_self inv_in_S subgroup.one_closed)
  have "x = \<one>\<^bsub>F\<^bsub>A\<^esub>\<^esub>" using  x(1) x(2) assms(2) 
    by (meson assms(1) freegroup_is_group gen_span.gen_one group.l_cancel_one span_liftgen subsetD)
  then show False using x(2) assms(2) by argo
qed

lemma (in group)
  assumes "S \<subseteq> carrier (freegroup A)"
          "\<one>\<^bsub>freegroup A\<^esub> \<notin> S"
   shows "\<exists>X. X \<subseteq> S \<and> X \<inter> (m_inv (freegroup A) ` X) = {} \<and> union_inv S A = union_inv X A"
proof-
  have one_notin:"\<one>\<^bsub>freegroup A\<^esub> \<notin>  m_inv (freegroup A) `S" using one_not_in_inv[OF assms]  .
  define Y where "Y = {X. X \<subseteq> S \<and>  X \<inter> (m_inv (freegroup A) ` X) = {}}"
   {fix C
    assume C:"subset.chain Y C"
    then have 1:"(\<Union> C) \<subseteq> S" using C unfolding Y_def subset.chain_def by blast
     have 11:"(\<Union> C)  \<inter> (m_inv (freegroup A) ` (\<Union> C) ) = {}" 
     proof(rule ccontr)
       assume asm:"\<Union> C \<inter> m_inv (freegroup A) ` \<Union> C \<noteq> {}"
       then obtain x where x:"x \<in> \<Union> C \<inter> m_inv (freegroup A) ` \<Union> C" by blast
       then have x_in:"x \<in> m_inv (freegroup A) ` \<Union> C" using IntD2 by blast
       then have 2:"inv\<^bsub>(freegroup A)\<^esub> x \<in>  \<Union> C" using inv_in_S[OF x_in]
           freegroup_is_group[of A] 1 assms by fastforce
       moreover have "x \<in> \<Union> C" using x IntD1 by blast
       then obtain P Q where P_Q:"P \<in> C" "Q \<in> C" "x \<in> P" "inv\<^bsub>(freegroup A)\<^esub> x \<in> Q"
         using 2 by blast
       then have Or:"P \<subseteq> Q \<or>  Q \<subseteq> P" using C unfolding subset.chain_def 
         by (meson C subset_chain_def)
       have "P \<subseteq> Q \<Longrightarrow> x \<in> Q \<and> m_inv (freegroup A) x \<in> Q" using P_Q by blast
       hence F1:"P \<subseteq> Q \<Longrightarrow> False" using C P_Q(2) Y_def
         unfolding subset.chain_def[of Y C] 
         by blast
       have "Q \<subseteq> P \<Longrightarrow> x \<in> P \<and> m_inv (freegroup A) x \<in> P"
         using P_Q by blast
       hence F2:"Q \<subseteq> P \<Longrightarrow> False" 
          using C P_Q(1) Y_def
         unfolding subset.chain_def[of Y C] 
         by blast
       show False using F1 F2 Or by argo
     qed
     then have "\<Union>C \<in> Y" using C 1 11 unfolding Y_def by force
   } note inter = this
   obtain M where M:"M \<in> Y" "\<forall>X\<in>Y. M \<subseteq> X \<longrightarrow> X = M" "M \<in> Y" 
     using subset_Zorn'[OF inter] by fast
   then have M_sub:"M \<subseteq> S" unfolding Y_def by blast
   then have inv_M_sub:
         "m_inv (freegroup A) `M \<subseteq> m_inv (freegroup A) ` S" by blast
   have a:"M \<inter> m_inv (freegroup A) `M = {}" using M 
     using Y_def by fastforce
   have "union_inv M A = union_inv S A"
     unfolding union_inv_def
   proof(rule ccontr)
     assume asm:"M \<union> m_inv (freegroup A) ` M \<noteq> S \<union> m_inv (freegroup A) ` S"
     have "M \<union> m_inv (freegroup A) ` M \<subseteq> S  \<union> m_inv (freegroup A) ` S"
       using M_sub inv_M_sub  by blast
     then obtain x where x:"x \<in> S  \<union> m_inv (freegroup A) ` S"
           "x \<notin> M \<union> m_inv (freegroup A) ` M " using asm
       by auto
     then have "x \<noteq> \<one>\<^bsub>F\<^bsub>A\<^esub>\<^esub>" using one_notin assms(2) by fastforce
     then have not_eq_inv:"x \<noteq> m_inv (freegroup A) x" using not_eq_inv[of x A] x(1) assms(1) 
       by (smt (verit) Un_iff gen_span.gen_inv image_iff liftgen_span span_liftgen subsetD)
     then show False
     proof (cases "x \<in> S")
       case True
       have x_not_in:"x \<notin> m_inv (freegroup A) ` M" using x(2) by blast
       then have "m_inv (freegroup A) x \<notin> M" using x 
        by (smt (verit, ccfv_threshold) UnE assms freegroup_is_group group.inv_inv imageE imageI in_mono)
       define M1 where "M1 = M \<union> {x}"  
       then have "M1 \<subseteq> S" using x M_sub True by fast
       moreover have "M1 \<inter> (m_inv (freegroup A) ` M1) = {}" using x(2) M(1)
         unfolding Y_def 
         using intersection_lemma[of M "\<lambda>x. (m_inv (freegroup A) x)" x] not_eq_inv
         unfolding M1_def 
         using \<open>inv\<^bsub>F\<^bsub>A\<^esub>\<^esub> x \<notin> M\<close> by fastforce  
       ultimately have "M1 \<in> Y" unfolding Y_def by force
       then have "M1 = M" using M(2) M1_def by fast
       then show False using M1_def x by blast
     next
       case False
       then obtain y where y:"y \<in> S" "x = m_inv (freegroup A) y"
         using x by blast
       then have y_inv:"y = m_inv (freegroup A) x" 
         by (metis assms(1) freegroup_is_group group.inv_inv subsetD)
       define M1 where M1:"M1 = M \<union> {y}"
       then have "M1 \<subseteq> S" using y M_sub  by fast
       then have "y \<notin> M" using y y_inv x  by blast
       moreover have " inv\<^bsub>F\<^bsub>A\<^esub>\<^esub> y \<notin> M" using y y_inv x by blast
       moreover have "y \<notin>  m_inv F\<^bsub>A\<^esub> ` M"  using y y_inv x 
         by (meson M_sub assms(1) calculation(2) freegroup_is_group in_mono inv_in_S subsetI)
       moreover have "y \<noteq> inv\<^bsub>F\<^bsub>A\<^esub>\<^esub> y" using y y_inv not_eq_inv by presburger
       ultimately have "M1 \<inter> (m_inv (freegroup A) ` M1) = {}" using y x(2) M(1)
         unfolding Y_def 
         using intersection_lemma[of M "\<lambda>x. (m_inv (freegroup A) x)" y] y y_inv not_eq_inv
         unfolding M1  by fast
       then have "M1 \<in> Y" unfolding Y_def 
         using \<open>M1 \<subseteq> S\<close> 
         using \<open>M1 \<inter> m_inv F\<^bsub>A\<^esub> ` M1 = {}\<close> by blast
       then have "M1 = M" using M(2) M1 by fast
       then show False using M1 y x by blast   
     qed
   qed
  then show ?thesis using M(1) M_sub exI unfolding Y_def 
    using CollectD by blast
qed

end
