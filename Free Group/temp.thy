theory temp
  imports "NielsonSchreier"
begin

lemma length_lex:
  assumes "length (red_rep A a) < length (red_rep A b)"
              "a \<in> carrier (freegroup A) \<and>
                 b \<in> carrier (freegroup A)"
      shows "(a,b) \<in> lex_L2_word A"
proof-
  have "(length (red_rep A a), length (red_rep A b)) \<in> nat_less" unfolding nat_less_def using assms by blast
  then show ?thesis unfolding lex_L2_word_def lex_prod_def using assms(2) unfolding freegroup_def by simp
qed

lemma inv_X_clos: assumes "H \<le> freegroup A"
  shows "m_inv F\<^bsub>A\<^esub> ` {g \<in> carrier (F\<^bsub>A\<^esub>\<lparr>carrier := H\<rparr>). g \<notin> G (F\<^bsub>A\<^esub>\<lparr>carrier := H\<rparr>) A g}
    \<subseteq> carrier F\<^bsub>A\<^esub>"
proof
  fix x assume "x \<in> m_inv F\<^bsub>A\<^esub> `
             {g \<in> carrier (F\<^bsub>A\<^esub>\<lparr>carrier := H\<rparr>). g \<notin> G (F\<^bsub>A\<^esub>\<lparr>carrier := H\<rparr>) A g}"
  then obtain y where y: "m_inv F\<^bsub>A\<^esub> y = x \<and> y \<in> {g \<in> carrier (F\<^bsub>A\<^esub>\<lparr>carrier := H\<rparr>). g \<notin> G (F\<^bsub>A\<^esub>\<lparr>carrier := H\<rparr>) A g}" by blast
  then have "y \<in> carrier F\<^bsub>A\<^esub>" using assms freegroup_is_group group.subgroupE(1) by auto
  then have "m_inv F\<^bsub>A\<^esub> y \<in> carrier F\<^bsub>A\<^esub>" using y assms subgroup.m_inv_closed subgroup.mem_carrier by fastforce
  then show "x \<in> carrier F\<^bsub>A\<^esub>" using y by blast
qed

lemma union_inv_clos:
  assumes "H \<le> freegroup A"
  shows "(union_inv (X (SG (freegroup A) H) A) A) \<subseteq> carrier (freegroup A)"
  unfolding X_def union_inv_def SG_def
proof-
  have "{g \<in> carrier (F\<^bsub>A\<^esub>\<lparr>carrier := H\<rparr>). g \<notin> G (F\<^bsub>A\<^esub>\<lparr>carrier := H\<rparr>) A g} \<subseteq> carrier (freegroup A)" using assms subgroup.subset by auto
  moreover have "m_inv F\<^bsub>A\<^esub> ` {g \<in> carrier (F\<^bsub>A\<^esub>\<lparr>carrier := H\<rparr>). g \<notin> G (F\<^bsub>A\<^esub>\<lparr>carrier := H\<rparr>) A g}
    \<subseteq> carrier F\<^bsub>A\<^esub>" using assms inv_X_clos by blast
  ultimately show "{g \<in> carrier (F\<^bsub>A\<^esub>\<lparr>carrier := H\<rparr>). g \<notin> G (F\<^bsub>A\<^esub>\<lparr>carrier := H\<rparr>) A g} \<union>
    m_inv F\<^bsub>A\<^esub> ` {g \<in> carrier (F\<^bsub>A\<^esub>\<lparr>carrier := H\<rparr>). g \<notin> G (F\<^bsub>A\<^esub>\<lparr>carrier := H\<rparr>) A g}
    \<subseteq> carrier F\<^bsub>A\<^esub>" by blast
qed

lemma lex_total:
  assumes "((x1 ⊗⇘F⇘A⇙⇙ y1), x1) ∈ lex_L2_word A ∨ ((x1 ⊗⇘F⇘A⇙⇙ y1), y1) ∈ lex_L2_word A"
  shows "(x1,y1) ∈ lex_L2_word A ∨ (y1, x1) ∈ lex_L2_word A" (*total*)
proof(cases "((x1 ⊗⇘F⇘A⇙⇙ y1), x1) ∈ lex_L2_word A")
  case True
  then show ?thesis sorry
next
  case False
  then show ?thesis sorry
qed

lemma union_inv_sub_H:
  assumes "H ≤ freegroup A" "x1 ∈ (union_inv (X (SG (freegroup A) H) A) A)" 
  shows "x1 ∈ H"
proof-
  have 1:"x1 ∈ (X (SG (freegroup A) H) A) ∪ (m_inv (freegroup A) ` (X (SG (freegroup A) H) A))" using union_inv_def using assms(2) by auto
  then show ?thesis 
  proof(cases "x1 ∈ (X (SG (freegroup A) H) A)")
    case True
    then have "x1 ∈ {g ∈ carrier (SG (freegroup A) H). g ∉ (G (SG (freegroup A) H) A g)}" using X_def by auto
    then have "x1 ∈ carrier (SG (freegroup A) H)" by simp
    then have "x1 ∈ carrier ((freegroup A)⦇carrier := H⦈)" using SG_def by metis
    then show ?thesis using assms(1) by auto
  next
    case False
    then have "x1 ∈ (m_inv (freegroup A) ` (X (SG (freegroup A) H) A))" using 1 by auto
    moreover then have "x1 ∈ carrier ((freegroup A)⦇carrier := H⦈)" using m_inv_def assms(1) SG_def X_def union_inv_clos by (smt (verit)  image_iff mem_Collect_eq partial_object.select_convs(1) partial_object.surjective partial_object.update_convs(1) subgroup.m_inv_closed) 
    ultimately show ?thesis using assms(1) by auto
  qed
qed

lemma N1:
  assumes "H ≤ freegroup A" 
  shows "∀x ∈ (red_rep A) ` (union_inv (X (SG (freegroup A) H) A) A). ∀y ∈ (red_rep A) ` (union_inv (X (SG (freegroup A) H) A) A). N1 x y"
  apply(rule ballI)+
proof-
  fix x y assume x: "x ∈ red_rep A ` union_inv (X (SG F⇘A⇙ H) A) A" and  y: "y ∈ red_rep A ` union_inv (X (SG F⇘A⇙ H) A) A"
  show "N1 x y"
  proof(rule ccontr)
    assume N1: "¬ N1 x y"
    then have "x ≠ wordinverse y" using N1_def by auto
    obtain x1 where x1:"red_rep A x1 = x ∧ x1 ∈ (union_inv (X (SG (freegroup A) H) A) A)" using x by blast
    then have x1A: "x1 ∈ carrier (freegroup A)" using assms union_inv_clos by blast
    obtain y1 where y1:"red_rep A y1 = y ∧ y1 ∈ (union_inv (X (SG (freegroup A) H) A) A)" using y by blast
    then have y1A: "y1 ∈ carrier (freegroup A)" using assms union_inv_clos by blast
    have H:"x1 ∈ H ∧ y1 ∈ H" using assms x1 x1A y1 using union_inv_sub_H by blast
    have "¬ (length (red_rep A (x1 ⊗⇘ F⇘A⇙⇙ y1)) ≥ length (red_rep A x1) ∧ length (red_rep A (x1 ⊗⇘ F⇘A⇙⇙ y1)) ≥ length (red_rep A y1))" using N1 x1 y1 y1A x1A length_N1 sorry
    then have "length (red_rep A (x1 ⊗⇘ F⇘A⇙⇙ y1)) < length (red_rep A x1) ∨ length (red_rep A (x1 ⊗⇘ F⇘A⇙⇙ y1)) <  length (red_rep A y1)" by auto
    moreover have "(x1 ⊗⇘ F⇘A⇙⇙ y1) ∈ carrier (freegroup A)" using x1A y1A by (simp add: freegroup_is_group group.subgroupE(4) group.subgroup_self)
    ultimately have cases:"((x1 ⊗⇘ F⇘A⇙⇙ y1), x1) ∈ lex_L2_word A ∨ ((x1 ⊗⇘ F⇘A⇙⇙ y1), y1) ∈ lex_L2_word A" using x1A y1A length_lex by blast
    then have "x1 ∉ (union_inv (X (SG (freegroup A) H) A) A) ∨ y1 ∉ (union_inv (X (SG (freegroup A) H) A) A)"
  proof(cases "((x1 ⊗⇘F⇘A⇙⇙ y1), x1) ∈ lex_L2_word A")
    case True note xy_x = this
    then have subcases: "(x1,y1) ∈ lex_L2_word A ∨ (y1, x1) ∈ lex_L2_word A" using lex_total by auto
    then show ?thesis 
    proof (cases "(x1,y1) ∈ lex_L2_word A")
      case True
      then have xy_y:"((x1 ⊗⇘F⇘A⇙⇙ y1), y1) ∈ lex_L2_word A" using xy_x sorry (*transitivity*)
      then have "y1 ∉ X (SG (F⇘A⇙) H) A" using True assms H lex_cont2 by (metis mult_SG)
      moreover have "m_inv ((SG (F⇘A⇙) H)) y1 ∉ (X (SG (F⇘A⇙) H) A)" using True xy_y H assms lex_cont2_inv by (metis mult_SG)
      ultimately have "y1 ∉ (union_inv (X (SG (F⇘A⇙) H) A) A)" sorry
      then show ?thesis by meson
    next
      case False
      then have yx:"(y1, x1) ∈ lex_L2_word A" using subcases by auto
      then have "x1 ∉ X (SG (F⇘A⇙) H) A" using xy_x H assms lex_cont1 by (metis mult_SG)
      moreover have "m_inv ((SG (F⇘A⇙) H)) x1 ∉ (X (SG (F⇘A⇙) H) A)" using yx xy_x H assms lex_cont1_inv by (metis mult_SG)
      ultimately have "x1 ∉ (union_inv (X (SG (F⇘A⇙) H) A) A)" sorry
      then show ?thesis by blast
    qed
  next
    case False
    then have xyy:"((x1 ⊗⇘F⇘A⇙⇙ y1), y1) ∈ lex_L2_word A" using cases by auto
    then have subcases: "(x1,y1) ∈ lex_L2_word A ∨ (y1, x1) ∈ lex_L2_word A" using lex_total by auto
    then show ?thesis
    proof (cases "(x1,y1) ∈ lex_L2_word A")
      case True
      have "y1 ∉ X (SG (F⇘A⇙) H) A" using True xyy H assms lex_cont2 by (metis mult_SG)
      moreover have "m_inv ((SG (F⇘A⇙) H)) y1 ∉ (X (SG (F⇘A⇙) H) A)" using True xyy H assms lex_cont2_inv by (metis mult_SG)
      ultimately have "y1 ∉ (union_inv (X (SG (F⇘A⇙) H) A) A)" sorry
      then show ?thesis by meson
    next
      case False
      then have yx:"(y1, x1) ∈ lex_L2_word A" using subcases by simp
      then have xy_x:"((x1 ⊗⇘F⇘A⇙⇙ y1), x1) ∈ lex_L2_word A" using xyy sorry (*transitivity*)
      then have "x1 ∉ X (SG (F⇘A⇙) H) A" using yx H assms lex_cont1 by (metis mult_SG)
      moreover have "m_inv ((SG (F⇘A⇙) H)) x1 ∉ (X (SG (F⇘A⇙) H) A)" using yx xy_x H assms lex_cont1_inv by (metis mult_SG)
      ultimately have "x1 ∉ (union_inv (X (SG (F⇘A⇙) H) A) A)" sorry
      then show ?thesis by blast
     qed
   qed
    
  

