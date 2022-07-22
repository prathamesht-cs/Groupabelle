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

lemma assumes "H \<le> freegroup A" 
  shows "\<forall>x \<in> (red_rep A) ` (union_inv (X (SG (freegroup A) H) A) A). \<forall>y \<in> (red_rep A) ` (union_inv (X (SG (freegroup A) H) A) A). N1 x y"
  apply(rule ballI)+
proof-
  fix x y assume x: "x \<in> red_rep A ` union_inv (X (SG F\<^bsub>A\<^esub> H) A) A" and  y: "y \<in> red_rep A ` union_inv (X (SG F\<^bsub>A\<^esub> H) A) A"
  show "N1 x y"
  proof(rule ccontr)
    assume N1: "\<not> N1 x y"
(*Show x \<noteq> wordinverse y*)
    obtain x1 where x1:"red_rep A x1 = x \<and> x1 \<in> (union_inv (X (SG (freegroup A) H) A) A)" using x by blast
(*Show x1 and y1 belong to H*)
    then have x1A: "x1 \<in> carrier (freegroup A)" using assms union_inv_clos by blast
    obtain y1 where y1:"red_rep A y1 = y \<and> y1 \<in> (union_inv (X (SG (freegroup A) H) A) A)" using y by blast
    then have y1A: "y1 \<in> carrier (freegroup A)" using assms union_inv_clos by blast
    have "\<not> (length (red_rep A (x1 \<otimes>\<^bsub>F\<^bsub>A\<^esub>\<^esub> y1)) \<ge> length (red_rep A x1) \<and> length (red_rep A (x1 \<otimes>\<^bsub>F\<^bsub>A\<^esub>\<^esub> y1)) \<ge>  length (red_rep A y1))" using N1 x1 y1 y1A x1A length_N1 by auto
    then have "length (red_rep A (x1 \<otimes>\<^bsub>F\<^bsub>A\<^esub>\<^esub> y1)) < length (red_rep A x1) \<or> length (red_rep A (x1 \<otimes>\<^bsub>F\<^bsub>A\<^esub>\<^esub> y1)) <  length (red_rep A y1)" by auto
    moreover have "(x1 \<otimes>\<^bsub>F\<^bsub>A\<^esub>\<^esub> y1) \<in> carrier (freegroup A)" using x1A y1A by (simp add: freegroup_is_group group.subgroupE(4) group.subgroup_self)
    ultimately have cases:"((x1 \<otimes>\<^bsub>F\<^bsub>A\<^esub>\<^esub> y1), x1) \<in> lex_L2_word A \<or> ((x1 \<otimes>\<^bsub>F\<^bsub>A\<^esub>\<^esub> y1), y1) \<in> lex_L2_word A" using x1A y1A length_lex by blast
    then have "x1 \<notin> (union_inv (X (SG (freegroup A) H) A) A) \<or> y1 \<notin> (union_inv (X (SG (freegroup A) H) A) A)"
    proof(cases "((x1 \<otimes>\<^bsub>F\<^bsub>A\<^esub>\<^esub> y1), x1) \<in> lex_L2_word A")
(*subcase (x1,y1) \<in> lex_L2_word A or (y1,x1) \<in> lex_L2_word A*)
