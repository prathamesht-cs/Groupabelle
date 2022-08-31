theory temp
  imports "NielsonSchreier"
begin

lemma N2:
  assumes "H \<le> freegroup A" 
    and "\<forall>x \<in> (red_rep A) ` (union_inv (X (SG (freegroup A) H) A) A). N0 x"
    and "\<forall>x \<in> (red_rep A) ` (union_inv (X (SG (freegroup A) H) A) A). \<forall>y \<in> (red_rep A) ` (union_inv (X (SG (freegroup A) H) A) A). N1 x y"
  shows "\<forall>x \<in> (red_rep A) ` (union_inv (X (SG (freegroup A) H) A) A). \<forall>y \<in> (red_rep A) ` (union_inv (X (SG (freegroup A) H) A) A). \<forall>z \<in> (red_rep A) ` (union_inv (X (SG (freegroup A) H) A) A). N2 x y z"
  apply(rule ballI)+
proof-
  fix x y z assume x: "x \<in> red_rep A ` union_inv (X (SG F\<^bsub>A\<^esub> H) A) A" and  y: "y \<in> red_rep A ` union_inv (X (SG F\<^bsub>A\<^esub> H) A) A" and z:"z \<in> red_rep A ` union_inv (X (SG F\<^bsub>A\<^esub> H) A) A"
  show "N2 x y z"
  proof(rule ccontr)
    assume N2: "\<not> N2 x y z"
    then have invxyz:"x \<noteq> wordinverse y \<and> y \<noteq> wordinverse z" using N2_def by auto
    obtain x1 where x1:"red_rep A x1 = x \<and> x1 \<in> (union_inv (X (SG (freegroup A) H) A) A)" using x by blast
    moreover then have x1A: "x1 \<in> carrier (freegroup A)" using assms union_inv_clos by blast
    ultimately have rx:"reduced x" using red_rep_the unfolding red_rep_def freegroup_def by auto
    obtain y1 where y1:"red_rep A y1 = y \<and> y1 \<in> (union_inv (X (SG (freegroup A) H) A) A)" using y by blast
    moreover then have y1A: "y1 \<in> carrier (freegroup A)" using assms union_inv_clos by blast
    ultimately have ry:"reduced y" using red_rep_the unfolding red_rep_def freegroup_def by auto
    obtain z1 where z1:"red_rep A z1 = z \<and> z1 \<in> (union_inv (X (SG (freegroup A) H) A) A)" using z by blast
    moreover then have z1A: "z1 \<in> carrier (freegroup A)" using assms union_inv_clos by blast
    ultimately have rz:"reduced z" using red_rep_the unfolding red_rep_def freegroup_def by auto
    have H:"x1 \<in> H \<and> y1 \<in> H \<and> z1 \<in> H" using assms x1 x1A y1 z1 z1A using union_inv_sub_H by blast
    have b:"(b3 (\<oslash>\<^bsub>3\<^esub> x y z) = [])" using N2 unfolding N2_def by fastforce
    then have xyz:"x = a3 (\<oslash>\<^bsub>3\<^esub> x y z) @ p3 (\<oslash>\<^bsub>3\<^esub> x y z) \<and>
           y = wordinverse (p3 (\<oslash>\<^bsub>3\<^esub> x y z)) @ q3 (\<oslash>\<^bsub>3\<^esub> x y z) \<and>
           z = wordinverse (q3 (\<oslash>\<^bsub>3\<^esub> x y z)) @ c3 (\<oslash>\<^bsub>3\<^esub> x y z) \<and>
           reduced (a3 (\<oslash>\<^bsub>3\<^esub> x y z) @ q3 (\<oslash>\<^bsub>3\<^esub> x y z)) \<and>
           reduced (wordinverse (p3 (\<oslash>\<^bsub>3\<^esub> x y z)) @ c3 (\<oslash>\<^bsub>3\<^esub> x y z))" using assms(3) rx ry rz x y z cancel3_the invxyz by (metis append.left_neutral)
    then have neq:"(p3 (\<oslash>\<^bsub>3\<^esub> x y z)) \<noteq> q3 (\<oslash>\<^bsub>3\<^esub> x y z)" using y assms(2) ry by (metis FreeGroupMain.inverse_wordinverse N0_def reduced.simps(1) reduced_reln_eq)
    have pa:"length (p3 (\<oslash>\<^bsub>3\<^esub> x y z)) \<le> length (a3 (\<oslash>\<^bsub>3\<^esub> x y z))" using assms(3) xyz rx ry rz x y z invxyz cancel2_the cancel_a2_a3 unfolding N1_def by (metis (no_types, lifting)  same_append_eq)
    have "length (p2 (y \<oslash>\<^bsub>2\<^esub> z)) \<le> length (b2 (y \<oslash>\<^bsub>2\<^esub> z))" using assms(3) ry rz y z xyz invxyz cancel2_the N1_def by blast
    then have qc: "length (q3 (\<oslash>\<^bsub>3\<^esub> x y z)) \<le> length (c3 (\<oslash>\<^bsub>3\<^esub> x y z))" using assms(3) xyz rx ry rz x y z invxyz cancel_b2_c3 cancel_p2_q3 by (metis (no_types, lifting))
    have "length (p2 (x \<oslash>\<^bsub>2\<^esub> y)) \<le> length (b2 (x \<oslash>\<^bsub>2\<^esub> y))"  using assms(3) rx ry x y xyz invxyz cancel2_the N1_def by blast
    then have pq: "length (p3 (\<oslash>\<^bsub>3\<^esub> x y z)) \<le> length (q3 (\<oslash>\<^bsub>3\<^esub> x y z))" using assms(3) xyz rx ry rz x y z invxyz cancel_b2_bq3 cancel_p2_p3 b by (metis append.left_neutral)
    have "length (p2 (y \<oslash>\<^bsub>2\<^esub> z)) \<le> length (b2 (y \<oslash>\<^bsub>2\<^esub> z))"  using assms(3) ry rz y z xyz invxyz cancel2_the N1_def by blast
    then have qp: "length (q3 (\<oslash>\<^bsub>3\<^esub> x y z)) \<le> length (p3 (\<oslash>\<^bsub>3\<^esub> x y z))" using assms(3) xyz rx ry rz x y z invxyz cancel_p2_q3 b by (metis N1_def append_Nil2 cancel_a2_pb3 length_wordinverse)
    then have leq:"length (q3 (\<oslash>\<^bsub>3\<^esub> x y z)) = length (p3 (\<oslash>\<^bsub>3\<^esub> x y z))" using pq by simp
    then have pc: "length (p3 (\<oslash>\<^bsub>3\<^esub> x y z)) \<le> length (c3 (\<oslash>\<^bsub>3\<^esub> x y z))" using qc by simp
    have qa: "length (q3 (\<oslash>\<^bsub>3\<^esub> x y z)) \<le> length (a3 (\<oslash>\<^bsub>3\<^esub> x y z))" using pa leq by simp
    have xneqy: "x \<noteq> y" using xyz neq by (metis append_eq_append_conv leq)
    have yneqz: "y \<noteq> z" using xyz neq leq neq_imp_invneq by (metis append_eq_conv_conj length_wordinverse)
    have x1y1in:"x1 \<otimes>\<^bsub>freegroup A\<^esub> y1 \<in> carrier (freegroup A)" by (meson H assms(1) subgroup.m_closed subgroup.mem_carrier)
    moreover have "(a3 (\<oslash>\<^bsub>3\<^esub> x y z) @ p3 (\<oslash>\<^bsub>3\<^esub> x y z) @ wordinverse (p3 (\<oslash>\<^bsub>3\<^esub> x y z)) @ q3 (\<oslash>\<^bsub>3\<^esub> x y z)) ~ (a3 (\<oslash>\<^bsub>3\<^esub> x y z) @ q3 (\<oslash>\<^bsub>3\<^esub> x y z)) \<and> x1 \<otimes>\<^bsub>freegroup A\<^esub> y1 = reln_tuple \<langle>A\<rangle> `` {a3 (\<oslash>\<^bsub>3\<^esub> x y z) @ p3 (\<oslash>\<^bsub>3\<^esub> x y z) @ wordinverse (p3 (\<oslash>\<^bsub>3\<^esub> x y z)) @ q3 (\<oslash>\<^bsub>3\<^esub> x y z)}"
      unfolding freegroup_def by (metis (no_types, lifting) append_assoc cancel2_reln freegroup_def monoid.select_convs(1) partial_object.select_convs(1) proj_append_wd red_rep_the redrep_in x1 x1A xyz y1 y1A)
    ultimately have "x1 \<otimes>\<^bsub>freegroup A\<^esub> y1 = reln_tuple \<langle>A\<rangle> `` {a3 (\<oslash>\<^bsub>3\<^esub> x y z)  @ q3 (\<oslash>\<^bsub>3\<^esub> x y z)}" sorry
    then have x1y1:"red_rep A (x1 \<otimes>\<^bsub>freegroup A\<^esub> y1) = (a3 (\<oslash>\<^bsub>3\<^esub> x y z) @ q3 (\<oslash>\<^bsub>3\<^esub> x y z))" using x1y1in unfolding freegroup_def using red_repI xyz by auto
    have y1z1in:"y1 \<otimes>\<^bsub>freegroup A\<^esub> z1 \<in> carrier (freegroup A)" by (meson H assms(1) subgroup.m_closed subgroup.mem_carrier)
    moreover have "(wordinverse (p3 (\<oslash>\<^bsub>3\<^esub> x y z)) @ q3 (\<oslash>\<^bsub>3\<^esub> x y z) @ wordinverse (q3 (\<oslash>\<^bsub>3\<^esub> x y z)) @ c3 (\<oslash>\<^bsub>3\<^esub> x y z))  ~ (wordinverse (p3 (\<oslash>\<^bsub>3\<^esub> x y z)) @ c3 (\<oslash>\<^bsub>3\<^esub> x y z)) \<and> y1 \<otimes>\<^bsub>freegroup A\<^esub> z1 = reln_tuple \<langle>A\<rangle> `` {(wordinverse (p3 (\<oslash>\<^bsub>3\<^esub> x y z)) @ q3 (\<oslash>\<^bsub>3\<^esub> x y z) @ wordinverse (q3 (\<oslash>\<^bsub>3\<^esub> x y z)) @ c3 (\<oslash>\<^bsub>3\<^esub> x y z))}"
      unfolding freegroup_def 
      by (metis append_assoc cancel2_reln freegroup_def monoid.select_convs(1) partial_object.select_convs(1) proj_append_wd red_rep_the redrep_in xyz y1 y1A z1 z1A)
    ultimately have "y1 \<otimes>\<^bsub>freegroup A\<^esub> z1 = reln_tuple \<langle>A\<rangle> `` {(wordinverse (p3 (\<oslash>\<^bsub>3\<^esub> x y z)) @ c3 (\<oslash>\<^bsub>3\<^esub> x y z))}" sorry
    then have y1z1:"red_rep A (y1 \<otimes>\<^bsub>freegroup A\<^esub> z1) = (wordinverse (p3 (\<oslash>\<^bsub>3\<^esub> x y z)) @ c3 (\<oslash>\<^bsub>3\<^esub> x y z))" using y1z1in unfolding freegroup_def using red_repI xyz  by auto
    have ineq:"wordinverse (p3 (\<oslash>\<^bsub>3\<^esub> x y z)) \<noteq> wordinverse (q3 (\<oslash>\<^bsub>3\<^esub> x y z))" by (simp add: neq neq_imp_invneq) 
    then have cases:"(wordinverse (p3 (\<oslash>\<^bsub>3\<^esub> x y z)), wordinverse (q3 (\<oslash>\<^bsub>3\<^esub> x y z))) \<in> lex_word \<or> (wordinverse (q3 (\<oslash>\<^bsub>3\<^esub> x y z)), wordinverse ( p3 (\<oslash>\<^bsub>3\<^esub> x y z))) \<in> lex_word" unfolding lex_word_def using lex_word_def lex_word_total by auto
    show False
    proof(cases "(wordinverse (p3 (\<oslash>\<^bsub>3\<^esub> x y z)), wordinverse (q3 (\<oslash>\<^bsub>3\<^esub> x y z))) \<in> lex_word")
      case True
      let ?p = "wordinverse (p3 (\<oslash>\<^bsub>3\<^esub> x y z))"
      let ?q = "wordinverse (q3 (\<oslash>\<^bsub>3\<^esub> x y z))"
      let ?c = "c3 (\<oslash>\<^bsub>3\<^esub> x y z)"
      have "red_rep A z1 = ?q @ ?c"  using xyz z1 by force
      moreover have "red_rep A (y1 \<otimes>\<^bsub>freegroup A\<^esub> z1) = ?p @ ?c" by (simp add: y1z1)
      moreover have "length ?p = length ?q" using leq by (metis length_wordinverse)
      moreover have "?p \<noteq> ?q" using ineq .
      moreover have "length ?p \<le> length ?c" by (metis length_wordinverse pc)
      moreover have "length ?q \<le> length ?c" by (metis length_wordinverse qc)
      moreover have "red_rep A (y1 \<otimes>\<^bsub>freegroup A\<^esub> z1) \<noteq> []" using y1z1 FreeGroupMain.wordinverse_symm invxyz xyz by fastforce
      moreover have "red_rep A z1 \<noteq> []" using N0_def assms(2) z1 by auto
      ultimately have cont:"((y1 \<otimes>\<^bsub>freegroup A\<^esub> z1), z1) \<in> lex_L2_word A" using True z1A y1z1in xyz z three_point_six[of "z1" "A" "(y1 \<otimes>\<^bsub>freegroup A\<^esub> z1)" "?p" "?c" "?q"] by (metis N0_def three_point_six)
      have subcases:"(y1, z1) \<in> lex_L2_word A \<or> (z1, y1) \<in> lex_L2_word A" by (simp add: invxyz lex_total y1 y1A yneqz z1 z1A)      
      then show ?thesis
      proof(cases "(y1, z1) \<in> lex_L2_word A")
        case True
        then have "z1 \<notin> X (SG (F\<^bsub>A\<^esub>) H) A" using lex_cont2[of "y1" "z1" "A" "H"] H assms(1) cont by (metis mult_SG)
        moreover have "inv\<^bsub>SG F\<^bsub>A\<^esub> H\<^esub> z1 \<notin> X (SG (F\<^bsub>A\<^esub>) H) A"  using lex_cont2_inv[of "y1" "z1" "A" "H"] H assms(1) cont True by (metis mult_SG)
        moreover have "X (SG (F\<^bsub>A\<^esub>) H) A \<subseteq> H"  unfolding X_def SG_def by simp
        ultimately have "z1 \<notin> (union_inv (X (SG (freegroup A) H) A) A)" using notin_union_inv[of "H" "A" "z1" "X (SG F\<^bsub>A\<^esub> H) A"] assms(1) by simp
        then show ?thesis using z1 by blast
      next
        case False
        then have F:"(z1, y1) \<in> lex_L2_word A" using subcases by blast
        then have "y1 \<notin> X (SG (F\<^bsub>A\<^esub>) H) A" using lex_cont1[of "z1" "y1" "A" "H"] H assms(1) cont sledgehammer
        moreover have "inv\<^bsub>SG F\<^bsub>A\<^esub> H\<^esub> y1 \<notin> X (SG (F\<^bsub>A\<^esub>) H) A" (* using lex_cont1_inv[of "z1" "y1" "A" "H"] H assms(1) cont F*) sorry
        moreover have "X (SG (F\<^bsub>A\<^esub>) H) A \<subseteq> H"  unfolding X_def SG_def by simp
        ultimately have "y1 \<notin> (union_inv (X (SG (freegroup A) H) A) A)" using notin_union_inv[of "H" "A" "y1" "X (SG F\<^bsub>A\<^esub> H) A"] assms(1) by simp
        then show ?thesis using y1 by blast
      qed
    next
      case False
      then show ?thesis sorry
    qed


    
