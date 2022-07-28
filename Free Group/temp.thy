theory temp
  imports "NielsonSchreier"
begin

lemma trans_lex_word:"trans lex_word"
proof-
  have 1: "trans (r_gen - Id)" using r_gen strict_linear_order_on_def strict_linear_order_on_diff_Id well_order_on_def by blast
  show ?thesis by (simp add: 1 lenlex_transI lex_word_def)
qed

lemma trans_lex_L2_word': "trans (lex_L2_word' A)"
  unfolding lex_L2_word'_def using trans_lex_word 
  by (smt (z3) case_prodD case_prodI mem_Collect_eq trans_def trans_lex_prod)

lemma trans_nat_less: "trans nat_less"
  unfolding nat_less_def
  by (metis (no_types, lifting) less_than_iff mem_Collect_eq old.prod.case transD transI trans_less_than)

lemma trans_lex_L2_word: "trans (lex_L2_word A)"
  unfolding lex_L2_word_def using trans_lex_L2_word' trans_nat_less
  by (smt (z3) case_prodD case_prodI mem_Collect_eq trans_def trans_lex_prod)

lemma lex_L2_word_total_1:
  assumes "x \<in> carrier (freegroup A)"
      and "y \<in> carrier (freegroup A)"
      and "length (red_rep A x) = length (red_rep A y)"
    shows "\<not> (x,y) \<in> lex_L2_word A \<and> \<not> (y, x) \<in> lex_L2_word A \<Longrightarrow> red_rep A x = red_rep A y \<or> red_rep A x = wordinverse (red_rep A y)"
  using assms unfolding freegroup_def using lex_L2_word_total1 lex_L2_word_total2 eq_L2_eq rev_L2_inv
  by (metis partial_object.select_convs(1))

lemma lex_L2_word_total_2:
  assumes "x \<in> carrier (freegroup A)"
      and "y \<in> carrier (freegroup A)"
      and "length (red_rep A x) = length (red_rep A y)"
    shows "red_rep A x \<noteq> red_rep A y \<and> red_rep A x \<noteq> wordinverse (red_rep A y) \<Longrightarrow> (x,y) \<in> lex_L2_word A \<or> (y, x) \<in> lex_L2_word A"
  using assms lex_L2_word_total_1 by blast

lemma lex_total:
  assumes "x \<in> carrier (freegroup A)"
      and "y \<in> carrier (freegroup A)" 
      and "red_rep A x \<noteq> wordinverse (red_rep A y)"
      and "red_rep A x \<noteq> (red_rep A y)"
  shows "(x,y) \<in> lex_L2_word A \<or> (y, x) \<in> lex_L2_word A"
proof(cases "length (red_rep A x) > length (red_rep A y)")
  case True 
  then have "(y,x) \<in> lex_L2_word A" using assms(1) assms(2) length_lex by blast
  then show ?thesis by blast
next
  case False note F = this
  then show ?thesis
  proof(cases "length (red_rep A x) < length (red_rep A y)")
    case True
    then have "(x,y) \<in> lex_L2_word A" using assms(1) assms(2) length_lex by blast
    then show ?thesis by blast
  next
    case False
    then have "length (red_rep A x) = length (red_rep A y)" using F by simp
    then show ?thesis using assms(1,2,3,4) lex_L2_word_total_2 by blast
  qed
qed

lemma reduced_inv_eq_imp_nil: "xs = wordinverse xs \<Longrightarrow> reduced xs \<Longrightarrow> xs = []"
proof-
  assume xs:"xs = wordinverse xs " and rxs:"reduced xs"
  then show "xs = []"
  proof(cases "odd (length xs)")
    case True
      then have 1:"length xs > 0" using True by fastforce
      then have 2:"length xs > (length xs div 2)" by simp
      have "length (drop (length xs div 2) xs) = length xs - (length xs div 2) " by simp
      then have "length (drop (length xs div 2) xs) > 0" using 2 by simp
      then have "(drop (length xs div 2) xs) \<noteq> []" by fast
      moreover have "drop ((length xs div 2)+1) xs = tl (drop ((length xs div 2)) xs)" using drop_Suc tl_drop by (simp add: drop_Suc tl_drop)
      ultimately have  "[hd (drop (length xs div 2) xs)] @  drop ((length xs div 2)+1) xs = (drop (length xs div 2) xs)" by simp
      moreover have "xs = take (length xs div 2) xs @ drop (length xs div 2) xs" by simp
      ultimately have 3:"xs = take (length xs div 2) xs @ [hd (drop (length xs div 2) xs)] @ drop ((length xs div 2)+1) xs" by presburger
      then have "wordinverse xs = (map inverse) (rev (take (length xs div 2) xs @ [hd (drop (length xs div 2) xs)] @ drop ((length xs div 2)+1) xs))" using wordinverse_redef2 by auto
      then have "wordinverse xs = (map inverse) (rev (drop ((length xs div 2)+1) xs)  @ rev [hd (drop (length xs div 2) xs)] @ rev (take (length xs div 2) xs))" by simp
      then have "wordinverse xs = ((map inverse) (rev (drop ((length xs div 2)+1) xs))  @ [inverse (hd (drop (length xs div 2) xs))] @ (map inverse) (rev (take (length xs div 2) xs)))" by simp
      moreover have "length (take (length xs div 2) xs) = length ((map inverse)(rev (drop ((length xs div 2)+1) xs)))" using True drop_odd_length by fastforce 
      ultimately have "[inverse (hd (drop (length xs div 2) xs))] = [hd (drop (length xs div 2) xs)]" using 3 xs by (metis (no_types, lifting) append_eq_append_conv hd_append2 list.sel(1) not_Cons_self2)
      then show ?thesis by (metis inverse_neq list.sel(1))
  next
    case False
    then have "even (length xs)" by blast
    then have x:"xs = L xs @ R xs" unfolding left_subword_def right_subword_def by simp
    moreover then have "wordinverse xs = wordinverse (R xs) @ wordinverse (L xs)" using wordinverse_append by metis
    moreover have "length (L xs) = length (wordinverse (R xs))" using False even_R xs by force
    ultimately have "(L xs) = wordinverse (R xs)" by (metis append_eq_append_conv xs)
    then have "xs = wordinverse (R xs) @ (R xs)" using x by auto
    then have  "\<not> reduced xs \<or> xs = []" by (metis inverse_wordinverse reduced.simps(1) reduced_reln_eq)
    then show ?thesis using rxs by blast
  qed
qed

lemma square_length:
  assumes "x \<in> carrier (freegroup A)"
  shows "length (red_rep A (x \<otimes>\<^bsub> F\<^bsub>A\<^esub>\<^esub> x)) \<ge> length (red_rep A x)"
proof-
  let ?x = "(red_rep A x)"
  let ?xx = "(cancel2 ?x ?x)"
  have xx: "(x \<otimes>\<^bsub>F\<^bsub>A\<^esub>\<^esub> x) \<in> carrier (freegroup A)" by (simp add: assms(1) freegroup_is_group group.subgroupE(4) group.subgroup_self)
  have 1:"reduced ?x" using assms(1) red_rep_def red_rep_the unfolding freegroup_def by fastforce
  then have "((red_rep A x) @ (red_rep A x)) ~ ((a2 ?xx) @ (b2 ?xx))" by (metis cancel2_reln cancel2_the)
  then have "(red_rep A (x \<otimes>\<^bsub>F\<^bsub>A\<^esub>\<^esub> x)) ~ ((a2 ?xx) @ (b2 ?xx))" using assms mult_reln using reln.trans by blast
  moreover have "reduced ((a2 ?xx) @ (b2 ?xx))" by (simp add: "1" cancel2_the)
  moreover have "reduced (red_rep A (x \<otimes>\<^bsub>F\<^bsub>A\<^esub>\<^esub> x))" using xx red_rep_def red_rep_the unfolding freegroup_def by fastforce
  ultimately have 3: "(red_rep A (x \<otimes>\<^bsub>F\<^bsub>A\<^esub>\<^esub> x)) = ((a2 ?xx) @ (b2 ?xx))" by (simp add: reduced_reln_eq)
  have A:"?x = (a2 ?xx) @ (p2 ?xx)" using 1 by (simp add: cancel2_the)
  then have rp:"reduced (p2 ?xx)" using "1" reduced_leftappend by metis
  have B:"?x =  wordinverse (p2 ?xx) @ (b2 ?xx)" using 1 by (simp add: cancel2_the)
  have C:"length (p2 ?xx) = length (wordinverse (p2 ?xx))" using length_wordinverse by blast
  then have D:"length (a2 ?xx) = length (b2 ?xx)" using A B by (metis add_diff_cancel_left' add_diff_cancel_right' length_append)
  show ?thesis
  proof(cases "length (b2 ?xx) > length (p2 ?xx)")
    case True
    then have "length ((a2 ?xx) @ (p2 ?xx)) \<le> length ((a2 ?xx) @ (b2 ?xx))" by simp
    then show ?thesis using 3 A by auto
  next
    case False
    then have F:"length (b2 ?xx) \<le> length (p2 ?xx)" by auto
    then show ?thesis
    proof(cases "length (b2 ?xx) = length (p2 ?xx)")
      case True
      then have "?x = wordinverse (p2 ?xx) @ (p2 ?xx)" by (metis A B D append_eq_append_conv)
      then have "\<not> reduced ?x \<or> ?x = []"  by (metis inverse_wordinverse reduced.simps(1) reduced_reln_eq)
      then show ?thesis by (simp add: 1)
    next
      case False
      then have cont:"length (b2 ?xx) < length (p2 ?xx)" using F by auto
      then obtain c where c:"?x = (a2 ?xx) @ c @ (b2 ?xx)" using A B by (metis D overlaprightexist)
      then have pc:"p2 ?xx = (c @ b2 ?xx)" using A by (metis same_append_eq)
      moreover have "wordinverse (p2 ?xx) = (a2 ?xx) @ c" using c B by (metis append.assoc append_same_eq)
      ultimately have "(c @ b2 ?xx) = (wordinverse c) @ (wordinverse (a2 ?xx))" by (simp add: wordinverse_append wordinverse_symm)
      then have "c = wordinverse c" using append_eq_append_conv length_wordinverse by fast
      moreover have "reduced c" using rp pc using reduced_rightappend by auto
      ultimately have "c = []" using reduced_inv_eq_imp_nil by blast
      then have "length (b2 ?xx) = length (p2 ?xx)" using pc by auto
      then show ?thesis using cont by auto
    qed
  qed
qed

lemma neq_N1:
  assumes "x \<in> carrier (freegroup A)" 
    and " y \<in> carrier (freegroup A)"
    and "length (red_rep A (x \<otimes>\<^bsub> F\<^bsub>A\<^esub>\<^esub> y)) < length (red_rep A x) \<or> length (red_rep A (x \<otimes>\<^bsub> F\<^bsub>A\<^esub>\<^esub> y)) <  length (red_rep A y)"
  shows "red_rep A x \<noteq> red_rep A y"
proof(rule ccontr)
  assume "\<not> red_rep A x \<noteq> red_rep A y"
  then have a: "red_rep A x = red_rep A y" by blast
  then have "x = y" using red_rep_the assms(1,2) unfolding freegroup_def by (metis partial_object.select_convs(1))
  then have "length (red_rep A (x \<otimes>\<^bsub> F\<^bsub>A\<^esub>\<^esub> y)) \<ge> length (red_rep A x) \<and> length (red_rep A (x \<otimes>\<^bsub> F\<^bsub>A\<^esub>\<^esub> y)) \<ge>  length (red_rep A y)" using assms(1) square_length by auto
  then show False using assms(3) by auto
qed

lemma SG_subgroup:
  assumes "H \<le> (freegroup A)"
  shows "group (SG (freegroup A) H)"
  unfolding SG_def using freegroup_is_group assms group.subgroup_imp_group by blast

lemma notin_union_inv:
  assumes "H \<le> (freegroup A)" "x \<notin> S" "m_inv (SG (freegroup A) H) x \<notin> S" "S \<subseteq> H"
  shows "x \<notin> union_inv S A"
proof(rule ccontr)
  assume "\<not> x \<notin> union_inv S A"
  then have "x \<in> union_inv S A"  by blast
  then have "x \<in> S \<or> x \<in> m_inv F\<^bsub>A\<^esub> ` S" unfolding union_inv_def by auto
  then have c:"x \<in> S \<or> x \<in> m_inv (SG (freegroup A) H) ` S" using inv_SG freegroup_is_group assms(1,4) by (metis (no_types, lifting) image_cong subset_eq)
  show False
  proof(cases "x \<in> S")
    case True
    then show ?thesis using assms(2) by blast
  next
    case False
    then have "x \<in> m_inv (SG (freegroup A) H) ` S" using c by blast
    then obtain y where y:"x = m_inv (SG (freegroup A) H) y \<and> y \<in> S" by blast
    moreover then have "y \<in> H" using assms(4) by auto
    moreover then have "y \<in> carrier (SG (freegroup A) H)" unfolding SG_def by simp
    ultimately have "y = m_inv (SG (freegroup A) H) x" using assms(1) by (simp add: SG_subgroup)
    then show ?thesis using y assms(3) by blast
  qed
qed

lemma N1:
  assumes "H \<le> freegroup A" 
  shows "\<forall>x \<in> (red_rep A) ` (union_inv (X (SG (freegroup A) H) A) A). \<forall>y \<in> (red_rep A) ` (union_inv (X (SG (freegroup A) H) A) A). N1 x y"
  apply(rule ballI)+
proof-
  fix x y assume x: "x \<in> red_rep A ` union_inv (X (SG F\<^bsub>A\<^esub> H) A) A" and  y: "y \<in> red_rep A ` union_inv (X (SG F\<^bsub>A\<^esub> H) A) A"
  show "N1 x y"
  proof(rule ccontr)
    assume N1: "\<not> N1 x y"
    then have nxiy:"x \<noteq> wordinverse y" using N1_def by auto
    obtain x1 where x1:"red_rep A x1 = x \<and> x1 \<in> (union_inv (X (SG (freegroup A) H) A) A)" using x by blast
    then have x1A: "x1 \<in> carrier (freegroup A)" using assms union_inv_clos by blast
    obtain y1 where y1:"red_rep A y1 = y \<and> y1 \<in> (union_inv (X (SG (freegroup A) H) A) A)" using y by blast
    then have y1A: "y1 \<in> carrier (freegroup A)" using assms union_inv_clos by blast
    have H:"x1 \<in> H \<and> y1 \<in> H" using assms x1 x1A y1 using union_inv_sub_H by blast
    have "\<not> (length (red_rep A (x1 \<otimes>\<^bsub> F\<^bsub>A\<^esub>\<^esub> y1)) \<ge> length (red_rep A x1) \<and> length (red_rep A (x1 \<otimes>\<^bsub> F\<^bsub>A\<^esub>\<^esub> y1)) \<ge> length (red_rep A y1))" using N1 x1 y1 y1A x1A length_N1 by blast
    then have t:"length (red_rep A (x1 \<otimes>\<^bsub> F\<^bsub>A\<^esub>\<^esub> y1)) < length (red_rep A x1) \<or> length (red_rep A (x1 \<otimes>\<^bsub> F\<^bsub>A\<^esub>\<^esub> y1)) <  length (red_rep A y1)" by auto
    moreover have "(x1 \<otimes>\<^bsub> F\<^bsub>A\<^esub>\<^esub> y1) \<in> carrier (freegroup A)" using x1A y1A by (simp add: freegroup_is_group group.subgroupE(4) group.subgroup_self)
    ultimately have cases:"((x1 \<otimes>\<^bsub> F\<^bsub>A\<^esub>\<^esub> y1), x1) \<in> lex_L2_word A \<or> ((x1 \<otimes>\<^bsub> F\<^bsub>A\<^esub>\<^esub> y1), y1) \<in> lex_L2_word A" using x1A y1A length_lex by blast
    have nxy:"x \<noteq> y" using neq_N1 t x1A y1A x1 y1 by auto
    have XH: "(X (SG F\<^bsub>A\<^esub> H) A) \<subseteq> H" unfolding X_def SG_def by simp
    have "x1 \<notin> (union_inv (X (SG (freegroup A) H) A) A) \<or> y1 \<notin> (union_inv (X (SG (freegroup A) H) A) A)"
  proof(cases "((x1 \<otimes>\<^bsub>F\<^bsub>A\<^esub>\<^esub> y1), x1) \<in> lex_L2_word A")
    case True note xy_x = this
    then have subcases: "(x1,y1) \<in> lex_L2_word A \<or> (y1, x1) \<in> lex_L2_word A" using lex_total nxy nxiy x1 y1 x1A y1A  by auto
    then show ?thesis 
    proof (cases "(x1,y1) \<in> lex_L2_word A")
      case True
      then have xy_y:"((x1 \<otimes>\<^bsub>F\<^bsub>A\<^esub>\<^esub> y1), y1) \<in> lex_L2_word A" using xy_x trans_lex_L2_word unfolding trans_def by blast
      then have "y1 \<notin> X (SG (F\<^bsub>A\<^esub>) H) A" using True assms H lex_cont2 by (metis mult_SG)
      moreover have "m_inv ((SG (F\<^bsub>A\<^esub>) H)) y1 \<notin> (X (SG (F\<^bsub>A\<^esub>) H) A)" using True xy_y H assms lex_cont2_inv by (metis mult_SG)
      ultimately have "y1 \<notin> (union_inv (X (SG (F\<^bsub>A\<^esub>) H) A) A)" using notin_union_inv XH assms by blast
      then show ?thesis by meson
    next
      case False
      then have yx:"(y1, x1) \<in> lex_L2_word A" using subcases by auto
      then have "x1 \<notin> X (SG (F\<^bsub>A\<^esub>) H) A" using xy_x H assms lex_cont1 by (metis mult_SG)
      moreover have "m_inv ((SG (F\<^bsub>A\<^esub>) H)) x1 \<notin> (X (SG (F\<^bsub>A\<^esub>) H) A)" using yx xy_x H assms lex_cont1_inv by (metis mult_SG)
      ultimately have "x1 \<notin> (union_inv (X (SG (F\<^bsub>A\<^esub>) H) A) A)" using notin_union_inv XH assms by blast
      then show ?thesis by blast
    qed
  next
    case False
    then have xyy:"((x1 \<otimes>\<^bsub>F\<^bsub>A\<^esub>\<^esub> y1), y1) \<in> lex_L2_word A" using cases by auto
    then have subcases: "(x1,y1) \<in> lex_L2_word A \<or> (y1, x1) \<in> lex_L2_word A" using lex_total nxy nxiy x1 y1 x1A y1A by auto
    then show ?thesis
    proof (cases "(x1,y1) \<in> lex_L2_word A")
      case True
      have "y1 \<notin> X (SG (F\<^bsub>A\<^esub>) H) A" using True xyy H assms lex_cont2 by (metis mult_SG)
      moreover have "m_inv ((SG (F\<^bsub>A\<^esub>) H)) y1 \<notin> (X (SG (F\<^bsub>A\<^esub>) H) A)" using True xyy H assms lex_cont2_inv by (metis mult_SG)
      ultimately have "y1 \<notin> (union_inv (X (SG (F\<^bsub>A\<^esub>) H) A) A)" using notin_union_inv XH assms by blast
      then show ?thesis by meson
    next
      case False
      then have yx:"(y1, x1) \<in> lex_L2_word A" using subcases by simp
      then have xy_x: "((x1 \<otimes>\<^bsub>F\<^bsub>A\<^esub>\<^esub> y1), x1) \<in> lex_L2_word A" using xyy trans_lex_L2_word unfolding trans_def by blast
      then have "x1 \<notin> X (SG (F\<^bsub>A\<^esub>) H) A" using yx H assms lex_cont1 by (metis mult_SG)
      moreover have "m_inv ((SG (F\<^bsub>A\<^esub>) H)) x1 \<notin> (X (SG (F\<^bsub>A\<^esub>) H) A)" using yx xy_x H assms lex_cont1_inv by (metis mult_SG)
      ultimately have "x1 \<notin> (union_inv (X (SG (F\<^bsub>A\<^esub>) H) A) A)" using notin_union_inv XH assms by blast
      then show ?thesis by blast
     qed
   qed
   then show False using y1 x1 by blast
 qed
qed
    