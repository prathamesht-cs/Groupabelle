theory temp
  imports "NielsonSchreier"
begin

lemma min_L2_inv:
  assumes "x \<in> carrier (freegroup A) \<and> xy \<in> carrier (freegroup A)"
  shows "min lex_word (L2(red_rep A x)) = min lex_word( L2(wordinverse (red_rep A x)))" unfolding left_tuple_def min.simps by (metis FreeGroupMain.wordinverse_of_wordinverse lex_word_total wf_lex_word wf_not_sym)

lemma length_eq:
  assumes "x = a@c" "y = b@c" "length a = length b"
  shows "length x = length y" using assms by simp

lemma lex_word_one: "(x,y) \<in> lex_word \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> (y,x) \<in> lex_word"
  by (metis wf_lex_word wf_not_sym)

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

lemma L_inv_eq: "L(xs) = L(wordinverse xs) \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> \<not> (reduced xs)"
proof-
  assume xs: "L(xs) = L(wordinverse xs)" and rxs:"xs \<noteq> []"
  then show "\<not> (reduced xs)"
  proof-
    have "L2 xs = \<down> (L2 xs)" unfolding left_tuple_def rev_tuple.simps using xs by simp
    moreover have "length xs = length xs" by simp
    ultimately have "xs = wordinverse xs" using rev_L2_inv by force
    then show ?thesis using rxs reduced_inv_eq_imp_nil by blast
  qed
qed

lemma lex_word_init:
  "(x, y) \<in> lex_word \<Longrightarrow> (length a = length b) \<Longrightarrow> (x@a, y@b) \<in> lex_word"
  unfolding lex_word_def by (simp add: lenlex_append1)

lemma left_includes: "a = x @ y \<Longrightarrow> length x \<le> length y \<Longrightarrow> \<exists>z. L a = x @ z"
  unfolding left_subword_def by (simp add: take_append take_length)

lemma take_bigger_half:"length a \<ge> length  b \<Longrightarrow> take (((length (a@b)+1) div 2)) (a@b) = take (((length (a@b)+1) div 2)) a"
  by simp
  
lemma lex_word_rightappend:
  assumes "(x,y) \<in> lex_word"
  shows "(x@c, y@c) \<in> lex_word"
  using lex_word_def lenlex_def assms lenlex_append1 by blast

lemma L_inverse_eq:
  assumes "x = (p @ (wordinverse a))"
          and "y = (q @ (wordinverse a))"
          and "length p = length q"
          and "length p \<le> length (wordinverse a)"
          and "length q \<le> length (wordinverse a)"
        shows "L (wordinverse x) = L (wordinverse y)"
proof-
  have "wordinverse x = a @ wordinverse p" using assms(1) by (metis FreeGroupMain.wordinverse_append FreeGroupMain.wordinverse_of_wordinverse)
  moreover have "length (wordinverse  p) \<le> length a" by (metis assms(4) length_wordinverse)
  ultimately have 1:"L (wordinverse x) = take (((length (wordinverse x)+1) div 2)) a" unfolding left_subword_def using take_bigger_half by auto
  have "wordinverse y = a @ wordinverse q" using assms(2) by (metis FreeGroupMain.wordinverse_append FreeGroupMain.wordinverse_of_wordinverse)
  moreover have "length (wordinverse  q) \<le> length a" by (metis assms(5) length_wordinverse)
  ultimately have "L (wordinverse y) = take (((length (wordinverse y)+1) div 2)) a" unfolding left_subword_def using take_bigger_half by auto
  then show ?thesis using 1 assms(3) length_wordinverse by (metis assms(1) assms(2) length_append)
qed

lemma neq_left_neq: "p \<noteq> q \<Longrightarrow> length p = length q \<Longrightarrow> length p \<le> length r \<Longrightarrow> L (p @ r) \<noteq> L (q @ r)"
  unfolding left_subword_def by simp

lemma lex_L2_inv2:
  assumes "(y,x) \<in> lex_L2_word A"
  shows "(inv\<^bsub>freegroup A\<^esub> y, x) \<in> lex_L2_word A"
proof-
  have 1:"y \<in> (\<langle>A\<rangle> // (reln_tuple \<langle>A\<rangle>))" using assms(1) unfolding lex_L2_word_def by blast
  then obtain invx where "invx = (inv\<^bsub>freegroup A\<^esub> y)" using freegroup_is_group by simp
  then have x:"(inv\<^bsub>freegroup A\<^esub> y) \<in> (\<langle>A\<rangle> // (reln_tuple \<langle>A\<rangle>))" using m_inv_def[of "freegroup A" "y"] freegroup_def
    by (metis (no_types, lifting) freegroup_is_group group.inv_closed partial_object.select_convs(1) 1)
  have y: "x \<in> (\<langle>A\<rangle> // (reln_tuple \<langle>A\<rangle>))" using assms(1) unfolding lex_L2_word_def by blast
  have 2:"(length (red_rep A y) < length (red_rep A x)) \<or> ((length (red_rep A y) = length (red_rep A x) \<and> (y,x) \<in> lex_L2_word' A))" 
    using nat_less_def assms unfolding lex_L2_word_def lex_prod_def by fastforce
  then show ?thesis 
  proof(cases "(length (red_rep A y) < length (red_rep A x))")
    case True
    then have "length (wordinverse (red_rep A y)) < length (red_rep A x)" using length_wordinverse by metis
    then have "length (red_rep A (inv\<^bsub>freegroup A\<^esub> y)) < length (red_rep A x)" using 1 red_rep_inv by metis
    then show ?thesis using x y by (simp add: lex_L2_word_def nat_less_def)
  next
    case False
    then have 3:"((length (red_rep A y) = length (red_rep A x) \<and> (y,x) \<in> lex_L2_word' A))" using 2 by blast
    then have 4:"length (red_rep A (inv\<^bsub>freegroup A\<^esub> y)) = length (red_rep A x)" using 1 red_rep_inv by (metis length_wordinverse)
    then have "((\<lambda>x. (min lex_word (L2 (red_rep A x)), max lex_word (L2 (red_rep A x)))) y 
                , (\<lambda>x. (min lex_word (L2 (red_rep A x)), max lex_word (L2 (red_rep A x)))) x) \<in> (lex_word <*lex*> lex_word)" using 3 unfolding lex_L2_word'_def by fastforce
    then have 5:"((min lex_word (L2 (red_rep A y))), (min lex_word (L2 (red_rep A x)))) \<in> lex_word \<or> 
               (min lex_word (L2 (red_rep A y))) = (min lex_word (L2 (red_rep A x))) \<and> 
               (max lex_word (L2 (red_rep A y)), max lex_word (L2 (red_rep A x))) \<in> lex_word" using lex_prod_def[of "lex_word" "lex_word"] by simp
    have "L2 (wordinverse (red_rep A y)) = (snd (L2 (red_rep A y)), fst (L2 (red_rep A y)))" using L2_wordinv by blast
    then have L2_winv:"min lex_word (L2 (red_rep A y)) = min lex_word (L2 (wordinverse (red_rep A y))) \<and>
                       max lex_word (L2 (red_rep A y)) = max lex_word (L2 (wordinverse (red_rep A y)))" using  wf_lex_word min.simps  by (metis (no_types, lifting) lex_word_total max.simps prod.exhaust_sel wf_asym)
    then have "((min lex_word (L2 (wordinverse(red_rep A y)))), (min lex_word (L2 (red_rep A x)))) \<in> lex_word \<or> 
               (min lex_word (L2 (wordinverse(red_rep A y)))) = (min lex_word (L2 (red_rep A x))) \<and> 
               (max lex_word (L2 (wordinverse(red_rep A y))), max lex_word (L2 (red_rep A x))) \<in> lex_word" using 5 by auto   
    then have "((min lex_word (L2 (red_rep A(inv\<^bsub>freegroup A\<^esub> y)))), (min lex_word (L2 (red_rep A x)))) \<in> lex_word \<or>
               (min lex_word (L2 (red_rep A(inv\<^bsub>freegroup A\<^esub> y)))) = (min lex_word (L2 (red_rep A x))) \<and> 
               (max lex_word (L2 (red_rep A(inv\<^bsub>freegroup A\<^esub> y))), max lex_word (L2 (red_rep A x))) \<in> lex_word" using red_rep_inv 1 by force    
    then have "((inv\<^bsub>freegroup A\<^esub> y),x) \<in> lex_L2_word' A" unfolding lex_L2_word'_def using x y by auto
    then show ?thesis using x y 2 4 lex_L2_word_length by blast
  qed
qed

lemma three_point_six:
  assumes "x \<in> carrier (freegroup A) \<and> xy \<in> carrier (freegroup A)"      
          "red_rep A x =  p@c \<and> red_rep A xy = q@c"
          "length p = length q" "length p \<le> length c" "length q \<le> length c"    
          "(p,q) \<in> lex_word" "p \<noteq> q" "N0 (red_rep A x)" "N0 (red_rep A xy)"
  shows   "(x, xy) \<in> lex_L2_word A"
proof-
  let ?X = "(red_rep A x)"
  let ?XY = "(red_rep A xy)"
  have rx:"reduced ?X" using freegroup_def[of "A"] assms(1) red_rep_the[of "x" "A"] by (simp add: red_rep_def)
  have rxy:"reduced ?XY" using freegroup_def[of "A"] assms(1) red_rep_the[of "xy" "A"] by (simp add: red_rep_def)
  have "L(?X) \<noteq> L (?XY)" using assms(2,3,4,7) neq_left_neq by fastforce
  obtain r where r:"L(?X) = (p @ r)" using assms(2,4) left_includes by blast
  obtain s where s:"L(?XY) = (q @ s)" using assms(2,5) left_includes by blast
  have lxxy:"length (L(?X)) = length (L(?XY))" using assms(2,3) rx rxy unfolding left_subword_def by auto
  then have "length (p@r) = length (q@s)" using r s by simp
  moreover then have "length r = length s" using assms(3) by simp
  ultimately have "((p@r), (q@s)) \<in> lex_word" using assms(6) lex_word_def lenlex_append1 by blast
  then have L_lex:"(L(?X), L(?XY)) \<in> lex_word" using r s by simp
  have L_eq:"L(wordinverse ?X) = L(wordinverse ?XY)" using L_inverse_eq assms(2,3,5) by (metis (no_types, lifting) wordinverse_symm)
  have length:"length (?X) = length (?XY)" using assms(2,3) length_eq by simp
  show ?thesis
  proof(cases "(L(wordinverse ?X), L(?X)) \<in> lex_word")
    case True
    then have "min lex_word (L2 (wordinverse ?X)) = L(wordinverse ?X)" unfolding left_tuple_def min.simps by (simp add: wordinverse_of_wordinverse)
    then have min1:"min lex_word (L2 (?X)) = L(wordinverse ?X)" using min_L2_inv using assms(1) by fastforce
    moreover then have max1:"max lex_word (L2 (?X)) = L (?X)" by (metis lex_word_one True left_tuple_def max.simps)       
    ultimately have "min lex_word (L2 ?XY) = L(wordinverse ?XY)" using L_eq L_lex transD lex_word_one trans_lex_word left_tuple_def min.simps by metis
    then have 1:"(L(wordinverse ?XY), L(?XY)) \<in> lex_word" unfolding left_tuple_def min.simps using L_eq L_lex True lex_word_one lex_word_total by fastforce
    then have "min lex_word (L2 (wordinverse ?XY)) = L(wordinverse ?XY)" unfolding left_tuple_def min.simps by (simp add: wordinverse_of_wordinverse)
    then have min2:"min lex_word (L2 (?XY)) = L(wordinverse ?XY)" using min_L2_inv using assms(1) by fastforce
    then have max2:"max lex_word (L2 (wordinverse ?XY)) = L(?XY)" by (metis FreeGroupMain.wordinverse_symm 1 left_tuple_def max.simps)
    have "x \<in> \<langle>A\<rangle> // reln_tuple \<langle>A\<rangle> \<and> xy \<in> \<langle>A\<rangle> // reln_tuple \<langle>A\<rangle>" using assms(1) freegroup_def[of "A"] by auto
    moreover have "(min lex_word (L2 (?X))) = (min lex_word (L2 (?XY)))" using min1 min2 L_eq by auto
    moreover have "((max lex_word (L2 (wordinverse (?X))), max lex_word (L2 (wordinverse (?XY))))) \<in> lex_word" using max1 max2 L_lex by (metis FreeGroupMain.wordinverse_symm True left_tuple_def max.simps)
    ultimately have "(x, xy) \<in> lex_L2_word' A" unfolding lex_L2_word'_def lex_prod_def left_tuple_def using wordinverse_symm left_tuple_def by (smt (z3) case_prod_conv  max.simps max1 mem_Collect_eq min.simps min1)
    then show ?thesis by (simp add: \<open>x \<in> \<langle>A\<rangle> // reln_tuple \<langle>A\<rangle> \<and> xy \<in> \<langle>A\<rangle> // reln_tuple \<langle>A\<rangle>\<close> length lex_L2_word_length)     
   next
    case False
    then have "(L(?X),L(wordinverse ?X)) \<in> lex_word" using L_inv_eq N0_def assms(8) lex_word_total rx by auto
    then have "min lex_word (L2 (wordinverse ?X)) = L(?X)" unfolding left_tuple_def min.simps by (simp add: False FreeGroupMain.wordinverse_of_wordinverse)
    then have min1:"min lex_word (L2 (?X)) = L(?X)" using min_L2_inv using assms(1) by fastforce
    then have max1:"max lex_word (L2 (wordinverse ?X)) = L (wordinverse ?X)" by (metis FreeGroupMain.wordinverse_symm False left_tuple_def max.simps)
    then show ?thesis
    proof(cases "(L(wordinverse ?XY), L(?XY)) \<in> lex_word")
      case True
      then have "min lex_word (L2 (wordinverse ?XY)) = L(wordinverse ?XY)" unfolding left_tuple_def min.simps by (simp add: wordinverse_of_wordinverse)
      then have min2:"min lex_word (L2 (?XY)) = L(wordinverse ?XY)" using min_L2_inv using assms(1) by fastforce
      then have max2:"max lex_word (L2 (wordinverse ?XY)) = L(?XY)" by (metis FreeGroupMain.wordinverse_symm True left_tuple_def max.simps)
      have "x \<in> \<langle>A\<rangle> // reln_tuple \<langle>A\<rangle> \<and> xy \<in> \<langle>A\<rangle> // reln_tuple \<langle>A\<rangle>" using assms(1) freegroup_def[of "A"] by auto
      moreover have "((min lex_word (L2 (red_rep A x))),(min lex_word (L2 (red_rep A xy)))) \<in> lex_word" using min1 min2 max2 L_eq using \<open>(L (red_rep A x), L (wordinverse (red_rep A x))) \<in> lex_word\<close> by auto
      ultimately have "(x, xy) \<in> lex_L2_word' A" unfolding lex_L2_word'_def lex_prod_def left_tuple_def using wordinverse_symm left_tuple_def by (smt (z3) case_prod_conv  max.simps max1 mem_Collect_eq min.simps min1)
      then show ?thesis unfolding lex_L2_word'_def using assms(1,6,7) freegroup_def length \<open>(x, xy) \<in> lex_L2_word' A\<close> lex_L2_word_length by blast
    next
      case False
      then have subcases:"(L(wordinverse ?XY) = L(?XY)) \<or> (L(?XY),(L(wordinverse ?XY))) \<in> lex_word" using lex_word_total by blast
      then show ?thesis
      proof(cases "(L(wordinverse ?XY) = L(?XY))")
        case True
        then have "reduced ?XY" using assms(1) freegroup_def red_rep_the by (metis partial_object.select_convs(1))
        then have "?XY = []" using L_inv_eq True by metis
        then have "(red_rep A xy) = []" by blast
        then show ?thesis using assms(9) N0_def by auto
      next
        case False
        then have false:"(L(?XY),(L(wordinverse ?XY))) \<in> lex_word" using subcases by simp
        then have 2:"min lex_word (L2 ?XY) = L(?XY)" unfolding left_tuple_def min.simps by (simp add: wordinverse_of_wordinverse)
        have 1:"(L ?XY, L (wordinverse ?X)) \<in> lex_word" using false L_eq by simp 
        have "x \<in> \<langle>A\<rangle> // reln_tuple \<langle>A\<rangle> \<and> xy \<in> \<langle>A\<rangle> // reln_tuple \<langle>A\<rangle>" using assms(1) freegroup_def[of "A"] by auto
        moreover have "((min lex_word (L2 (red_rep A x))),(min lex_word (L2 (red_rep A xy)))) \<in> lex_word" using 1 2 false L_eq min1 using L_lex by auto
        ultimately have "(x, xy) \<in> lex_L2_word' A" unfolding lex_L2_word'_def lex_prod_def left_tuple_def using wordinverse_symm left_tuple_def by (smt (z3) case_prod_conv  max.simps max1 mem_Collect_eq min.simps min1)    
       then show ?thesis unfolding lex_L2_word'_def using assms(1,6,7) freegroup_def length \<open>(x, xy) \<in> lex_L2_word' A\<close> lex_L2_word_length by blast
      qed
    qed
  qed
qed


lemma three_point_seven:assumes "x \<in> (carrier (freegroup A))"
          and "xy \<in> (carrier (freegroup A))"
          and "red_rep A x = (a @ (wordinverse p))"
          and "red_rep A xy = (a @ (wordinverse q))"
          and "length (wordinverse p) = length (wordinverse q)"
          and "length (wordinverse p) \<le> length a"
          and "length (wordinverse q) \<le> length a"
          and "(q, p) \<in> lex_word"
          and "p \<noteq> q"
          and "(red_rep A x) \<noteq> []"
          and "(red_rep A xy) \<noteq> []"
        shows "(xy, x) \<in> lex_L2_word A"
proof-
  let ?X = "(red_rep A (m_inv (freegroup A) x))"
  have 1:"(red_rep A (m_inv (freegroup A) x)) = wordinverse (red_rep A x)" using assms(1) unfolding freegroup_def using red_rep_inv by (metis freegroup_def partial_object.select_convs(1))
  then have x:"?X = (p @ (wordinverse a))" using assms(3) wordinverse_append wordinverse_of_wordinverse by metis
  let ?XY = "(red_rep A (m_inv (freegroup A) xy))"
  have 2:"(red_rep A (m_inv (freegroup A) xy)) = wordinverse (red_rep A xy)" using assms(2) unfolding freegroup_def using red_rep_inv by (metis freegroup_def partial_object.select_convs(1))
  then have xy:"?XY = (q @ (wordinverse a))" using assms(4) wordinverse_append wordinverse_of_wordinverse by metis
  have "L (?XY) \<noteq> L (?X)" using xy x neq_left_neq assms(5,9) assms(7) by (metis length_wordinverse) 
  have pq:"length p = length q" using assms(5) by (metis length_wordinverse)
  have p:"length p \<le> length (wordinverse a)" by (metis assms(6) length_wordinverse)
  then obtain r where r:"p @ r = L (?X)" using x left_includes by metis
  have "length q \<le> length (wordinverse a)" by (metis assms(7) length_wordinverse)
  then obtain s where s:"q @ s = L (?XY)" using xy left_includes by metis
  have "length (L ?X) = length (L ?XY)" using x xy pq unfolding left_subword_def by simp
  then have "length (p @ r) = length (q @ s)" using r s by simp
  moreover then have "length r = length s" using pq by simp
  ultimately have "((q@s), (p@r)) \<in> lex_word" by (simp add: lex_word_init assms(8))
  then have L:"((L ?XY),(L ?X)) \<in> lex_word" by (simp add: r s)
  have R:"L (wordinverse ?X) = L (wordinverse ?XY)" using L_inverse_eq x xy pq assms(6) assms(7) p by fastforce
  have Xneq: "L (?X) \<noteq> L (wordinverse ?X)"
  proof(rule ccontr)
    assume "\<not> L (red_rep A (inv\<^bsub>F\<^bsub>A\<^esub>\<^esub> x)) \<noteq> L (wordinverse (red_rep A (inv\<^bsub>F\<^bsub>A\<^esub>\<^esub> x)))"
    then have "L (red_rep A (inv\<^bsub>F\<^bsub>A\<^esub>\<^esub> x)) = L (wordinverse (red_rep A (inv\<^bsub>F\<^bsub>A\<^esub>\<^esub> x)))" by blast
    moreover have "reduced ?X" unfolding red_rep_def using red_rep_the assms(1) unfolding freegroup_def by (metis "1" freegroup_def partial_object.select_convs(1) red_rep_def reduced_wordinverse)
    ultimately have "?X = []" using L_inv_eq by blast
    then have "(red_rep A x) = []" by (metis "1" FreeGroupMain.wordinverse_symm wordinverse.simps(1))
    then show False using assms(10) by blast
  qed
  have XYneq: "L (?XY) \<noteq> L (wordinverse ?XY)"
  proof(rule ccontr)
    assume "\<not> L (red_rep A (inv\<^bsub>F\<^bsub>A\<^esub>\<^esub> xy)) \<noteq> L (wordinverse (red_rep A (inv\<^bsub>F\<^bsub>A\<^esub>\<^esub> xy)))"
    then have "L (red_rep A (inv\<^bsub>F\<^bsub>A\<^esub>\<^esub> xy)) = L (wordinverse (red_rep A (inv\<^bsub>F\<^bsub>A\<^esub>\<^esub> xy)))" by blast
    moreover have "reduced ?XY" unfolding red_rep_def using red_rep_the assms(2) unfolding freegroup_def by (metis "2" freegroup_def partial_object.select_convs(1) red_rep_def reduced_wordinverse)
    ultimately have "?XY = []" using L_inv_eq by blast
    then have "(red_rep A xy) = []" by (metis "2" FreeGroupMain.wordinverse_symm wordinverse.simps(1))
    then show False using assms(11) by blast
  qed
  have xyin:"(inv\<^bsub>F\<^bsub>A\<^esub>\<^esub> xy) \<in> \<langle>A\<rangle> // reln_tuple \<langle>A\<rangle>" using assms(2) freegroup_is_group unfolding freegroup_def using group.inv_closed by fastforce
  have xin: "(inv\<^bsub>F\<^bsub>A\<^esub>\<^esub> x) \<in> \<langle>A\<rangle> // reln_tuple \<langle>A\<rangle>" using assms(1) freegroup_is_group unfolding freegroup_def using group.inv_closed by fastforce
  have "length ?XY = length ?X" using x xy pq by simp
  then have "((m_inv (freegroup A) xy, m_inv (freegroup A) x) \<in> lex_L2_word A) = ((m_inv (freegroup A) xy, m_inv (freegroup A) x) \<in> lex_L2_word' A)" unfolding lex_L2_word_def lex_prod_def sorry
  moreover have "((m_inv (freegroup A) xy, m_inv (freegroup A) x) \<in> lex_L2_word' A)"
  proof(cases "(L (?XY), L (wordinverse ?XY)) \<in> lex_word")
    case True note first = this
    then have 1:"(min lex_word (L2 ?XY)) = L (?XY)" unfolding left_tuple_def min.simps by simp
    then show ?thesis
    proof(cases "(L (?X), L (wordinverse ?X)) \<in> lex_word")
      case True
      then have "(min lex_word (L2 ?X)) = L ((?X))" unfolding left_tuple_def min.simps by simp
      then have "((min lex_word (L2 ?XY)), min lex_word (L2 ?X)) \<in> lex_word" using L 1 by fastforce
      then show ?thesis unfolding lex_L2_word'_def lex_prod_def using xin xyin by fast
    next
      case False
      then have "(min lex_word (L2 ?X)) = L (wordinverse ?X)" unfolding left_tuple_def min.simps by simp
      moreover have "(L ?XY, L (wordinverse ?X)) \<in> lex_word" using R first by simp 
      ultimately have "((min lex_word (L2 ?XY)), min lex_word (L2 ?X)) \<in> lex_word" using R 1 by fastforce
      then show ?thesis unfolding lex_L2_word'_def lex_prod_def using xin xyin by fast
    qed    
  next
    case False
    then have 1: "(L (wordinverse ?XY),L ?XY) \<in> lex_word" using XYneq lex_word_total by auto
    have A:"(min lex_word (L2 ?XY)) = L (wordinverse ?XY)" unfolding left_tuple_def min.simps using False by simp
    have 2:"(L (wordinverse ?X),L (?X)) \<in> lex_word" using 1 L R trans_lex_word transD by fastforce
    then have "(min lex_word (L2 ?X)) = L (wordinverse ?X)" unfolding left_tuple_def min.simps using lex_word_one by auto
    then have min:"(min lex_word (L2 ?X)) = (min lex_word (L2 ?XY))" using A R by simp
    have "max lex_word (L2 ?XY) = L (?XY)" by (simp add: False left_tuple_def)
    moreover have "max lex_word (L2 ?X) = L (?X)" using 2 lex_word_one unfolding left_tuple_def max.simps by force
    ultimately have "((max lex_word (L2 ?XY)), max lex_word (L2 ?X)) \<in> lex_word" using L by simp
    then show ?thesis unfolding lex_L2_word'_def lex_prod_def using xin xyin min by auto
  qed
  ultimately have "((m_inv (freegroup A) xy, m_inv (freegroup A) x) \<in> lex_L2_word A)" by simp
  then have "(m_inv (freegroup A) (m_inv (freegroup A) xy), m_inv (freegroup A) x) \<in> lex_L2_word A" by (simp add: lex_L2_inv2)
  then have "(m_inv (freegroup A) (m_inv (freegroup A) xy), m_inv (freegroup A) (m_inv (freegroup A) x)) \<in> lex_L2_word A" by (simp add: lex_L2_inv)
  then show ?thesis using assms(1,2) by (simp add: freegroup_is_group)
qed

lemma N0:
  assumes "H \<le> freegroup A" 
  shows "\<forall>x \<in> (red_rep A) ` (union_inv (X (SG (freegroup A) H) A) A). N0 x"
proof
  fix x assume x:"x \<in> red_rep A ` union_inv (X (SG F\<^bsub>A\<^esub> H) A) A"
  show "N0 x"
  proof(rule ccontr)
    assume "\<not> N0 x"
    then have "x = []" unfolding N0_def by simp
    moreover obtain x1 where x1:"red_rep A x1 = x \<and> x1 \<in> (union_inv (X (SG (freegroup A) H) A) A)" using x by blast
    moreover then have xin:"x1 \<in> carrier(freegroup A)" using assms assms union_inv_clos by blast
    ultimately have 1:"x1 = \<one>\<^bsub>freegroup A\<^esub>" unfolding red_rep_def freegroup_def using red_rep_the x1 by force
    then have "x1 \<in> (X (SG (freegroup A) H) A) " 
    proof(cases "x1 \<in> (X (SG (freegroup A) H) A)")
      case True
      then show ?thesis  by simp
    next
      case False
      then have "x1 \<in> m_inv (freegroup A) ` (X (SG (freegroup A) H) A)" using x1 unfolding union_inv_def  by simp
      then obtain x2 where x2:"m_inv (freegroup A) x2 = x1 \<and> x2 \<in> (X (SG (freegroup A) H) A)" by blast
      moreover then have "x2 \<in> carrier(freegroup A)"  using assms union_inv_clos union_inv_def by fastforce
      ultimately have "m_inv (freegroup A) x1 = x2" using freegroup_is_group group.inv_inv  by fast
      then have "x2 = \<one>\<^bsub>freegroup A\<^esub>" using 1 freegroup_is_group by (metis group.inv_eq_1_iff xin)
      then show ?thesis using x2 1 by simp
    qed
    moreover have "\<one>\<^bsub>freegroup A\<^esub> \<in> G (SG (freegroup A) H) A (\<one>\<^bsub>freegroup A\<^esub>)" unfolding G_def by (metis (no_types, lifting) gen_span.simps one_SG)
    ultimately show False  unfolding X_def using 1 by blast
  qed
qed

lemma cancel_p2_q3:
  assumes "reduced x"
      and "reduced y"
      and "reduced z"
      and "N1 x y"
      and "N1 y z"
      and "x \<noteq> wordinverse y"
      and "y \<noteq> wordinverse z"
    shows "p2 (cancel2 y z) = q3 (cancel3 x y z)"
proof-
  have 1:"x = a3 (cancel3 x y z) @  (p3 (cancel3 x y z)) \<and> y = wordinverse  (p3 (cancel3 x y z)) @ b3 (cancel3 x y z) @ (q3 (cancel3 x y z)) \<and> z = (wordinverse  (q3 (cancel3 x y z))) @ (c3 (cancel3 x y z)) \<and> reduced (a3 (cancel3 x y z) @ b3 (cancel3 x y z) @ q3 (cancel3 x y z)) \<and> reduced (wordinverse  (p3 (cancel3 x y z)) @ b3 (cancel3 x y z) @ c3 (cancel3 x y z))" using assms cancel3_the by blast
  have 2:"y = (a2 (cancel2 y z)) @ (p2 (cancel2 y z)) \<and> z = (wordinverse (p2 (cancel2 y z))) @ (b2 (cancel2 y z)) \<and> reduced ((a2 (cancel2 y z)) @ (b2 (cancel2 y z)))" using assms(2,3) by (simp add: cancel2_the)
  define w2 where 3:"w2 = ((wordinverse  (p3 (cancel3 x y z)) @ b3 (cancel3 x y z)), (q3 (cancel3 x y z)), (c3 (cancel3 x y z)))"
  then have "y = (a2 w2) @ (p2 w2) \<and> z = (wordinverse (p2 w2)) @ (b2 w2) \<and> reduced ((a2 w2) @ (b2 w2))" using 1 by auto
  then have "w2 = (cancel2 y z)" using 2 assms(2,3) cancel2E' by blast
  then have "p2 w2 = p2 (cancel2 y z)" by simp
  then show ?thesis using 3 by simp
qed

lemma cancel_b2_c3:
  assumes "reduced x"
      and "reduced y"
      and "reduced z"
      and "N1 x y"
      and "N1 y z"
      and "x \<noteq> wordinverse y"
      and "y \<noteq> wordinverse z"
    shows "b2 (cancel2 y z) = c3 (cancel3 x y z)"
proof-
  have 1:"x = a3 (cancel3 x y z) @  (p3 (cancel3 x y z)) \<and> y = wordinverse  (p3 (cancel3 x y z)) @ b3 (cancel3 x y z) @ (q3 (cancel3 x y z)) \<and> z = (wordinverse  (q3 (cancel3 x y z))) @ (c3 (cancel3 x y z)) \<and> reduced (a3 (cancel3 x y z) @ b3 (cancel3 x y z) @ q3 (cancel3 x y z)) \<and> reduced (wordinverse  (p3 (cancel3 x y z)) @ b3 (cancel3 x y z) @ c3 (cancel3 x y z))" using assms cancel3_the by blast
  have 2:"y = (a2 (cancel2 y z)) @ (p2 (cancel2 y z)) \<and> z = (wordinverse (p2 (cancel2 y z))) @ (b2 (cancel2 y z)) \<and> reduced ((a2 (cancel2 y z)) @ (b2 (cancel2 y z)))" using assms(2,3) by (simp add: cancel2_the)
  define w2 where 3:"w2 = ((wordinverse  (p3 (cancel3 x y z)) @ b3 (cancel3 x y z)), (q3 (cancel3 x y z)), (c3 (cancel3 x y z)))"
  then have "y = (a2 w2) @ (p2 w2) \<and> z = (wordinverse (p2 w2)) @ (b2 w2) \<and> reduced ((a2 w2) @ (b2 w2))" using 1 by auto
  then have "w2 = (cancel2 y z)" using 2 assms(2,3) cancel2E' by blast
  then have "b2 w2 = b2 (cancel2 y z)" by simp
  then show ?thesis using 3 by simp
qed

lemma cancel_b2_bq3:
  assumes "reduced x"
      and "reduced y"
      and "reduced z"
      and "N1 x y"
      and "N1 y z"
      and "x \<noteq> wordinverse y"
      and "y \<noteq> wordinverse z"
    shows "b2 (cancel2 x y) =  (b3 (cancel3 x y z)) @ q3 (cancel3 x y z)"
proof-
  have 1:"x = a3 (cancel3 x y z) @  (p3 (cancel3 x y z)) \<and> y = wordinverse  (p3 (cancel3 x y z)) @ b3 (cancel3 x y z) @ (q3 (cancel3 x y z)) \<and> z = (wordinverse  (q3 (cancel3 x y z))) @ (c3 (cancel3 x y z)) \<and> reduced (a3 (cancel3 x y z) @ b3 (cancel3 x y z) @ q3 (cancel3 x y z)) \<and> reduced (wordinverse  (p3 (cancel3 x y z)) @ b3 (cancel3 x y z) @ c3 (cancel3 x y z))" using assms cancel3_the by blast
  have 2:"y = (a2 (cancel2 y z)) @ (p2 (cancel2 y z)) \<and> z = (wordinverse (p2 (cancel2 y z))) @ (b2 (cancel2 y z)) \<and> reduced ((a2 (cancel2 y z)) @ (b2 (cancel2 y z)))" using assms(2,3) by (simp add: cancel2_the)
  define w2 where 3:"w2 = ((a3 (cancel3 x y z)), ((p3 (cancel3 x y z))), b3 (cancel3 x y z)@ (q3 (cancel3 x y z)))"
  then have "y = (wordinverse (p2 w2)) @ (b2 w2) \<and> x = ((a2 w2)) @ (p2 w2) \<and> reduced ((a2 w2) @ (b2 w2))" using 1 by auto
  then have "w2 = (cancel2 x y)" using 2 3 assms(1,2,3) cancel2E' cancel2_the[of "x" "y"] by blast
  then have "b2 w2 = b2 (cancel2 x y)" by simp
  then show ?thesis using 3 by simp
qed

lemma cancel_p2_p3:
  assumes "reduced x"
      and "reduced y"
      and "reduced z"
      and "N1 x y"
      and "N1 y z"      
      and "x \<noteq> wordinverse y"
      and "y \<noteq> wordinverse z"
    shows "p2 (cancel2 x y) = p3 (cancel3 x y z)"
proof-
  have "x = a3 (cancel3 x y z) @  (p3 (cancel3 x y z))" using assms cancel3_the by blast
  moreover have "x = (a2 (cancel2 x y)) @ (p2 (cancel2 x y))" using assms(1,2) by (simp add: cancel2_the)
  ultimately show ?thesis using cancel_a2_a3 assms by (metis same_append_eq)
qed

lemma neq_imp_invneq: "p \<noteq> q \<Longrightarrow> wordinverse p \<noteq> wordinverse q"
  by (metis FreeGroupMain.wordinverse_symm)

lemma reln_eq_image:
  assumes "x ∈ ⟨S⟩ ∧ y ∈ ⟨S⟩ ∧ x~y"
  shows "((reln_tuple ⟨S⟩)`` {x}) =( (reln_tuple ⟨S⟩)`` {y})" using assms reln_tuple_def[of "⟨S⟩"] equiv_class_eq reln_equiv by fastforce
  
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
    then moreover have "x1 \<otimes>\<^bsub>freegroup A\<^esub> y1 = reln_tuple \<langle>A\<rangle> `` {a3 (\<oslash>\<^bsub>3\<^esub> x y z)  @ q3 (\<oslash>\<^bsub>3\<^esub> x y z)}" sorry
    ultimately have "red_rep A (x1 \<otimes>\<^bsub>freegroup A\<^esub> y1) = (a3 (\<oslash>\<^bsub>3\<^esub> x y z) @ q3 (\<oslash>\<^bsub>3\<^esub> x y z))" using xyz red_rep_the unfolding red_rep_def freegroup_def sorry
    have y1z1in:"y1 \<otimes>\<^bsub>freegroup A\<^esub> z1 \<in> carrier (freegroup A)" by (meson H assms(1) subgroup.m_closed subgroup.mem_carrier)
    moreover have "(a3 (\<oslash>\<^bsub>3\<^esub> x y z) @ p3 (\<oslash>\<^bsub>3\<^esub> x y z) @ wordinverse (p3 (\<oslash>\<^bsub>3\<^esub> x y z)) @ q3 (\<oslash>\<^bsub>3\<^esub> x y z)) ~ (a3 (\<oslash>\<^bsub>3\<^esub> x y z) @ q3 (\<oslash>\<^bsub>3\<^esub> x y z)) \<and> x1 \<otimes>\<^bsub>freegroup A\<^esub> y1 = reln_tuple \<langle>A\<rangle> `` {a3 (\<oslash>\<^bsub>3\<^esub> x y z) @ p3 (\<oslash>\<^bsub>3\<^esub> x y z) @ wordinverse (p3 (\<oslash>\<^bsub>3\<^esub> x y z)) @ q3 (\<oslash>\<^bsub>3\<^esub> x y z)}"
      unfolding freegroup_def by (metis (no_types, lifting) append_assoc cancel2_reln freegroup_def monoid.select_convs(1) partial_object.select_convs(1) proj_append_wd red_rep_the redrep_in x1 x1A xyz y1 y1A)
    then moreover have "x1 \<otimes>\<^bsub>freegroup A\<^esub> y1 = reln_tuple \<langle>A\<rangle> `` {a3 (\<oslash>\<^bsub>3\<^esub> x y z)  @ q3 (\<oslash>\<^bsub>3\<^esub> x y z)}" sorry
    ultimately have "red_rep A (x1 \<otimes>\<^bsub>freegroup A\<^esub> y1) = (a3 (\<oslash>\<^bsub>3\<^esub> x y z) @ q3 (\<oslash>\<^bsub>3\<^esub> x y z))" using xyz red_rep_the unfolding red_rep_def freegroup_def sorry
    have "(p3 (\<oslash>\<^bsub>3\<^esub> x y z), q3 (\<oslash>\<^bsub>3\<^esub> x y z)) \<in> lex_word \<or> (q3 (\<oslash>\<^bsub>3\<^esub> x y z), p3 (\<oslash>\<^bsub>3\<^esub> x y z)) \<in> lex_word" unfolding lex_word_def using neq lex_word_def lex_word_total by auto
    show False
    proof(cases "(p3 (\<oslash>\<^bsub>3\<^esub> x y z), q3 (\<oslash>\<^bsub>3\<^esub> x y z)) \<in> lex_word")
      case True
      then have ""
      then show ?thesis sorry
    next
      case False
      then show ?thesis sorry
    qed
    
