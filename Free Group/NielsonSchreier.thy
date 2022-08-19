theory NielsonSchreier
imports "UniversalProperty" "HOL.Nat" "Conjugacy"
begin

lemma one_list:"length xs = 1 \<Longrightarrow> \<exists>x. xs = [x]"
  by (metis Cons_eq_append_conv append_butlast_last_id le_numeral_extra(4) length_0_conv length_butlast subtract_greater zero_neq_one)

lemma inverse_neq:"x \<noteq> inverse x"
  by (metis inverse.elims prod.inject)

lemma red_repelem:
  assumes "w \<in> (\<langle>S\<rangle> // (reln_tuple \<langle>S\<rangle>))"
  shows "\<exists>x \<in> w. reduced x \<and> ((reln_tuple \<langle>S\<rangle>)`` {x} = w)"
proof-
  obtain c where c: "w = (reln_tuple \<langle>S\<rangle>) `` {c}" by (meson assms quotientE)
  then have cs: "c \<in> \<langle>S\<rangle>" using assms by (metis proj_def proj_in_iff reln_equiv)
  obtain rc where rc: "rc = (iter (length c) reduce c)" by simp
  then have "reduced rc" by (simp add: reduced_iter_length)
  then have "c ~ rc" using rc cancels_imp_rel iter_cancels_to by auto
  moreover then have "rc \<in> \<langle>S\<rangle>" using cs rc using cancels_to_preserves iter_cancels_to by blast
  ultimately have crc: "(c, rc) \<in> reln_tuple \<langle>S\<rangle>" using cs reln_tuple_def by auto
  then have "((reln_tuple \<langle>S\<rangle>)`` {rc} = w)"using c by (smt (verit, ccfv_SIG) equiv_class_eq_iff reln_equiv)
  moreover then have "rc \<in> w" using c crc by simp
  ultimately show ?thesis using \<open>reduced rc\<close> by auto
qed

lemma redelem_unique :
  assumes "w \<in> (\<langle>S\<rangle> // (reln_tuple \<langle>S\<rangle>))"
  shows "\<exists>!x \<in> w. reduced x \<and> ((reln_tuple \<langle>S\<rangle>)`` {x} = w)"
proof(rule classical)
  assume 1:"\<not>(\<exists>!x \<in> w. reduced x \<and> ((reln_tuple \<langle>S\<rangle>)`` {x} = w))"
  have "\<exists>x \<in> w. reduced x \<and> ((reln_tuple \<langle>S\<rangle>)`` {x} = w)" using assms red_repelem by auto
  then obtain x where x:"x \<in> w \<and> reduced x" by auto
  obtain y where y:"(y \<in> w \<and> reduced y \<and> (reln_tuple \<langle>S\<rangle>)`` {x} = w) \<and> y \<noteq> x " using 1 x by (smt (verit, best) assms equiv_class_eq_iff equiv_class_self quotientE quotient_eq_iff reln_equiv)
  then have "(x, y) \<in> reln_tuple \<langle>S\<rangle>" using x y by blast
  then have "x ~ y" using reln_tuple_def by auto
  then have "y = x" using x y 1 reduced_cancel_eq reln_imp_cancels by blast
  moreover then have "(reln_tuple \<langle>S\<rangle>)`` {x} = (reln_tuple \<langle>S\<rangle>)`` {y}" by simp
  ultimately have False by (simp add: y)
  then show "\<exists>!x \<in> w. reduced x \<and> ((reln_tuple \<langle>S\<rangle>)`` {x} = w)" by simp 
qed

definition red_rep :: "('a, 'b) monoidgentype set \<Rightarrow> ('a, 'b) word set \<Rightarrow> ('a, 'b) word"
  where "red_rep S w = (THE x. x \<in> w \<and> reduced x \<and> (w = reln_tuple \<langle>S\<rangle> `` {x}))"

lemma red_rep_the:
  assumes "w \<in> (\<langle>S\<rangle> // (reln_tuple \<langle>S\<rangle>))"
  shows "((red_rep S w) \<in> w)  \<and> reduced ((red_rep S w)) \<and> (w = reln_tuple \<langle>S\<rangle> `` {(red_rep S w)})"
  unfolding red_rep_def
proof(rule theI')
  show "\<exists>!x. x \<in> w \<and> reduced x \<and> w = reln_tuple \<langle>S\<rangle> `` {x}" using redelem_unique[of "w" "S"] assms by metis 
qed

lemma equivred_equiv:
  assumes "w \<in> (\<langle>S\<rangle> // (reln_tuple \<langle>S\<rangle>))"
  shows "\<forall>x\<in>w. (reln_tuple \<langle>S\<rangle>) `` {x} = (reln_tuple \<langle>S\<rangle>) `` {red_rep S w}"
proof-
  obtain x where x:"x \<in> w" using assms red_repelem by auto
  then have xs: "x \<in> \<langle>S\<rangle>" using append_congruent assms equiv_2f_clos reln_equiv rightappend_span freewords_on_def by fastforce
  have rw: "red_rep S w \<in> w" using x red_rep_def redelem_unique red_rep_the assms by blast
  then have rs: "red_rep S w \<in> \<langle>S\<rangle>" using assms by (meson quotient_eq_iff refl_onD1 reln_equiv reln_refl)
  then have "(x,red_rep S w)\<in>(reln_tuple \<langle>S\<rangle>)" using xs x rs rw by (meson assms quotient_eq_iff reln_equiv)
  then have "(reln_tuple \<langle>S\<rangle>) `` {x} = (reln_tuple \<langle>S\<rangle>) `` {red_rep S w}" by (meson equiv_class_eq_iff reln_equiv)
  then show ?thesis using x assms by (smt (verit, best)  equiv_class_eq_iff quotient_eq_iff reln_equiv)
qed

definition equivinv :: "('a, 'b) monoidgentype set \<Rightarrow> ('a, 'b) word set \<Rightarrow> ('a, 'b) word set"
  where "equivinv S w = (reln_tuple \<langle>S\<rangle> `` {wordinverse (red_rep S w)})"

(*

definition equal_equiv where "equal_equiv S x y = (red_rep S x = red_rep S y)"

definition inv_equiv where "inv_equiv S x y = (x = equivinv S y)"

fun nielson_reln :: "('a, 'b) monoidgentype set \<Rightarrow> ('a, 'b) word set \<Rightarrow> ('a, 'b) word set \<Rightarrow> bool"
  where
"nielson_reln S x y = (equal_equiv S x y \<or> inv_equiv S x y)"

definition nielson_set :: "('a, 'b) monoidgentype set \<Rightarrow>(('a,'b) word  \<times> ('a,'b) word) set"
  where
"nielson_set S = {(w,z). \<exists>x y . x \<in> (\<langle>S\<rangle> // (reln_tuple \<langle>S\<rangle>)) \<and> w = red_rep S x \<and> y \<in> (\<langle>S\<rangle> // (reln_tuple \<langle>S\<rangle>)) \<and> z = red_rep S y \<and> nielson_reln S x y}"

lemma refl_nielson : "\<forall> x. nielson_reln S x x"
  using nielson_reln.simps equal_equiv_def by blast

lemma sym_nielson : "\<forall> x y. nielson_reln S x y \<Longrightarrow> nielson_reln S y x"
  using nielson_reln.simps equal_equiv_def by blast

lemma trans_nielson : "\<forall> x y z. nielson_reln S x y \<Longrightarrow> nielson_reln S y z \<Longrightarrow> nielson_reln S x z"
  using nielson_reln.simps equal_equiv_def by blast

fun compare :: "(('a,'b) groupgentype \<times> ('a,'b) groupgentype) set \<Rightarrow>('a, 'b) word \<Rightarrow> ('a, 'b) word \<Rightarrow> bool"
  where
"compare r x y = (if x = [] \<or> ((hd x \<noteq> hd y) \<and> (hd x, hd y) \<in> r) 
                     then True else (if \<not>((hd x \<noteq> hd y) \<and> (hd y, hd x) \<in> r) 
                                     then compare r (tl x) (tl y) else False))"

fun compare_alt :: "(('a, 'b) groupgentype \<times> ('a, 'b) groupgentype) set \<Rightarrow> ('a, 'b) word \<Rightarrow> ('a, 'b) word \<Rightarrow> bool"
  where
"compare_alt r x y = (x = y \<or> (\<exists> a b c. x = (a @ b) \<and> y = (a @ c) \<and> (hd b) \<noteq> (hd c) \<and> (hd b, hd c) \<in> r))"

definition compare_set 
  where "compare_set A r = {(x, y). x \<in> \<langle>A\<rangle> \<and> y \<in> \<langle>A\<rangle> \<and> compare r x y }"

lemma refl_compare : 
  assumes "well_order_on (invgen A) r"v 
  shows "\<forall> x \<in> \<langle>A\<rangle>. compare r x x"
proof
  fix x 
  assume "x \<in> \<langle>A\<rangle>"
  then show "compare r x x" 
  proof (induction x)
    case Nil
    then show ?case by simp
  next
    case (Cons a x)
    have "x \<in> \<langle>A\<rangle>" using Cons.prems span_cons freewords_on_def by blast
    then have "compare r (tl (a # x)) (tl (a # x))" using compare.simps using Cons.IH \<open>x \<in> \<langle>A\<rangle>\<close> by auto
    then show ?case by simp
  qed
qed

lemma reflon_comp :
  assumes "well_order_on (invgen A) r"
  shows "refl_on \<langle>A\<rangle> (compare_set A r)"
proof-
  have "\<forall>(x,y) \<in> (compare_set A r). x \<in> \<langle>A\<rangle> \<and> y \<in> \<langle>A\<rangle>" using compare_set_def using Pair_inject by blast
  then have "(compare_set A r) \<subseteq> (\<langle>A\<rangle> \<times> \<langle>A\<rangle>)" using compare_set_def by auto 
  moreover have "\<forall> x \<in> \<langle>A\<rangle>. compare r x x" using assms refl_compare by blast
  moreover have "(\<forall> x \<in> \<langle>A\<rangle>. (x, x) \<in> (compare_set A r))" using compare_set_def using calculation(2) by blast
  ultimately show ?thesis using refl_on_def by blast
qed

lemma comp_compalt : 
  assumes "length x = length y"
    and "well_order_on (invgen S) r"
    and "x \<in> \<langle>S\<rangle>"
    and "y \<in> \<langle>S\<rangle>"
    and "compare r x y" 
  shows "compare_alt r x y"
  using assms
proof(induct x y rule: compare.induct)
  case (1 r x y)
  then show ?case
  proof(cases "x = []")
    case True
    then have "x = y" using "1.prems"(1) by auto
    then show ?thesis by auto
  next
    case False
    then show ?thesis
    proof(cases "hd x = hd y")
      case True
      then have T2: "hd x = hd y" by simp
      have y:"y \<noteq> []" using False "1.prems"(1) by auto
      then have A:"(\<not> (x = [] \<or> hd x \<noteq> hd y \<and> (hd x, hd y) \<in> r))" using False True by simp
      moreover have "\<not> (hd x \<noteq> hd y \<and> (hd y, hd x) \<in> r)" by (simp add: True)
      moreover have "length (tl x) = length (tl y)" using False "1.prems"(1) by auto
      moreover have "(tl x) \<in> \<langle>S\<rangle>" using False "1.prems"(3) span_cons freewords_on_def by (metis list.exhaust_sel)
      moreover have "(tl y) \<in> \<langle>S\<rangle>" using y "1.prems"(4) span_cons freewords_on_def by (metis list.exhaust_sel)
      moreover have "compare r x y = compare r (tl x) (tl y)" using True False y  by simp
      ultimately have tlc:"compare_alt r (tl x) (tl y)" using "1.hyps" "1.prems"(2) "1.prems"(5) by blast
      then show ?thesis
      proof(cases "(tl x) = (tl y)")
        case True
        have "x = y" using T2 by (simp add: True False list.expand y)
        then show ?thesis by auto
      next
        case False
        then obtain a b c where "tl x = (a @ b) \<and> tl y = (a @ c) \<and> (hd b) \<noteq> (hd c) \<and> (hd b, hd c) \<in> r" using tlc by auto
        then have "x = (hd x#(a @ b)) \<and> y = (hd x#(a @ c)) \<and> (hd b) \<noteq> (hd c) \<and> (hd b, hd c) \<in> r" using T2 by (metis A list.exhaust_sel y)
        then have "x = ((hd x#a) @ b) \<and> y = ((hd x#a) @ c) \<and> (hd b) \<noteq> (hd c) \<and> (hd b, hd c) \<in> r" by auto
        then show ?thesis using compare_alt.simps by blast
      qed
    next
      case False
      then have F2:"hd x \<noteq> hd y" by simp
      then show ?thesis
      proof(cases "(hd x, hd y) \<in> r")
        case True
        then have "x = ([] @ x) \<and> y = ([] @ y) \<and> (hd x) \<noteq> (hd y) \<and> (hd x, hd y) \<in> r" using False True by simp
        then show ?thesis using compare_alt.simps by force
      next
        case False
        have "hd x \<in> (invgen S)" using  "1.prems"(3) by (metis "1.prems"(1) F2 append_eq_append_conv append_self_conv2 gen_spanset freewords_on_def)
        moreover have "hd y \<in> (invgen S)" using  "1.prems"(4) by (metis "1.prems"(1) F2 append_eq_append_conv append_self_conv gen_spanset freewords_on_def)
        ultimately have "(hd y, hd x) \<in> r" using False F2 "1.prems"(2) unfolding well_order_on_def linear_order_on_def total_on_def by blast
        then have "compare r x y = False" using F2 "1.prems"(1) False by force
        then show ?thesis using "1.prems"(5) by blast
      qed
    qed
  qed
qed

lemma compare_subword:
  assumes "length x = length y"
    and "well_order_on (invgen S) r"
    and "x \<in> \<langle>S\<rangle>"
    and "y \<in> \<langle>S\<rangle>"
    and "a \<in> \<langle>S\<rangle>"
  shows "compare r (a@x) (a@y) = compare r x y"
  using assms
proof(induction "(a@x)" "(a@y)" arbitrary: a rule: compare.induct)
  case (1 r)
  then show ?case
  proof(cases "a = []")
    case True
    then show ?thesis by simp
  next
    case False
    have A:"hd (a @ x) = hd (a @ y)" using False by simp
    moreover then have "\<not> (a @ x = [] \<or> hd (a @ x) \<noteq> hd (a @ y) \<and> (hd (a @ x), hd (a @ y)) \<in> r)" by (simp add: False)
    moreover then have "\<not> (hd (a @ x) \<noteq> hd (a @ y) \<and> (hd (a @ y), hd (a @ x)) \<in> r)" by (simp add: A)
    moreover have B:"tl (a @ x) = (tl a) @ x" by (simp add: False)
    moreover have C:"tl (a @ y) = (tl a) @ y" by (simp add: False)
    moreover have "tl a \<in> \<langle>S\<rangle>" using "1.prems" span_cons freewords_on_def False  by (metis list.collapse)
    ultimately have "compare r ((tl a) @ x) ((tl a) @ y) = compare r x y" using "1.hyps" "1.prems"(2) assms(1) assms(3) assms(4) by presburger
    then have "compare r (tl (a @ x)) (tl (a @ y)) = compare r x y" using B C by presburger
    moreover have "compare r (tl (a @ x)) (tl (a @ y)) = compare r (a @ x) (a @ y)" by (simp add: A)
    ultimately show ?thesis by blast
qed
qed

lemma compalt_comp : 
  assumes "length x = length y"
    and "well_order_on (invgen S) r"
    and "x \<in> \<langle>S\<rangle>"
    and "y \<in> \<langle>S\<rangle>"
    and "compare_alt r x y" 
  shows "compare r x y"
  using assms
proof(cases "x=y")
  case True
  then show ?thesis using refl_compare assms(1) assms(2) assms(4) by metis
next
  case False
  then have "(\<exists>a b c. x = (a @ b) \<and> y = (a @ c) \<and> (hd b) \<noteq> (hd c) \<and> (hd b, hd c) \<in> r)" using assms(5) by auto
  then obtain a b c where "x = (a @ b) \<and> y = (a @ c) \<and> (hd b) \<noteq> (hd c) \<and>(hd b, hd c) \<in> r" by blast
  moreover have  "b \<in> \<langle>S\<rangle>" using assms(3) freewords_on_def using calculation rightappend_span by blast
  moreover have  "c \<in> \<langle>S\<rangle>" using assms(4) freewords_on_def using calculation rightappend_span by blast
  moreover have "compare r b c" by (simp add: calculation(1))
  moreover have "compare r x y = compare r b c" using compare_subword by (metis add_left_imp_eq assms(1) assms(2) assms(4) calculation(1) calculation(2) calculation(3) leftappend_span length_append freewords_on_def)
  ultimately show ?thesis  by blast
qed

lemma antisym_compare :
  assumes "well_order_on (invgen A) r"
  shows "(\<forall>x y. (length x = length y) \<longrightarrow> (x, y) \<in> compare_set A r \<longrightarrow> (y, x) \<in> compare_set A r \<longrightarrow> x = y)"
  apply (rule allI)+ 
  apply (rule impI)+
proof-
  fix x y
  assume l: "length x = length y" and xy: "(x, y) \<in> compare_set A r" 
                                  and yx: "(y, x) \<in> compare_set A r"
  then show "x = y" using assms
  proof(induct x y rule : compare.induct)
    case (1 r x y)
    then show ?case 
    proof (cases "x = []")
      case True
      have "y = []" using "1.prems"(1) True by auto
      then show ?thesis using True by simp
    next
      case False
      then show ?thesis 
      proof (cases "hd x = hd y")
        case True
        have a: "x \<noteq> []" using False by simp
        then have b: "y \<noteq> []" using 1 by auto
        have "x \<in> \<langle>A\<rangle>" using "1.prems"(2) unfolding compare_set_def by simp
        then have tlx:"tl x \<in> \<langle>A\<rangle>" using a freewords_on_def span_cons by (metis list.collapse)
        have "y \<in> \<langle>A\<rangle>" using "1.prems"(2) unfolding compare_set_def by simp
        then have tly:"tl y \<in> \<langle>A\<rangle>" using b freewords_on_def span_cons by (metis list.collapse)
        have "compare r x y" using "1.prems"(2) unfolding compare_set_def by blast
        then have rxy: "compare r (tl x) (tl y)" using True by (simp add: a)
        have c:"((tl x), (tl y)) \<in> compare_set A r" using tlx tly rxy unfolding compare_set_def by blast
        have "compare r y x" using "1.prems"(3) unfolding compare_set_def by blast 
        then have ryx:"compare r (tl y) (tl x)" using True by (simp add: b)
        have d:"((tl y), (tl x)) \<in> compare_set A r" using tlx tly ryx unfolding compare_set_def by blast
        have "length x = length y" using 1 by auto
        then have "length (tl x) = length (tl y)" using a b by fastforce
        then have "(tl x) = (tl y)" using 1 a b True c d by blast
        then show ?thesis using True using a b list.expand by blast
      next
        case False
        then have A: "hd x \<noteq> hd y" by simp
        have "x \<in> \<langle>A\<rangle>" using "1.prems"(2) unfolding compare_set_def by simp
        then have B:"hd x \<in> (invgen A)" by (metis "1.prems"(1) False append.left_neutral append_eq_append_conv gen_spanset freewords_on_def)
        have "y \<in> \<langle>A\<rangle>" using "1.prems"(2) unfolding compare_set_def by simp
        then have C:"hd y \<in> (invgen A)" by (metis "1.prems"(1) False append_eq_append_conv append_self_conv2 gen_spanset freewords_on_def)
        then show ?thesis
        proof(cases "(hd x, hd y) \<in> r")
          case True
          then have D: "(hd x, hd y) \<in> r" by simp
          then show ?thesis 
          proof(cases "(hd y, hd x) \<in> r")
            case True
            have "(\<forall>x y. (x, y) \<in> r \<longrightarrow> (y, x) \<in> r \<longrightarrow> x = y)" using  "1.prems"(4)  unfolding well_order_on_def linear_order_on_def  partial_order_on_def antisym_def by blast
            then have "hd x = hd y" using D True by blast
            then show ?thesis using A by blast
          next
            case False
            then have "compare r y x = False" using A using "1.prems"(1) True by auto
            then have "(y, x) \<notin> compare_set A r" unfolding compare_set_def by simp
            then show ?thesis using "1.prems"(3)  by simp
          qed
        next
          case False
          then have "(hd y, hd x) \<in> r" using A B C "1.prems"(4) unfolding well_order_on_def linear_order_on_def total_on_def by auto
          then have "compare r x y = False" using A using "1.prems"(1) False  by auto
            then have "(x, y) \<notin> compare_set A r" unfolding compare_set_def by simp
            then show ?thesis using "1.prems"(2)  by simp
        qed
      qed
    qed
  qed
qed

lemma eq_lenless: 
  assumes "(a @ b = c @ d)"
      and "length a \<le> length c"
    shows "\<exists>x. c = a@x"
proof(rule classical)
  assume 1: "\<not>(\<exists>x. c = a@x)"
  then have "\<nexists>x. c = a@x" by auto
  then have "length a \<ge> length c" using assms(2) by (metis append_eq_append_conv2 append_eq_append_conv_if append_take_drop_id assms(1))
  then have "length a = length c" using assms(2) by simp
  then have "c = a @ []" using assms(1) by auto
  then have False using "1" by auto
  then show "\<exists>x. c = a@x" by auto
qed

lemma eq_lengr :
  assumes "(a @ b = c @ d)"
      and "length a > length c"
    shows "\<exists>s. a = (c @ s)"
proof(rule classical)
  assume 1: "(\<not> (\<exists>s. a = (c @ s)))"
  then have "\<nexists>s. a = (c@s)" by auto
  then have "length a \<le> length c" using assms(2) by (metis assms(1) eq_lenless nat_le_linear)
  then have "length a = length c" using assms(2) by simp
  then have "a = (c@[])" using assms(2) nat_neq_iff by blast
  then have False using 1 by simp
  then show "\<exists>s. a = (c@s)" by auto
qed

lemma trans_r:
  assumes "well_order_on (invgen A) r"
      and "x \<in> (invgen A)"
      and "y \<in> (invgen A)"
      and "z \<in> (invgen A)"
      and "(x\<noteq>y) \<and> (x,y) \<in> r"
      and "(y\<noteq>z) \<and> (y,z) \<in> r"
    shows "(x \<noteq> z) \<and> (x, z) \<in> r"
proof-
  have "linear_order_on (invgen A) r" using assms(1) by (metis well_order_on_Well_order wo_rel.LIN wo_rel.intro)
  then have par: "partial_order_on (invgen A) r" by (simp add: linear_order_on_def)
  then have "preorder_on (invgen A) r" by (simp add: partial_order_on_def)
  then have 1:"trans r" by (simp add: preorder_on_def)
  have "x \<noteq> z" using assms(5,6) par antisymD assms(5) assms(6) partial_order_onD(3) by fastforce
  then show ?thesis using 1 by (meson assms(5) assms(6) transD)
qed

lemma "noteq_eqlength":
  assumes "a \<noteq> b"
  and "length a = length b"
shows "a \<noteq> [] \<and> b \<noteq> [] \<and> (\<exists>x y z. a = (x @ y) \<and> b = (x @ z) \<and> (hd y \<noteq> hd z))"
  using assms
proof(induction a arbitrary: b)
  case Nil
  then have "b = []" by force
  then show ?case using Nil.prems by simp
next
  case (Cons a1 a2)
  then have A:"length a2 = length (tl b)" by fastforce
   have 1:"(a1#a2) \<noteq> []" by simp
  then have 2:"b \<noteq> []" using "Cons.prems"(2) by (metis length_0_conv)
  show ?case
  proof(cases "a2 = tl b")
    case True
    then have "a1 \<noteq> hd b" using Cons.prems(1) using 2 by auto
    then have "(a1#a2) = ([] @ (a1#a2)) \<and> b = ([] @ b) \<and> (hd (a1#a2) \<noteq> hd b)" by simp
    then show ?thesis using 1 2 by blast
  next
    case False
    then have "a2 \<noteq> [] \<and> (tl b) \<noteq> [] \<and> (\<exists>x y z. a2 = x @ y \<and> (tl b)= x @ z \<and> hd y \<noteq> hd z)" using A Cons.IH by presburger
    then obtain x y z where "(a2 = x @ y \<and> (tl b)= x @ z \<and> hd y \<noteq> hd z)"  by blast
    then have "((a1#a2) = (a1#(x @ y)) \<and>  b = (hd b#(x @ z)) \<and> hd y \<noteq> hd z)" using 2 list.collapse by force
    then have 3:"((a1#a2) = ((a1#x) @ y) \<and>  b = ((hd b#x) @ z) \<and> hd y \<noteq> hd z)"  by auto
    then show ?thesis
    proof(cases "a1 = hd b")
      case True
      then show ?thesis using 1 2 3 by blast
    next
      case False
      then have "(a1#a2) = ([] @ (a1#a2)) \<and> b = ([] @ b) \<and> (hd (a1#a2) \<noteq> hd b)" by simp
      then show ?thesis using 1 2 by blast
    qed
  qed
qed

lemma total_on_compare:
  assumes "well_order_on (invgen A) r"
  shows "(\<forall>x\<in>\<langle>A\<rangle>. \<forall>y\<in>\<langle>A\<rangle>. (length x = length y) \<longrightarrow> x \<noteq> y \<longrightarrow> (x, y) \<in> compare_set A r \<or> (y, x) \<in> compare_set A r)"
  apply(rule ballI)+
  apply(rule impI)+
proof-
  fix x y assume x: "x \<in> \<langle>A\<rangle>" and  y: "y \<in> \<langle>A\<rangle>" and lxy: "length x = length y" and xy:"x \<noteq> y"
  then have 2:"x \<noteq> [] \<and> y  \<noteq> [] \<and> (\<exists>a b c. x = (a @ b) \<and> y = (a @ c) \<and> (hd b \<noteq> hd c))" using noteq_eqlength by auto
  then obtain a b c where 1:"x = (a @ b) \<and> y = (a @ c) \<and> (hd b \<noteq> hd c)" by auto
  then show "(x, y) \<in> compare_set A r \<or> (y, x) \<in> compare_set A r"
  proof(cases "(hd b, hd c) \<in> r")
    case True
    then have "compare_alt r x y" using compare_alt.simps 1  by auto
    then have "compare r x y" using lxy assms compalt_comp x y by blast
    then show ?thesis unfolding compare_set_def  using x y by blast
  next
    case False
    then have bc: "(hd b, hd c) \<notin> r" by simp
    then show ?thesis
    proof(cases "b = []")
      case True
      then have "c = []" using 1 lxy by auto
      then have "x = y" using 1 by (simp add: True)
      then have "compare_alt r x y" using compare_alt.simps by auto
      then have "compare r x y" using lxy assms compalt_comp x y by blast
      then show ?thesis unfolding compare_set_def  using x y by blast
    next
      case False
      then have "c \<noteq> []" using 1 lxy by force
      moreover have "c \<in> \<langle>A\<rangle>" using y 1 rightappend_span unfolding freewords_on_def by auto
      ultimately have c:"hd c \<in> (invgen A)"  by (simp add: gen_spanset freewords_on_def)
      have "b \<in> \<langle>A\<rangle>" using x 1 rightappend_span unfolding freewords_on_def by auto
      then have "hd b \<in> (invgen A)" using False by (simp add: gen_spanset freewords_on_def)
      then have "(hd c, hd b) \<in> r" using assms c bc 1 2 unfolding well_order_on_def linear_order_on_def total_on_def by blast
      then have "compare_alt r y x" using compare_alt.simps 1 by fastforce
      then have "compare r y x" using lxy assms compalt_comp x y by metis
      then show ?thesis unfolding compare_set_def  using x y by blast
    qed
  qed
qed

lemma trans_compare:
  assumes "well_order_on (invgen A) r"
  shows "(\<forall>x y z. (length x = length y) \<longrightarrow> (length y = length z) \<longrightarrow>(x, y) \<in> compare_set A r \<longrightarrow> (y, z) \<in> compare_set A r \<longrightarrow> (x, z) \<in> compare_set A r)"
  apply (rule allI)+ 
  apply (rule impI)+
proof
  fix x y z
  assume lxy: "length x = length y" and lyz: "length y = length z"
    and  xy: "(x, y) \<in> compare_set A r" and yz: "(y, z) \<in> compare_set A r"
  have cxy: "x \<in> \<langle>A\<rangle> \<and> y \<in> \<langle>A\<rangle> \<and> compare r x y" using xy compare_set_def by blast
  then have "compare r x y" by blast
  then have "compare_alt r x y" using comp_compalt assms lxy cxy by auto
  then have 1:"(x = y \<or> (\<exists> a b c. x = (a @ b) \<and> y = (a @ c) \<and> (hd b) \<noteq> (hd c) \<and> (hd b, hd c) \<in> r))" using compare_alt.cases by simp
  then show "(x, z) \<in> compare_set A r"
  proof (cases "x = y")
    case True note T1 = this
    have cyz: "y \<in> \<langle>A\<rangle> \<and> z \<in> \<langle>A\<rangle> \<and> compare r y z" using yz compare_set_def case_prod_conv by blast
    then have "compare r y z" by blast
    then have "compare_alt r y z" using comp_compalt assms lyz cyz by blast
    then have 2: "(y = z \<or> (\<exists> d e f. y = (d @ e) \<and> z = (d @ f) \<and> (hd e) \<noteq> (hd f) \<and> (hd e, hd f) \<in> r))" using compare_alt.cases by simp
    then show ?thesis 
    proof (cases "y = z")
      case True
      then show ?thesis using T1 xy by auto
    next
      case False
      then have "(\<exists> d e f. y = (d @ e) \<and> z = (d @ f) \<and> (hd e) \<noteq> (hd f) \<and> (hd e, hd f) \<in> r)" using False "2" by auto
      then obtain d e f where "y = (d @ e) \<and> z = (d @ f) \<and> (hd e) \<noteq> (hd f) \<and> (hd e, hd f) \<in> r" by auto
      then have "x = (d @ e) \<and> (hd e) \<noteq> (hd f) \<and> (hd e, hd f) \<in> r" using T1 by simp
      then show ?thesis using True yz by auto
    qed
  next
    case False note xny = this
    then have "(\<exists> a b c. x = (a @ b) \<and> y = (a @ c) \<and> (hd b) \<noteq> (hd c) \<and> (hd b, hd c) \<in> r)" using 1 by auto
    then obtain a b c where abc: " x = (a @ b) \<and> y = (a @ c) \<and> (hd b) \<noteq> (hd c) \<and> (hd b, hd c) \<in> r" by auto
    have cyz: "y \<in> \<langle>A\<rangle> \<and> z \<in> \<langle>A\<rangle> \<and> compare r y z" using yz compare_set_def case_prod_conv by blast
    then have "compare r y z" by blast
    then have "compare_alt r y z" using comp_compalt assms lyz cyz by blast
    then have 2: "(y = z \<or> (\<exists> d e f. y = (d @ e) \<and> z = (d @ f) \<and> (hd e) \<noteq> (hd f) \<and> (hd e, hd f) \<in> r))" using compare_alt.cases by simp
    then show ?thesis
    proof(cases "y = z")
      case True
      then have "y = z" by auto
      have "y = (a @ c) \<and> (hd b) \<noteq> (hd c) \<and> (hd b, hd c) \<in> r" using False abc by auto
      then have "z = (a @ c) \<and> (hd b) \<noteq> (hd c) \<and> (hd b, hd c) \<in> r" using True by auto
      then show ?thesis using True xy by auto
    next
      case False note ynz = this
      then have "(\<exists> d e f. y = (d @ e) \<and> z = (d @ f) \<and> (hd e) \<noteq> (hd f) \<and> (hd e, hd f) \<in> r)" using 2 by auto
      then obtain d e f where def :"y = (d @ e) \<and> z = (d @ f) \<and> (hd e) \<noteq> (hd f) \<and> (hd e, hd f) \<in> r" by auto
      have "x = (a @ b) \<and> y = (a @ c) \<and> (hd b) \<noteq> (hd c) \<and> (hd b, hd c) \<in> r" using abc by auto
      have "y = (d @ e) \<and> z = (d @ f) \<and> (hd e) \<noteq> (hd f) \<and> (hd e, hd f) \<in> r" using def by auto
      then show ?thesis 
      proof(cases "length a \<le> length d")
        case True
        have y1:"y = (a @ c) \<and> y = (d @ e)" using abc def by blast
        then have "\<exists>s. d = a@s" using True eq_lenless by blast
        then obtain s where s: "d = (a @ s)" by auto
        then have "d = (a @ s)" by auto
        then have y:"y = (a @ s @ e) \<and> (hd e) \<noteq> (hd f) \<and> (hd e, hd f) \<in> r" using def by (simp add: def)
        have z:"z = (a @ s @ f) \<and> (hd e) \<noteq> (hd f) \<and> (hd e, hd f) \<in> r" using def by (simp add: \<open>d = a @ s\<close>)
        have x:"x = (a @ b) \<and> (hd b) \<noteq> (hd c) \<and> (hd b, hd c) \<in> r" using abc by auto
        have y2: "y = (a@c)" using abc by auto
        have A:"x \<in> \<langle>A\<rangle> \<and> y \<in> \<langle>A\<rangle> \<and> z \<in> \<langle>A\<rangle>" using xy yz compare_set_def by (simp add: cxy cyz)
        then show ?thesis 
        proof(cases "s = []")
          case True
          then have ad: "a = d" using s by auto
          then have "y = a@e \<and> z = a@f \<and> (hd e) \<noteq> (hd f) \<and> (hd e, hd f) \<in> r" using def by simp
          have "(a@c) = (a@e)"using y2 y True by simp
          then have "c = e" by simp
          then have "hd c = hd e" by simp
          then have t1: "(hd b \<noteq> hd e) \<and> (hd b, hd e) \<in> r" using x by auto
          have t2: "(hd e \<noteq> hd f) \<and> (hd e, hd f) \<in> r" using y by auto         
          moreover have "(x = (a@b)) \<and> (y = (d@e)) \<and> (z = (d@f))" using abc def by auto
          ultimately have "b \<in> \<langle>A\<rangle> \<and> e \<in> \<langle>A\<rangle> \<and> f \<in> \<langle>A\<rangle>" using A rightappend_span freewords_on_def by blast
          then have 3:"((hd b) \<in> (invgen A)) \<and> ((hd e) \<in> (invgen A)) \<and> ((hd f) \<in> (invgen A))" by (meson assms t1 t2 well_order_on_domain)
          then have 4:"(hd b \<noteq> hd f) \<and> (hd b, hd f) \<in> r" using assms 3 t1 t2 trans_r by blast
          moreover have "x = (a@b) \<and> z = (a@f)" using def ad by (simp add: x)
          ultimately have "\<exists> a b f. x = (a@b) \<and> z = (a@f) \<and> (hd b \<noteq> hd f) \<and> (hd b, hd f) \<in> r" by auto
          then have "compare_alt r x z" by simp
          then have "compare r x z" using compalt_comp by (metis assms cxy cyz lxy lyz)
          then have "x \<in> \<langle>A\<rangle> \<and> y \<in> \<langle>A\<rangle> \<and> (compare r x z)" using A by auto
          then have "(x, z) \<in> compare_set A r" using A compare_set_def by blast
          then show ?thesis by simp
        next
          case False
          then have "(a@c) = (a@s@e)"using y y1 by simp
          then have "c = (s @ e)" by simp
          then have "(hd c) = (hd s)" using False by auto
          then have "(hd b) \<noteq> (hd s) \<and> (hd b, hd s) \<in> r" using abc by auto
          moreover have "x = (a@b) \<and> z = (a@s@f)" using abc by (simp add: z)
          ultimately have "\<exists> a b s f. x = (a@b) \<and> z = (a@s@f) \<and> (hd b \<noteq> hd s) \<and> (hd b, hd s) \<in> r" by auto
          then have "compare_alt r x z" by (metis (no_types, lifting) False \<open>hd c = hd s\<close> abc compare_alt.simps hd_append2 z)
          then have "compare r x z" using compalt_comp by (metis assms cxy cyz lxy lyz)
          then have "x \<in> \<langle>A\<rangle> \<and> z \<in> \<langle>A\<rangle> \<and> (compare r x z)" using A by auto
          then have "(x, z) \<in> compare_set A r" using A compare_set_def by blast
          then show ?thesis by simp
        qed
      next
        case False
        then have "length a > length d" by auto
        moreover have y1:"y = (a @ c) \<and> y = (d @ e)" using abc def by blast
        ultimately have "\<exists>s. a = (d@s)" using eq_lengr by blast
        then obtain s where s: "a = d@s" by auto
        then have xy1: "x = (d@s@b) \<and> y= (d@s@c)" using abc by simp
        then show ?thesis 
        proof(cases "s = []")
          case True
          then have ad: "a = d" using s by auto
          then have "y = a@e \<and> z = a@f \<and> (hd e) \<noteq> (hd f) \<and> (hd e, hd f) \<in> r" using def by simp
          have "(d@c) = (d@e)" using y1 ad by blast
          then have "c = e" by simp
          then have "hd c = hd e" by simp
          then have t1: "(hd b \<noteq> hd e) \<and> (hd b, hd e) \<in> r" using abc by auto 
          have t2: "(hd e \<noteq> hd f) \<and> (hd e, hd f) \<in> r"  by (simp add: def)         
          moreover have "(x = (a@b)) \<and> (y = (d@e)) \<and> (z = (d@f))" using abc def by auto
          ultimately have "b \<in> \<langle>A\<rangle> \<and> e \<in> \<langle>A\<rangle> \<and> f \<in> \<langle>A\<rangle>" using False ad by auto
          then have 3:"((hd b) \<in> (invgen A)) \<and> ((hd e) \<in> (invgen A)) \<and> ((hd f) \<in> (invgen A))" by (meson assms t1 t2 well_order_on_domain)
          then have 4:"(hd b \<noteq> hd f) \<and> (hd b, hd f) \<in> r" using assms 3 t1 t2 trans_r by blast
          moreover have "x = (a@b) \<and> z = (a@f)" using False ad by auto
          ultimately have "\<exists> a b f. x = (a@b) \<and> z = (a@f) \<and> (hd b \<noteq> hd f) \<and> (hd b, hd f) \<in> r" by auto
          then have "compare_alt r x z" by simp
          then have "compare r x z" using compalt_comp by (metis assms cxy cyz lxy lyz)
          then have "x \<in> \<langle>A\<rangle> \<and> y \<in> \<langle>A\<rangle> \<and> (compare r x z)" using cxy by auto
          then have "(x, z) \<in> compare_set A r" using False ad by blast
          then show ?thesis by simp
        next
          case False
          then have "s \<noteq> []" by auto
          then have "(hd b \<noteq> hd c) \<and> (hd b, hd c) \<in> r" using abc by auto
          have "d@s@c = d@e" using xy1 def by simp
          then have "hd s = hd e" using False by fastforce
          moreover have "(hd e \<noteq> hd f) \<and> (hd e, hd f) \<in> r" using def by auto
          ultimately have "(hd s \<noteq> hd f) \<and> (hd s, hd f) \<in> r" by simp
          then have "\<exists> d s f b. x = (d@s@b) \<and> z = (d@f) \<and> (hd s \<noteq> hd f) \<and> (hd s, hd f) \<in> r" using def xy1 by blast
          then have "compare_alt r x z" by (metis (no_types, lifting) False \<open>hd s = hd e\<close> compare_alt.simps def hd_append2 xy1)
          then have cxz: "compare r x z" using compalt_comp by (metis assms cxy cyz lxy lyz)
          have "x \<in> \<langle>A\<rangle> \<and> z \<in> \<langle>A\<rangle>" by (simp add: cxy cyz)
          then have "(x,z) \<in> compare_set A r" using cxz compare_set_def by auto
          then show ?thesis by simp
        qed
      qed      
    qed
  qed
qed(simp)

fun lex :: "((('a,'b) groupgentype \<times> ('a,'b) groupgentype)) set \<Rightarrow> ('a, 'b) word \<Rightarrow> ('a, 'b) word \<Rightarrow> bool"
  where
"lex r x y = (if length x < length y then True else (if \<not> (length x > length y) then compare r x y else False))"

definition lex_set where "lex_set A r = {(x, y). x \<in> \<langle>A\<rangle> \<and> y \<in> \<langle>A\<rangle> \<and> lex r x y}"

lemma lex_refl_on:
  assumes "well_order_on (invgen A) r"
  shows "refl_on \<langle>A\<rangle> (lex_set A r)"
proof-
  have "\<forall>(x,y) \<in> (lex_set A r). x \<in> \<langle>A\<rangle> \<and> y \<in> \<langle>A\<rangle>" using lex_set_def using case_prod_conv by blast
  then have 1:"(lex_set A r) \<subseteq> \<langle>A\<rangle> \<times>\<langle>A\<rangle>" by auto
  have "\<forall>x\<in>\<langle>A\<rangle>. lex r x x" by (metis assms lex.elims(3) refl_compare)
  then have 2:"(\<forall>x\<in>\<langle>A\<rangle>. (x, x) \<in> (lex_set A r))" using lex_set_def by blast
  then have "refl_on \<langle>A\<rangle> (lex_set A r)" by (simp add: "1" refl_onI)
  then show ?thesis by auto
qed


lemma antisymm_lex :
  assumes "well_order_on (invgen A) r"
  shows "(\<forall>x y.  (x, y) \<in> lex_set A r \<longrightarrow> (y, x) \<in> lex_set A r \<longrightarrow> x = y)"
  apply (rule allI)+
  apply (rule impI)+
proof-
  fix x y
  assume xy: "(x, y) \<in> lex_set A r" and yx: "(y, x) \<in> lex_set A r"
  have lexy:"lex r x y" using xy yx assms lex_set_def using case_prodD by blast
  then show "x = y"
  proof(cases "length x < length y")
    case True
    have lxy: "length x < length y" using True by auto
    have "lex r y x" using yx assms lex_set_def using case_prodD by blast
    then show ?thesis 
    proof(cases "length x > length y")
      case True
      then have "length x = length y" using True lxy by simp
      then show ?thesis using True nat_neq_iff by blast
    next
      case False
      then have "length x < length y" using lxy by blast
      then have "\<not>(length y > length x)" using \<open>NielsonSchreier.lex r y x\<close> by auto
      then show ?thesis by (simp add: lxy)
    qed
  next
    case False
    then have glxy: "length x \<ge> length y" by auto
    have lyx:"lex r y x" using yx assms lex_set_def using case_prodD by blast
    then show ?thesis 
    proof (cases "length x = length y")
      case True
      then have "length x = length y" using glxy by simp
      moreover then have cryx: "compare r y x" using lex_def False lyx by force
      moreover have crxy : "compare r x y" using xy False lexy by (metis lex.elims(2))
      have cxy: "(x,y) \<in> compare_set A r" using crxy compare_set_def lexy assms refl_on_domain lex_refl_on xy by fastforce
      have cyx: "(y,x) \<in> compare_set A r" using cryx compare_set_def lyx using assms cxy refl_on_domain reflon_comp by fastforce
      then show ?thesis using antisym_compare True cyx cxy compare_set_def using assms by blast
    next
      case False
      then have "\<not>(lex r x y)"  by (metis glxy leD lex.elims(2) order_le_imp_less_or_eq)
      then show ?thesis using lexy by simp
    qed
  qed
qed

lemma lex_antisym:
  assumes "well_order_on (invgen A) r"
  shows "antisym (lex_set A r)"
  using antisymm_lex by (metis antisymI assms)
 
lemma lex_trans:
  assumes "well_order_on (invgen A) r"
  shows "trans (lex_set A r)"
  unfolding trans_def
  apply(rule allI)+
  apply(rule impI)+
proof-
  fix x y z assume xy:"(x, y) \<in> (lex_set A r)" and yz: "(y, z) \<in> (lex_set A r)"
  then show "(x, z) \<in> lex_set A r"
  proof(cases "length x < length y")
    case True
    then have lxy: "length x < length y" by simp
    then show ?thesis
    proof(cases "length y < length z")
      case True
      then have "length x < length z" using lxy less_trans by blast
      then show ?thesis using lex.simps xy yz unfolding lex_set_def by auto
    next
      case False
      then have "length y = length z" using yz lex.simps unfolding lex_set_def using linorder_neqE_nat by force
      then have "length x < length z" using lxy by auto
      then show ?thesis using lex.simps xy yz unfolding lex_set_def by auto
    qed
  next
    case False
    then have exy: "length x = length y" using xy lex.simps unfolding lex_set_def  by (metis (no_types, lifting) case_prodD linorder_neqE_nat mem_Collect_eq)
    then show ?thesis
    proof(cases "length y < length z")
      case True
      then have "length x < length z" by (simp add: True exy)
      then show ?thesis using lex.simps xy yz unfolding lex_set_def by auto
    next
      case False
      then have eyz:"length y = length z" using yz lex.simps unfolding lex_set_def using linorder_neqE_nat by force
      then have "lex r y z = compare r y z" using lex.simps by auto
      moreover have "lex r x y = compare r x y" using exy lex.simps by auto
      moreover have "y \<in> \<langle>A\<rangle> \<and> z \<in> \<langle>A\<rangle> \<and> lex r y z" using yz unfolding lex_set_def by blast
      moreover have "x \<in> \<langle>A\<rangle> \<and> lex r x y" using xy unfolding lex_set_def by blast
      ultimately have "(x,y) \<in> compare_set A r \<and> (y, z) \<in> compare_set A r" unfolding compare_set_def by blast 
      then have "compare r x z" using exy eyz assms trans_compare[of "A" "r"] unfolding compare_set_def using case_prodD mem_Collect_eq by blast
      moreover have "lex r x  z = compare r x z" using exy eyz lex.simps by auto
      ultimately show ?thesis using xy yz unfolding lex_set_def by fastforce
    qed
  qed
qed

lemma lex_total_on:
  assumes "well_order_on (invgen A) r"
  shows "total_on \<langle>A\<rangle> (lex_set A r)"
  unfolding total_on_def
  apply(rule ballI)+
  apply(rule impI)
proof-
  fix x y assume x: "x \<in> \<langle>A\<rangle>" and y: "y \<in> \<langle>A\<rangle>" and xy: "x \<noteq> y"
  then show "(x, y) \<in> lex_set A r \<or> (y, x) \<in> lex_set A r"
  proof(cases "length x = length y")
    case True
    then have "lex r x y = compare r x y" using lex.simps by simp
    moreover have "lex r y x = compare r y x"  using True lex.simps by simp
    moreover have "(x, y) \<in> compare_set A r \<or> (y, x) \<in> compare_set A r" using x y xy True total_on_compare[of "A" "r"] assms by blast
    ultimately show ?thesis using x y unfolding lex_set_def compare_set_def by fastforce
  next
    case False
    then have lxy: "length x \<noteq> length y" by simp
    then show ?thesis
    proof(cases "length x < length y")
      case True
      then have "lex r x y" by simp
      then show ?thesis using x y unfolding lex_set_def by blast
    next
      case False
      then have "length x > length y" using lxy by auto
      then have "lex r y x" by simp
      then show ?thesis using x y unfolding lex_set_def by blast
    qed
  qed
qed

fun lex_lift :: "('a,'b) monoidgentype set \<Rightarrow> ((('a,'b) groupgentype \<times> ('a,'b) groupgentype)) set \<Rightarrow> ('a, 'b) word set \<Rightarrow> ('a,'b) word set \<Rightarrow> bool"
  where
"lex_lift S r a b = (lex r (red_rep S a) (red_rep S b))"

definition lexlift_set :: "('a,'b) monoidgentype set \<Rightarrow> (('a,'b) word set) set \<Rightarrow> (('a,'b) groupgentype \<times> ('a,'b) groupgentype) set \<Rightarrow> ((('a,'b) word set \<times> ('a,'b) word set)) set"
  where "lexlift_set S A r = {(a,b). a \<in> A \<and> b \<in> A \<and> lex_lift S r a b}"

definition least :: "('a \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> 'a"
  where
"least r A = (THE x. x \<in> A \<and> (\<forall>w \<in> A. (x,w) \<in> r))"
(*least (nat_eq_less) (length ` S) \<le> (length ` S)*)

definition least_hd :: "(('a,'b) groupgentype \<times> ('a,'b) groupgentype) set \<Rightarrow> ('a, 'b) word set \<Rightarrow> ('a,'b) groupgentype"
  where
"least_hd r A = least r (hd ` A)"

lemma hd_sub_span:
  assumes "[] \<notin> S"
    and "S \<subseteq> \<llangle>A\<rrangle>"
  shows "hd ` S \<subseteq>  A"
proof(rule subsetI)
  fix x assume x: "x \<in> hd ` S"
  moreover then have "x \<in> hd ` \<llangle>A\<rrangle>" using assms(2) by blast
  ultimately show "x \<in>  A" by (metis (no_types, lifting) assms(1) assms(2) gen_spanset image_iff in_mono)
qed


lemma least_exists: 
  assumes "well_order_on (invgen A) r"
  and "[] \<notin> S"
  and "S \<noteq> {}" 
  and "S \<subseteq> \<langle>A\<rangle>"
shows "\<exists>x \<in>  hd ` S.  \<forall>w \<in> hd ` S. (x,w) \<in> r"
proof-
  have 1:"hd ` S \<subseteq> (invgen A)" using assms(2) assms(4) unfolding freewords_on_def by (simp add: hd_sub_span)
  obtain x where "x \<in> S" using assms(3) by auto
  then obtain hx where "hx \<in>  hd ` S" by blast
  then show ?thesis using assms(1) assms(3) unfolding well_order_on_def by (metis Linear_order_wf_diff_Id 1 assms(1) image_is_empty well_order_on_Field)
qed

lemma least_unique: 
  assumes "well_order_on (invgen A) r"
  and "[] \<notin> S"
  and "S \<noteq> {}" 
  and "S \<subseteq> \<langle>A\<rangle>"
shows "\<exists>!x \<in>  hd ` S.  \<forall>w \<in> hd ` S. (x,w) \<in> r"
proof(rule classical)
  have "\<exists>x \<in>  hd ` S.  \<forall>w \<in> hd ` S. (x,w) \<in> r" using least_exists assms by auto
  then obtain x where x:"x \<in>  hd ` S \<and>  (\<forall>w \<in> hd ` S. (x,w) \<in> r)" by blast
  assume "\<not>(\<exists>!x \<in>  hd ` S.  \<forall>w \<in> hd ` S. (x,w) \<in> r)"
  then obtain y where y:"y \<in>  hd ` S \<and>  (\<forall>w \<in> hd ` S. (y,w) \<in> r) \<and> y \<noteq> x" using x by metis
  then have "(x,y) \<in> r \<and> (y, x) \<in> r" using x y by blast
  then have "x = y" by (metis assms(1) trans_r well_order_on_domain)
  then have False using y by auto
  then show "\<exists>!x \<in>  hd ` S.  \<forall>w \<in> hd ` S. (x,w) \<in> r" by simp
qed

lemma least_hd_the: 
  assumes "well_order_on (invgen A) r"
  and "[] \<notin> S"
  and "S \<noteq> {}" 
  and "S \<subseteq> \<langle>A\<rangle>"
shows "(least_hd r S) \<in>  hd ` S \<and> (\<forall>x \<in> hd ` S. ((least_hd r S),x) \<in> r)"
  unfolding least_hd_def least_def
proof(rule theI')
  show "\<exists>!x. x \<in> hd ` S \<and> (\<forall>w\<in>hd ` S. (x, w) \<in> r)" using assms least_unique[of "A" "r" "S"] by auto
qed

fun leastcons_comp :: "(('a,'b) groupgentype \<times> ('a,'b) groupgentype) set \<Rightarrow> (('a, 'b) word \<times> (('a, 'b) word set)) \<Rightarrow> (('a, 'b) word \<times> ('a, 'b) word set)"
  where
"leastcons_comp r (xs, A) =  (xs@[(least_hd r A)], {w \<in> tl ` A. ([least_hd r A]@w \<in> A)})"

fun tuple_appendset :: "('a list \<times> 'a list set) \<Rightarrow> ('a list set)"
  where
"tuple_appendset (xs, S) = (append xs) ` S"

lemma tuple_append: assumes "a \<in> tuple_appendset (xs, S)"
  shows "\<exists>ys \<in> S. a = (xs @ ys)"
proof-
  have "a \<in> (append xs) ` S" using assms tuple_appendset.simps by blast
  then show ?thesis by (simp add: image_iff)
qed

lemma least_consappend_in: 
  assumes "leastcons_comp r (xs, S) = (ys, T)"
  and "zs \<in> T"
shows "[(least_hd r S)]@zs \<in> S"
proof-
  have "T = {w \<in> tl ` S. [least_hd r S] @ w \<in> S}" using assms(1) leastcons_comp.simps[of "r" "xs" "S"] by force
  then show ?thesis using assms(2) using assms(1) by fastforce
qed

lemma least_consappend_sub: 
  assumes "well_order_on (invgen A) r"
  and "S \<subseteq> \<langle>A\<rangle>"
  and "leastcons_comp r (xs, S) = (ys, T)"
shows "tuple_appendset (ys, T) \<subseteq> tuple_appendset (xs, S)"
proof(rule subsetI)
  fix x assume x:  "x \<in> tuple_appendset (ys, T)"
  then obtain zs where zs:"zs \<in> T \<and> x = ys@zs" using tuple_append by blast
  moreover have "ys = xs@[(least_hd r S)]" using leastcons_comp.simps  assms(3) by force
  moreover have "[(least_hd r S)]@zs \<in> S" using zs assms(3)  least_consappend_in  by blast
  ultimately show "x \<in> tuple_appendset (xs, S)" using tuple_appendset.simps by simp
qed


lemma least_cons_lesshd:
  assumes "well_order_on (invgen A) r"
  and "S \<subseteq> \<langle>A\<rangle>"   
  and "leastcons_comp r (xs, S) = (ys, T)"
  and "[] \<notin> S"
  and "x \<in> tuple_appendset (xs, S) \<and> x = (xs@x1)"
  and "x \<notin> tuple_appendset (ys, T)"
shows "hd x1 \<noteq> (least_hd r S)"
proof(rule ccontr)
  assume "\<not> (hd x1 \<noteq> (least_hd r S))"
  then have c:"hd x1 = (least_hd r S)" by simp
  moreover have 1:"x1 \<in> S" using assms(5) by auto
  ultimately have "x = xs@([(least_hd r S)]@(tl x1))" using assms(4)  by (metis append_Cons append_self_conv2 assms(5) list.collapse)
  moreover have "ys = xs @ [(least_hd r S)]" using assms(3) leastcons_comp.simps[of "r" "xs" "S"] by auto
  ultimately have 2:"x = ys@(tl x1)" by simp
  have "tl x1 \<in> {w \<in> tl ` S. [least_hd r S] @ w \<in> S}" using c 1 by (metis (no_types, lifting) append_Cons append_Nil assms(4) image_eqI list.collapse mem_Collect_eq)
  then have "tl x1 \<in> T" using assms(3) leastcons_comp.simps[of "r" "xs" "S"] by auto
  then have "x \<in> tuple_appendset (ys, T)" using 2 tuple_appendset.simps[of "ys" "T"] by simp
  then show False using assms(6) by blast
qed

lemma length_decrease:
  assumes "leastcons_comp r (xs, S) = (ys, T)"
  and "\<forall>x \<in> S. length x = n"
  and "n > 0"
shows "\<forall>x \<in> T. length x = n - 1"
proof(rule ballI)
  fix x assume x:"x \<in> T"
  then have "x \<in> {w \<in> tl ` S. ([least_hd r S]@w \<in> S)}" using assms(1) leastcons_comp.simps by auto
  then obtain x1 where "x1 \<in> S \<and> x = tl x1"  by blast
  moreover then have "length x1 = n" using assms(2) by simp
  ultimately show "length x = n - 1" using assms(3)  by simp
qed

lemma length_increase:
  assumes "leastcons_comp r (xs, S) = (ys, T)"
  and "\<forall>x \<in> S. length x = n"
  and "n > 0"
shows "length ys = length xs + 1"
proof-
  have "ys = xs @ [least_hd r S]" using assms(1) leastcons_comp.simps by simp
  then show ?thesis  by simp
qed

lemma length_invariant:
assumes "leastcons_comp r (xs, S) = (ys, T)"
  and "\<forall>x \<in> S. length x = n"
  and "n > 0"
shows "\<forall>x y. (x \<in> tuple_appendset (xs, S) \<and>  y \<in> tuple_appendset (ys, T)) \<longrightarrow> length x = length y"
  apply(rule allI)+
  apply(rule impI)
proof-
  fix x y assume xy: "x \<in> tuple_appendset (xs, S) \<and>  y \<in> tuple_appendset (ys, T)"
  obtain x1 where x:"x1 \<in> S \<and> x = xs @ x1" using xy tuple_append by blast
  then have x1: "length x1 = n" using assms(2) by auto
  then have lx:"length x = length xs + n" using x by simp
  obtain y1 where "y1 \<in> T \<and> y = ys @ y1" using xy tuple_append by blast
  moreover then have "length y1 = (n - 1)" using assms length_decrease by auto
  moreover have "length ys = length xs + 1" using assms length_increase by auto
  ultimately have "length y = length xs + n" by (simp add: assms(3))
  then show "length x = length y" using lx by simp
qed

lemma least_cons_less:
assumes "well_order_on (invgen A) r"
  and "S \<subseteq> \<langle>A\<rangle>"
  and "[] \<notin> S" 
  and "leastcons_comp r (xs, S) = (ys, T)"
and "\<forall>x \<in> S. length x = n"
  and "n > 0"
  and "xs \<in> \<langle>A\<rangle>"
shows "\<forall>x y. (x \<in> tuple_appendset (xs, S) \<and>  x \<notin> tuple_appendset (ys, T)) \<longrightarrow> y \<in> tuple_appendset (ys, T) \<longrightarrow> (y, x) \<in> compare_set A r"
  apply(rule allI)+
  apply(rule impI)+
proof-
  fix x y assume x:"x \<in> tuple_appendset (xs, S) \<and> x \<notin> tuple_appendset (ys, T)" and y: "y \<in> tuple_appendset (ys, T)"
  obtain x1 where x1:"x1 \<in> S \<and> x = xs@x1" using tuple_append x by blast
  then have 1:"hd x1 \<noteq> (least_hd r S)" using assms(1) assms(2) assms(3) assms(4) least_cons_lesshd x by blast
  have "hd x1 \<in> hd ` S" using x1 by simp
  then have 2:"((least_hd r S),hd x1) \<in> r" using least_hd_the[of "A" "r" "S"] assms by blast
  have "ys = xs @ [(least_hd r S)]" using assms(4) leastcons_comp.simps by fastforce
  moreover obtain y1 where y1:"y1 \<in> T \<and> y = ys@y1" using tuple_append y by blast
  ultimately have ya:"y = xs @ ([(least_hd r S)] @ y1)" by simp
  moreover have "hd ([(least_hd r S)] @ y1) = (least_hd r S)" by simp
  ultimately have "x = xs@x1 \<and> y = xs @ ([(least_hd r S)] @ y1) \<and> hd ([(least_hd r S)] @ y1) \<noteq> hd x1 \<and> (hd ([(least_hd r S)] @ y1), hd x1) \<in> r" using x1 1 2 compare_alt.simps by auto
  then have "compare_alt r y x" using compare_alt.simps[of "r" "x" "y"] by force
  moreover have "length x = length y" using assms(4) assms(5) assms(6) length_invariant x y by auto
  moreover have xA: "x \<in> \<langle>A\<rangle>" using assms(2) assms(7) span_append freewords_on_def x1 by blast
  moreover have yA: "y \<in> \<langle>A\<rangle>"  using ya assms(2) assms(4) assms(7) least_consappend_in span_append freewords_on_def y1 by blast
  ultimately have "compare r y x" using compalt_comp assms(1) by metis
  then show "(y, x) \<in> compare_set A r" using compare_set_def xA yA by blast
qed

fun leastn_comp :: "(('a,'b) groupgentype \<times> ('a,'b) groupgentype) set \<Rightarrow> nat \<Rightarrow> (('a, 'b) word \<times> (('a, 'b) word set)) \<Rightarrow> (('a, 'b) word \<times> (('a, 'b) word set))"
  where
"leastn_comp r 0 (xs, A) = (xs, A)"|
"leastn_comp r n (xs, A) = leastn_comp r (n - 1) (leastcons_comp r (xs, A))"

definition least_comp :: "(('a,'b) groupgentype \<times> ('a,'b) groupgentype) set \<Rightarrow> nat \<Rightarrow> ('a, 'b) word set \<Rightarrow> ('a, 'b) word"
  where
"least_comp r n A = fst (leastn_comp r n ([], A))"

lemma leastcons_comp_fstsub:
assumes "well_order_on (invgen A) r"
  and "S \<subseteq> \<langle>A\<rangle>"
  and "leastcons_comp r (xs, S) = (ys, T)"
shows "T \<subseteq> \<langle>A\<rangle>"
proof(rule subsetI)
  fix x assume x:"x \<in> T"
  then have "x \<in> {w \<in> tl ` S. [least_hd r S] @ w \<in> S}" using assms(3) leastcons_comp.simps by simp
  then show "x \<in> \<langle>A\<rangle>" using assms(2) span_cons by (metis (no_types, lifting) x append_Cons append_Nil2 append_eq_append_conv2 assms(3) in_mono least_consappend_in same_append_eq freewords_on_def)
qed

lemma leastcons_notempty:
assumes "well_order_on (invgen A) r"
  and "S \<subseteq> \<langle>A\<rangle>"
  and "\<forall>x \<in> S. length x = n"
  and "n > 0"
  and "S \<noteq> {}"
  and "leastcons_comp r (xs, S) = (ys, T)"
shows "T \<noteq> {}"
proof-
  have 1:"[] \<notin> S" using assms(3) assms(4)  by auto
  then have "(least_hd r S) \<in>  hd ` S"using assms  using least_hd_the by blast
  moreover then obtain x where "x \<in> S \<and> hd x = (least_hd r S)" by auto
  then have "tl x \<in> {w \<in> tl ` S. [least_hd r S] @ w \<in> S}" using 1 assms(6) by (metis (no_types, lifting) append_Cons append_self_conv2 hd_Cons_tl image_eqI mem_Collect_eq)
  then show ?thesis using leastcons_comp.simps[of "r" "xs" "S"] using assms(6) by fastforce
qed

lemma nil_set:
  assumes "S \<noteq> {}"
  and "\<forall>x \<in> S. length x = n"
  and "n = 0"
shows "S = {[]}"
proof-
  have A:"[] \<in> S"
  proof-
  obtain x where 1:"x \<in> S" using subsetI assms(1) by blast
  then have "length x = 0" using assms(2) assms(3) by simp
  then have "x = []"  by simp
  then show ?thesis using 1  by simp
qed
  then have "{[]} \<subseteq> S" by simp
  moreover have "S \<subseteq> {[]}"
  proof(rule subsetI)
    fix x assume "x \<in> S"
    then have "length x = 0" using assms(2) assms(3) by simp
    then have "x = []"  by simp
    then show "x \<in> {[]}"  by simp
  qed 
  ultimately show ?thesis by auto
qed

lemma leastn_comp_empty:
assumes "well_order_on (invgen A) r"
  and "S \<subseteq> \<langle>A\<rangle>"
  and "\<forall>x \<in> S. length x = n"
  and "n > 0"
  and "leastn_comp r n (x, S) = (xs, T)"
  and "S \<noteq> {}"
shows "T = {[]}"
  using assms
proof(induction n arbitrary:x  S)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?ys = "fst (leastcons_comp r (x, S))"
  let ?U = "snd (leastcons_comp r (x, S))"
  have "leastn_comp r (Suc n) (x, S) = leastn_comp r n (leastcons_comp r (x, S))" using leastn_comp.simps(2) by simp
  then have "leastn_comp r (Suc n) (x, S) = leastn_comp r n (?ys, ?U)" by simp
  then have 1:"leastn_comp r n (?ys, ?U) = (xs, T)" using Suc.prems by argo
  have "\<forall>x \<in> ?U. length x = (Suc n) - 1" using Suc.prems length_decrease[of "r" "x" "S" "?ys" "?U" "Suc n"] using surjective_pairing by blast
  then have U:"\<forall>x \<in> ?U. length x = n" by simp
  have "leastcons_comp r (x, S) = (fst (leastcons_comp r (x, S)), snd (leastcons_comp r (x, S)))" by simp
  then have US: "?U \<noteq> {}" using Suc.prems leastcons_notempty[of "A" "r" "S" "n" "x" "?ys" "?U"] using leastcons_notempty by blast
  show ?case
  proof(cases "n > 0")
    case True
    have "(leastcons_comp r (x, S)) = (?ys, ?U)" by simp
    then have "?U \<subseteq> \<langle>A\<rangle>" using Suc.prems leastcons_comp_fstsub[of "A" "r" "S" "x" "?ys" "?U"] by auto
    then show ?thesis using US Suc.prems Suc.IH[of "?U"] 1 U True by blast
  next
    case False
    then have n:"n = 0" by auto
    then have "leastn_comp r n (?ys, ?U) = (?ys, ?U)" using leastn_comp.simps(1) by fast
    then have "?U = T" by (metis "1" prod.inject)
    moreover have "?U = {[]}" using U n US nil_set[of "?U" "n"] by linarith
    ultimately show ?thesis by simp
  qed
qed

lemma leastn_comp_fst:
assumes "well_order_on (invgen A) r"
  and "S \<subseteq> \<langle>A\<rangle>"
  and "\<forall>x \<in> S. length x = n"
  and "n > 0"
  and "leastn_comp r n (x, S) = (xs, T)"
  and "S \<noteq> {}"
shows "\<forall>y \<in> tuple_appendset (xs, T). y = fst (xs, T)"
proof-
  have "T = {[]}" using leastn_comp_empty assms by blast
  then have "tuple_appendset (xs, T) = {xs}" using tuple_appendset.simps by (simp add: image_is_empty)
  then show ?thesis by auto
qed

lemma leastn_comp_sub:
assumes "well_order_on (invgen A) r"
  and "S \<subseteq> \<langle>A\<rangle>"
  and "\<forall>x \<in> S. length x = n"
  and "n > 0"
  and "leastn_comp r n (xs, S) = (ys, T)"
  and "S \<noteq> {}"
shows "tuple_appendset (ys, T) \<subseteq> tuple_appendset (xs, S)"
  using assms
proof(induction n arbitrary: ys S xs T)
  case 0
  then show ?case by blast
next
  case (Suc n)
  let ?ys = "fst (leastcons_comp r (xs, S))"
  let ?U = "snd (leastcons_comp r (xs, S))"
  have "leastn_comp r (Suc n) (xs, S) = leastn_comp r n (leastcons_comp r (xs, S))" using leastn_comp.simps(2) by simp
  then have "leastn_comp r (Suc n) (xs, S) = leastn_comp r n (?ys, ?U)" by simp
  then have 1:"leastn_comp r n (?ys, ?U) = (ys, T)" using Suc.prems by argo
  have A:"tuple_appendset (?ys, ?U) \<subseteq> tuple_appendset (xs, S)" by auto
  have "\<forall>x \<in> ?U. length x = (Suc n) - 1" using Suc.prems length_decrease[of "r" "xs" "S" "?ys" "?U" "Suc n"] using surjective_pairing by blast
  then have U:"\<forall>x \<in> ?U. length x = n" by simp
  have "leastcons_comp r (xs, S) = (fst (leastcons_comp r (xs, S)), snd (leastcons_comp r (xs, S)))" by simp
  then have US: "?U \<noteq> {}" using Suc.prems leastcons_notempty[of "A" "r" "S" "n" "xs" "?ys" "?U"] using leastcons_notempty by blast
  have "tuple_appendset (ys, T) \<subseteq> tuple_appendset (?ys, ?U)"
  proof(cases "n > 0")
    case True
    have "(leastcons_comp r (xs, S)) = (?ys, ?U)" by simp
    then have "?U \<subseteq> \<langle>A\<rangle>" using Suc.prems leastcons_comp_fstsub[of "A" "r" "S" "xs" "?ys" "?U"] by auto
    then show ?thesis using 1 U US Suc.prems(1) True Suc.IH[of "?U" "?ys" "ys" "T"]  by blast
next
  case False
  then have "(?ys, ?U) = (ys, T)" using 1 leastn_comp.simps  by auto
  then show ?thesis  by simp
qed
  then show ?case using A  by blast
qed

lemma least_hd_span:
assumes "well_order_on (invgen A) r"
  and "S \<subseteq> \<langle>A\<rangle>"
  and "[] \<notin> S"
  and "S \<noteq> {}"
  and "xs \<in> \<langle>A\<rangle>"
shows  "[(least_hd r S)] \<in> \<langle>A\<rangle>"
proof-
  have "least_hd r S \<in> hd ` S" using assms(1) assms(2) assms(3) assms(4) least_hd_the by auto
  moreover have "hd ` S \<subseteq> invgen A" by (metis assms(2) assms(3) hd_sub_span freewords_on_def)
  ultimately show ?thesis unfolding freewords_on_def using group_spanset.empty group_spanset.gen subsetD by blast
qed

lemma leastn_comp_less:
assumes "well_order_on (invgen A) r"
  and "S \<subseteq> \<langle>A\<rangle>"
  and "\<forall>x \<in> S. length x = n"
  and "n > 0"
  and "leastn_comp r n (xs, S) = (ys, T)"
  and "S \<noteq> {}"
  and "xs \<in> \<langle>A\<rangle>"
shows  "\<forall>x y. (x \<in> tuple_appendset (xs, S) \<and>  x \<notin> tuple_appendset (ys, T)) \<longrightarrow> y \<in> tuple_appendset (ys, T) \<longrightarrow> (y, x) \<in> compare_set A r"
  using assms
proof(induction n arbitrary: xs S ys T)
  case 0
  then show ?case by blast
next
  case (Suc n)
  let ?ys = "fst (leastcons_comp r (xs, S))"
  let ?U = "snd (leastcons_comp r (xs, S))"
  have "leastn_comp r (Suc n) (xs, S) = leastn_comp r n (leastcons_comp r (xs, S))" using leastn_comp.simps(2) by simp
  then have "leastn_comp r (Suc n) (xs, S) = leastn_comp r n (?ys, ?U)" by simp
  then have 1:"leastn_comp r n (?ys, ?U) = (ys, T)" using Suc.prems by argo
  have A:"tuple_appendset (?ys, ?U) \<subseteq> tuple_appendset (xs, S)" by auto
  have L:"(leastcons_comp r (xs, S)) = (?ys, ?U)" by simp
 have eS: "[] \<notin> S" using Suc.prems(3)  by (metis Suc.prems(4) bot_nat_0.not_eq_extremum list.size(3))
  have C:"\<forall>x y. (x \<in> tuple_appendset (xs, S) \<and>  x \<notin> tuple_appendset (?ys, ?U)) \<longrightarrow> y \<in> tuple_appendset (?ys, ?U) \<longrightarrow> (y, x) \<in> compare_set A r" using L Suc.prems eS least_cons_less[of "A" "r"  "S" "xs"  "?ys" "?U" "Suc n"] by fastforce
  have "\<forall>x \<in> ?U. length x = (Suc n) - 1" using Suc.prems length_decrease[of "r" "xs" "S" "?ys" "?U" "Suc n"] using surjective_pairing by blast
  then have U:"\<forall>x \<in> ?U. length x = n" by simp
  have "leastcons_comp r (xs, S) = (fst (leastcons_comp r (xs, S)), snd (leastcons_comp r (xs, S)))" by simp
  then have US: "?U \<noteq> {}" using Suc.prems leastcons_notempty[of "A" "r" "S" "n" "xs" "?ys" "?U"] using leastcons_notempty by blast
  then show ?case
  proof(cases "n > 0")
    case True
    then have n: "n > 0" by simp
    then have eU:"[] \<notin> ?U" using U by fastforce
    have "[(least_hd r S)] \<in> \<langle>A\<rangle>" using least_hd_span  by (metis Suc.prems(2) Suc.prems(3) Suc.prems(6) Zero_not_Suc assms(1) assms(7) list.size(3))
    then have yA: "?ys \<in> \<langle>A\<rangle>" using Suc.prems(7) leastcons_comp.simps freewords_on_def span_append by fastforce
    then have UA:"?U \<subseteq> \<langle>A\<rangle>" using Suc.prems leastcons_comp_fstsub[of "A" "r" "S" "xs" "?ys" "?U"] by auto
    then have A:"\<forall>x y. x \<in> tuple_appendset (?ys, ?U) \<and> x \<notin> tuple_appendset (ys, T) \<longrightarrow> y \<in> tuple_appendset (ys, T) \<longrightarrow> (y, x) \<in> compare_set A r"
     using yA 1 U US Suc.prems(1) True Suc.IH[of "?U" "?ys" "ys" "T"] by blast
    then  have B: "\<forall>x y. x \<in> tuple_appendset (?ys, ?U) \<and> y \<in> tuple_appendset (ys, T) \<longrightarrow> (y, x) \<in> compare_set A r \<or> x \<in> tuple_appendset (ys, T)" by blast
    show ?thesis apply(rule allI)+ apply(rule impI)+
    proof-
      fix x y assume x: "x \<in> tuple_appendset (xs, S) \<and> x \<notin> tuple_appendset (ys, T)" and y: "y \<in> tuple_appendset (ys, T) "
      then have yy:"y \<in> tuple_appendset (?ys, ?U)" using Suc.prems(1) UA U True US 1 leastn_comp_sub[of "A" "r" "?U" "n" "?ys" "ys" "T"] by blast
      show "(y, x) \<in> compare_set A r"
      proof(cases "x \<in> tuple_appendset (?ys, ?U)")
        case True
        then show ?thesis using x B  y by blast
      next
        case False
        then show ?thesis using C yy  x by blast
      qed
    qed
  next
    case False
    then have "n = 0" by simp
    then have "(ys, T) = (?ys, ?U)" using 1 by auto
    then show ?thesis using C by blast
  qed
qed

lemma leastn_comp_single:
assumes "well_order_on (invgen A) r"
  and "S \<subseteq> \<langle>A\<rangle>"
  and "\<forall>x \<in> S. length x = n"
  and "n > 0"
  and "S \<noteq> {}"
shows "tuple_appendset (leastn_comp r n ([], S)) = {least_comp r n S}"
proof-
  let ?ys = "fst (leastn_comp r n ([], S))" and ?T = "snd (leastn_comp r n ([], S))"
  have a:"(leastn_comp r n ([], S)) = (?ys, ?T)" by simp
  then have T: "?T = {[]}" using assms leastn_comp_empty by blast
  then have b:"tuple_appendset (?ys, ?T) = {fst(?ys, ?T)}" using T tuple_appendset.simps by force
  have "fst (leastn_comp r n ([], S)) = fst (?ys, ?T)" using a by simp
  then have c:"{least_comp r n S} = {fst (?ys, ?T)}" using least_comp_def by auto
  then show ?thesis using a b c by presburger
qed

lemma least_comp_least:
assumes "well_order_on (invgen A) r"
  and "S \<subseteq> \<langle>A\<rangle>"
  and "\<forall>x \<in> S. length x = n"
  and "n > 0"
  and "S \<noteq> {}"
shows "\<forall>x \<in> S. ((least_comp r n S), x) \<in> compare_set A r"
  apply(rule ballI)
proof-
  fix x assume x: "x \<in> S"
  have 1:"tuple_appendset (leastn_comp r n ([], S)) = {(least_comp r n S)}" using assms leastn_comp_single by blast
  have 2:"tuple_appendset ([], S) = S" using tuple_appendset.simps  by simp
  have 3:"x \<in> \<langle>A\<rangle>" using assms(2) x by blast
  then show "(least_comp r n S, x) \<in> compare_set A r"
  proof(cases "x = (least_comp r n S)")
    case True
    have "compare r (least_comp r n S) x" using refl_compare assms(1) 3 True by blast
    then show ?thesis using 3 unfolding compare_set_def True by blast
  next
    case False
    let ?T = "snd (leastn_comp r n ([], S))"
    have A:"leastn_comp r n ([], S) = ((least_comp r n S), ?T)" by (simp add: least_comp_def)
    then have B:"tuple_appendset ((least_comp r n S), ?T) = {(least_comp r n S)}" using 1 by auto
    then have "x \<notin> tuple_appendset ((least_comp r n S), ?T)" using 1 False by auto
    moreover have "least_comp r n S \<in> tuple_appendset ((least_comp r n S), ?T)" using 1 B by auto
    moreover have "x \<in> tuple_appendset ([], S)" using x 2 by auto
    moreover have "[] \<in> \<langle>A\<rangle>" unfolding freewords_on_def using empty by auto
    ultimately show ?thesis using assms A leastn_comp_less by blast
  qed
qed

lemma least_comp_in:
assumes "well_order_on (invgen A) r"
  and "S \<subseteq> \<langle>A\<rangle>"
  and "\<forall>x \<in> S. length x = n"
  and "n > 0"
  and "S \<noteq> {}"
shows "(least_comp r n S) \<in> S"
proof-
  let ?ys = "fst (leastn_comp r n ([], S))"
  let ?T = "snd (leastn_comp r n ([], S))"
  have "tuple_appendset (?ys, ?T) = {least_comp r n S}" using assms leastn_comp_single by (metis prod.collapse)
  moreover have "[] \<in> \<langle>A\<rangle>" unfolding freewords_on_def using empty by auto
  ultimately have "{least_comp r n S} \<subseteq> tuple_appendset ([], S)" using leastn_comp_sub[of "A" "r" "S" "n" "[]" "?ys" "?T"] assms by simp
  moreover have "tuple_appendset ([], S) = S" using tuple_appendset.simps by auto
  ultimately show ?thesis by blast
qed

lemma least_comp_least_lex:
assumes "well_order_on (invgen A) r"
  and "S \<subseteq> \<langle>A\<rangle>"
  and "\<forall>x \<in> S. length x = n"
  and "n > 0"
  and "S \<noteq> {}"
shows "\<forall>x \<in> S.((least_comp r n S), x) \<in> lex_set A r"
proof
  fix x assume x: "x \<in> S"
  then have "((least_comp r n S), x) \<in> compare_set A r" using least_comp_least assms by blast
  then have 1:"(least_comp r n S) \<in> \<langle>A\<rangle> \<and> x \<in> \<langle>A\<rangle> \<and> compare r (least_comp r n S) x" unfolding compare_set_def by fastforce
  have S:"(least_comp r n S) \<in> S" unfolding least_comp_def using assms least_comp_in least_comp_def by metis  
  have "length (least_comp r n S) \<le> length x" using S assms(3) x by force
  then have "lex r (least_comp r n S) x" using lex.simps 1 x S assms(3) by force
  then show "((least_comp r n S), x) \<in> lex_set A r" unfolding lex_set_def using 1 by blast
qed
 
definition nat_leq_less :: "(nat \<times> nat) set"
  where
"nat_leq_less = {(x,y). x \<le> y}"

definition belongs
  where
"belongs S x = (x \<in> S)"

lemma nat_least_exists:
  assumes "(S:: nat set) \<noteq> {}"
  shows "\<exists>x\<in>S.\<forall>y\<in>S. (x, y) \<in> nat_leq_less"
proof-
  obtain x where x:"x \<in> S" using assms by auto
  then show ?thesis
  proof(cases "0 \<in> S")
    case True
    have "\<forall>y \<in> S. 0\<le>y" using True by simp
    then have "\<forall>y \<in> S.(0,y) \<in> nat_leq_less" unfolding nat_leq_less_def by auto
    then show ?thesis using True by auto
  next
    case False
    then obtain k where k:"(belongs S k) \<and> (\<forall>i<k. (\<not> (belongs S i))) \<and> k \<le> x" using assms x ex_least_nat_le[of "belongs S" x] belongs_def by metis
    have "\<forall>y \<in> S. (k, y) \<in> nat_leq_less"
    proof(rule ballI)
      fix y assume y:"y \<in> S"
      then show "(k, y) \<in> nat_leq_less"
      proof(cases "k \<le> y")
      case True
      then show ?thesis unfolding nat_leq_less_def by simp 
    next
      case False
      then have "k > y" by auto
      then have "y \<notin> S" using k belongs_def by metis
      then show ?thesis using y by auto 
    qed
  qed
    then show ?thesis using belongs_def k by force
  qed 
qed

lemma nat_unique_least:
  assumes "(S:: nat set) \<noteq> {}"
  shows "\<exists>!x\<in>S.\<forall>y\<in>S. (x, y) \<in> nat_leq_less"
proof(rule classical)
  assume assm: "\<not>(\<exists>!x\<in>S.\<forall>y\<in>S. (x, y) \<in> nat_leq_less)"
  have least:"\<exists>x\<in>S.\<forall>y\<in>S. (x, y) \<in> nat_leq_less" using nat_least_exists assms by simp
  then obtain x where x:"(x\<in> S) \<and> (\<forall>y\<in>S. (x, y) \<in> nat_leq_less)" by auto
  then obtain z where z: "(z \<in> S) \<and> (\<forall>y\<in>S. (z, y) \<in> nat_leq_less) \<and> (z \<noteq> x)" using assm least by metis
  then have "(z \<in> S) \<and> (x \<in> S)" using x by auto
  then have "((x, z) \<in> nat_leq_less) \<and> ((z, x) \<in> nat_leq_less)" using x z by simp
  then have "x = z" unfolding nat_leq_less_def using mem_Collect_eq by auto
  then show ?thesis using z by linarith
qed

definition least_length :: "'a list set \<Rightarrow> 'a list  set"
  where
"least_length S = {x \<in> S. length x = (least (nat_leq_less) (length ` S))}"

lemma least_length_the:
  assumes "S \<noteq> {}"
  shows "((least (nat_leq_less) (length ` S)) \<in> (length ` S)) \<and>
                     (\<forall>y\<in>(length ` S). ((least (nat_leq_less) (length ` S)), y) \<in> nat_leq_less)"
  unfolding least_def
proof(rule theI')
  have "(length ` S) \<noteq> {}" using assms by auto
  then show "\<exists>!y. y \<in> length ` S \<and> (\<forall>w\<in>length ` S. (y, w) \<in> nat_leq_less)" using nat_unique_least[of "(length ` S)"] by linarith
qed

lemma least_length_least:
  assumes "S \<noteq> {}"
  shows "\<forall>y \<in> (length ` S). ((least (nat_leq_less) (length ` S)), y) \<in> nat_leq_less"
proof-
  have l:"(length ` S) \<noteq> {}" using assms by force
  then have 1:"\<exists>!x\<in>(length ` S).\<forall>y\<in>(length ` S). (x, y) \<in> nat_leq_less" using nat_unique_least assms by presburger
  moreover have "(least (nat_leq_less) (length ` S)) \<in> (length ` S)" using least_def l nat_least_exists nat_unique_least by (smt (verit, del_insts) assms image_is_empty theI)   
  ultimately show ?thesis unfolding least_def assms nat_least_exists nat_unique_least by (smt (verit, ccfv_threshold) "1" theI)
qed

lemma least_length_lesser: 
  assumes "well_order_on (invgen A) r"
  and "[] \<notin> S"
  and "S \<noteq> {}" 
  and "S \<subseteq> \<langle>A\<rangle>"
  and "x \<in> S"
  and "x \<notin> least_length S"
shows "\<forall>y \<in> least_length S. (lex r y x)"
proof-
  have y:"\<forall>y \<in> least_length S. length y = least (nat_leq_less) (length ` S)" unfolding least_length_def assms(3) by fastforce
  then have 1:"\<forall>y \<in> least_length S. \<forall>w \<in> (length ` S). (length y, w) \<in> nat_leq_less" using least_length_least assms(3) by (metis (no_types, lifting))
  have "(length x) \<in> (length ` S)" using assms(5) by auto
  then have "\<forall>y \<in> least_length S.(length y, length x) \<in> nat_leq_less" using 1 by fast
  then have l:"\<forall>y \<in> least_length S. length y \<le> length x" using nat_leq_less_def by blast
  have "length x \<noteq> least (nat_leq_less) (length ` S)" using least_length_def assms(5,6) by blast
  then have "\<forall>y \<in> least_length S. length y \<noteq> length x" using y by simp
  then have "\<forall>y \<in> least_length S. length y < length x" using l using le_neq_implies_less by blast
  then show ?thesis using lex.simps by fastforce
qed

(*1. nat least is unique
  2. x : S and x \<notin> least_length S \<Rightarrow> x > y. \<forall>y : least_length S (*least_hd_the*)
  3. least_length S \<subseteq> S*)
(*least (nat_eq_less) (length ` S) \<le> (length ` S)*)

lemma preorder_words :
  assumes "well_order_on (invgen A) r"
  shows "preorder_on \<langle>A\<rangle> (lex_set A r)"
  unfolding preorder_on_def using lex_refl_on lex_trans assms by blast

lemma partial_order_words :
  assumes "well_order_on (invgen A) r"
  shows "partial_order_on \<langle>A\<rangle> (lex_set A r)"
  unfolding partial_order_on_def using lex_antisym preorder_words assms by blast

lemma linear_order_words :
  assumes "well_order_on (invgen A) r"
  shows "linear_order_on \<langle>A\<rangle> (lex_set A r)"
  unfolding linear_order_on_def using partial_order_words lex_total_on assms by fast

definition tuple_set
  where
"tuple_set r Q = {x \<in> Q. (\<exists>y\<in>Q. ((x, y) \<in> r \<or> (y, x) \<in> r))}"

lemma tuple_set_subset :
"tuple_set r Q \<subseteq> Q" 
  unfolding tuple_set_def by simp 

lemma tuple_set_reln :
"tuple_set (lex_set A r) Q \<subseteq> \<langle>A\<rangle>"
  unfolding tuple_set_def lex_set_def by fastforce

lemma tuple_set_not:
"\<forall>x \<in> Q. \<forall> y \<in> Q.  x \<notin> tuple_set (lex_set A r) Q \<longrightarrow> (x, y) \<notin> (lex_set A r) \<and> (y, x) \<notin> (lex_set A r)"
  apply(rule ballI)+
  apply(rule impI)
proof(rule ccontr)
  fix x y assume x: "x \<in> Q" and y:"y \<in> Q" and nx: "x \<notin> tuple_set (lex_set A r) Q"
    and "\<not> ((x, y) \<notin> lex_set A r \<and> (y, x) \<notin> lex_set A r)"
  then have c:"(x, y) \<in> lex_set A r \<or> (y, x) \<in> lex_set A r" by blast
  then show False
  proof(cases "(x, y) \<in> lex_set A r")
    case True
    then have "x \<in> tuple_set (lex_set A r) Q" using x y unfolding tuple_set_def by blast
    then show ?thesis using nx by blast
  next
    case False
    then have "(y, x) \<in> lex_set A r" using c by simp
    then have "x \<in> tuple_set (lex_set A r) Q" using x y unfolding tuple_set_def by blast
    then show ?thesis using nx by blast
  qed
qed

lemma least_length_subset:
"(least_length S) \<subseteq> S"
  unfolding least_length_def
  by simp

lemma least_lex:
  assumes "well_order_on (invgen A) r"
     and "S \<subseteq> \<langle>A\<rangle>"
     and "S \<noteq> {}"
     and "[] \<notin> S"
   shows "\<forall>x \<in> S. ((least_comp r ((least (nat_leq_less) (length ` S))) (least_length S)),x) \<in> lex_set A r"
proof
  fix x assume x: "x \<in> S" 
  then show "((least_comp r ((least (nat_leq_less) (length ` S))) (least_length S)),x) \<in> lex_set A r" 
  proof(cases "x \<in> least_length S")
    case True
    have "0 \<notin> (length ` S)" using assms(4) by auto
    have 1:"(length ` S) \<noteq> {}" using assms(3) by auto
    then have "(least (nat_leq_less) (length ` S)) \<in> (length ` S)" using least_def nat_unique_least by (smt (verit, del_insts) assms image_is_empty theI)   
    then have 2:"(least (nat_leq_less) (length ` S)) > 0" using assms(4) by fastforce
    then have 3:"\<forall>x \<in>(least_length S). length x  = (least (nat_leq_less) (length ` S))" using  least_length_the least_length_def leastn_comp_less mem_Collect_eq by blast
    moreover have "(least_length S) \<subseteq> \<langle>A\<rangle>" using assms(2) least_length_subset by blast
    ultimately show ?thesis using assms 1 2 least_comp_least_lex[of "A" "r" "least_length S" "(least (nat_leq_less) (length ` S))"] True by blast
  next
    case False
    have LS: "(least_length S) \<subseteq> \<langle>A\<rangle>" using assms(2) least_length_subset by blast
    have 1:"(length ` S) \<noteq> {}" using assms(3) by auto
    then have l:"(least (nat_leq_less) (length ` S)) \<in> (length ` S)" using least_def nat_unique_least by (smt (verit, del_insts) assms image_is_empty theI)
    then have S:"least_length S \<noteq> {}" unfolding least_length_def  using assms empty_iff image_iff mem_Collect_eq by force
    then obtain a where a:"a \<in> least_length S" by blast
    then have "(lex r a x)" using False assms least_length_lesser[of "A" "r" "S" "x"]  x by blast
    then have ax:"(a,x) \<in> lex_set A r" unfolding lex_set_def using x assms(2) a LS by blast
    then have "(least (nat_leq_less) (length ` S)) \<in> (length ` S)" using 1 least_def nat_unique_least l by auto   
    then have 2:"(least (nat_leq_less) (length ` S)) > 0" using assms(4) by fastforce
    then have 3:"\<forall>x \<in>(least_length S). length x  = (least (nat_leq_less) (length ` S))" using  least_length_the least_length_def leastn_comp_less mem_Collect_eq by blast
    moreover have "(least_length S) \<subseteq> \<langle>A\<rangle>" using assms(2) least_length_subset by blast
    ultimately have "((least_comp r ((least (nat_leq_less) (length ` S))) (least_length S)), a) \<in> lex_set A r" using assms S 1 2 least_comp_least_lex[of "A" "r" "least_length S" "(least (nat_leq_less) (length ` S))"] a  by fastforce
    then show ?thesis using ax assms(1) lex_trans unfolding trans_def by fast
  qed
qed

lemma minimalelem_words:
  assumes "well_order_on (invgen A) r"
  shows"\<And>x Q. x \<in> Q \<Longrightarrow> \<exists>z\<in>Q. \<forall>y. (y, z) \<in> (lex_set A r - Id) \<longrightarrow> y \<notin> Q"
proof-
  fix x Q assume x: "x \<in> (Q :: (('a \<times> 'b) \<times> bool) list set)"
  then show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> (lex_set A r - Id) \<longrightarrow> y \<notin> Q"
  proof(cases "[] \<in> Q")
    case True
    then have "\<nexists>z. (z, []) \<in> (lex_set A r - Id)" unfolding lex_set_def using lex.simps[of "r" "z" "[]"] by auto   
    then show ?thesis using True by blast
  next
    case False
    then have nQ:"[] \<notin> Q" by simp
    then show ?thesis
    proof(cases "tuple_set (lex_set A r) Q = {}")
      case True
      have "\<forall>y. (y, x) \<in> (lex_set A r - Id) \<longrightarrow> y \<notin> Q"
        apply(rule allI) apply(rule impI)
      proof-
        fix y assume y:"(y, x) \<in> (lex_set A r - Id)" 
        show "y \<notin> Q"
      proof(rule ccontr)
        assume "\<not> y \<notin> Q"
        then have cont :"y \<in> Q" by blast
        then have 1:"y \<in> tuple_set (lex_set A r) Q" using x tuple_set_def lex_set_def using DiffD1 tuple_set_not y by fastforce
        then show False using True by blast
      qed
    qed
    then show ?thesis using x by blast
    next
      case False
      moreover have 1:"tuple_set (lex_set A r) Q \<subseteq> \<langle>A\<rangle>" using tuple_set_reln by fast
      moreover have nN: "[] \<notin> tuple_set (lex_set A r) Q" using nQ tuple_set_subset[of "(lex_set A r)" "Q"] by blast
      ultimately have lst:"\<forall>x \<in> tuple_set (lex_set A r) Q. ((least_comp r ((least (nat_leq_less) (length ` tuple_set (lex_set A r) Q))) (least_length (tuple_set (lex_set A r) Q))),x) \<in> lex_set A r" using assms least_lex[of "A" "r" "(tuple_set (lex_set A r) Q)"] by blast
      let ?z = "(least_comp r ((least (nat_leq_less) (length ` tuple_set (lex_set A r) Q))) (least_length (tuple_set (lex_set A r) Q)))"
      have "(length ` tuple_set (lex_set A r) Q) \<noteq> {}" using False by auto
      then have lste:"(least (nat_leq_less) (length ` tuple_set (lex_set A r) Q)) \<in> (length ` tuple_set (lex_set A r) Q)" using least_length_the[of "tuple_set (lex_set A r) Q"] by blast  
      then have 2:"(least (nat_leq_less) (length ` (tuple_set (lex_set A r) Q))) > 0" using nN by fastforce
      then have 3:"\<forall>x \<in>(least_length (tuple_set (lex_set A r) Q)). length x  = (least (nat_leq_less) (length ` (tuple_set (lex_set A r) Q)))" using  least_length_the least_length_def leastn_comp_less mem_Collect_eq by blast
      have "least_length (tuple_set (lex_set A r) Q) \<subseteq> \<langle>A\<rangle>" using 1 least_length_subset by fastforce
      moreover have "least_length (tuple_set (lex_set A r) Q) \<noteq> {}" using False lste  unfolding least_length_def  by fastforce
      ultimately have "?z \<in> (least_length (tuple_set (lex_set A r) Q))" using least_comp_in[of "A" "r" "(least_length (tuple_set (lex_set A r) Q))" "((least (nat_leq_less) (length ` tuple_set (lex_set A r) Q)))"] assms 2 3  by blast
      then have zQ:"?z \<in> Q" using least_length_subset[of "(tuple_set (lex_set A r) Q)"] tuple_set_subset[of "(lex_set A r)" "Q"] by fast
      have "\<forall>y. (y, ?z) \<in> (lex_set A r - Id) \<longrightarrow> y \<notin> Q"
        apply(rule allI) apply(rule impI)
      proof-
        fix y assume y:"(y, ?z) \<in> lex_set A r - Id"
        show "y \<notin> Q"
        proof(rule ccontr)
          assume "\<not> y \<notin> Q"
          then have cy:"y \<in> Q" by blast
          show False
          proof(cases "y \<in> tuple_set (lex_set A r) Q")
            case True
            then have yt:"y \<in> tuple_set (lex_set A r) Q" by simp
            then show ?thesis
            proof(cases "y = ?z")
              case True
              then show ?thesis using y by simp
            next
              case False
              then have "(?z, y) \<in> lex_set A r" using lst yt by simp
              moreover have "(y, ?z) \<in> lex_set A r" using y by blast
              ultimately show ?thesis using lex_antisym assms False unfolding antisym_def by blast
            qed
          next
            case False
            then have "((x, ?z) \<notin> lex_set A r \<and> (y, ?z) \<notin> lex_set A r)" using tuple_set_not[of "Q" "A" "r"] cy zQ y by blast
            then show ?thesis using y by fast
          qed
        qed
      qed
      moreover have "?z \<in> Q" using zQ .
      ultimately show ?thesis by blast
    qed 
  qed
qed

(*fix x, x\<in>Q
Cases:
1: [] \<in> Q
Not 1:
1.1:tuple_set (lex_set A r) Q = {}, then x is the z (proof by contradiction: if (y,x) and y \<in> Q then x \<in> tuple_set (lex_set A r) Q)"
Not 1.1: use least_lex and Id, contradiction
*)
 
lemma wf_words :
  assumes "well_order_on (invgen A) r"
  shows "wf (lex_set A r - Id)"
  using minimalelem_words assms wf_eq_minimal by fastforce

lemma well_order_words :
  assumes "well_order_on (invgen A) r"
  shows "well_order_on \<langle>A\<rangle> (lex_set A r)"
  unfolding well_order_on_def using linear_order_words wf_words assms by blast

definition left_subword :: "('a, 'b) word \<Rightarrow> ('a, 'b) word" ("L")
  where
"left_subword xs = take (((length xs+1) div 2)) xs"

value "((((6::nat)) div 2))"

lemma left_subword_word: "xs = (left_subword xs) @ (drop (((length xs+1) div 2)) xs)"
  unfolding left_subword_def
  by auto

definition left_lex_set where "left_lex_set A r = {(x,y). x \<in> L ` \<langle>A\<rangle> \<and> y \<in> L ` \<langle>A\<rangle> \<and>  lex r x y}"

definition invleft_lex_set where "invleft_lex_set A r = {(x, y). x \<in> L` (wordinverse ` \<langle>A\<rangle>) \<and> y \<in> L` (wordinverse ` \<langle>A\<rangle>) \<and> lex r x y}"

definition L_lex where "L_lex A r = ((left_lex_set A r) - Id) <*lex*> ((invleft_lex_set A r) - Id)"

definition left_tuple ("L2")
  where "left_tuple x = (L x, L (wordinverse x))"

definition L_lex_set where "L_lex_set A r = {(x,y). x \<in> \<langle>A\<rangle> \<and> y \<in> \<langle>A\<rangle> \<and> (L2 x, L2 y) \<in> L_lex A r}"

lemma half_n:assumes "n > 0"
  shows "(((((n::nat) + n-1)+1) div 2)) = n"
  using assms  by linarith


lemma left_span:
"\<langle>A\<rangle> = L ` \<langle>A\<rangle>"
proof
  show "\<langle>A\<rangle> \<subseteq> L ` \<langle>A\<rangle>"
  proof(rule subsetI)
    fix x assume x: "x \<in> \<langle>A\<rangle>"
    show "x \<in> L ` \<langle>A\<rangle>"
    proof(cases "x = []")
      case True
      then have "x \<in> \<langle>A\<rangle>" using empty unfolding freewords_on_def by auto
      moreover have "L x = x" using True unfolding left_subword_def by fastforce
      ultimately show ?thesis by force
    next
      case False
      then have "tl x \<in>  \<langle>A\<rangle>" using freewords_on_def x by (metis hd_Cons_tl span_cons)
      then have A:"x @ (tl x) \<in> \<langle>A\<rangle>" using span_append x unfolding freewords_on_def by blast
      have "length (tl x) = length x - 1" by fastforce
      moreover have "length x > 0" using False by simp
      moreover have "length (x @ tl x) = length x + length x - 1" by auto
      ultimately have "length x = (length (x @ tl x) + 1) div 2" using half_n[of "length x"] by simp
      then have "L (x @ (tl x)) = x" unfolding left_subword_def by auto
      then show ?thesis using A by force
    qed
  qed
next
  show "L ` \<langle>A\<rangle> \<subseteq> \<langle>A\<rangle>"
  proof(rule subsetI)
    fix x assume x: "x \<in> L ` \<langle>A\<rangle>"
    then obtain a where a:"a \<in> \<langle>A\<rangle> \<and> L a = x" by blast
    have "a = (L a) @ (drop ((((length a)+1) div 2)) a)" using left_subword_word by blast
    then show "x\<in> \<langle>A\<rangle>" using leftappend_span a unfolding freewords_on_def by metis
  qed
qed

lemma inv_span:
"\<langle>A\<rangle> = wordinverse ` \<langle>A\<rangle>"
proof
  show "\<langle>A\<rangle> \<subseteq> wordinverse ` \<langle>A\<rangle>"
  proof(rule subsetI)
    fix x assume x: "x \<in> \<langle>A\<rangle>"
    then have "wordinverse x \<in> \<langle>A\<rangle>" by (simp add: span_wordinverse)
    moreover have "wordinverse (wordinverse x) = x" by (metis wordinverse_symm)
    ultimately show "x \<in> wordinverse ` \<langle>A\<rangle>" by (metis image_eqI)
  qed
next
  show "wordinverse ` \<langle>A\<rangle> \<subseteq> \<langle>A\<rangle>"
  proof(rule subsetI)
    fix x assume x: "x \<in> wordinverse ` \<langle>A\<rangle>"
    then obtain a where "a \<in> \<langle>A\<rangle> \<and> wordinverse a = x" by blast
    then show "x \<in> \<langle>A\<rangle>" using span_wordinverse by auto
  qed
qed

lemma wf_L_lex:
  assumes "well_order_on (invgen A) r"
  shows "wf (L_lex A r)"
proof-
  have "left_lex_set A r = lex_set A r" unfolding left_lex_set_def lex_set_def using left_span[of "A"]  by fastforce
  then have 1:"wf (left_lex_set A r - Id)" using wf_words assms(1) by auto
  have "invleft_lex_set A r  = lex_set A r" unfolding invleft_lex_set_def lex_set_def using left_span[of "A"] inv_span[of "A"] by fastforce
  then have "wf (invleft_lex_set A r - Id)" using wf_words assms(1) by auto
  then show ?thesis unfolding L_lex_def using 1 by (simp add: wf_lex_prod)
qed

lemma wf_L_lex_set:
  assumes "well_order_on (invgen A) r"
  shows "wf (L_lex_set A r)"
proof(rule wfI_min)
  fix x Q assume x: "x \<in> (Q :: (('a \<times> 'b) \<times> bool) list set)"
  show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> L_lex_set A r \<longrightarrow> y \<notin> Q"
  proof(cases "tuple_set (L_lex A r) (L2 ` Q) = {}")
    case True
    have "\<forall>y. (y, x) \<in> L_lex_set A r \<longrightarrow> y \<notin> Q" 
      apply (rule allI) apply (rule impI)
    proof-
      fix y assume y: "(y, x) \<in> L_lex_set A r"
      then have "(L2 y, L2 x) \<in> L_lex A r" unfolding L_lex_set_def by fastforce
      then show "y \<notin> Q" using True x unfolding tuple_set_def by blast
    qed
    then show ?thesis using x by blast
  next
    case False
    then obtain x where "x \<in> tuple_set (L_lex A r) (L2 ` Q)" by auto
    then obtain z where z: "z \<in> tuple_set (L_lex A r) (L2 ` Q) \<and> (\<forall>y. (y, z) \<in> (L_lex A r) \<longrightarrow> y \<notin> tuple_set (L_lex A r) (L2 ` Q))" using wfE_min wf_L_lex by (metis assms)
    then have z1: "z \<in> (L2 ` Q)" using tuple_set_subset[of "(L_lex A r)" "(L2 ` Q)"] by auto
    then obtain w where w: "w \<in> Q \<and> L2 w = z" by auto
    moreover have "\<forall>y. (y, w) \<in> L_lex_set A r \<longrightarrow> y \<notin> Q" 
      apply(rule allI) apply (rule impI)
    proof-
      fix y assume a: "(y, w) \<in> L_lex_set A r"
      then have contr: "(L2 y, L2 w) \<in> L_lex A r" unfolding L_lex_set_def by auto
      show "y \<notin> Q"
      proof(rule ccontr)
        assume "\<not> y \<notin> Q"
        then have y:"y \<in> Q" by blast
        then show False
        proof(cases "L2 y \<notin> tuple_set (L_lex A r) (L2 ` Q)")
        case True
        have "(L2 y, L2 w) \<notin> L_lex A r"
          proof(rule ccontr)
            assume assm: "\<not> (L2 y, L2 w) \<notin> L_lex A r"
            then have "(L2 y, L2 w) \<in> L_lex A r" by blast
            then have "L2 y \<in> tuple_set (L_lex A r) (L2 ` Q)" unfolding tuple_set_def using w y by auto
            then show False using True by blast
          qed
        then show ?thesis using contr by blast
      next
        case False
        have "L2 y \<notin> tuple_set (L_lex A r) (L2 ` Q)" using z contr w by blast
        then show ?thesis using False by blast
      qed
    qed
  qed
  ultimately show ?thesis by blast
qed
qed

definition L_lex_set' 
  where 
"L_lex_set' A r = {(x,y). x \<in> \<langle>A\<rangle> // reln_tuple \<langle>A\<rangle> \<and> x \<in> \<langle>A\<rangle> // reln_tuple \<langle>A\<rangle> \<and>(red_rep A x, red_rep A y) \<in> L_lex_set A r}"


lemma wf_L_lex_set':
  assumes "well_order_on (invgen A) r"
  shows "wf (L_lex_set' A r)"
proof(rule wfI_min)
  fix x Q assume x: "x \<in> (Q :: (('a \<times> 'b) \<times> bool) list set set)"
  show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> L_lex_set' A r \<longrightarrow> y \<notin> Q"
  proof(cases "tuple_set (L_lex_set A r) (red_rep A ` Q) = {}")
    case True
    have "\<forall>y. (y, x) \<in> L_lex_set' A r \<longrightarrow> y \<notin> Q" 
      apply (rule allI) apply (rule impI)
    proof-
      fix y assume y: "(y, x) \<in> L_lex_set' A r"
      then have "(red_rep A y, red_rep A x) \<in> L_lex_set A r" unfolding L_lex_set'_def by fast
      then show "y \<notin> Q" using True x unfolding tuple_set_def by blast
    qed
    then show ?thesis using x by blast
  next
    case False
    then obtain x where "x \<in> tuple_set (L_lex_set A r) (red_rep A ` Q)" by auto
    then obtain z where z: "z \<in> tuple_set (L_lex_set A r) (red_rep A ` Q) \<and> (\<forall>y. (y, z) \<in> (L_lex_set A r) \<longrightarrow> y \<notin> tuple_set (L_lex_set A r) (red_rep A ` Q))" using wfE_min wf_L_lex_set assms by metis 
    then have z1: "z \<in> (red_rep A ` Q)" using tuple_set_subset[of "(L_lex_set A r)" "(red_rep A ` Q)"] by auto
    then obtain w where w: "w \<in> Q \<and> (red_rep A  w) = z" by auto
    moreover have "\<forall>y. (y, w) \<in> L_lex_set' A r \<longrightarrow> y \<notin> Q"
      apply(rule allI) apply (rule impI)
    proof-
      fix y assume a: "(y, w) \<in> L_lex_set' A r"
      then have contr: "(red_rep A y, red_rep A w) \<in> L_lex_set A r" unfolding L_lex_set'_def by auto
      show "y \<notin> Q"
      proof(rule ccontr)
        assume "\<not> y \<notin> Q"
        then have y:"y \<in> Q" by blast
        then show False
        proof(cases "red_rep A y \<notin> tuple_set (L_lex_set A r) (red_rep A ` Q)")
        case True
        have "(red_rep A y, red_rep A w) \<notin> L_lex_set A r"
          proof(rule ccontr)
            assume assm: "\<not> (red_rep A y, red_rep A w) \<notin> L_lex_set A r"
            then have "(red_rep A y, red_rep A w) \<in> L_lex_set A r" by blast
            then have "red_rep A y \<in> tuple_set (L_lex_set A r) (red_rep A ` Q)" unfolding tuple_set_def using w y by auto
            then show False using True by blast
          qed
        then show ?thesis using contr by blast
      next
        case False
        have "red_rep A y \<notin> tuple_set (L_lex_set A r) (red_rep A ` Q)" using z contr w by blast
        then show ?thesis using False by blast
      qed
    qed
  qed
  ultimately show ?thesis by blast
qed
qed

*)

definition left_subword :: "('a, 'b) word \<Rightarrow> ('a, 'b) word" ("L")
  where
"left_subword xs = take (((length xs+1) div 2)) xs"

definition left_tuple ("L2")
  where "left_tuple x = (L x, L (wordinverse x))"

definition r_gen
  where
"r_gen = (SOME r :: ('a, 'b) groupgentype rel. Well_order r \<and> Field r = UNIV)"

lemma r_gen:
"Well_order r_gen \<and> Field r_gen = UNIV"
  unfolding r_gen_def using someI_ex[of "\<lambda> r. Well_order r \<and> Field r = UNIV"] well_ordering 
  by (simp add: \<open>\<exists>x. Well_order x \<and> Field x = UNIV \<Longrightarrow> Well_order (SOME x. Well_order x \<and> Field x = UNIV) \<and> Field (SOME x. Well_order x \<and> Field x = UNIV) = UNIV\<close> well_ordering)

lemma wf_r_gen:
"wf (r_gen - Id)"
  using r_gen well_order_on_def by auto

definition lex_word
  where
"lex_word = lenlex (r_gen - Id)"

lemma wf_lex_word:
"wf lex_word"
  unfolding lex_word_def by (simp add: wf_r_gen wf_lenlex)

lemma wf_inv1:
  assumes "wf r"
  shows "wf {(x,y). (f x, f y) \<in> r}"
  by (metis assms inv_image_def wf_inv_image)

fun min 
where
"min r (x, y) = (if (x, y) \<in> r then x else y)"

definition lex_min_L2_word
  where
"lex_min_L2_word = {(x,y). (min lex_word x, min lex_word y) \<in> lex_word}"

lemma wf_lex_min_L2_word:
"wf (lex_min_L2_word)"
  unfolding lex_min_L2_word_def by (simp add: wf_inv1 wf_lex_word)

fun max 
where
"max r (x, y) = (if (x, y) \<in> r then y else x)"

definition lex_max_L2_word
  where
"lex_max_L2_word = {(x,y). (max lex_word x, max lex_word y) \<in> lex_word}"

lemma wf_lex_max_L2_word:
"wf (lex_max_L2_word)"
  unfolding lex_max_L2_word_def by (simp add: wf_inv1 wf_lex_word)

definition lex_L2_word'
  where
"lex_L2_word' A = {(x,y). x \<in> (\<langle>A\<rangle> // (reln_tuple \<langle>A\<rangle>)) \<and> y \<in> (\<langle>A\<rangle> // (reln_tuple \<langle>A\<rangle>)) \<and>  ((\<lambda>x. (min lex_word (L2 (red_rep A x)), max lex_word (L2 (red_rep A x)))) x , (\<lambda>x. (min lex_word (L2 (red_rep A x)), max lex_word (L2 (red_rep A x)))) y) \<in> (lex_word <*lex*> lex_word)}"

lemma wf_lex_word_prod:
 "wf (lex_word <*lex*> lex_word)"
  by (simp add: wf_lex_prod wf_lex_word)

lemma wf_lex_L2_word':
"wf (lex_L2_word' A)"
proof-
  have "wf {(x,y) . ((\<lambda>x. (min lex_word (L2 (red_rep A x)), max lex_word (L2 (red_rep A x)))) x , (\<lambda>x. (min lex_word (L2 (red_rep A x)), max lex_word (L2 (red_rep A x)))) y) \<in> (lex_word <*lex*> lex_word)}" using wf_inv1 wf_lex_word_prod by fast
  moreover have "lex_L2_word' A \<subseteq> {(x,y) . ((\<lambda>x. (min lex_word (L2 (red_rep A x)), max lex_word (L2 (red_rep A x)))) x , (\<lambda>x. (min lex_word (L2 (red_rep A x)), max lex_word (L2 (red_rep A x)))) y) \<in> (lex_word <*lex*> lex_word)}" unfolding lex_L2_word'_def by auto
  ultimately show ?thesis using wf_subset by blast
qed

definition nat_less :: "(nat \<times> nat) set"
  where
"nat_less = {(x,y). x < y}"

lemma wf_nat_less:
"wf nat_less"
proof-
  have "nat_less = less_than" unfolding nat_less_def less_than_def using less_eq by blast
  then show ?thesis using wf_less_than by argo
qed
                               
lemma wf_lex_L2_word'_prod:
"wf (nat_less <*lex*> lex_L2_word' A)"
  by (simp add: wf_lex_L2_word' wf_lex_prod wf_nat_less)

definition lex_L2_word
  where
"lex_L2_word A = {(x,y). x \<in> (\<langle>A\<rangle> // (reln_tuple \<langle>A\<rangle>)) \<and> y \<in> (\<langle>A\<rangle> // (reln_tuple \<langle>A\<rangle>)) \<and>  ((\<lambda>x. (length (red_rep A x), x)) x, (\<lambda>x. (length (red_rep A x), x)) y) \<in> (nat_less <*lex*> lex_L2_word' A)}"

lemma wf_lex_L2_word:
"wf (lex_L2_word A)"
proof-
  have "wf {(x,y). ((\<lambda>x. (length (red_rep A x), x)) x, (\<lambda>x. (length (red_rep A x), x)) y) \<in> (nat_less <*lex*> lex_L2_word' A)}" using wf_inv1 wf_lex_L2_word'_prod by fast
  moreover have "lex_L2_word A \<subseteq>{(x,y). ((\<lambda>x. (length (red_rep A x), x)) x, (\<lambda>x. (length (red_rep A x), x)) y) \<in> (nat_less <*lex*> lex_L2_word' A)}" unfolding lex_L2_word_def by auto
  ultimately show ?thesis  using wf_subset by blast
qed

lemma lex_L2_word_length:
  assumes "x \<in> (\<langle>A\<rangle> // (reln_tuple \<langle>A\<rangle>)) \<and> y \<in> (\<langle>A\<rangle> // (reln_tuple \<langle>A\<rangle>))"
      and "length ((red_rep A) x) = length ((red_rep A) y)"
    shows "(x,y) \<in> (lex_L2_word A) \<longleftrightarrow>  (x,y) \<in> (lex_L2_word' A)"
  unfolding lex_L2_word_def by (simp add: assms(1) assms(2) wf_nat_less)

lemma lex_L2_word_length_conv:
  assumes "x \<in> (\<langle>A\<rangle> // (reln_tuple \<langle>A\<rangle>)) \<and> y \<in> (\<langle>A\<rangle> // (reln_tuple \<langle>A\<rangle>))"
      and "length ((red_rep A) x) = length ((red_rep A) y)"
    shows "(x,y) \<in> (lex_L2_word' A) \<Longrightarrow> (x,y) \<in> (lex_L2_word A)"
  unfolding lex_L2_word_def by (simp add: assms(1) assms(2))

lemma total_Id: "total r \<Longrightarrow> total (r - Id)"
  by simp

lemma total_r_gen_Id: "total (r_gen - Id)"
  using r_gen total_Id unfolding well_order_on_def linear_order_on_def by metis


lemma lex_word_total:
"\<not> (x,y) \<in> (lex_word) \<Longrightarrow> \<not> (y,x) \<in> (lex_word) \<Longrightarrow> x = y"
proof-
  assume "\<not> (x,y) \<in> (lex_word)" and "\<not> (y,x) \<in> (lex_word) "
  then show "x = y" using total_r_gen_Id unfolding lex_word_def by (metis UNIV_I total_lenlex total_on_def)
qed

lemma lex_L2_word_total1:
  assumes "x \<in> (\<langle>A\<rangle> // (reln_tuple \<langle>A\<rangle>)) \<and> y \<in> (\<langle>A\<rangle> // (reln_tuple \<langle>A\<rangle>))"
      and "length ((red_rep A) x) = length ((red_rep A) y)"
    shows "\<not> (x,y) \<in> (lex_L2_word A) \<Longrightarrow> \<not> (y,x) \<in> (lex_L2_word A) \<Longrightarrow> min lex_word (L2 (red_rep A x)) = min lex_word (L2 (red_rep A y)) \<and> max lex_word (L2 (red_rep A x)) = max lex_word (L2 (red_rep A y))"
proof-
  assume "\<not> (x,y) \<in> (lex_L2_word A)" and "\<not> (y,x) \<in> (lex_L2_word A)"
  then have 1: "\<not> (x,y) \<in> (lex_L2_word' A) \<and> \<not> (y,x) \<in> (lex_L2_word' A)" using assms lex_L2_word_length by auto
  have "\<not> (min lex_word (L2 (red_rep A x)), min lex_word (L2 (red_rep A y))) \<in> lex_word"
  proof(rule ccontr)
    assume "\<not> (min lex_word (L2 (red_rep A x)), min lex_word (L2 (red_rep A y))) \<notin> lex_word"
    then have "(min lex_word (L2 (red_rep A x)), min lex_word (L2 (red_rep A y))) \<in> lex_word" by blast
    then have "(x,y) \<in> (lex_L2_word' A)" unfolding lex_L2_word'_def lex_prod_def using assms(1)  by simp
    then show False using 1 by blast
  qed
  moreover have "\<not> (min lex_word (L2 (red_rep A y)), min lex_word (L2 (red_rep A x))) \<in> lex_word"
  proof(rule ccontr)
    assume "\<not> (min lex_word (L2 (red_rep A y)), min lex_word (L2 (red_rep A x))) \<notin> lex_word"
    then have "(min lex_word (L2 (red_rep A y)), min lex_word (L2 (red_rep A x))) \<in> lex_word" by blast
    then have "(y,x) \<in> (lex_L2_word' A)" unfolding lex_L2_word'_def lex_prod_def using assms(1)  by simp
    then show False using 1 by blast
  qed
  ultimately have min: "min lex_word (L2 (red_rep A x)) = min lex_word (L2 (red_rep A y))" using lex_word_total by blast 
  have "\<not> (max lex_word (L2 (red_rep A x)), max lex_word (L2 (red_rep A y))) \<in> lex_word"
  proof(rule ccontr)
    assume "\<not> (max lex_word (L2 (red_rep A x)), max lex_word (L2 (red_rep A y))) \<notin> lex_word"
    then have "(max lex_word (L2 (red_rep A x)), max lex_word (L2 (red_rep A y))) \<in> lex_word" by blast
    then have "(x,y) \<in> (lex_L2_word' A)" unfolding lex_L2_word'_def lex_prod_def using assms(1) min  by simp
    then show False using 1 by blast
  qed
  moreover have "\<not> (max lex_word (L2 (red_rep A y)), max lex_word (L2 (red_rep A x))) \<in> lex_word"
  proof(rule ccontr)
    assume "\<not> (max lex_word (L2 (red_rep A y)), max lex_word (L2 (red_rep A x))) \<notin> lex_word"
    then have "(max lex_word (L2 (red_rep A y)), max lex_word (L2 (red_rep A x))) \<in> lex_word" by blast
    then have "(y,x) \<in> (lex_L2_word' A)" unfolding lex_L2_word'_def lex_prod_def using assms(1) min  by simp
    then show False using 1 by blast
  qed
  ultimately show "min lex_word (L2 (red_rep A x)) = min lex_word (L2 (red_rep A y)) \<and> max lex_word (L2 (red_rep A x)) = max lex_word (L2 (red_rep A y))" using min lex_word_total by blast
qed

fun rev_tuple ("\<down>")
  where
"\<down> (x,y) = (y,x)"

lemma lex_L2_word_total2:
"min lex_word (L2 x) = min lex_word (L2 y) \<and> max lex_word (L2 x) = max lex_word (L2 y) \<Longrightarrow> (L2 x = L2 y) \<or> (\<down> (L2 x) = L2 y)" 
  by (metis left_tuple_def max.simps min.simps rev_tuple.simps)

lemma "(L2 x = L2 y) \<or> (\<down> (L2 x) = L2 y) \<Longrightarrow> min lex_word (L2 x) = min lex_word (L2 y) \<and> max lex_word (L2 x) = max lex_word (L2 y)"
  by (metis (no_types, hide_lams) left_tuple_def lex_word_total max.simps min.simps rev_tuple.simps wf_asym wf_lex_word)
(*
lemma "even (length x) \<Longrightarrow> take ((length (a#x) + 1) div 2) (a#x) = a#take ((length x + 1) div 2) x"
  by simp

lemma "odd (length x) \<Longrightarrow> take ((length (a#x) + 1) div 2) (a#x) = a#take ((length x) div 2) x"
  by simp

lemma "(odd (length x) \<and> L (wordinverse x) = wordinverse (drop ((length x + 1) div 2) x)) \<or> (even (length x) \<and> L (wordinverse x) = wordinverse (drop ((length x) div 2) x))"
  unfolding left_subword_def
proof(induction x)
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  then show ?case sorry
qed
*)

definition right_subword ("R")
  where
"right_subword xs =  drop (((length xs+1) div 2)) xs"

lemma length_wordinverse:"length xs = length (wordinverse xs)"
  by (simp add: wordinverse_redef1)

lemma even_div2:
"even (x :: nat) \<Longrightarrow> x - ((x + 1) div 2) = ((x + 1) div 2)"
   by fastforce

lemma odd_div2:
"odd (x :: nat) \<Longrightarrow> x - ((x + 1) div 2) = ((x + 1) div 2) - 1"
  by (metis (no_types, lifting) add_diff_cancel_right add_diff_cancel_right' even_div2 odd_even_add odd_one odd_succ_div_two odd_two_times_div_two_succ)

lemma even_R:
"even (length xs) \<Longrightarrow> L (wordinverse xs) = wordinverse (R xs)"
  unfolding right_subword_def left_subword_def
proof-
  assume "even (length xs)"
  then have 1:"length xs - (length xs + 1) div 2 = (length xs + 1) div 2" using even_div2 by blast
  have "take ((length (wordinverse xs) + 1) div 2) (wordinverse xs) = take ((length xs + 1) div 2) (rev ((map inverse) xs))" by (simp add: wordinverse_redef1)
  moreover then have "... = rev (drop ((length xs + 1) div 2) ((map inverse) xs))" using 1 length_map take_rev by metis
  moreover then have "... = wordinverse (drop ((length xs + 1) div 2) xs)" by (simp add: drop_map wordinverse_redef1)
  ultimately show "take ((length (wordinverse xs) + 1) div 2) (wordinverse xs) =
    wordinverse (drop ((length xs + 1) div 2) xs)" by presburger
qed

lemma take_length:
 "n \<le> length xs \<Longrightarrow>length (take n xs) = n"
  by simp

lemma drop_odd_length: "odd (length xs) \<Longrightarrow> (length (drop ((length xs + 1) div 2 - 1) xs) = ((length xs + 1) div 2))"
proof-
  assume odd:"odd (length xs)"
  then have "length xs > 0" using odd by force
  then have 1:"((length xs + 1) div 2) \<le> length xs" by simp
  have "drop ((length xs + 1) div 2 - 1) (rev xs) = rev (take ((length xs + 1) div 2) xs)" using odd rev_take odd_div2 by metis
  moreover have "length (rev (take ((length xs + 1) div 2) xs)) = ((length xs + 1) div 2)" using 1 take_length length_rev by metis
  moreover have "length (drop ((length xs + 1) div 2 - 1) (rev xs)) = length (drop ((length xs + 1) div 2 - 1) xs)"  by simp
  ultimately show "(length (drop ((length xs + 1) div 2 - 1) xs) = ((length xs + 1) div 2))" by presburger
qed

lemma odd_R:
"odd (length xs) \<Longrightarrow>  take (((length xs+1) div 2) - 1) (L (wordinverse xs)) = wordinverse (R xs)"
  unfolding right_subword_def left_subword_def
proof-
  assume odd:"odd (length xs)"
  then have  1:"length xs - (length xs + 1) div 2 = (length xs + 1) div 2 - 1" using odd_div2 by blast
  have "take ((length xs + 1) div 2 - 1)
     (take ((length (wordinverse xs) + 1) div 2) (wordinverse xs)) =  take ((length xs + 1) div 2 - 1)
     (take ((length xs + 1) div 2) (rev (map inverse xs)))" by (simp add: wordinverse_redef1)
  moreover then have "... = take ((length xs + 1) div 2 - 1) (rev (drop ((length xs + 1) div 2 - 1) ((map inverse) xs)))" using 1 length_map take_rev by metis
  moreover then have "... = rev (drop (length (drop ((length xs + 1) div 2 - 1) ((map inverse) xs)) -  ((length xs + 1) div 2 - 1))  (drop ((length xs + 1) div 2 - 1) ((map inverse) xs)))" using take_rev by blast
  moreover then have "... = rev (drop (((length xs + 1) div 2) -  ((length xs + 1) div 2 - 1))  (drop ((length xs + 1) div 2 - 1) ((map inverse) xs)))" using drop_odd_length length_map odd by metis
  moreover then have "... = rev (drop 1  (drop ((length xs + 1) div 2 - 1) ((map inverse) xs)))" by (simp add: odd)
  moreover then have "... = rev ((drop ((length xs + 1) div 2) ((map inverse) xs)))" by (simp add: odd)
  moreover then have "... = rev ((map inverse) (drop ((length xs + 1) div 2)  xs))" using drop_map by blast
  moreover then have "... = wordinverse (drop ((length xs + 1) div 2) xs)" by (simp add: wordinverse_redef1)
  ultimately show "take ((length xs + 1) div 2 - 1)
     (take ((length (wordinverse xs) + 1) div 2) (wordinverse xs)) =
    wordinverse (drop ((length xs + 1) div 2) xs)" by presburger
qed

lemma LR_eq:
  assumes "L x = L y"
          and "R x = R y"
        shows "x = y"
proof-
  have "L x @ R x = x" unfolding left_subword_def right_subword_def by simp
  moreover have  "L y @ R y = y" unfolding left_subword_def right_subword_def by simp
  ultimately show ?thesis using assms(1,2) by argo
qed

lemma L2_eq:
  assumes "length x = length y"
          and "(L2 x = L2 y)"  
        shows "L x = L y \<and> R x = R y" 
proof(cases "odd (length x)")
  case True
  have 1: "L x = L y" using assms(2) left_tuple_def by (metis prod.inject)
  have "L (wordinverse x) = L (wordinverse y)" using assms(2) left_tuple_def by (metis prod.inject)
  then have "take (((length x+1) div 2) - 1) (L (wordinverse x)) =  take (((length y+1) div 2) - 1) (L (wordinverse y))" using assms(1) by presburger
  then have "wordinverse (R x) = wordinverse (R y)" using True assms(1) odd_R by metis
  then have "R x = R y" using wordinverse_of_wordinverse by metis
  then show ?thesis using 1 by blast
next
  case False
  have 1: "L x = L y" using assms(2) left_tuple_def by (metis prod.inject)
  have "L (wordinverse x) = L (wordinverse y)" using assms(2) left_tuple_def by (metis prod.inject)
  then have "wordinverse (R x) = wordinverse (R y)" using False assms(1) even_R by metis
  then have "R x = R y" using wordinverse_of_wordinverse by metis
  then show ?thesis using 1 by blast
qed

lemma eq_L2_eq:
  assumes "length x = length y"
          and "(L2 x = L2 y)"  
        shows "x = y"
  using L2_eq LR_eq assms(1) assms(2) by auto

lemma rev_L2_inv:
  assumes "length x = length y"
          and "((\<down> (L2 x)) = L2 y)"
        shows "x = wordinverse y"
proof(cases "odd (length x)")
  case True
  have 1: "L x = L (wordinverse y)" using assms(2) left_tuple_def old.prod.inject rev_tuple.simps by metis
  have "L (wordinverse x) = L y" using assms(2) left_tuple_def old.prod.inject rev_tuple.simps by metis
  then have "take (((length x+1) div 2) - 1) (L (wordinverse x)) =  take (((length y+1) div 2) - 1) (L y)" using assms(1) by presburger
  then have "take (((length x+1) div 2) - 1) (L (wordinverse x)) =  take (((length y+1) div 2) - 1) (L (wordinverse (wordinverse y)))" using wordinverse_of_wordinverse by metis
  then have "take (((length x+1) div 2) - 1) (L (wordinverse x)) =  take (((length (wordinverse (wordinverse y))+1) div 2) - 1) (L (wordinverse (wordinverse y)))" using length_wordinverse by metis
  then have "wordinverse (R x) = wordinverse  (R (wordinverse y))" using True assms(1) odd_R length_wordinverse by metis
  then have "R x = R (wordinverse y)" using wordinverse_of_wordinverse  by metis
  then show ?thesis using 1 LR_eq by blast
next
  case False
  then have even: "even (length x)" by auto
  have 1:"L x = L (wordinverse y)" using assms(2) left_tuple_def old.prod.inject rev_tuple.simps by metis
  have "L (wordinverse x) = L y" using assms(2) left_tuple_def old.prod.inject rev_tuple.simps by metis
  then have "L (wordinverse x) = L (wordinverse (wordinverse y))" by (simp add: wordinverse_of_wordinverse)
  then have "wordinverse (R x) = wordinverse  (R (wordinverse y))" using even_R assms(1) even by (metis length_wordinverse)
  then have "R x = (R (wordinverse y))" using wordinverse_of_wordinverse by metis
  then show ?thesis using 1 LR_eq by blast
qed

lemma assumes "x \<in> (\<langle>A\<rangle> // (reln_tuple \<langle>A\<rangle>)) \<and> y \<in> (\<langle>A\<rangle> // (reln_tuple \<langle>A\<rangle>))"
      and "length ((red_rep A) x) = length ((red_rep A) y)"
    shows "\<not> (x,y) \<in> (lex_L2_word A) \<Longrightarrow> \<not> (y,x) \<in> (lex_L2_word A) \<Longrightarrow> (red_rep A x) = (red_rep A y) \<or> (red_rep A x) = wordinverse (red_rep A y)"
  using assms lex_L2_word_total1 lex_L2_word_total2 eq_L2_eq rev_L2_inv by blast+

lemma red_rep_wordinv:
  assumes "x ∈ (⟨A⟩ // (reln_tuple ⟨A⟩))" 
  shows "red_rep A ((reln_tuple ⟨A⟩) `` {wordinverse (red_rep A x)}) = wordinverse (red_rep A x)" 
proof-
  have "reduced (wordinverse (red_rep A x))" using red_rep_def[of "A" "x"] reduced_wordinverse[of "red_rep A x"] red_rep_the assms by blast
  moreover have "wordinverse (red_rep A x) ∈ ((reln_tuple ⟨A⟩) `` {wordinverse (red_rep A x)})" using assms eq_equiv_class_iff2 in_quotient_imp_subset red_rep_the reln_equiv span_wordinverse by fastforce
  ultimately show ?thesis using red_rep_def[of "A" "((reln_tuple ⟨A⟩) `` {wordinverse (red_rep A x)})"] assms group.wordinverse_inv by (smt (verit, best) Image_singleton_iff quotientI red_rep_the redelem_unique refl_onD2 reln_refl)
qed

lemma red_rep_inv:
  assumes "x ∈ (⟨A⟩ // (reln_tuple ⟨A⟩))" 
  shows "(red_rep A (inv⇘freegroup A⇙ x)) = wordinverse (red_rep A x)"
proof-
  have grpA:"group (freegroup A)" by (simp add: freegroup_is_group)
  then have "x∈ carrier (freegroup A)" using assms freegroup_def by (metis partial_object.select_convs(1))
  moreover have "x = (reln_tuple ⟨A⟩) `` {red_rep A x}" using assms by (simp add: red_rep_the)
  ultimately have "inv⇘(freegroup A)⇙ x = (reln_tuple ⟨A⟩) `` {wordinverse (red_rep A x)}" using group.wordinverse_inv grpA by blast
  then have "(red_rep A (inv⇘freegroup A⇙ x)) = red_rep A ((reln_tuple ⟨A⟩) `` {wordinverse (red_rep A x)})" by auto
  then show ?thesis  unfolding red_rep_def red_rep_wordinv using assms by (metis equivinv_def red_rep_def red_rep_wordinv)
qed
  
lemma L2_wordinv:
  "L2 (wordinverse x) = (snd (L2 x), fst (L2 x))" 
  by (simp add: FreeGroupMain.wordinverse_of_wordinverse left_tuple_def)

lemma lex_L2_inv:
  assumes "(y,x) ∈ lex_L2_word A"
  shows "(y,inv⇘freegroup A⇙ x) ∈ lex_L2_word A" 
proof-
  have 1:"x ∈ (⟨A⟩ // (reln_tuple ⟨A⟩))" using assms(1) unfolding lex_L2_word_def by blast
  then obtain invx where "invx = (inv⇘freegroup A⇙ x)" using freegroup_is_group by simp
  then have x:"(inv⇘freegroup A⇙ x) ∈ (⟨A⟩ // (reln_tuple ⟨A⟩))" using m_inv_def[of "freegroup A" "x"] freegroup_def
    by (metis (no_types, lifting) freegroup_is_group group.inv_closed partial_object.select_convs(1) 1)
  have y: "y ∈ (⟨A⟩ // (reln_tuple ⟨A⟩))" using assms(1) unfolding lex_L2_word_def by blast
  have 2:"(length (red_rep A y) < length (red_rep A x)) ∨ ((length (red_rep A y) = length (red_rep A x) ∧ (y,x) ∈ lex_L2_word' A))" 
    using nat_less_def assms unfolding lex_L2_word_def lex_prod_def by fastforce
  then show ?thesis 
  proof(cases "(length (red_rep A y) < length (red_rep A x))")
    case True
    then have "length (red_rep A y) < length (wordinverse (red_rep A x))" using length_wordinverse by metis
    then have "length (red_rep A y) < length (red_rep A (inv⇘freegroup A⇙ x))" using 1 red_rep_inv by metis
    then show ?thesis using x y by (simp add: lex_L2_word_def nat_less_def)
  next
    case False
    then have 3:"((length (red_rep A y) = length (red_rep A x) ∧ (y,x) ∈ lex_L2_word' A))" using 2 by blast
    then have 4:"length (red_rep A y) = length (red_rep A (inv⇘freegroup A⇙ x))" using 1 red_rep_inv by (metis length_wordinverse)
    then have "((λx. (min lex_word (L2 (red_rep A x)), max lex_word (L2 (red_rep A x)))) y 
                , (λx. (min lex_word (L2 (red_rep A x)), max lex_word (L2 (red_rep A x)))) x) ∈ (lex_word <*lex*> lex_word)" using 3 unfolding lex_L2_word'_def by fastforce
    then have 5:"((min lex_word (L2 (red_rep A y))), (min lex_word (L2 (red_rep A x)))) ∈ lex_word ∨ 
               (min lex_word (L2 (red_rep A y))) = (min lex_word (L2 (red_rep A x))) ∧ 
               (max lex_word (L2 (red_rep A y)), max lex_word (L2 (red_rep A x))) ∈ lex_word" using lex_prod_def[of "lex_word" "lex_word"] by simp
    have "L2 (wordinverse (red_rep A x)) = (snd (L2 (red_rep A x)), fst (L2 (red_rep A x)))" using L2_wordinv by blast
    then have L2_winv:"min lex_word (L2 (red_rep A x)) = min lex_word (L2 (wordinverse (red_rep A x))) ∧
                       max lex_word (L2 (red_rep A x)) = max lex_word (L2 (wordinverse (red_rep A x)))" using  wf_lex_word min.simps  by (metis (no_types, lifting) lex_word_total max.simps prod.exhaust_sel wf_asym)
    then have "((min lex_word (L2 (red_rep A y))), (min lex_word (L2 (wordinverse(red_rep A x))))) ∈ lex_word ∨ 
               (min lex_word (L2 (red_rep A y))) = (min lex_word (L2 (wordinverse(red_rep A x)))) ∧ 
               (max lex_word (L2 (red_rep A y)), max lex_word (L2 (wordinverse(red_rep A x)))) ∈ lex_word" using 5 by auto   
    then have "((min lex_word (L2 (red_rep A y))), (min lex_word (L2 (red_rep A (inv⇘freegroup A⇙ x))))) ∈ lex_word ∨
               (min lex_word (L2 (red_rep A y))) = (min lex_word (L2 (red_rep A (inv⇘freegroup A⇙ x)))) ∧ 
               (max lex_word (L2 (red_rep A y)), max lex_word (L2 (red_rep A (inv⇘freegroup A⇙ x)))) ∈ lex_word" using red_rep_inv 1 by force    
    then have "(y,(inv⇘freegroup A⇙ x)) ∈ lex_L2_word' A" unfolding lex_L2_word'_def using x y by auto
    then show ?thesis using x y 2 4 lex_L2_word_length by blast
  qed
qed

lemma reduced_tl:"reduced (x#xs) \<Longrightarrow> reduced xs"
  by (metis append_Nil assoc_Cons reduced_leftappend)

definition l_concat :: "'a list list \<Rightarrow> 'a list"
  where
"l_concat l \<equiv> (foldr (@) l [])"

fun m_concat
  where
"m_concat H [] = \<one>\<^bsub>H\<^esub>"|
"m_concat H (x#xs) = x \<otimes>\<^bsub>H\<^esub> (m_concat H xs)"

lemma append_equivred_span:
  assumes "set l \<subseteq> carrier (freegroup S)"
  shows "l_concat (map (red_rep S) l) \<in> \<langle>S\<rangle>"
proof-
  have "\<forall>x\<in> set l. \<forall>n\<in>x. n \<in> \<langle>S\<rangle>" using assms in_quotient_imp_subset reln_equiv unfolding freegroup_def by fastforce
  then have 1:"\<forall>x\<in> set l. x \<subseteq> \<langle>S\<rangle>" by auto
  then have "\<forall>x\<in> set l. x \<in> \<langle>S\<rangle> // reln_tuple \<langle>S\<rangle> " using assms freegroup_def by (metis partial_object.select_convs(1) subset_code(1))
  moreover then have "\<forall>x\<in> set l. (red_rep S x \<in> x)" by (simp add: red_rep_the)
  ultimately have "\<forall>x\<in> set l. (red_rep S x \<in> \<langle>S\<rangle>)" using 1 by auto
  then have "set(map (red_rep S) l) \<subseteq> \<langle>S\<rangle>" by auto
  then show ?thesis unfolding l_concat_def
  proof(induction l)
    case Nil
    then show ?case using span_append freewords_on_def[of "S"] words_on.empty by auto
  next
    case (Cons a l)
    then have "set (map (red_rep S) l) \<subseteq> \<langle>S\<rangle>" by simp
    then have 1:"foldr (@) (map (red_rep S) l) [] \<in> \<langle>S\<rangle>" using Cons.IH by auto
    have "[(foldr (@) (map (red_rep S) (a # l)) [])] = [foldr (@) [((foldr (@) (map (red_rep S) [a]) [])@(foldr (@) (map (red_rep S) l) []))] []]" by simp    
    then show ?case using span_append freewords_on_def 1 by (metis (no_types, lifting) Cons.prems concat.simps(2) concat_conv_foldr list.set_intros(1) list.simps(9) subset_code(1))
  qed
qed

lemma
  assumes "set l \<subseteq> carrier (freegroup S)"
  shows "m_concat (freegroup S) l = (reln_tuple \<langle>S\<rangle>) `` {(l_concat (map(red_rep S) l))}"
  using assms
proof(induction l)
  case Nil
  have "m_concat (freegroup S) [] = \<one>\<^bsub>freegroup S\<^esub>" unfolding m_concat.simps(2) by simp
  moreover have "l_concat (map (red_rep S) []) = []" unfolding l_concat_def by simp
  moreover have "reln_tuple \<langle>S\<rangle> `` {[]} = \<one>\<^bsub>freegroup S\<^esub>" using freegroup_def[of "S"] by simp
  ultimately show ?case by simp
next
  case (Cons a l)
  then have "set l \<subseteq> carrier (freegroup S)" by simp
  then have I:"m_concat (freegroup S) l = reln_tuple \<langle>S\<rangle> `` {l_concat (map (red_rep S) l)}" using Cons.IH by auto
  have 1:"reln_tuple \<langle>S\<rangle> `` {l_concat (map (red_rep S) (a # l))} = reln_tuple \<langle>S\<rangle> `` {((red_rep S) a @ l_concat (map (red_rep S) l))}" unfolding l_concat_def by simp
  have a1:"a \<in> carrier (freegroup S)" using Cons by simp
  then have a:"(red_rep S) a \<in> \<langle>S\<rangle>" unfolding freegroup_def using red_rep_the in_quotient_imp_subset reln_equiv by fastforce
  have "l_concat (map (red_rep S) l) \<in> \<langle>S\<rangle>" using Cons.prems append_equivred_span unfolding freegroup_def by auto
  then have "reln_tuple \<langle>S\<rangle> `` {l_concat (map (red_rep S) (a # l))} = reln_tuple \<langle>S\<rangle> `` {(red_rep S) a} \<otimes>\<^bsub>freegroup S\<^esub>  reln_tuple \<langle>S\<rangle> `` {(l_concat (map (red_rep S) l))}" using proj_append_wd[of "(red_rep S) a" "S" " l_concat (map (red_rep S) l)"] 1 a unfolding freegroup_def by auto
  moreover have "m_concat (freegroup S) (a # l) = a \<otimes>\<^bsub>freegroup S\<^esub> m_concat (freegroup S) l" unfolding m_concat.simps(2) by blast
  moreover have "a = reln_tuple \<langle>S\<rangle> `` {(red_rep S) a}" using red_rep_the a1 freegroup_def by (metis partial_object.select_convs(1))
  ultimately show ?case using I by simp
qed


lemma reducedE:
"\<exists>w. a ~ w \<and> reduced w"
proof-
  have "a ~ (iter (length a) reduce) a" by (simp add: cancels_imp_rel iter_cancels_to)
  moreover have "reduced ((iter (length a) reduce) a)" by (simp add: reduced_iter_length)
  ultimately show ?thesis by blast
qed

lemma "\<exists>! w. a ~ w \<and> reduced w"
proof(rule ex_ex1I)
  show "\<exists>w. a ~ w \<and> reduced w" using reducedE by blast
next
  show "\<And>w y. a ~ w \<and> reduced w \<Longrightarrow> a ~ y \<and> reduced y \<Longrightarrow> w = y "
  proof-
    fix w y assume "a ~ w \<and> reduced w" and "a ~ y \<and> reduced y"
    moreover then have "w ~ y" using reln.sym reln.trans by blast
    ultimately show "w = y"  by (simp add: reduced_cancel_eq reln_imp_cancels)
  qed
qed

fun a2
  where
"a2 (x,y,z) = x"

fun b2
  where
"b2 (x,y,z) = z"

fun p2
  where
"p2 (x,y,z) = y"


lemma cancel2E:
  assumes "reduced x"
          and "reduced y"
        shows "\<exists>w. x = (a2 w) @ (p2 w) \<and> y = (wordinverse (p2 w)) @ (b2 w) \<and> reduced ((a2 w) @ (b2 w))"
  using assms
proof(induction x)
  case Nil
  have "[] = [] @ []" by simp
  moreover have "y = wordinverse [] @ y" by simp
  moreover have "reduced ([] @ y)" using Nil.prems(2) by simp
  ultimately show ?case by simp
next
  case (Cons z zs)
  have "reduced zs" using Cons.prems(1) reduced_tl by blast
  then obtain w where w:"zs = a2 w @ p2 w \<and> y = wordinverse (p2 w) @ b2 w \<and> reduced (a2 w @ b2 w)" using Cons.IH Cons.prems(2) by blast
  then show ?case
  proof(cases "a2 w = []")
    case True note a2 = this
    then show ?thesis
    proof(cases "b2 w = []")
      case True
      have "(z#zs) = [z] @ p2 w" using a2 w by simp
      moreover have "reduced ([z] @ b2 w)" using True by simp
      moreover define w' where w':"w' = ([z], p2 w, b2 w)"
      moreover have "a2 w' = [z]" using w' by simp
      moreover have "b2 w' = b2 w" using w' by simp
      moreover have "p2 w' = p2 w" using w' by simp 
      ultimately show ?thesis using w by metis
    next
      case False
      then obtain b bs where b2:"b#bs = b2 w" using list.exhaust by metis
      have rb2: "reduced (b2 w)" using w reduced_leftappend by blast
      then have rbs: "reduced bs" using b2 using reduced_tl by metis
      then show ?thesis
      proof(cases "z = inverse b")
        case True
        then have 1:"wordinverse ([z]@(p2 w)) = (wordinverse (p2 w)) @ [b]" using inverse_of_inverse by fastforce
        define w' where w':"w' = (([]::('a,'b) word), ([z]@(p2 w)), bs)"
        moreover then have "(z#zs) = a2 w' @ p2 w'" using w a2 by simp
        moreover have "y = wordinverse (p2 w') @ (b2 w')" using w w' 1 b2 by auto
        moreover have "reduced (a2 w' @ b2 w')" using w' rbs by simp
        ultimately show ?thesis by blast
      next
        case False
        define w' where w': "w' = ([z], (p2 w),b#bs)"
        moreover then have "(z#zs) = a2 w' @ p2 w'" using w a2 by simp
        moreover have "y = wordinverse (p2 w') @ (b2 w')" using w w' b2 by auto
        moreover have "(a2 w' @ b2 w') = (z#b#bs)" using b2 w' by simp
        moreover then have "reduced (a2 w' @ b2 w')" using rb2 b2 False reduced.simps(3) by metis
        ultimately show ?thesis by blast
      qed
    qed
  next
    case False
    then obtain a as where a2:"a2 w = a#as" using list.exhaust by metis
    then have za:"z \<noteq> inverse a"  using Cons.prems(1) w by auto
    define w' where w':"w' = ((z#a#as), p2 w, b2 w)"
    moreover have zzs:"(z#zs) = a2 w' @ p2 w'" using w w' a2 by simp
    moreover have "y = wordinverse (p2 w') @ (b2 w')" using w w' by simp
    moreover have "reduced ((a2 w') @ (b2 w'))" using Cons.prems(1) za w w' zzs reduced.simps(3) by auto 
    ultimately show ?thesis by blast
  qed
qed

lemma cancel2E':
  assumes "reduced x"
      and "reduced y"
    shows "\<exists>! w. x = (a2 w) @ (p2 w) \<and> y = (wordinverse (p2 w)) @ (b2 w) \<and> reduced ((a2 w) @ (b2 w))"
proof(rule ex_ex1I)
  show "\<exists>w. x = a2 w @ p2 w \<and> y = wordinverse (p2 w) @ b2 w \<and> reduced (a2 w @ b2 w)" using cancel2E assms by blast
next
  fix w v
  assume w:"x = a2 w @ p2 w \<and> y = wordinverse (p2 w) @ b2 w \<and> reduced (a2 w @ b2 w)"
  and v: "x = a2 v @ p2 v \<and> y = wordinverse (p2 v) @ b2 v \<and> reduced (a2 v @ b2 v)"
  then obtain c where c:"p2 w = c @ p2 v \<and> (a2 v = a2 w @ c) \<or> p2 v = c @ p2 w \<and> (a2 w = a2 v @ c)" using append_eq_append_conv2[of "a2 w" "p2 w" "a2 v" "p2 v"] by metis
  have wd: "w = (a2 w, p2 w, b2 w)" by (metis a2.simps b2.elims p2.simps)
  have vd: "v = (a2 v, p2 v, b2 v)" by (metis a2.simps b2.elims p2.simps)
  then show "w = v"
  proof(cases "c = []")
    case True
    then have "p2 w = p2 v" using c by auto
    moreover then have "a2 w = a2 v" using w v by simp
    moreover then have "b2 w = b2 v" using v w by auto
    ultimately show ?thesis using wd vd by simp
  next
    case False note cn = this
    then show ?thesis
    proof(cases "p2 w = c @ p2 v \<and> (a2 v = a2 w @ c)")
      case True
      then have "wordinverse (p2 w) = wordinverse (p2 v) @ wordinverse c" using c wordinverse_append by metis
      then have "wordinverse c @ b2 w = b2 v" using w v by auto
      then have 1:"a2 v @ b2 v = a2 w @ c @ wordinverse c @ b2 w" using True by simp
      then have "(a2 v @ b2 v) ~ a2 w @ c @ wordinverse c @ b2 w" using reln.refl by simp
      moreover have "(c @ wordinverse c) ~ []" by (simp add: wordinverse_inverse)
      ultimately have  "(a2 v @ b2 v) ~ a2 w @ b2 w" using 1 by (metis (no_types, lifting) append_Nil2 append_assoc mult reln.refl)
      then have "(a2 v @ b2 v) = a2 w @ b2 w" using w v  by (simp add: reduced_cancel_eq reln_imp_cancels)
      moreover have "(a2 v @ b2 v) \<noteq> a2 w @ b2 w" using 1 cn by simp
      ultimately show ?thesis by blast
    next
      case False
      then have F:"p2 v = c @ p2 w \<and> (a2 w = a2 v @ c)" using c by blast
      then have "wordinverse (p2 v) = wordinverse (p2 w) @ wordinverse c" using c wordinverse_append by metis
      then have "wordinverse c @ b2 v = b2 w" using w v by auto
      then have 1:"a2 w @ b2 w = a2 v @ c @ wordinverse c @ b2 v" using F by simp
      then have "(a2 w @ b2 w) ~ a2 v @ c @ wordinverse c @ b2 v" using reln.refl by simp
      moreover have "(c @ wordinverse c) ~ []" by (simp add: wordinverse_inverse)
      ultimately have  "(a2 w @ b2 w) ~ a2 v @ b2 v" using 1 by (metis (no_types, lifting) append_Nil2 append_assoc mult reln.refl)
      then have "(a2 w @ b2 w) = a2 v @ b2 v" using w v  by (simp add: reduced_cancel_eq reln_imp_cancels)
      moreover have "(a2 w @ b2 w) \<noteq> a2 v @ b2 v" using 1 cn by simp
      ultimately show ?thesis by blast
    qed 
  qed
qed

definition cancel2 :: "('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> (('a,'b) word \<times> ('a,'b) word \<times> ('a,'b) word)" (infix "\<oslash>\<^bsub>2\<^esub>" 65)
  where
"cancel2 x y = (THE w. x = a2 w @  p2 w \<and> y = (wordinverse (p2 w)) @ b2 w \<and> reduced (a2 w@b2 w))"

lemma cancel2_the:
  assumes "reduced x"
      and "reduced y"
    shows "x = a2 (x\<oslash>\<^bsub>2\<^esub>y)  @  p2 (x\<oslash>\<^bsub>2\<^esub>y) \<and> y = (wordinverse (p2 (x\<oslash>\<^bsub>2\<^esub>y))) @ b2 (x\<oslash>\<^bsub>2\<^esub>y) \<and> reduced (a2 (x\<oslash>\<^bsub>2\<^esub>y)@b2 (x\<oslash>\<^bsub>2\<^esub>y))"
  unfolding cancel2_def
  by(rule theI', simp add: assms cancel2E')

definition N1 :: "('a,'b) word \<Rightarrow> ('a, 'b) word \<Rightarrow> bool"
  where
"N1 x y = ((x \<noteq> wordinverse y) \<longrightarrow> (less_eq (length (p2 (x\<oslash>\<^bsub>2\<^esub>y))) (length (a2 (x\<oslash>\<^bsub>2\<^esub>y))) \<and> less_eq (length (p2 (x\<oslash>\<^bsub>2\<^esub>y))) (length (b2 (x\<oslash>\<^bsub>2\<^esub>y)))))"

lemma red_rep_proj_app:
  assumes "k ∈ (⟨A⟩ // reln_tuple ⟨A⟩) ∧ m ∈ (⟨A⟩ // reln_tuple ⟨A⟩)"           
  shows "((red_rep A (proj_append ⟨A⟩ k m))) = iter (length ((red_rep A k) @ (red_rep A m))) reduce ((red_rep A k) @ (red_rep A m))"
proof-
  let ?rk = "red_rep A k" 
  let ?rm = "red_rep A m"
  let ?rkm = "((iter (length (?rk@?rm)) reduce (?rk@?rm)))"
  have appA:"(?rk@?rm) ∈ ⟨A⟩" using red_rep_def assms(1) by (smt (verit) append_congruent equiv_2f_clos red_rep_the reln_equiv)
  have 1:"equiv ⟨A⟩ (reln_tuple ⟨A⟩)" by (simp add: reln_equiv)
  moreover have "(red_rep A k) ∈ ⟨A⟩ ∧ (red_rep A m) ∈ ⟨A⟩" using red_rep_def assms calculation in_quotient_imp_subset red_rep_the by blast
  moreover have "proj_append ⟨A⟩ (reln_tuple ⟨A⟩ `` {red_rep A k}) (reln_tuple ⟨A⟩ `` {red_rep A m}) = reln_tuple ⟨A⟩ `` {red_rep A k @ red_rep A m}" unfolding proj_append_def using assms append_congruent[of "A"] proj_append_wd[of "red_rep A k" "A" "red_rep A m"] calculation(2) proj_append_def by blast   
  ultimately have 2:"proj_append ⟨A⟩ k m  = reln_tuple ⟨A⟩ `` {red_rep A k @ red_rep A m}" using assms by (metis (no_types, opaque_lifting) red_rep_the)
  then have "(?rkm) ~ (?rk@?rm)" using cancels_imp_rel iter_cancels_to reln.sym by blast
  moreover then have "(?rkm) ∈ ⟨A⟩" using appA cancels_to_preserves iter_cancels_to by blast
  ultimately have crc: "((?rk@?rm), ?rkm) ∈ reln_tuple ⟨A⟩" using appA reln_tuple_def by (smt (z3) case_prodI mem_Collect_eq reln.sym)
  then have "(reln_tuple ⟨A⟩`` {?rkm}) = (reln_tuple ⟨A⟩ `` {?rk@?rm})" using "1" equiv_class_eq_iff by fastforce
  moreover then have a:"?rkm ∈ (reln_tuple ⟨A⟩ `` {?rk@?rm})" using  crc by simp
  moreover have "reduced ?rkm" using reduced_iter_length by blast
  ultimately have "red_rep A (reln_tuple ⟨A⟩ `` {?rk@?rm}) = ?rkm" using red_rep_def assms(1) 2 by (metis (no_types, lifting) proj_append_clos red_rep_the redelem_unique)
  then show ?thesis unfolding proj_append_def using 1 2 assms append_congruent[of "A"] proj_append_wd[of "red_rep A k" "A" "red_rep A m"] red_rep_def equiv_2f_wd[of "(freewords_on A)" "(reln_tuple (freewords_on A))" "append" "red_rep A k" "red_rep A m"] by (simp add: proj_append_def)
qed

lemma iter_wordinv:
  assumes "(k @ m) = (a@b@(wordinverse b)@c)"
          "reduced (a@c)"
    shows "(iter (length (k@m)) reduce (k@m)) = (a@c)"
proof-
  have "(iter (length (b@(wordinverse b))) reduce (b@(wordinverse b))) = []" using FreeGroupMain.wordinverse_inverse cancels_imp_iter reln_imp_cancels by fastforce
  then show ?thesis using assms by (metis (no_types, opaque_lifting) append.assoc append.left_neutral cancels_eq_leftappend cancels_eq_rightappend cancels_imp_iter iter_imp_cancels reduced_iter_eq reduced_iter_length)
qed

lemma N1_length:
  assumes "k ∈ (⟨A⟩ // reln_tuple ⟨A⟩) ∧ m ∈ (⟨A⟩ // reln_tuple ⟨A⟩)" 
          "N1 (red_rep A k) (red_rep A m)"
          "((red_rep A k) ≠ wordinverse (red_rep A m))"
          "(length ((red_rep A (proj_append ⟨A⟩ k m)))) = b"
          "length (red_rep A k) = a"
          "length (red_rep A m) = c"
    shows "(greater_eq b a) ∧ (greater_eq b c)"
proof-
  let ?rk = "red_rep A k" 
  let  ?rm = "red_rep A m"
  have N1:"(less_eq (length (p2 (?rk⊘⇘2⇙?rm))) (length (a2 (?rk⊘⇘2⇙?rm)))) 
         ∧ less_eq (length (p2 (?rk⊘⇘2⇙?rm))) (length (b2 (?rk⊘⇘2⇙?rm)))" using assms(2,3) N1_def by blast
  then have x:"?rk = ((a2 (?rk⊘⇘2⇙?rm)) @ (p2 (?rk⊘⇘2⇙?rm)))" using cancel2_def[of "?rk" "?rm"] cancel2_the red_rep_def assms(1) red_rep_the by blast
  have y:"?rm = ((wordinverse(p2 (?rk⊘⇘2⇙?rm))) @ (b2 (?rk⊘⇘2⇙?rm)))" using cancel2_def[of "?rk" "?rm"] cancel2_the red_rep_def assms(1) red_rep_the by blast
  have rac:"reduced ((a2 (?rk⊘⇘2⇙?rm))@(b2 (?rk⊘⇘2⇙?rm)))" using cancel2_def[of "?rk" "?rm"] cancel2_the red_rep_def assms(1) red_rep_the by blast
  have a:"length(p2 (?rk⊘⇘2⇙?rm)) ≤ length (a2 (?rk⊘⇘2⇙?rm))" using x y rac N1_def assms(2) using N1 by blast
  have b:"length(p2 (?rk⊘⇘2⇙?rm)) ≤ length (b2 (?rk⊘⇘2⇙?rm))" using x y rac N1_def assms(2) using N1 by blast  
  have 1:"((red_rep A (proj_append ⟨A⟩ k m))) = (iter (length (?rk @ ?rm)) reduce (?rk @ ?rm))" using assms(1) red_rep_proj_app by blast
  then have "(?rk @ ?rm) = ((a2 (?rk⊘⇘2⇙?rm)) @ (p2 (?rk⊘⇘2⇙?rm))@(wordinverse(p2 (?rk⊘⇘2⇙?rm))) @ (b2 (?rk⊘⇘2⇙?rm)))" using x y by auto
  then have 2:"(iter (length (?rk @ ?rm)) reduce (?rk @ ?rm)) = ((a2 (?rk⊘⇘2⇙?rm)) @ (b2 (?rk⊘⇘2⇙?rm)))" using rac iter_wordinv by blast
  have "(length (iter (length (?rk @ ?rm)) reduce (?rk @ ?rm))) ≤ length (?rk @ ?rm)" using length_reduce_iter by blast
  have "(b ≥ (length ?rk)) ∧ (b ≥ (length ?rm))" using a b 1 2 by (metis (no_types, lifting) add_le_mono1 assms(4) length_append length_wordinverse nat_add_left_cancel_le x y)
  then show ?thesis using assms(3,4,5,6) a b by auto
qed

lemma reduced_reln_eq:
"a ~ b \<Longrightarrow> reduced a \<Longrightarrow> reduced b \<Longrightarrow> a = b"
  by (simp add: reduced_cancel_eq reln_imp_cancels)
     
lemma cancel2_reln:
  assumes "x = a @ p \<and> y = (wordinverse p) @ b"
  shows "(x@y) ~ (a@b)"
proof-
  have "(p @ wordinverse p) ~ []" by (simp add: wordinverse_inverse)
  then show ?thesis using assms  mult reln.refl  by (metis append_Nil2 append.assoc)
qed

lemma reln_eq: assumes "reln_tuple ⟨A⟩ `` {a} = reln_tuple ⟨A⟩ `` {b}" "a ∈ ⟨A⟩" "b ∈ ⟨A⟩"
  shows "a ~ b"
  using assms unfolding reln_tuple_def by blast

lemma redrep_in:  assumes "x ∈ carrier (freegroup A)"
  shows "red_rep A x ∈ ⟨A⟩"
  using assms red_rep_def red_rep_the unfolding freegroup_def
  using Union_quotient reln_equiv by fastforce

lemma mult_reln:
  assumes "x ∈ carrier (freegroup A)" "y ∈ carrier (freegroup A)"
  shows "(red_rep A (x ⊗⇘F⇘A⇙⇙ y)) ~ ((red_rep A x) @ (red_rep A y))"
proof-
  have "x = reln_tuple ⟨A⟩ `` {red_rep A x}" using red_rep_def red_rep_the assms(1) unfolding freegroup_def by fastforce
  moreover have 1:"red_rep A x ∈ ⟨A⟩" using assms(1) redrep_in by blast
  moreover have "y = reln_tuple ⟨A⟩ `` {red_rep A y}" using red_rep_def red_rep_the assms(2) unfolding freegroup_def by fastforce
  moreover have 2: "red_rep A y ∈ ⟨A⟩" using assms(2) redrep_in by blast
  ultimately have "reln_tuple ⟨A⟩ `` {(red_rep A (x ⊗⇘F⇘A⇙⇙ y))} = reln_tuple ⟨A⟩ `` {((red_rep A x) @ (red_rep A y))}" using proj_append_wd unfolding freegroup_def
    by (metis assms(1) assms(2) freegroup_def monoid.select_convs(1) partial_object.select_convs(1) proj_append_clos red_rep_the)
  moreover have "((red_rep A x) @ (red_rep A y)) ∈ ⟨A⟩" using 1 2 unfolding freewords_on_def by (simp add: span_append)
  moreover have "(red_rep A (x ⊗⇘F⇘A⇙⇙ y)) ∈ ⟨A⟩" by (simp add: assms(1) assms(2) freegroup_is_group group.subgroup_self redrep_in subgroup.m_closed)
  ultimately show ?thesis using reln_eq by auto
qed

lemma length_N1:
  assumes "x ∈ carrier (freegroup A)" "y ∈ carrier (freegroup A)"  "length (red_rep A (x ⊗⇘F⇘A⇙⇙ y)) ≥ length (red_rep A x) ∧ length (red_rep A (x ⊗⇘F⇘A⇙⇙ y)) ≥  length (red_rep A y)"
  shows "N1 (red_rep A x) (red_rep A y)"
proof-
  let ?x = "(red_rep A x)"
  let ?y = "(red_rep A y)"
  let ?xy = "(cancel2 ?x ?y)"
  have xy: "(x ⊗⇘F⇘A⇙⇙ y) ∈ carrier (freegroup A)" by (simp add: assms(1) assms(2) freegroup_is_group group.subgroupE(4) group.subgroup_self)
  have 1:"reduced ?x" using assms(1) red_rep_def red_rep_the unfolding freegroup_def by fastforce
  moreover have 2:"reduced ?y" using assms(2) red_rep_def red_rep_the  unfolding freegroup_def by fastforce
  ultimately have "((red_rep A x) @ (red_rep A y)) ~ ((a2 ?xy) @ (b2 ?xy))" by (metis cancel2_reln cancel2_the)
  then have "(red_rep A (x ⊗⇘F⇘A⇙⇙ y)) ~ ((a2 ?xy) @ (b2 ?xy))" using assms mult_reln using reln.trans by blast
  moreover have "reduced ((a2 ?xy) @ (b2 ?xy))" by (simp add: "1" "2" cancel2_the)
  moreover have "reduced (red_rep A (x ⊗⇘F⇘A⇙⇙ y))" using xy red_rep_def red_rep_the unfolding freegroup_def by fastforce
  ultimately have 3: "(red_rep A (x ⊗⇘F⇘A⇙⇙ y)) = ((a2 ?xy) @ (b2 ?xy))" by (simp add: reduced_reln_eq)
  have "?x = (a2 ?xy) @ (p2 ?xy)" using 1 2 by (simp add: cancel2_the)
  then have "length ((a2 ?xy) @ (b2 ?xy)) ≥ length ((a2 ?xy) @ (p2 ?xy))" using assms(3) 3 by auto
  then have A:"length (b2 ?xy) ≥ length (p2 ?xy)" by auto
  have "?y =  wordinverse (p2 ?xy) @ (b2 ?xy)" using 1 2 by (simp add: cancel2_the)
  then have "length ((a2 ?xy) @ (b2 ?xy)) ≥ length (wordinverse (p2 ?xy) @ (b2 ?xy))" using 3 assms(3) by auto
  then have "length (a2 ?xy) ≥ length (wordinverse (p2 ?xy))" by auto
  then have "length (a2 ?xy) ≥ length (p2 ?xy)" by (metis length_wordinverse)
  then show ?thesis unfolding N1_def using A by blast
qed

fun a3 where
"a3 (v,w,x,y,z) = v"

fun b3 where
"b3 (v,w,x,y,z) = x"

fun c3 where
"c3 (v,w,x,y,z) = z"

fun p3 where
"p3 (v,w,x,y,z) = w"

fun q3 where
"q3 (v,w,x,y,z) = y"

definition cancel3 :: "('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> (('a,'b) word \<times> ('a,'b) word \<times> ('a,'b) word \<times> ('a,'b) word \<times> ('a,'b) word)" ("\<oslash>\<^bsub>3\<^esub>")
  where
"cancel3 x y z = (THE w. x = a3 w @  (p3 w) \<and> y = wordinverse  (p3 w) @ b3 w @ (q3 w) \<and> z = (wordinverse  (q3 w)) @ (c3 w) \<and> reduced (a3 w@b3 w @ q3 w) \<and> reduced (wordinverse  (p3 w) @ b3 w @ c3 w))"

lemma tuple3:
"\<forall>v. v  = (a3 v, p3 v, b3 v, q3 v, c3 v)"
  by simp


lemma appendeq_length1:
  assumes "a@b = c@d"
      and "length a < length b"
      and "length d < length c"
    shows "length a < length c"
  using assms by (metis (no_types, lifting) length_append less_add_eq_less linorder_neqE_nat order.strict_trans)

lemma appendeq_length2:
  assumes "a@b = c@d"
      and "length a < length b"
      and "length d < length c"
    shows "length d < length b"
  using assms by (metis (no_types, lifting) length_append less_add_eq_less linorder_neqE_nat order.strict_trans)


lemma appendeq_length3:
  assumes "a@b = c@d"
      and "length a < length b"
      and "length d = length c"
    shows "length a < length c"
  using assms  by (metis (no_types, lifting) length_append less_add_eq_less linorder_neqE_nat order.strict_trans)

lemma appendeq_length4:
  assumes "a@b = c@d"
      and "length a < length b"
      and "length d = length c"
    shows "length d < length b"
  using assms by (metis (no_types, lifting) length_append less_add_eq_less linorder_neqE_nat order.strict_trans)

lemma appendeq_length5:
  assumes "a@b = c@d"
      and "length a = length b"
      and "length d < length c"
    shows "length a < length c"
  using assms by (metis (no_types, lifting) append_eq_append_conv dual_order.strict_trans length_append less_add_eq_less linorder_neqE_nat)

lemma appendeq_length6:
  assumes "a@b = c@d"
      and "length a = length b"
      and "length d < length c"
    shows "length d < length b"
  using assms by (metis (no_types, lifting) append_eq_append_conv dual_order.strict_trans length_append less_add_eq_less linorder_neqE_nat)

lemma overlap_middle_exists:
  assumes "a@b = c@d"
      and "length a \<le> length b"
      and "length d \<le> length c"
    shows "\<exists>x. a@x@d = a@b"
proof(cases "length a < length b")
  case True note ab = this
  then show ?thesis
  proof(cases "length d < length c")
    case True
    from assms(1) have "length a < length c" using ab True appendeq_length1 by auto
    hence y:"\<exists>y. a@y = c" using assms(1) overlapleftexist by blast
    from assms(1) have "length d < length b" using ab True appendeq_length2 by auto
    hence x:"\<exists>x. x@d = b" using assms(1) overlaprightexist by metis
    from x y assms(1) show ?thesis by auto
  next
    case False
    then have l:"length d = length c" using assms(3) by simp
    then have "length a < length c" using assms(1) ab appendeq_length3 by blast
    hence y:"\<exists>y. a@y = c" using assms(1) overlapleftexist by blast
    from assms(1) have "length d < length b" using ab l appendeq_length4 by blast
    hence x:"\<exists>x. x@d = b" using assms(1) overlaprightexist by metis
    from x y assms(1) show ?thesis by auto
  qed
next
  case False
  then have la:"length a = length b" using assms(2) by auto
  then show ?thesis
  proof(cases "length d < length c")
    case True
    from assms(1) have "length a < length c" using True la appendeq_length5 by blast
    hence y:"\<exists>y. a@y = c" using assms(1) overlapleftexist by blast
    from assms(1) have "length d < length b" using True la appendeq_length6 by blast
    hence x:"\<exists>x. x@d = b" using assms(1) overlaprightexist by metis
    from x y assms(1) show ?thesis by auto
  next
    case False
    then have l:"length d = length c" using assms(3) by simp
    then have "length a = length c" using assms(1) la by (metis (mono_tags, lifting) "appendeq_length1" length_append less_add_eq_less nat_neq_iff)
    then show ?thesis using assms(1) by auto
  qed
qed

lemma cancel3E:
  assumes "reduced x"
      and "reduced y"
      and "reduced z"
      and "N1 x y"
      and "N1 y z"
      and "x \<noteq> wordinverse y"
      and "y \<noteq> wordinverse z"
    shows "\<exists>w. x = a3 w @  (p3 w) \<and> y = wordinverse  (p3 w) @ b3 w @ (q3 w) \<and> z = (wordinverse  (q3 w)) @ (c3 w) \<and> reduced (a3 w @ b3 w @ q3 w) \<and> reduced (wordinverse  (p3 w) @ b3 w @ c3 w)"
proof-
  have xy:"x = a2 (x\<oslash>\<^bsub>2\<^esub>y)  @  p2 (x\<oslash>\<^bsub>2\<^esub>y) \<and> y = (wordinverse (p2 (x\<oslash>\<^bsub>2\<^esub>y))) @ b2 (x\<oslash>\<^bsub>2\<^esub>y) \<and> reduced (a2 (x\<oslash>\<^bsub>2\<^esub>y)@b2 (x\<oslash>\<^bsub>2\<^esub>y))" using assms(1,2) cancel2_the by fastforce
  then have 1:"(less_eq (length (p2 (x\<oslash>\<^bsub>2\<^esub>y))) (length (a2 (x\<oslash>\<^bsub>2\<^esub>y))) \<and> less_eq (length (p2 (x\<oslash>\<^bsub>2\<^esub>y))) (length (b2 (x\<oslash>\<^bsub>2\<^esub>y))))" using assms(4,6) unfolding N1_def by blast
  have yz:"y = a2 (y\<oslash>\<^bsub>2\<^esub>z)  @  p2 (y\<oslash>\<^bsub>2\<^esub>z) \<and> z = (wordinverse (p2 (y\<oslash>\<^bsub>2\<^esub>z))) @ b2 (y\<oslash>\<^bsub>2\<^esub>z) \<and> reduced (a2 (y\<oslash>\<^bsub>2\<^esub>z)@b2 (y\<oslash>\<^bsub>2\<^esub>z))" using assms(2,3) cancel2_the by fastforce
  then have 2:"(less_eq (length (p2 (y\<oslash>\<^bsub>2\<^esub>z))) (length (a2 (y\<oslash>\<^bsub>2\<^esub>z))) \<and> less_eq (length (p2 (y\<oslash>\<^bsub>2\<^esub>z))) (length (b2 (y\<oslash>\<^bsub>2\<^esub>z))))" using assms(5,7) unfolding N1_def by blast
  let ?a = "a2 (x\<oslash>\<^bsub>2\<^esub>y)"
  let ?b1 = "b2 (x\<oslash>\<^bsub>2\<^esub>y)"
  let ?b2 = "a2  (y\<oslash>\<^bsub>2\<^esub>z)"
  let ?c = "b2  (y\<oslash>\<^bsub>2\<^esub>z)"
  let ?p = "p2 (x\<oslash>\<^bsub>2\<^esub>y)"
  let ?q = "p2 (y\<oslash>\<^bsub>2\<^esub>z)"
  have "wordinverse (p2 (x \<oslash>\<^bsub>2\<^esub> y)) @ b2 (x \<oslash>\<^bsub>2\<^esub> y) = a2 (y \<oslash>\<^bsub>2\<^esub> z) @ p2 (y \<oslash>\<^bsub>2\<^esub> z)" using xy yz by simp
  moreover have "(length ?p) = (length (wordinverse ?p))" using length_wordinverse by blast
  moreover then have "length (wordinverse (p2 (x \<oslash>\<^bsub>2\<^esub> y))) \<le> length (b2 (x \<oslash>\<^bsub>2\<^esub> y))" using 1 by auto
  moreover have "length (p2 (y \<oslash>\<^bsub>2\<^esub> z)) \<le> length (a2 (y \<oslash>\<^bsub>2\<^esub> z))" using 2 by simp
  ultimately obtain b where b:"(wordinverse ?p)@b@(?q) = y" using 1 2 xy yz overlap_middle_exists[of "(wordinverse ?p)" "?b1" "?b2" "?q"] by auto
  define w where w:"w = (?a, ?p, b, ?q, ?c)"
  then have "x = a3 w @ (p3 w)" using xy by auto
  moreover have "y = wordinverse  (p3 w) @ b3 w @ (q3 w)" using w b by auto
  moreover have "z = (wordinverse  (q3 w)) @ (c3 w)" using w yz by auto
  moreover have "reduced (a3 w @ b3 w @ q3 w)" using xy yz w b a3.simps b3.simps q3.simps by (metis same_append_eq)
  moreover have "reduced (wordinverse  (p3 w) @ b3 w @ c3 w)" using xy yz w b p3.simps b3.simps c3.simps by (metis (no_types, lifting) append.assoc append_same_eq)
  ultimately show ?thesis using w by blast
qed

lemma cancel3E':
  assumes "reduced x"
      and "reduced y"
      and "reduced z"
      and "N1 x y"
      and "N1 y z"
      and "x \<noteq> wordinverse y"
      and "y \<noteq> wordinverse z"
    shows "\<exists>!w. x = a3 w @  (p3 w) \<and> y = wordinverse  (p3 w) @ b3 w @ (q3 w) \<and> z = (wordinverse  (q3 w)) @ (c3 w) \<and> reduced (a3 w@b3 w @ q3 w) \<and> reduced (wordinverse  (p3 w) @ b3 w @ c3 w)"
proof(rule ex_ex1I)
  show "\<exists>w. x = a3 w @ p3 w \<and>
        y = wordinverse (p3 w) @ b3 w @ q3 w \<and>
        z = wordinverse (q3 w) @ c3 w \<and>
        reduced (a3 w @ b3 w @ q3 w) \<and> reduced (wordinverse (p3 w) @ b3 w @ c3 w)"
    using cancel3E assms by blast
next
  fix v w assume v:"x = a3 (v::(('a,'b) word \<times> ('a,'b) word \<times> ('a,'b) word \<times> ('a,'b) word \<times> ('a,'b) word))
       @ p3 v \<and>
       y = wordinverse (p3 v) @ b3 v @ q3 v \<and>
       z = wordinverse (q3 v) @ c3 v \<and>
       reduced (a3 v @ b3 v @ q3 v) \<and> reduced (wordinverse (p3 v) @ b3 v @ c3 v)"
          and w: "x = a3 (w::(('a,'b) word \<times> ('a,'b) word \<times> ('a,'b) word \<times> ('a,'b) word \<times> ('a,'b) word))
       @ p3 w \<and>
       y = wordinverse (p3 w) @ b3 w @ q3 w \<and>
       z = wordinverse (q3 w) @ c3 w \<and>
       reduced (a3 w @ b3 w @ q3 w) \<and> reduced (wordinverse (p3 w) @ b3 w @ c3 w)"
  define v1 where v1:"v1 = (a3 v, p3 v, (b3 v @ q3 v))"
  define w1 where w1:"w1 = (a3 w, p3 w, (b3 w @ q3 w))"
  have "x = a2 v1 @ p2 v1 \<and>
       y = wordinverse (p2 v1) @ b2 v1 \<and>
       reduced (a2 v1 @ b2 v1)" using v v1 by simp
  moreover have "x = a2 w1 @ p2 w1 \<and>
       y = wordinverse (p2 w1) @ b2 w1 \<and>
       reduced (a2 w1 @ b2 w1)" using w w1 by simp
  ultimately have 1:"v1 = w1" using cancel2E' assms(1,2) by blast
  define v2 where v2:"v2 = (wordinverse (p3 v) @ b3 v, q3 v, c3 v)"
  define w2 where w2:"w2 = (wordinverse (p3 w) @ b3 w, q3 w, c3 w)"
  have "y = a2 v2 @ p2 v2 \<and>
       z = wordinverse (p2 v2) @ b2 v2 \<and>
       reduced (a2 v2 @ b2 v2)" using v v2 by simp
  moreover have "y = a2 w2 @ p2 w2 \<and>
       z = wordinverse (p2 w2) @ b2 w2 \<and>
       reduced (a2 w2 @ b2 w2)" using w w2 by simp
  ultimately have "v2 = w2" using cancel2E' assms(2,3) by blast
  then have 2:"a3 v = a3 w \<and> p3 v = p3 w \<and> q3 v = q3 w \<and> c3 v = c3 w" using 1 v1 v2 w1 w2 by fast
  then moreover have "b3 v = b3 w" using v w by simp
  moreover have "v  = (a3 v, p3 v, b3 v, q3 v, c3 v)" using tuple3 by blast
  moreover have "w  = (a3 w, p3 w, b3 w, q3 w, c3 w)" using tuple3 by blast
  ultimately show "v = w" by presburger
qed

lemma cancel3_the:
  assumes "reduced x"
      and "reduced y"
      and "reduced z"
      and "N1 x y"
      and "N1 y z"
      and "x \<noteq> wordinverse y"
      and "y \<noteq> wordinverse z"
    shows "x = a3 (\<oslash>\<^bsub>3\<^esub> x y z) @  (p3 (\<oslash>\<^bsub>3\<^esub> x y z)) \<and> y = wordinverse  (p3 (\<oslash>\<^bsub>3\<^esub> x y z)) @ b3 (\<oslash>\<^bsub>3\<^esub> x y z) @ (q3 (\<oslash>\<^bsub>3\<^esub> x y z)) \<and> z = (wordinverse  (q3 (\<oslash>\<^bsub>3\<^esub> x y z))) @ (c3 (\<oslash>\<^bsub>3\<^esub> x y z)) \<and> reduced (a3 (\<oslash>\<^bsub>3\<^esub> x y z)@b3 (\<oslash>\<^bsub>3\<^esub> x y z) @ q3 (\<oslash>\<^bsub>3\<^esub> x y z)) \<and> reduced (wordinverse  (p3 (\<oslash>\<^bsub>3\<^esub> x y z)) @ b3 (\<oslash>\<^bsub>3\<^esub> x y z) @ c3 (\<oslash>\<^bsub>3\<^esub> x y z))"
    unfolding cancel3_def
    by(rule theI', simp add: assms cancel3E')

lemma cancel3_reln:
  assumes "x = a @ p  \<and> y = (wordinverse  p)  @ b @ q \<and> z = (wordinverse  q) @ c"
  shows "(x@y@z) ~ (a@b@c)"
proof-
  have "(p @ wordinverse p) ~ []" by (simp add: wordinverse_inverse)
  then have 1:"(x@y@z) ~ (a@b@q@(wordinverse q)@c)" using assms cancel2_reln by auto
  have "(q @ wordinverse q) ~ []" by (simp add: wordinverse_inverse)
  then have "(a@b@q@(wordinverse q)@c) ~ (a@b@c)"  by (metis append_assoc cancel2_reln)
  then show ?thesis using trans 1  by fast
qed

definition N2 :: "('a,'b) word \<Rightarrow> ('a, 'b) word \<Rightarrow> ('a, 'b) word \<Rightarrow> bool"
  where
"N2 x y z = ((x \<noteq> wordinverse y \<and> y \<noteq> wordinverse z) \<longrightarrow> (b3 (\<oslash>\<^bsub>3\<^esub> x y z) \<noteq> []))"

lemma reduced_overlap:
  assumes "reduced (a@b)"
      and "reduced (b@c)" 
      and "b \<noteq> []"
    shows "reduced (a@b@c)"
  using assms
proof(induction a)
  case Nil
  then show ?case by simp
next
  case (Cons a1 a2)
  then moreover have "reduced (a2 @ b)" by (metis assoc_Cons reduced_tl)
  ultimately have r:"reduced (a2@b@c)" by simp
  obtain b1 b2 where b:"b = b1#b2" using Cons.prems(3) list.exhaust by blast
  show ?case
  proof(cases "a2 = []")
    case True
    then have "a1 \<noteq> inverse b1" using Cons.prems(1) b by auto
    then show ?thesis using b True r by auto
  next
    case False
    then obtain a3 a4 where "a2 = a3#a4" using list.exhaust by blast
    moreover then have "a1 \<noteq> inverse a3" using Cons.prems(1) by auto
    ultimately show ?thesis  using r by auto
  qed
qed

lemma cancel3_b:
  assumes "reduced x"
      and "reduced y"
      and "reduced z"
      and "N1 x y"
      and "N1 y z"
      and "N2 x y z"
      and "x \<noteq> wordinverse y"
      and "y \<noteq> wordinverse z"
    shows "reduced (a3 (\<oslash>\<^bsub>3\<^esub> x y z) @ b3 (\<oslash>\<^bsub>3\<^esub> x y z) @ c3 (\<oslash>\<^bsub>3\<^esub> x y z))"
proof-
  have 1:"x = a3 (\<oslash>\<^bsub>3\<^esub> x y z) @  (p3 (\<oslash>\<^bsub>3\<^esub> x y z)) \<and> y = wordinverse  (p3 (\<oslash>\<^bsub>3\<^esub> x y z)) @ b3 (\<oslash>\<^bsub>3\<^esub> x y z) @ (q3 (\<oslash>\<^bsub>3\<^esub> x y z)) \<and> z = (wordinverse  (q3 (\<oslash>\<^bsub>3\<^esub> x y z))) @ (c3 (\<oslash>\<^bsub>3\<^esub> x y z)) \<and> reduced (a3 (\<oslash>\<^bsub>3\<^esub> x y z)@b3 (\<oslash>\<^bsub>3\<^esub> x y z) @ q3 (\<oslash>\<^bsub>3\<^esub> x y z)) \<and> reduced (wordinverse  (p3 (\<oslash>\<^bsub>3\<^esub> x y z)) @ b3 (\<oslash>\<^bsub>3\<^esub> x y z) @ c3 (\<oslash>\<^bsub>3\<^esub> x y z))" using assms cancel3_the by blast
  then have "reduced (b3 (\<oslash>\<^bsub>3\<^esub> x y z) @ c3 (\<oslash>\<^bsub>3\<^esub> x y z))" using reduced_leftappend by auto
  moreover have "reduced (a3 (\<oslash>\<^bsub>3\<^esub> x y z)@b3 (\<oslash>\<^bsub>3\<^esub> x y z))" using reduced_rightappend 1  by (metis append.assoc)
  moreover have "(b3 (\<oslash>\<^bsub>3\<^esub> x y z) \<noteq> [])" using assms(6,7,8) unfolding N2_def by blast
  ultimately show ?thesis using reduced_overlap by blast
qed

lemma cancel_a2_pb3:
  assumes "reduced x"
      and "reduced y"
      and "reduced z"
      and "N1 x y"
      and "N1 y z"
      and "N2 x y z"
      and "x \<noteq> wordinverse y"
      and "y \<noteq> wordinverse z"
    shows "a2 (cancel2 y z) = wordinverse  (p3 (cancel3 x y z)) @ b3 (cancel3 x y z)"
proof-
  have 1:"x = a3 (cancel3 x y z) @  (p3 (cancel3 x y z)) \<and> y = wordinverse  (p3 (cancel3 x y z)) @ b3 (cancel3 x y z) @ (q3 (cancel3 x y z)) \<and> z = (wordinverse  (q3 (cancel3 x y z))) @ (c3 (cancel3 x y z)) \<and> reduced (a3 (cancel3 x y z) @ b3 (cancel3 x y z) @ q3 (cancel3 x y z)) \<and> reduced (wordinverse  (p3 (cancel3 x y z)) @ b3 (cancel3 x y z) @ c3 (cancel3 x y z))" using assms cancel3_the by blast
  have 2:"y = (a2 (cancel2 y z)) @ (p2 (cancel2 y z)) \<and> z = (wordinverse (p2 (cancel2 y z))) @ (b2 (cancel2 y z)) \<and> reduced ((a2 (cancel2 y z)) @ (b2 (cancel2 y z)))" using assms(2,3) by (simp add: cancel2_the)
  define w2 where 3:"w2 = ((wordinverse  (p3 (cancel3 x y z)) @ b3 (cancel3 x y z)), (q3 (cancel3 x y z)), (c3 (cancel3 x y z)))"
  then have "y = (a2 w2) @ (p2 w2) \<and> z = (wordinverse (p2 w2)) @ (b2 w2) \<and> reduced ((a2 w2) @ (b2 w2))" using 1 by auto
  then have "w2 = (cancel2 y z)" using 2 assms(2,3) cancel2E' by blast
  then have "a2 w2 = a2 (cancel2 y z)" by simp
  then show ?thesis using 3 by simp
qed

lemma cancel_a2_a3:
  assumes "reduced x"
      and "reduced y"
      and "reduced z"
      and "N1 x y"
      and "N1 y z"
      and "N2 x y z"
      and "x \<noteq> wordinverse y"
      and "y \<noteq> wordinverse z"
    shows "a2 (cancel2 x y) = a3 (cancel3 x y z)"
proof-
  have 1:"x = a3 (cancel3 x y z) @  (p3 (cancel3 x y z)) \<and> y = wordinverse  (p3 (cancel3 x y z)) @ b3 (cancel3 x y z) @ (q3 (cancel3 x y z)) \<and> z = (wordinverse  (q3 (cancel3 x y z))) @ (c3 (cancel3 x y z)) \<and> reduced (a3 (cancel3 x y z) @ b3 (cancel3 x y z) @ q3 (cancel3 x y z)) \<and> reduced (wordinverse  (p3 (cancel3 x y z)) @ b3 (cancel3 x y z) @ c3 (cancel3 x y z))" using assms cancel3_the by blast
  have 2:"x = (a2 (cancel2 x y)) @ (p2 (cancel2 x y)) \<and> y = (wordinverse (p2 (cancel2 x y))) @ (b2 (cancel2 x y)) \<and> reduced ((a2 (cancel2 x y)) @ (b2 (cancel2 x y)))" using assms(1,2) by (simp add: cancel2_the)
  define w2 where 3:"w2 = (a3 (cancel3 x y z), (p3 (cancel3 x y z)), b3 (cancel3 x y z) @ (q3 (cancel3 x y z)))"
  then have "x = (a2 w2) @ (p2 w2) \<and> y = (wordinverse (p2 w2)) @ (b2 w2) \<and> reduced ((a2 w2) @ (b2 w2))" using 1 by auto
  then have "w2 = (cancel2 x y)" using 2 assms(1,2) cancel2E' by blast
  then have "a2 w2 = a2 (cancel2 x y)" by simp
  then show ?thesis using 3 by simp
qed

definition G
  where
"G H A g = \<langle>{h \<in> carrier H. (h,g) \<in> (lex_L2_word A)}\<rangle>\<^bsub>H\<^esub>"
(* G g := {<g'>. g' < g} *)

definition X
  where
"X H A = {g \<in> carrier H. g \<notin> (G H A g)}"

(*y <lex x and  xy <lex x = = > x not in X and x-1 not in X = = > x not in X U X-1*)


lemma subset_span:
  assumes "A \<subseteq> \<langle>S\<rangle>\<^bsub>H\<^esub>"
  shows "\<langle>A\<rangle>\<^bsub>H\<^esub> \<subseteq> \<langle>S\<rangle>\<^bsub>H\<^esub>"
proof
  fix x assume "x \<in> \<langle>A\<rangle>\<^bsub>H\<^esub>"
  then show "x \<in> \<langle>S\<rangle>\<^bsub>H\<^esub>"
  proof(induction rule: gen_span.induct)
    case gen_one
    then show ?case by simp
  next
    case (gen_gens x)
    then show ?case using assms by blast
  next
    case (gen_inv x)
    then show ?case by (simp add: gen_span.gen_inv)
  next
    case (gen_mult x y)
    then show ?case by (simp add: gen_span.gen_mult)
  qed
qed

lemma subgroup_is_group:
  assumes "group A"
      and "subgroup H A" 
  shows "group (A\<lparr>carrier := H\<rparr>)"
  by (simp add: assms(1) assms(2) subgroup.subgroup_is_group)

definition SG
  where
"SG A H = (A\<lparr>carrier := H\<rparr>)"

lemma
  assumes "H \<le> freegroup A"
  shows "\<langle>X (SG (freegroup A) H) A\<rangle>\<^bsub>(SG (freegroup A) H)\<^esub> = carrier (SG (freegroup A) H)"
proof(rule ccontr)
  assume a:"\<langle>X (SG (freegroup A) H) A\<rangle>\<^bsub>(SG (freegroup A) H)\<^esub> \<noteq> carrier (SG (freegroup A) H)"
  have "X (SG (freegroup A) H) A \<subseteq> carrier (SG (freegroup A) H)" unfolding X_def SG_def by fastforce
  moreover have "group (SG (freegroup A) H)" using assms freegroup_is_group subgroup_is_group unfolding SG_def by blast
  ultimately have "\<langle>X (SG (freegroup A) H) A\<rangle>\<^bsub>(SG (freegroup A) H)\<^esub> \<subseteq> carrier (SG (freegroup A) H)" using group.gen_span_closed by blast
  then have "carrier (SG (freegroup A) H) - \<langle>X (SG (freegroup A) H) A\<rangle>\<^bsub>(SG (freegroup A) H)\<^esub> \<noteq> {}" using a by blast
  then obtain x where "x \<in> (carrier (SG (freegroup A) H) - \<langle>X (SG (freegroup A) H) A\<rangle>\<^bsub>(SG (freegroup A) H)\<^esub>)" by blast
  then obtain x' where 1:"x'\<in> (carrier (SG (freegroup A) H) - \<langle>X (SG (freegroup A) H) A\<rangle>\<^bsub>(SG (freegroup A) H)\<^esub>) \<and>  (\<forall>y. (y, x') \<in> lex_L2_word A \<longrightarrow> y \<notin> (carrier (SG (freegroup A) H) - \<langle>X (SG (freegroup A) H) A\<rangle>\<^bsub>(SG (freegroup A) H)\<^esub>))" using wfE_min[of "(lex_L2_word A)" "x" "(carrier (SG (freegroup A) H) - \<langle>X (SG (freegroup A) H) A\<rangle>\<^bsub>(SG (freegroup A) H)\<^esub>)"] wf_lex_L2_word by metis
  then have "\<forall>y \<in> (carrier (SG (freegroup A) H)). (y,x') \<in> (lex_L2_word A) \<longrightarrow> y \<in> \<langle>X (SG (freegroup A) H) A\<rangle>\<^bsub>(SG (freegroup A) H)\<^esub>" by blast
  then have "{h \<in> (carrier (SG (freegroup A) H)). (h,x') \<in> (lex_L2_word A)} \<subseteq> \<langle>X (SG (freegroup A) H) A\<rangle>\<^bsub>(SG (freegroup A) H)\<^esub>" by blast
  then have "\<langle>{h \<in> (carrier (SG (freegroup A) H)). (h,x') \<in> (lex_L2_word A)}\<rangle>\<^bsub>(SG (freegroup A) H)\<^esub> \<subseteq> \<langle>X (SG (freegroup A) H) A\<rangle>\<^bsub>(SG (freegroup A) H)\<^esub>" using subset_span by blast
  moreover have 2: "x' \<notin> \<langle>X (SG (freegroup A) H) A\<rangle>\<^bsub>(SG (freegroup A) H)\<^esub>" using 1 by blast
  ultimately have "x' \<notin> G (SG (freegroup A) H) A x'" unfolding G_def X_def by blast
  moreover have "x' \<in> (carrier (SG (freegroup A) H))" using 1 by blast
  ultimately have "x' \<in> X (SG (freegroup A) H) A" unfolding X_def by blast
  then have "x' \<in> (\<langle>X (SG (freegroup A) H) A\<rangle>\<^bsub>(SG (freegroup A) H)\<^esub>)" by (simp add: gen_span.gen_gens)
  then show False using 2 by blast
qed

definition N0
  where
"N0 x = (x \<noteq> [])"

lemma sublist_inverse:
"\<forall>n < (length (x#xs) - 1). ((x#xs)!n) \<noteq> (wordinverse ((x#xs)!(n+1))) \<Longrightarrow> \<forall>n < (length (xs) - 1). ((xs)!n) \<noteq> (wordinverse ((xs)!(n+1)))"
proof-
  assume assm:"\<forall>n < (length (x#xs) - 1). ((x#xs)!n) \<noteq> (wordinverse ((x#xs)!(n+1)))"
  show "\<forall>n < (length (xs) - 1). ((xs)!n) \<noteq> (wordinverse ((xs)!(n+1)))"
    apply(rule allI)
    apply(rule impI)
  proof-
    fix n assume n:"n < length xs - 1"
    have 1:"((x#xs)!(n+1)) = (xs!n)" by auto
    have 2: "((x#xs)!(n+2)) = (xs!(n+1))" by simp 
    have 3:"(n+1) < length (x#xs) - 1" using n by simp
    show "((xs)!n) \<noteq> (wordinverse ((xs)!(n+1)))"
    proof(rule ccontr)
      assume " \<not> xs ! n \<noteq> wordinverse (xs ! (n + 1))"
      then have "xs ! n = wordinverse (xs ! (n + 1))" by blast
      then have "((x#xs)!(n+1)) = wordinverse ((x#xs)!(n+2))" using 1 2 by argo
      then show False using 3 assm by fastforce
    qed
  qed
qed

lemma hd_notempty:
  assumes "B \<subseteq> (red_rep A ` carrier (freegroup A))"
      and "\<forall>x \<in> B. N0 x"
      and "\<forall>x \<in> B. \<forall>y \<in> B. N1 x y"
      and "\<forall>x \<in> B. \<forall>y \<in> B. \<forall>z \<in> B. N2 x y z"
      and "set (x#xs) \<subseteq> B"
      and "\<forall>n < (length (x#xs) - 1). ((x#xs)!n) \<noteq> (wordinverse ((x#xs)!(n+1)))"
    shows "\<exists>a b c. x = a@b \<and> l_concat (x#xs) ~ a@c \<and> reduced (a@c) \<and> a \<noteq> [] \<and> ((xs \<noteq> []) \<longrightarrow> a =  a2 (cancel2 x (hd xs)))"
  using assms
proof(induction "(x#xs)" arbitrary: x xs)
  case (Cons y z)
    have y: "y \<in> B" using Cons.prems(5) by auto
    moreover then obtain Y where "Y \<in> carrier (freegroup A) \<and> y = red_rep A Y" using Cons.prems(1) by blast
    ultimately have ry:"reduced y" using Cons.prems(1) unfolding freegroup_def by (simp add: red_rep_the)
    have y0:"y \<noteq> []" using N0_def y assms(2) by auto
  then show ?case
  proof(cases "z = []")
    case True
    have "l_concat (y # z) = y" using True unfolding l_concat_def by simp
    moreover have "y = y@[]" by simp
    moreover then have "y ~ y" using refl by fast
    ultimately show ?thesis using ry y0 True by metis
  next
    case False
    then obtain z1 z2 where z:"z = (z1#z2)" using list.exhaust by blast
    have z1:"z1 \<in> B" using Cons.prems(5) z by auto
    then have z10:"z1 \<noteq> []" using N0_def assms(2) by auto
    obtain Z1 where "Z1 \<in> carrier (freegroup A) \<and> z1 = red_rep A Z1" using Cons.prems(1) z1 by blast
    then have rz1: "reduced z1" using z1 using Cons.prems(1) unfolding freegroup_def by (simp add: red_rep_the)
    then show ?thesis
    proof(cases "z2 = []")
      case True
      then have 1:"l_concat (y#z) = (y@z1)" using z unfolding l_concat_def by simp
      have N1:"N1 y z1" using Cons.prems(3) y z1 by simp
      have yz1:"y \<noteq> wordinverse z1" using z True Cons.prems(6) by force
      define w where w:"w = cancel2 y z1"
      then have w':"y = a2 w @  p2 w \<and> z1 = (wordinverse (p2 w)) @ b2 w \<and> reduced (a2 w@b2 w)" unfolding cancel2_def using cancel2_the ry rz1 w by fastforce
      moreover then have "(y@z1) ~ (a2 w@b2 w)" using cancel2_reln by blast
      moreover have "a2 w \<noteq> []"
      proof(rule ccontr)
        assume "\<not> a2 w \<noteq> []"
        then have a2w:"a2 w = []" by blast
        have "p2 w = []" using w a2w N1 yz1 unfolding N1_def by simp
        then have "y = []" using w' a2w  by simp
        then show False using y0 by blast
      qed
      moreover have "hd z = z1" using z by simp
      ultimately show ?thesis using 1 w by force
    next
      case False
      then obtain z3 z4 where z2:"z2 = (z3#z4)" using list.exhaust by auto
      then have "set (z1#z3#z4) \<subseteq> B" using z using Cons.prems(5) by auto
      moreover have "\<forall>n < (length (z1#z3#z4) - 1). ((z1#z3#z4)!n) \<noteq> (wordinverse ((z1#z3#z4)!(n+1)))" using z2 z Cons.prems(6) sublist_inverse by blast
      ultimately obtain a b c where  1:"z1 = a @ b \<and>
       l_concat (z1 # z3 # z4) ~ a @ c \<and> reduced (a @ c) \<and> a \<noteq> [] \<and>  ((z3#z4 \<noteq> []) \<longrightarrow> (a = a2 (z1 \<oslash>\<^bsub>2\<^esub> hd (z3#z4))))" using Cons z2 z by blast
      then have a:"a = a2 (z1 \<oslash>\<^bsub>2\<^esub> z3)" using False z2 by fastforce
      have N2:"N2 y z1 z3" using Cons.prems(1,4,5) z z2 by auto
      have 11:"N1 y z1" using Cons.prems(1,3,5) z z2  by fastforce
      have 12:"N1 z1 z3" using Cons.prems(1,3,5) z z2  by fastforce
      obtain Z3 where "Z3 \<in> carrier (freegroup A) \<and> z3 = red_rep A Z3" using Cons.prems(1,5) z z2 by auto
      then have rz3: "reduced z3" using z1 using Cons.prems(1) unfolding freegroup_def by (simp add: red_rep_the)
      define w where w:"w = cancel3 y z1 z3"
      have "(y#z) = (y#z1#z3#z4)"using z z2 by auto
      then have inv:"y \<noteq> wordinverse z1 \<and> z1 \<noteq> wordinverse z3" using Cons.prems(6) Ex_list_of_length by auto
      then have 2:"y = a3 w @ (p3 w) \<and> z1 = wordinverse  (p3 w) @ b3 w @ (q3 w) \<and> z3 = (wordinverse  (q3 w)) @ (c3 w) \<and> reduced (a3 w @ b3 w @ q3 w) \<and> reduced (wordinverse  (p3 w) @ b3 w @ c3 w)" using N2 11 12 ry rz1 rz3 w by (simp add: cancel3_the)
      have apb:"a =  wordinverse (p3 w) @ b3 w" using N2 11 12 ry rz1 rz3 w a cancel_a2_pb3 inv by blast
      have "l_concat (y # z) ~ a3 w @ (b3 w @ c)"
      proof-
        have "l_concat (y # z) = y@ l_concat (z1 # z3 # z4)" unfolding l_concat_def using z z2 by auto
        then have "l_concat (y # z) ~ y@a@c" using 1  mult reln.refl by metis
        moreover have "y@a@c = a3 w @ (p3 w) @ wordinverse (p3 w) @ b3 (w)@c" using 2 apb by simp
        moreover have "(a3 w @ (p3 w) @ wordinverse (p3 w) @ b3 w @ c) ~ (a3 w @ (b3 w @ c))" using cancel2_reln by auto
        ultimately show ?thesis using reln.trans by auto
      qed
      moreover have "reduced (a3 w @ (b3 w @ c))"
      proof-
        have A:"reduced (wordinverse (p3 w) @ b3 w @ c)" using 1 apb by force
        then have "reduced (b3 w @ c)" using reduced_leftappend by blast
        moreover have "reduced (a3 w @ b3 w)" using 2 reduced_rightappend by (metis append.assoc)
        ultimately show ?thesis using N2 N2_def inv reduced_overlap w by blast
      qed
      moreover have "a3 w \<noteq> [] \<and> a3 w = a2 (cancel2 y (hd z))"
      proof-
        have "hd z = z1" using z by force
        then have A:"a3 w = a2 (cancel2 y (hd z))" using w N2 11 12 ry rz1 rz3 inv cancel_a2_a3 by metis
        define v where v:"v = cancel2 y z1"
        then have vv:"y = a2 v @  p2 v \<and> z1 = (wordinverse (p2 v)) @ b2 v \<and> reduced (a2 v@b2 v)" using cancel2_the ry rz1 w by fastforce
        have B: "a3 w \<noteq> []"
        proof(rule ccontr)
          assume "\<not> a3 w \<noteq> []"
          then have "a3 w = []" by simp
          then have "a2 v = []" using v w N2 11 12 ry rz1 rz3 inv cancel_a2_a3 by metis
          moreover then have "p2 v = []" using v 11 inv unfolding N1_def by simp
          ultimately have "y = []" using vv by simp
          then show "False" using y0 by blast
        qed
        then show ?thesis using A B by blast
      qed
      ultimately show ?thesis using 2 by blast
    qed
  qed
qed

lemma n_reduced_cancel:
  assumes "B \<subseteq> (red_rep A ` carrier (freegroup A))"
      and "\<forall>x \<in> B. N0 x"
      and "\<forall>x \<in> B. \<forall>y \<in> B. N1 x y"
      and "\<forall>x \<in> B. \<forall>y \<in> B. \<forall>z \<in> B. N2 x y z"
      and "set l \<subseteq> B"
      and "\<forall>n < (length l - 1). (l!n) \<noteq> (wordinverse (l!(n+1)))"
      and "l \<noteq> []"
    shows "\<not> (l_concat l ~ [])"
proof-
  obtain x xs where l:"l = (x#xs)" using assms(7) list.exhaust by blast
  then obtain a b c where A:"x = a@b \<and> l_concat (x#xs) ~ a@c \<and> reduced (a@c) \<and> a \<noteq> [] \<and> ((xs \<noteq> []) \<longrightarrow> a =  a2 (cancel2 x (hd xs)))" using assms hd_notempty[of "B" "A"] by presburger
  show ?thesis
  proof(rule ccontr)
    assume "\<not> \<not> l_concat l ~ []"
    then have "l_concat l ~ []" by blast
    moreover have "l_concat l ~ (a@c)" using l A by blast
    ultimately have "(a@c) ~ []" using reln.sym reln.trans by blast
    moreover have "reduced (a@c)" using A by blast
    moreover have "reduced []" by simp
    ultimately have "(a@c) = []" using reduced_reln_eq by blast
    moreover have "(a@c) \<noteq> []" using A by blast
    ultimately show False by blast
  qed
qed

definition union_inv
  where
"union_inv S A \<equiv> S \<union> (m_inv (freegroup A) ` S)"

lemma span_subset:
  assumes "A ⊆ B"
  shows "⟨A⟩⇘H⇙ ⊆ ⟨B⟩⇘H⇙"
  using assms gen_span.gen_gens subset_iff subset_span by metis

lemma one_SG:  "𝟭⇘H⇙ = 𝟭⇘SG H K⇙"
  unfolding SG_def by simp

lemma mult_SG: "x ⊗⇘H⇙ y = x ⊗⇘SG H K⇙ y"
  by (simp add: SG_def)

lemma inv_SG: "group H ⟹ y ∈ K ⟹ subgroup K H ⟹ inv⇘H⇙ y = inv⇘SG H K⇙ y"
  unfolding SG_def by (simp add: group.m_inv_consistent)

lemma lex_cont1:
  assumes "(y,x) ∈ lex_L2_word A"
      and "(x ⊗⇘SG F⇘A⇙ H⇙ y, x) ∈ lex_L2_word A"
      and "x ∈ H"
      and "y ∈ H"
      and "H ≤ F⇘A⇙"
    shows "x ∉ X (SG (F⇘A⇙) H) A"
proof-
  have "group F⇘A⇙"  by (simp add: freegroup_is_group)
  then have 1: "group (SG (F⇘A⇙) H)"  unfolding SG_def  by (simp add: subgroup_is_group assms(5))
  have xH:"x ⊗⇘SG F⇘A⇙ H⇙ y ∈ H" by (metis assms(3) assms(4) assms(5) mult_SG subgroup_def)
  then have "{y, x ⊗⇘SG F⇘A⇙ H⇙ y} ⊆ {h ∈ H. (h,x) ∈ (lex_L2_word A)}" using assms(1) assms(2) assms(4) by auto
  moreover have H:"H = carrier (SG F⇘A⇙ H)" unfolding SG_def by simp
  ultimately have 2:"⟨{y, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙ ⊆ G (SG (F⇘A⇙) H) A x" unfolding G_def using span_subset by (metis (no_types, lifting) Collect_cong)
  have "inv ⇘SG F⇘A⇙ H⇙ y ∈ ⟨{y, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙" by (simp add: gen_span.gen_gens gen_span.gen_inv)
  moreover have 3: "x ⊗⇘SG F⇘A⇙ H⇙ y ∈ ⟨{y, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙" by (simp add: gen_span.gen_gens)
  ultimately have "x ⊗⇘SG F⇘A⇙ H⇙ y ⊗⇘SG F⇘A⇙ H⇙ inv ⇘SG F⇘A⇙ H⇙ y ∈ ⟨{y, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙" by (simp add: gen_span.gen_mult)
  then have "x  ⊗⇘SG F⇘A⇙ H⇙ 𝟭⇘SG F⇘A⇙ H⇙ ∈ ⟨{y, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙" using 1 3 xH H  assms(3) assms(4) gen_span.gen_mult gen_span.gen_one by (metis group.inv_solve_right')
  then have "x ∈ ⟨{y, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙" using 1 H assms(3) group.is_monoid by force
  then have "x ∈  G (SG (F⇘A⇙) H) A x" using 2 by auto
  then show ?thesis by (simp add: X_def)
qed

lemma lex_cont1_inv:
  assumes "(y,x) ∈ lex_L2_word A"
      and "(x ⊗⇘SG F⇘A⇙ H⇙ y, x) ∈ lex_L2_word A"
      and "x ∈ H"
      and "y ∈ H"
      and "H ≤ F⇘A⇙"
    shows "inv⇘SG F⇘A⇙ H⇙ x ∉ X (SG (F⇘A⇙) H) A"
proof-
  have "group F⇘A⇙"  by (simp add: freegroup_is_group)
  then have 1: "group (SG (F⇘A⇙) H)"  unfolding SG_def  by (simp add: subgroup_is_group assms(5))
  have y:"(y,inv⇘SG F⇘A⇙ H⇙ x) ∈ lex_L2_word A" using freegroup_is_group assms(1) assms(3) assms(5) inv_SG lex_L2_inv by metis
  have xy: "(x ⊗⇘SG F⇘A⇙ H⇙ y, inv⇘SG F⇘A⇙ H⇙ x) ∈ lex_L2_word A"  using freegroup_is_group assms(2) assms(3) assms(5) inv_SG lex_L2_inv by metis
  have xH:"x ⊗⇘SG F⇘A⇙ H⇙ y ∈ H" by (metis assms(3) assms(4) assms(5) mult_SG subgroup_def)
  then have "{y, x ⊗⇘SG F⇘A⇙ H⇙ y} ⊆ {h ∈ H. (h,inv⇘SG F⇘A⇙ H⇙ x) ∈ (lex_L2_word A)}" using y xy assms(4) by auto
  moreover have H:"H = carrier (SG F⇘A⇙ H)" unfolding SG_def by simp
  ultimately have 2:"⟨{y, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙ ⊆ G (SG (F⇘A⇙) H) A (inv⇘SG F⇘A⇙ H⇙ x)" unfolding G_def using span_subset by (metis (no_types, lifting) Collect_cong)
  have "inv ⇘SG F⇘A⇙ H⇙ y ∈ ⟨{y, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙" by (simp add: gen_span.gen_gens gen_span.gen_inv)
  moreover have 3: "x ⊗⇘SG F⇘A⇙ H⇙ y ∈ ⟨{y, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙" by (simp add: gen_span.gen_gens)
  ultimately have "x ⊗⇘SG F⇘A⇙ H⇙ y ⊗⇘SG F⇘A⇙ H⇙ inv ⇘SG F⇘A⇙ H⇙ y ∈ ⟨{y, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙" by (simp add: gen_span.gen_mult)
  then have "x  ⊗⇘SG F⇘A⇙ H⇙ 𝟭⇘SG F⇘A⇙ H⇙ ∈ ⟨{y, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙" using 1 3 xH H  assms(3) assms(4) gen_span.gen_mult gen_span.gen_one by (metis group.inv_solve_right')
  then have "x ∈ ⟨{y, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙" using 1 H assms(3) group.is_monoid by force
  then have "(inv⇘SG F⇘A⇙ H⇙ x) ∈ ⟨{y, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙"  by (simp add: gen_span.gen_inv)
  then have "(inv⇘SG F⇘A⇙ H⇙ x) ∈  G (SG (F⇘A⇙) H) A (inv⇘SG F⇘A⇙ H⇙ x)" using 2 by blast
  then show ?thesis by (simp add: X_def)
qed

lemma lex_cont2_inv:
  assumes "(x,y) ∈ lex_L2_word A"
      and "(x ⊗⇘SG F⇘A⇙ H⇙ y, y) ∈ lex_L2_word A"
      and "x ∈ H"
      and "y ∈ H"
      and "H ≤ F⇘A⇙"
    shows "inv⇘SG F⇘A⇙ H⇙ y ∉ X (SG (F⇘A⇙) H) A"
proof-
  have "group F⇘A⇙"  by (simp add: freegroup_is_group)
  then have 1: "group (SG (F⇘A⇙) H)"  unfolding SG_def  by (simp add: subgroup_is_group assms(5))
  have x:"(x,inv⇘SG F⇘A⇙ H⇙ y) ∈ lex_L2_word A" using freegroup_is_group assms(1) assms(4) assms(5) inv_SG lex_L2_inv by metis
  have xy: "(x ⊗⇘SG F⇘A⇙ H⇙ y, inv⇘SG F⇘A⇙ H⇙ y) ∈ lex_L2_word A" using freegroup_is_group assms(2) assms(4) assms(5) inv_SG lex_L2_inv by metis
  have xH:"x ⊗⇘SG F⇘A⇙ H⇙ y ∈ H" by (metis assms(3) assms(4) assms(5) mult_SG subgroup_def)
  then have "{x, x ⊗⇘SG F⇘A⇙ H⇙ y} ⊆ {h ∈ H. (h,inv⇘SG F⇘A⇙ H⇙ y) ∈ (lex_L2_word A)}" using x xy assms(3) by auto
  moreover have H:"H = carrier (SG F⇘A⇙ H)" unfolding SG_def by simp
  ultimately have 2:"⟨{x, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙ ⊆ G (SG (F⇘A⇙) H) A (inv⇘SG F⇘A⇙ H⇙ y)" unfolding G_def using span_subset by (metis (no_types, lifting) Collect_cong)
  have "inv ⇘SG F⇘A⇙ H⇙ x ∈ ⟨{x, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙" by (simp add: gen_span.gen_gens gen_span.gen_inv)
  moreover have 3: "x ⊗⇘SG F⇘A⇙ H⇙ y ∈ ⟨{x, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙" by (simp add: gen_span.gen_gens)
  ultimately have "inv ⇘SG F⇘A⇙ H⇙ x ⊗⇘SG F⇘A⇙ H⇙ x ⊗⇘SG F⇘A⇙ H⇙ y  ∈ ⟨{x, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙" using 1 H assms(3) assms(4) gen_span.gen_mult group.inv_closed group.is_monoid monoid.m_assoc by fastforce
  then have "𝟭⇘SG F⇘A⇙ H⇙  ⊗⇘SG F⇘A⇙ H⇙ y ∈ ⟨{x, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙" using 1 3 xH H  assms(3) assms(4) group.l_inv by fastforce
  then have "y ∈ ⟨{x, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙" using 1 H assms(4) group.is_monoid by force
  then have "inv⇘SG F⇘A⇙ H⇙ y ∈ ⟨{x, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙" by (simp add: gen_span.gen_inv)
  then have "inv⇘SG F⇘A⇙ H⇙ y ∈  G (SG (F⇘A⇙) H) A (inv⇘SG F⇘A⇙ H⇙ y)" using 2 by auto
  then show ?thesis by (simp add: X_def)
qed

lemma lex_cont2:
  assumes "(x,y) ∈ lex_L2_word A"
      and "(x ⊗⇘SG F⇘A⇙ H⇙ y, y) ∈ lex_L2_word A"
      and "x ∈ H"
      and "y ∈ H"
      and "H ≤ F⇘A⇙"
    shows "y ∉ X (SG (F⇘A⇙) H) A"
proof-
  have "group F⇘A⇙"  by (simp add: freegroup_is_group)
  then have 1: "group (SG (F⇘A⇙) H)"  unfolding SG_def  by (simp add: subgroup_is_group assms(5))
  have xH:"x ⊗⇘SG F⇘A⇙ H⇙ y ∈ H" by (metis assms(3) assms(4) assms(5) mult_SG subgroup_def)
  then have "{x, x ⊗⇘SG F⇘A⇙ H⇙ y} ⊆ {h ∈ H. (h,y) ∈ (lex_L2_word A)}" using assms(1) assms(2) assms(3) by auto
  moreover have H:"H = carrier (SG F⇘A⇙ H)" unfolding SG_def by simp
  ultimately have 2:"⟨{x, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙ ⊆ G (SG (F⇘A⇙) H) A y" unfolding G_def using span_subset by (metis (no_types, lifting) Collect_cong)
  have "inv ⇘SG F⇘A⇙ H⇙ x ∈ ⟨{x, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙" by (simp add: gen_span.gen_gens gen_span.gen_inv)
  moreover have 3: "x ⊗⇘SG F⇘A⇙ H⇙ y ∈ ⟨{x, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙" by (simp add: gen_span.gen_gens)
  ultimately have "inv ⇘SG F⇘A⇙ H⇙ x ⊗⇘SG F⇘A⇙ H⇙ x ⊗⇘SG F⇘A⇙ H⇙ y  ∈ ⟨{x, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙" using 1 H assms(3) assms(4) gen_span.gen_mult group.inv_closed group.is_monoid monoid.m_assoc by fastforce
  then have "𝟭⇘SG F⇘A⇙ H⇙  ⊗⇘SG F⇘A⇙ H⇙ y ∈ ⟨{x, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙" using 1 3 xH H  assms(3) assms(4) group.l_inv by fastforce
  then have "y ∈ ⟨{x, x ⊗⇘SG F⇘A⇙ H⇙ y}⟩⇘SG F⇘A⇙ H⇙" using 1 H assms(4) group.is_monoid by force
  then have "y ∈  G (SG (F⇘A⇙) H) A y" using 2 by auto
  then show ?thesis by (simp add: X_def)
qed

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

definition N_reduced ("N")
  where
"N_reduced S A = ((\<forall>x \<in> (red_rep A) ` (union_inv S A). N0 x) \<and> 
                  (\<forall>x \<in> (red_rep A) ` (union_inv S A). \<forall>y \<in> (red_rep A) ` (union_inv S A). N1 x y) \<and> 
                  (\<forall>x \<in> (red_rep A) ` (union_inv S A). \<forall>y \<in> (red_rep A) ` (union_inv S A). \<forall>z \<in> (red_rep A) ` (union_inv S A). N2 x y z))"

definition minimal_set
  where
"minimal_set S A = (SOME X. X \<subseteq> S \<and>  X \<inter> (m_inv (freegroup A) ` X) = {} \<and> union_inv S A = union_inv X A)"

lemma "\<exists>X. X \<subseteq> S \<and> X \<inter> (m_inv (freegroup A) ` X) = {} \<and> union_inv S A = union_inv X A"
  sorry

lemma "(\<forall>x \<in> (red_rep A) ` (union_inv (X H A) A). N0 x)"
  sorry

lemma "(\<forall>x \<in> (red_rep A) ` (union_inv S A). \<forall>y \<in> (red_rep A) ` (union_inv S A). N1 x y)"
  sorry

definition (in group) free :: "('a, 'b) monoid_scheme \<Rightarrow> bool"
  where "free H \<equiv> (\<exists>X. H \<cong> (freegroup X))"

lemma LS: assumes "subgroup S H" "S \<inter> (m_inv H ` S) = {}"
  shows "(free (SG H \<langle>S\<rangle>\<^bsub>H\<^esub>)) \<longleftrightarrow> set l \<subseteq> S \<union> (m_inv H ` S) \<Longrightarrow> l \<noteq> [] \<Longrightarrow> (\<forall>n < (length l - 1). (l!n) \<otimes>\<^bsub>H\<^esub> (l!(n+1)) \<noteq> \<one>\<^bsub>H\<^esub>) \<Longrightarrow>  m_concat H l \<noteq> \<one>\<^bsub>H\<^esub>" 
  sorry

lemma 
  assumes "x \<in> carrier (freegroup S)"
  shows "inv\<^bsub>(freegroup S)\<^esub> x = x \<Longrightarrow> x = \<one>\<^bsub>(freegroup S)\<^esub>"
  sorry

end
