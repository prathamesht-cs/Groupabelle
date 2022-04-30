theory NielsonSchreier
imports "UniversalProperty" "HOL.Nat"
begin

lemma equiv_redelem:
  assumes "w \<in> (\<langle>S\<rangle> // (reln_set \<langle>S\<rangle>))"
  shows "\<exists>x \<in> w. reduced x \<and> ((reln_set \<langle>S\<rangle>)`` {x} = w)"
proof-
  obtain c where c: "w = (reln_set \<langle>S\<rangle>) `` {c}" by (meson assms quotientE)
  then have cs: "c \<in> \<langle>S\<rangle>" using assms by (metis proj_def proj_in_iff reln_equiv)
  obtain rc where rc: "rc = (iter (length c) reduct c)" by simp
  then have "reduced rc" by (simp add: reduced_iter_length)
  then have "c ~ rc" using rc cancels_imp_rel iter_cancels_to by auto
  moreover then have "rc \<in> \<langle>S\<rangle>" using cs rc using cancels_to_preserves iter_cancels_to by blast
  ultimately have crc: "(c, rc) \<in> reln_set \<langle>S\<rangle>" using cs reln_set_def by auto
  then have "((reln_set \<langle>S\<rangle>)`` {rc} = w)"using c by (smt (verit, ccfv_SIG) equiv_class_eq_iff reln_equiv)
  moreover then have "rc \<in> w" using c crc by simp
  ultimately show ?thesis using \<open>reduced rc\<close> by auto
qed

lemma redelem_unique :
  assumes "w \<in> (\<langle>S\<rangle> // (reln_set \<langle>S\<rangle>))"
  shows "\<exists>!x \<in> w. reduced x \<and> ((reln_set \<langle>S\<rangle>)`` {x} = w)"
proof(rule classical)
  assume 1:"\<not>(\<exists>!x \<in> w. reduced x \<and> ((reln_set \<langle>S\<rangle>)`` {x} = w))"
  have "\<exists>x \<in> w. reduced x \<and> ((reln_set \<langle>S\<rangle>)`` {x} = w)" using assms equiv_redelem by auto
  then obtain x where x:"x \<in> w \<and> reduced x" by auto
  obtain y where y:"(y \<in> w \<and> reduced y \<and> (reln_set \<langle>S\<rangle>)`` {x} = w) \<and> y \<noteq> x " using 1 x by (smt (verit, best) assms equiv_class_eq_iff equiv_class_self quotientE quotient_eq_iff reln_equiv)
  then have "(x, y) \<in> reln_set \<langle>S\<rangle>" using x y by blast
  then have "x ~ y" using reln_set_def by auto
  then have "y = x" using x y 1 reduced_cancel_eq reln_imp_cancels by blast
  moreover then have "(reln_set \<langle>S\<rangle>)`` {x} = (reln_set \<langle>S\<rangle>)`` {y}" by simp
  ultimately have False by (simp add: y)
  then show "\<exists>!x \<in> w. reduced x \<and> ((reln_set \<langle>S\<rangle>)`` {x} = w)" by simp 
qed

definition equiv_red :: "('a, 'b) monoidgentype set \<Rightarrow> ('a, 'b) word set \<Rightarrow> ('a, 'b) word"
  where "equiv_red S w = (THE x. x \<in> w \<and> reduced x \<and> (w = reln_set \<langle>S\<rangle> `` {x}))"

lemma equiv_red_the:
  assumes "w \<in> (\<langle>S\<rangle> // (reln_set \<langle>S\<rangle>))"
  shows "((equiv_red S w) \<in> w)  \<and> reduced ((equiv_red S w)) \<and> (w = reln_set \<langle>S\<rangle> `` {(equiv_red S w)})"
  unfolding equiv_red_def
proof(rule theI')
  show "\<exists>!x. x \<in> w \<and> reduced x \<and> w = reln_set \<langle>S\<rangle> `` {x}" using redelem_unique[of "w" "S"] assms by metis 
qed

lemma equivred_equiv:
  assumes "w \<in> (\<langle>S\<rangle> // (reln_set \<langle>S\<rangle>))"
  shows "\<forall>x\<in>w. (reln_set \<langle>S\<rangle>) `` {x} = (reln_set \<langle>S\<rangle>) `` {equiv_red S w}"
proof-
  obtain x where x:"x \<in> w" using assms equiv_redelem by auto
  then have xs: "x \<in> \<langle>S\<rangle>" using append_congruent assms equiv_2f_clos reln_equiv rightappend_span spanset_def by fastforce
  have rw: "equiv_red S w \<in> w" using x equiv_red_def redelem_unique equiv_red_the assms by blast
  then have rs: "equiv_red S w \<in> \<langle>S\<rangle>" using assms by (meson quotient_eq_iff refl_onD1 reln_equiv reln_refl)
  then have "(x,equiv_red S w)\<in>(reln_set \<langle>S\<rangle>)" using xs x rs rw by (meson assms quotient_eq_iff reln_equiv)
  then have "(reln_set \<langle>S\<rangle>) `` {x} = (reln_set \<langle>S\<rangle>) `` {equiv_red S w}" by (meson equiv_class_eq_iff reln_equiv)
  then show ?thesis using x assms by (smt (verit, best)  equiv_class_eq_iff quotient_eq_iff reln_equiv)
qed

definition equivinv :: "('a, 'b) monoidgentype set \<Rightarrow> ('a, 'b) word set \<Rightarrow> ('a, 'b) word set"
  where "equivinv S w = (reln_set \<langle>S\<rangle> `` {wordinverse (equiv_red S w)})"

definition equal_equiv where "equal_equiv S x y = (equiv_red S x = equiv_red S y)"

definition inv_equiv where "inv_equiv S x y = (x = equivinv S y)"

fun nielson_reln :: "('a, 'b) monoidgentype set \<Rightarrow> ('a, 'b) word set \<Rightarrow> ('a, 'b) word set \<Rightarrow> bool"
  where
"nielson_reln S x y = (equal_equiv S x y \<or> inv_equiv S x y)"

definition nielson_set :: "('a, 'b) monoidgentype set \<Rightarrow>(('a,'b) word  \<times> ('a,'b) word) set"
  where
"nielson_set S = {(w,z). \<exists>x y . x \<in> (\<langle>S\<rangle> // (reln_set \<langle>S\<rangle>)) \<and> w = equiv_red S x \<and> y \<in> (\<langle>S\<rangle> // (reln_set \<langle>S\<rangle>)) \<and> z = equiv_red S y \<and> nielson_reln S x y}"

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
    have "x \<in> \<langle>A\<rangle>" using Cons.prems span_cons spanset_def by blast
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
      moreover have "(tl x) \<in> \<langle>S\<rangle>" using False "1.prems"(3) span_cons spanset_def by (metis list.exhaust_sel)
      moreover have "(tl y) \<in> \<langle>S\<rangle>" using y "1.prems"(4) span_cons spanset_def by (metis list.exhaust_sel)
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
        have "hd x \<in> (invgen S)" using  "1.prems"(3) by (metis "1.prems"(1) F2 append_eq_append_conv append_self_conv2 gen_spanset spanset_def)
        moreover have "hd y \<in> (invgen S)" using  "1.prems"(4) by (metis "1.prems"(1) F2 append_eq_append_conv append_self_conv gen_spanset spanset_def)
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
    moreover have "tl a \<in> \<langle>S\<rangle>" using "1.prems" span_cons spanset_def False  by (metis list.collapse)
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
  moreover have  "b \<in> \<langle>S\<rangle>" using assms(3) spanset_def using calculation rightappend_span by blast
  moreover have  "c \<in> \<langle>S\<rangle>" using assms(4) spanset_def using calculation rightappend_span by blast
  moreover have "compare r b c" by (simp add: calculation(1))
  moreover have "compare r x y = compare r b c" using compare_subword by (metis add_left_imp_eq assms(1) assms(2) assms(4) calculation(1) calculation(2) calculation(3) leftappend_span length_append spanset_def)
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
        then have tlx:"tl x \<in> \<langle>A\<rangle>" using a spanset_def span_cons by (metis list.collapse)
        have "y \<in> \<langle>A\<rangle>" using "1.prems"(2) unfolding compare_set_def by simp
        then have tly:"tl y \<in> \<langle>A\<rangle>" using b spanset_def span_cons by (metis list.collapse)
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
        then have B:"hd x \<in> (invgen A)" by (metis "1.prems"(1) False append.left_neutral append_eq_append_conv gen_spanset spanset_def)
        have "y \<in> \<langle>A\<rangle>" using "1.prems"(2) unfolding compare_set_def by simp
        then have C:"hd y \<in> (invgen A)" by (metis "1.prems"(1) False append_eq_append_conv append_self_conv2 gen_spanset spanset_def)
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
      moreover have "c \<in> \<langle>A\<rangle>" using y 1 rightappend_span unfolding spanset_def by auto
      ultimately have c:"hd c \<in> (invgen A)"  by (simp add: gen_spanset spanset_def)
      have "b \<in> \<langle>A\<rangle>" using x 1 rightappend_span unfolding spanset_def by auto
      then have "hd b \<in> (invgen A)" using False by (simp add: gen_spanset spanset_def)
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
          ultimately have "b \<in> \<langle>A\<rangle> \<and> e \<in> \<langle>A\<rangle> \<and> f \<in> \<langle>A\<rangle>" using A rightappend_span spanset_def by blast
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

definition lex_set where "lex_set A r = {(x, y). x \<in> A \<and> y \<in> A \<and> lex r x y}"

lemma lex_refl_on:
  assumes "well_order_on (invgen A) r"
  shows "refl_on \<langle>A\<rangle> (lex_set \<langle>A\<rangle> r)"
proof-
  have "\<forall>(x,y) \<in> (lex_set \<langle>A\<rangle> r). x \<in> \<langle>A\<rangle> \<and> y \<in> \<langle>A\<rangle>" using lex_set_def using case_prod_conv by blast
  then have 1:"(lex_set \<langle>A\<rangle> r) \<subseteq> \<langle>A\<rangle> \<times>\<langle>A\<rangle>" by auto
  have "\<forall>x\<in>\<langle>A\<rangle>. lex r x x" by (metis assms lex.elims(3) refl_compare)
  then have 2:"(\<forall>x\<in>\<langle>A\<rangle>. (x, x) \<in> (lex_set \<langle>A\<rangle> r))" using lex_set_def by blast
  then have "refl_on \<langle>A\<rangle> (lex_set \<langle>A\<rangle> r)" by (simp add: "1" refl_onI)
  then show ?thesis by auto
qed


lemma antisymm_lex :
  assumes "well_order_on (invgen A) r"
  shows "(\<forall>x y.  (x, y) \<in> lex_set \<langle>A\<rangle> r \<longrightarrow> (y, x) \<in> lex_set \<langle>A\<rangle> r \<longrightarrow> x = y)"
  apply (rule allI)+
  apply (rule impI)+
proof-
  fix x y
  assume xy: "(x, y) \<in> lex_set \<langle>A\<rangle> r" and yx: "(y, x) \<in> lex_set \<langle>A\<rangle> r"
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
      then have "\<not>(lex r x y)" using lex_def by (metis glxy leD lex.elims(2) order_le_imp_less_or_eq)
      then show ?thesis using lexy by simp
    qed
  qed
qed

lemma lex_antisym:
  assumes "well_order_on (invgen A) r"
  shows "antisym (lex_set \<langle>A\<rangle> r)"
  using antisymm_lex by (metis antisymI assms)
 
lemma lex_trans:
  assumes "well_order_on (invgen A) r"
  shows "trans (lex_set \<langle>A\<rangle> r)"
  unfolding trans_def
  apply(rule allI)+
  apply(rule impI)+
proof-
  fix x y z assume xy:"(x, y) \<in> (lex_set \<langle>A\<rangle> r)" and yz: "(y, z) \<in> (lex_set \<langle>A\<rangle> r)"
  then show "(x, z) \<in> lex_set \<langle>A\<rangle> r"
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
  shows "total_on \<langle>A\<rangle> (lex_set \<langle>A\<rangle> r)"
  unfolding total_on_def
  apply(rule ballI)+
  apply(rule impI)
proof-
  fix x y assume x: "x \<in> \<langle>A\<rangle>" and y: "y \<in> \<langle>A\<rangle>" and xy: "x \<noteq> y"
  then show "(x, y) \<in> lex_set \<langle>A\<rangle> r \<or> (y, x) \<in> lex_set \<langle>A\<rangle> r"
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
"lex_lift S r a b = (lex r (equiv_red S a) (equiv_red S b))"

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
  have 1:"hd ` S \<subseteq> (invgen A)" using assms(2) assms(4) unfolding spanset_def by (simp add: hd_sub_span)
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
  moreover have xA: "x \<in> \<langle>A\<rangle>" using assms(2) assms(7) span_append spanset_def x1 by blast
  moreover have yA: "y \<in> \<langle>A\<rangle>"  using ya assms(2) assms(4) assms(7) least_consappend_in span_append spanset_def y1 by blast
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
  then show "x \<in> \<langle>A\<rangle>" using assms(2) span_cons by (metis (no_types, lifting) x append_Cons append_Nil2 append_eq_append_conv2 assms(3) in_mono least_consappend_in same_append_eq spanset_def)
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
  moreover have "hd ` S \<subseteq> invgen A" by (metis assms(2) assms(3) hd_sub_span spanset_def)
  ultimately show ?thesis unfolding spanset_def using group_spanset.empty group_spanset.gen subsetD by blast
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
    then have yA: "?ys \<in> \<langle>A\<rangle>" using Suc.prems(7) leastcons_comp.simps spanset_def span_append by fastforce
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
    moreover have "[] \<in> \<langle>A\<rangle>" unfolding spanset_def using empty by auto
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
  moreover have "[] \<in> \<langle>A\<rangle>" unfolding spanset_def using empty by auto
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
shows "\<forall>x \<in> S.((least_comp r n S), x) \<in> lex_set \<langle>A\<rangle> r"
proof
  fix x assume x: "x \<in> S"
  then have "((least_comp r n S), x) \<in> compare_set A r" using least_comp_least assms by blast
  then have 1:"(least_comp r n S) \<in> \<langle>A\<rangle> \<and> x \<in> \<langle>A\<rangle> \<and> compare r (least_comp r n S) x" unfolding compare_set_def by fastforce
  have S:"(least_comp r n S) \<in> S" unfolding least_comp_def using assms least_comp_in least_comp_def by metis  
  have "length (least_comp r n S) \<le> length x" using S assms(3) x by force
  then have "lex r (least_comp r n S) x" using lex.simps 1 x S assms(3) by force
  then show "((least_comp r n S), x) \<in> lex_set \<langle>A\<rangle> r" unfolding lex_set_def using 1 by blast
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
  then have "\<forall>y \<in> least_length S. length y < length x" using l by (meson nless_le)
  then show ?thesis using lex.simps by fastforce
qed

(*1. nat least is unique
  2. x : S and x \<notin> least_length S \<Rightarrow> x > y. \<forall>y : least_length S (*least_hd_the*)
  3. least_length S \<subseteq> S*)
(*least (nat_eq_less) (length ` S) \<le> (length ` S)*)

lemma preorder_words :
  assumes "well_order_on (invgen A) r"
  shows "preorder_on \<langle>A\<rangle> (lex_set \<langle>A\<rangle> r)"
  unfolding preorder_on_def using lex_refl_on lex_trans assms by blast

lemma partial_order_words :
  assumes "well_order_on (invgen A) r"
  shows "partial_order_on \<langle>A\<rangle> (lex_set \<langle>A\<rangle> r)"
  unfolding partial_order_on_def using lex_antisym preorder_words assms by blast

lemma linear_order_words :
  assumes "well_order_on (invgen A) r"
  shows "linear_order_on \<langle>A\<rangle> (lex_set \<langle>A\<rangle> r)"
  unfolding linear_order_on_def using partial_order_words lex_total_on assms by fast

definition tuple_set
  where
"tuple_set r Q = {x \<in> Q. (\<exists>y\<in>Q. ((x, y) \<in> r \<or> (y, x) \<in> r))}"

lemma tuple_set_subset :
"tuple_set r Q \<subseteq> Q" 
  unfolding tuple_set_def by simp 

lemma tuple_set_reln :
"tuple_set (lex_set \<langle>A\<rangle> r) Q \<subseteq> \<langle>A\<rangle>"
  unfolding tuple_set_def lex_set_def by fastforce

lemma tuple_set_not:
"\<forall>x \<in> Q. \<forall> y \<in> Q.  x \<notin> tuple_set (lex_set \<langle>A\<rangle> r) Q \<longrightarrow> (x, y) \<notin> (lex_set \<langle>A\<rangle> r) \<and> (y, x) \<notin> (lex_set \<langle>A\<rangle> r)"
  apply(rule ballI)+
  apply(rule impI)
proof(rule ccontr)
  fix x y assume x: "x \<in> Q" and y:"y \<in> Q" and nx: "x \<notin> tuple_set (lex_set \<langle>A\<rangle> r) Q"
    and "\<not> ((x, y) \<notin> lex_set \<langle>A\<rangle> r \<and> (y, x) \<notin> lex_set \<langle>A\<rangle> r)"
  then have c:"(x, y) \<in> lex_set \<langle>A\<rangle> r \<or> (y, x) \<in> lex_set \<langle>A\<rangle> r" by blast
  then show False
  proof(cases "(x, y) \<in> lex_set \<langle>A\<rangle> r")
    case True
    then have "x \<in> tuple_set (lex_set \<langle>A\<rangle> r) Q" using x y unfolding tuple_set_def by blast
    then show ?thesis using nx by blast
  next
    case False
    then have "(y, x) \<in> lex_set \<langle>A\<rangle> r" using c by simp
    then have "x \<in> tuple_set (lex_set \<langle>A\<rangle> r) Q" using x y unfolding tuple_set_def by blast
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
   shows "\<forall>x \<in> S. ((least_comp r ((least (nat_leq_less) (length ` S))) (least_length S)),x) \<in> lex_set \<langle>A\<rangle> r"
proof
  fix x assume x: "x \<in> S" 
  then show "((least_comp r ((least (nat_leq_less) (length ` S))) (least_length S)),x) \<in> lex_set \<langle>A\<rangle> r" 
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
    then have "(least (nat_leq_less) (length ` S)) \<in> (length ` S)" using least_def nat_unique_least by (smt (verit, del_insts) assms image_is_empty theI)
    then have S:"least_length S \<noteq> {}" unfolding least_length_def  using assms empty_iff image_iff mem_Collect_eq by force
    then obtain a where a:"a \<in> least_length S" by blast
    then have "(lex r a x)" using False assms least_length_lesser[of "A" "r" "S" "x"]  x by blast
    then have ax:"(a,x) \<in> lex_set \<langle>A\<rangle> r" unfolding lex_set_def using x assms(2) a LS by blast
    then have "(least (nat_leq_less) (length ` S)) \<in> (length ` S)" using 1 least_def nat_unique_least by (smt (verit, del_insts) assms image_is_empty theI)   
    then have 2:"(least (nat_leq_less) (length ` S)) > 0" using assms(4) by fastforce
    then have 3:"\<forall>x \<in>(least_length S). length x  = (least (nat_leq_less) (length ` S))" using  least_length_the least_length_def leastn_comp_less mem_Collect_eq by blast
    moreover have "(least_length S) \<subseteq> \<langle>A\<rangle>" using assms(2) least_length_subset by blast
    ultimately have "((least_comp r ((least (nat_leq_less) (length ` S))) (least_length S)), a) \<in> lex_set \<langle>A\<rangle> r" using assms S 1 2 least_comp_least_lex[of "A" "r" "least_length S" "(least (nat_leq_less) (length ` S))"] a  by fastforce
    then show ?thesis using ax assms(1) lex_trans unfolding trans_def by fast
  qed
qed

lemma minimalelem_words:
  assumes "well_order_on (invgen A) r"
  shows"\<And>x Q. x \<in> Q \<Longrightarrow> \<exists>z\<in>Q. \<forall>y. (y, z) \<in> (lex_set \<langle>A\<rangle> r - Id) \<longrightarrow> y \<notin> Q"
proof-
  fix x Q assume x: "x \<in> (Q :: (('a \<times> 'b) \<times> bool) list set)"
  then show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> (lex_set \<langle>A\<rangle> r - Id) \<longrightarrow> y \<notin> Q"
  proof(cases "[] \<in> Q")
    case True
    then have "\<nexists>z. (z, []) \<in> (lex_set \<langle>A\<rangle> r - Id)" unfolding lex_set_def using lex.simps[of "r" "z" "[]"] by auto   
    then show ?thesis using True by blast
  next
    case False
    then have nQ:"[] \<notin> Q" by simp
    then show ?thesis
    proof(cases "tuple_set (lex_set \<langle>A\<rangle> r) Q = {}")
      case True
      have "\<forall>y. (y, x) \<in> (lex_set \<langle>A\<rangle> r - Id) \<longrightarrow> y \<notin> Q"
        apply(rule allI) apply(rule impI)
      proof-
        fix y assume y:"(y, x) \<in> (lex_set \<langle>A\<rangle> r - Id)" 
        show "y \<notin> Q"
      proof(rule ccontr)
        assume "\<not> y \<notin> Q"
        then have cont :"y \<in> Q" by blast
        then have 1:"y \<in> tuple_set (lex_set \<langle>A\<rangle> r) Q" using x tuple_set_def lex_set_def using DiffD1 tuple_set_not y by fastforce
        then show False using True by blast
      qed
    qed
    then show ?thesis using x by blast
    next
      case False
      moreover have 1:"tuple_set (lex_set \<langle>A\<rangle> r) Q \<subseteq> \<langle>A\<rangle>" using tuple_set_reln by fast
      moreover have nN: "[] \<notin> tuple_set (lex_set \<langle>A\<rangle> r) Q" using nQ tuple_set_subset[of "(lex_set \<langle>A\<rangle> r)" "Q"] by blast
      ultimately have lst:"\<forall>x \<in> tuple_set (lex_set \<langle>A\<rangle> r) Q. ((least_comp r ((least (nat_leq_less) (length ` tuple_set (lex_set \<langle>A\<rangle> r) Q))) (least_length (tuple_set (lex_set \<langle>A\<rangle> r) Q))),x) \<in> lex_set \<langle>A\<rangle> r" using assms least_lex[of "A" "r" "(tuple_set (lex_set \<langle>A\<rangle> r) Q)"] by blast
      let ?z = "(least_comp r ((least (nat_leq_less) (length ` tuple_set (lex_set \<langle>A\<rangle> r) Q))) (least_length (tuple_set (lex_set \<langle>A\<rangle> r) Q)))"
      have "(length ` tuple_set (lex_set \<langle>A\<rangle> r) Q) \<noteq> {}" using False by auto
      then have lste:"(least (nat_leq_less) (length ` tuple_set (lex_set \<langle>A\<rangle> r) Q)) \<in> (length ` tuple_set (lex_set \<langle>A\<rangle> r) Q)" using least_length_the[of "tuple_set (lex_set \<langle>A\<rangle> r) Q"] by blast  
      then have 2:"(least (nat_leq_less) (length ` (tuple_set (lex_set \<langle>A\<rangle> r) Q))) > 0" using nN by fastforce
      then have 3:"\<forall>x \<in>(least_length (tuple_set (lex_set \<langle>A\<rangle> r) Q)). length x  = (least (nat_leq_less) (length ` (tuple_set (lex_set \<langle>A\<rangle> r) Q)))" using  least_length_the least_length_def leastn_comp_less mem_Collect_eq by blast
      have "least_length (tuple_set (lex_set \<langle>A\<rangle> r) Q) \<subseteq> \<langle>A\<rangle>" using 1 least_length_subset by fastforce
      moreover have "least_length (tuple_set (lex_set \<langle>A\<rangle> r) Q) \<noteq> {}" using False lste  unfolding least_length_def  by fastforce
      ultimately have "?z \<in> (least_length (tuple_set (lex_set \<langle>A\<rangle> r) Q))" using least_comp_in[of "A" "r" "(least_length (tuple_set (lex_set \<langle>A\<rangle> r) Q))" "((least (nat_leq_less) (length ` tuple_set (lex_set \<langle>A\<rangle> r) Q)))"] assms 2 3  by blast
      then have zQ:"?z \<in> Q" using least_length_subset[of "(tuple_set (lex_set \<langle>A\<rangle> r) Q)"] tuple_set_subset[of "(lex_set \<langle>A\<rangle> r)" "Q"] by fast
      have "\<forall>y. (y, ?z) \<in> (lex_set \<langle>A\<rangle> r - Id) \<longrightarrow> y \<notin> Q"
        apply(rule allI) apply(rule impI)
      proof-
        fix y assume y:"(y, ?z) \<in> lex_set \<langle>A\<rangle> r - Id"
        show "y \<notin> Q"
        proof(rule ccontr)
          assume "\<not> y \<notin> Q"
          then have cy:"y \<in> Q" by blast
          show False
          proof(cases "y \<in> tuple_set (lex_set \<langle>A\<rangle> r) Q")
            case True
            then have yt:"y \<in> tuple_set (lex_set \<langle>A\<rangle> r) Q" by simp
            then show ?thesis
            proof(cases "y = ?z")
              case True
              then show ?thesis using y by simp
            next
              case False
              then have "(?z, y) \<in> lex_set \<langle>A\<rangle> r" using lst yt by simp
              moreover have "(y, ?z) \<in> lex_set \<langle>A\<rangle> r" using y by blast
              ultimately show ?thesis using lex_antisym assms False unfolding antisym_def by blast
            qed
          next
            case False
            then have "((x, ?z) \<notin> lex_set \<langle>A\<rangle> r \<and> (y, ?z) \<notin> lex_set \<langle>A\<rangle> r)" using tuple_set_not[of "Q" "A" "r"] cy zQ y by blast
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
1.1:tuple_set (lex_set \<langle>A\<rangle> r) Q = {}, then x is the z (proof by contradiction: if (y,x) and y \<in> Q then x \<in> tuple_set (lex_set \<langle>A\<rangle> r) Q)"
Not 1.1: use least_lex and Id, contradiction
*)
 
lemma wf_words :
  assumes "well_order_on (invgen A) r"
  shows "wf (lex_set \<langle>A\<rangle> r - Id)"
  using minimalelem_words assms wf_eq_minimal by fastforce

lemma well_order_words :
  assumes "well_order_on (invgen A) r"
  shows "well_order_on \<langle>A\<rangle> (lex_set \<langle>A\<rangle> r)"
  unfolding well_order_on_def using linear_order_words wf_words assms by blast

definition left_subword :: "('a, 'b) word \<Rightarrow> ('a, 'b) word" ("L")
  where
"left_subword xs = take (((length xs+1) div 2)) xs"

value "((((6::nat)) div 2))"

lemma left_subword_word: "xs = (left_subword xs) @ (drop (((length xs+1) div 2)) xs)"
  unfolding left_subword_def
  by auto

definition left_lex_set where "left_lex_set A r = {(x,y). x \<in> L ` A \<and> y \<in> L ` A \<and>  lex r x y}"

definition invleft_lex_set where "invleft_lex_set A r = {(x, y). x \<in> L` (wordinverse ` A) \<and> y \<in> L` (wordinverse ` A) \<and> lex r x y}"

definition L_lex where "L_lex A r = ((left_lex_set A r) - Id) <*lex*> ((invleft_lex_set A r) - Id)"

definition left_tuple ("L2")
  where "left_tuple x = (L x, L (wordinverse x))"

definition L_lex_set where "L_lex_set A r = {(x,y). x \<in> A \<and> y \<in> A \<and> (L2 x, L2 y) \<in> L_lex A r}"

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
      then have "x \<in> \<langle>A\<rangle>" using empty unfolding spanset_def by auto
      moreover have "L x = x" using True unfolding left_subword_def by fastforce
      ultimately show ?thesis by force
    next
      case False
      then have "tl x \<in>  \<langle>A\<rangle>" using spanset_def x by (metis hd_Cons_tl span_cons)
      then have A:"x @ (tl x) \<in> \<langle>A\<rangle>" using span_append x unfolding spanset_def by blast
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
    then show "x\<in> \<langle>A\<rangle>" using leftappend_span a unfolding spanset_def by metis
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
  shows "wf (L_lex \<langle>A\<rangle> r)"
proof-
  have "left_lex_set \<langle>A\<rangle> r = lex_set \<langle>A\<rangle> r" unfolding left_lex_set_def lex_set_def using left_span[of "A"]  by fastforce
  then have 1:"wf (left_lex_set \<langle>A\<rangle> r - Id)" using wf_words assms(1) by auto
  have "invleft_lex_set \<langle>A\<rangle> r  = lex_set \<langle>A\<rangle> r" unfolding invleft_lex_set_def lex_set_def using left_span[of "A"] inv_span[of "A"] by fastforce
  then have "wf (invleft_lex_set \<langle>A\<rangle> r - Id)" using wf_words assms(1) by auto
  then show ?thesis unfolding L_lex_def using 1 by (simp add: wf_lex_prod)
qed

lemma wf_L_lex_set:
  assumes "well_order_on (invgen A) r"
  shows "wf (L_lex_set \<langle>A\<rangle> r)"
proof(rule wfI_min)
  fix x Q assume x: "x \<in> (Q :: (('a \<times> 'b) \<times> bool) list set)"
  show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> L_lex_set \<langle>A\<rangle> r \<longrightarrow> y \<notin> Q"
  proof(cases "tuple_set (L_lex \<langle>A\<rangle> r) (L2 ` Q) = {}")
    case True
    have "\<forall>y. (y, x) \<in> L_lex_set \<langle>A\<rangle> r \<longrightarrow> y \<notin> Q" 
      apply (rule allI) apply (rule impI)
    proof-
      fix y assume y: "(y, x) \<in> L_lex_set \<langle>A\<rangle> r"
      then have "(L2 y, L2 x) \<in> L_lex \<langle>A\<rangle> r" unfolding L_lex_set_def by fastforce
      then show "y \<notin> Q" using True x unfolding tuple_set_def by blast
    qed
    then show ?thesis using x by blast
  next
    case False
    then obtain x where "x \<in> tuple_set (L_lex \<langle>A\<rangle> r) (L2 ` Q)" by auto
    then obtain z where z: "z \<in> tuple_set (L_lex \<langle>A\<rangle> r) (L2 ` Q) \<and> (\<forall>y. (y, z) \<in> (L_lex \<langle>A\<rangle> r) \<longrightarrow> y \<notin> tuple_set (L_lex \<langle>A\<rangle> r) (L2 ` Q))" using wfE_min wf_L_lex by (metis assms)
    then have z1: "z \<in> (L2 ` Q)" using tuple_set_subset[of "(L_lex \<langle>A\<rangle> r)" "(L2 ` Q)"] by auto
    then obtain w where w: "w \<in> Q \<and> L2 w = z" by auto
    moreover have "\<forall>y. (y, w) \<in> L_lex_set \<langle>A\<rangle> r \<longrightarrow> y \<notin> Q" 
      apply(rule allI) apply (rule impI)
    proof-
      fix y assume a: "(y, w) \<in> L_lex_set \<langle>A\<rangle> r"
      then have contr: "(L2 y, L2 w) \<in> L_lex \<langle>A\<rangle> r" unfolding L_lex_set_def by auto
      show "y \<notin> Q"
      proof(rule ccontr)
        assume "\<not> y \<notin> Q"
        then have y:"y \<in> Q" by blast
        then show False
        proof(cases "L2 y \<notin> tuple_set (L_lex \<langle>A\<rangle> r) (L2 ` Q)")
        case True
        have "(L2 y, L2 w) \<notin> L_lex \<langle>A\<rangle> r"
          proof(rule ccontr)
            assume assm: "\<not> (L2 y, L2 w) \<notin> L_lex \<langle>A\<rangle> r"
            then have "(L2 y, L2 w) \<in> L_lex \<langle>A\<rangle> r" by blast
            then have "L2 y \<in> tuple_set (L_lex \<langle>A\<rangle> r) (L2 ` Q)" unfolding tuple_set_def using w y by auto
            then show False using True by blast
          qed
        then show ?thesis using contr by blast
      next
        case False
        have "L2 y \<notin> tuple_set (L_lex \<langle>A\<rangle> r) (L2 ` Q)" using z contr w by blast
        then show ?thesis using False by blast
      qed
    qed
  qed
  ultimately show ?thesis by blast
qed
qed

(*
Sorry proposition 1.9

*)

