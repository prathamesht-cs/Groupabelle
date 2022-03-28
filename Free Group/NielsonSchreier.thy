theory NielsonSchreier
imports "UniversalProperty"
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
  then have "y = x" using x y using 1 reduced_cancel_eq reln_imp_cancels by blast
  moreover then have "(reln_set \<langle>S\<rangle>)`` {x} = (reln_set \<langle>S\<rangle>)`` {y}" by simp
  ultimately have False by (simp add: y)
  then show "\<exists>!x \<in> w. reduced x \<and> ((reln_set \<langle>S\<rangle>)`` {x} = w)" by simp 
qed

definition equiv_red :: "('a, 'b) monoidgentype set \<Rightarrow> ('a, 'b) word set \<Rightarrow> ('a, 'b) word"
  where "equiv_red S w = (THE x. x \<in> w \<and> reduced x \<and> (w = reln_set \<langle>S\<rangle> `` {x}))"

lemma equivred_equiv:
  assumes "w \<in> (\<langle>S\<rangle> // (reln_set \<langle>S\<rangle>))"
  shows "\<forall>x\<in>w. (reln_set \<langle>S\<rangle>) `` {x} = (reln_set \<langle>S\<rangle>) `` {equiv_red S w}"
proof-
  obtain x where x:"x \<in> w" using assms equiv_redelem by auto
  then have xs: "x \<in> \<langle>S\<rangle>" using append_congruent assms equiv_2f_clos reln_equiv rightappend_span spanset_def by fastforce
  have rw: "equiv_red S w \<in> w" using equiv_red_def redelem_unique by (metis (no_types, lifting) Uniq_I assms the1_equality')
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
  assumes "well_order_on (invgen A) r"
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
  then have "partial_order_on (invgen A) r" by (simp add: linear_order_on_def)
  then have "preorder_on (invgen A) r" by (simp add: partial_order_on_def)
  then have 1:"trans r" by (simp add: preorder_on_def)
  have "x \<noteq> z" using assms(5,6) \<open>partial_order_on (invgen A) r\<close> antisymD assms(5) assms(6) partial_order_onD(3) by fastforce
  then show ?thesis using 1 by (meson assms(5) assms(6) transD)
qed

lemma ab_eqlen:
  assumes "a \<noteq> b"
  and "length a = length b"
shows "a \<noteq> [] \<and> b \<noteq> [] \<and> (\<exists>x y z. a = (x @ y) \<and> b = (x @ z) \<and> (hd y \<noteq> hd z))"
  sorry

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
    case True
    have T1 : "x = y" using True by auto
    have cyz: "y \<in> \<langle>A\<rangle> \<and> z \<in> \<langle>A\<rangle> \<and> compare r y z" using yz compare_set_def case_prod_conv by blast
    then have "compare r y z" by blast
    then have "compare_alt r y z" using comp_compalt assms lyz cyz by blast
    then have 2: "(y = z \<or> (\<exists> d e f. y = (d @ e) \<and> z = (d @ f) \<and> (hd e) \<noteq> (hd f) \<and> (hd e, hd f) \<in> r))" using compare_alt.cases by simp
    then show ?thesis 
    proof (cases "y = z")
      case True
      then have "x = z" using T1 by auto 
      then show ?thesis using T1 xy by auto
    next
      case False
      then have "(\<exists> d e f. y = (d @ e) \<and> z = (d @ f) \<and> (hd e) \<noteq> (hd f) \<and> (hd e, hd f) \<in> r)" using False "2" by auto
      then obtain d e f where "y = (d @ e) \<and> z = (d @ f) \<and> (hd e) \<noteq> (hd f) \<and> (hd e, hd f) \<in> r" by auto
      then have "x = (d @ e) \<and> (hd e) \<noteq> (hd f) \<and> (hd e, hd f) \<in> r" using T1 by simp
      then show ?thesis using True yz by auto
    qed
  next
    case False
    then have xny: "x \<noteq> y" by auto
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
      case False
      then have ynz: "y \<noteq> z" by auto
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
  then show "\<And>x y z.
       length x = length y \<Longrightarrow>
       length y = length z \<Longrightarrow>
       (x, y) \<in> compare_set A r \<Longrightarrow>
       (y, z) \<in> compare_set A r \<Longrightarrow> compare_set A r \<subseteq> compare_set A r" by simp
qed

fun lex :: "((('a,'b) groupgentype \<times> ('a,'b) groupgentype)) set \<Rightarrow> ('a, 'b) word \<Rightarrow> ('a, 'b) word \<Rightarrow> bool"
  where
"lex r x y = (if length x < length y then True else compare r x y)"

definition lex_set where "lex_set A r = {(x, y). x \<in> A \<and> y \<in> A \<and> lex r x y}"

fun lex_lift :: "('a,'b) monoidgentype set \<Rightarrow> ((('a,'b) groupgentype \<times> ('a,'b) groupgentype)) set \<Rightarrow> ('a, 'b) word set \<Rightarrow> ('a,'b) word set \<Rightarrow> bool"
  where
"lex_lift S r a b = (lex r (equiv_red S a) (equiv_red S b))"

definition lexlift_set :: "('a,'b) monoidgentype set \<Rightarrow> (('a,'b) word set) set \<Rightarrow> (('a,'b) groupgentype \<times> ('a,'b) groupgentype) set \<Rightarrow> ((('a,'b) word set \<times> ('a,'b) word set)) set"
  where "lexlift_set S A r = {(a,b). a \<in> A \<and> b \<in> A \<and> lex_lift S r a b}"


definition least :: "('a \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> 'a"
  where
"least r A = (THE x. \<forall>w \<in> A. (x,w) \<in> r)"

fun least_hd :: "(('a,'b) groupgentype \<times> ('a,'b) groupgentype) set \<Rightarrow> ('a, 'b) word set \<Rightarrow> ('a,'b) groupgentype"
  where
"least_hd r A = (THE x. x = least r (hd ` A))"

fun least_comp :: "(('a,'b) groupgentype \<times> ('a,'b) groupgentype) set \<Rightarrow> (('a, 'b) word \<times> (('a, 'b) word set)) \<Rightarrow> (('a, 'b) word \<times> ('a, 'b) word set)"
  where
"least_comp r (xs, A) = (if A = {[]} then (xs, A) 
                              else (xs@[(least_hd r A)], {w. (w \<in> tl ` A \<and>(hd w = least_hd r A))}))"

fun tuple_appendset :: "('a list \<times> 'a list set)  \<Rightarrow> ('a list set)"
  where
"tuple_appendset (xs, S) = (\<Union>x \<in> S. {xs @ x})"

lemma least_is_least :
  assumes "well_order_on (invgen A) r"
      and "S \<subseteq> \<langle>A\<rangle>"
      and "\<forall> x \<in> S. \<forall> y \<in> S. length x = length y"
    shows "\<forall>x \<in> S. \<forall> y \<in> (tuple_appendset (least_comp r ([], S))). (x, y) \<in> compare_set A r"
  sorry

lemma well_order_words :
  assumes "well_order_on A r"
  shows "well_order_on \<llangle>A\<rrangle> (lex_set \<llangle>A\<rrangle> r)"
  unfolding well_order_on_def
  sorry



