theory NielsonSchreier
imports "UniversalProperty"
begin

fun compare :: "((('a,'b) groupgentype \<times> ('a,'b) groupgentype)) set \<Rightarrow>('a, 'b) word \<Rightarrow> ('a, 'b) word \<Rightarrow> bool"
  where
"compare r x y = (if  x = [] \<or> ((hd x \<noteq> hd y) \<and> (hd x, hd y) \<in> r)  
                     then True else (if \<not>((hd x \<noteq> hd y) \<and> (hd y, hd x) \<in> r) then compare r (tl x) (tl y) else False))"

fun compare_alt :: "((('a,'b) groupgentype \<times> ('a,'b) groupgentype)) set \<Rightarrow>('a, 'b) word \<Rightarrow> ('a, 'b) word \<Rightarrow> bool"
  where
"compare_alt r x y = (x = y \<or> (\<exists>a b c. x = (a @ b) \<and> y = (a @ c) \<and> (hd b) \<noteq> (hd c) \<and>(hd b, hd c) \<in> r))"

definition compare_set 
  where "compare_set A r = {(x, y). x \<in> \<langle>A\<rangle> \<and> y \<in> \<langle>A\<rangle> \<and> compare r x y }"

lemma refl_compare: 
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

lemma 
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

lemma 
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
  then have "(\<exists>a b c. x = (a @ b) \<and> y = (a @ c) \<and> (hd b) \<noteq> (hd c) \<and>(hd b, hd c) \<in> r)" using assms(5) by auto
  then obtain a b c where "x = (a @ b) \<and> y = (a @ c) \<and> (hd b) \<noteq> (hd c) \<and>(hd b, hd c) \<in> r" by blast
  moreover have  "b \<in> \<langle>S\<rangle>" using assms(3) spanset_def using calculation rightappend_span by blast
  moreover have  "c \<in> \<langle>S\<rangle>" using assms(4) spanset_def using calculation rightappend_span by blast
  moreover have "compare r b c" by (simp add: calculation(1))
  moreover have "compare r x y = compare r b c" using compare_subword by (metis add_left_imp_eq assms(1) assms(2) assms(4) calculation(1) calculation(2) calculation(3) leftappend_span length_append spanset_def)
  ultimately show ?thesis  by blast
qed

lemma antisym_compare :
  assumes "well_order_on (invgen A) r"
  shows "(\<forall>x y. (length x = length y) \<longrightarrow>(x, y) \<in> compare_set A r \<longrightarrow> (y, x) \<in> compare_set A r \<longrightarrow> x = y)"
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
      then have 
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

            
fun lex :: "((('a,'b) groupgentype \<times> ('a,'b) groupgentype)) set \<Rightarrow> ('a, 'b) word \<Rightarrow> ('a, 'b) word \<Rightarrow> bool"
  where
"lex r x y = (if length x < length y then True else (if length x = length y then compare r x y else False))"

definition lex_set where "lex_set A r = {(x, y). x \<in> A \<and> y \<in> A \<and> lex r x y}"

fun lex_lift :: "('a,'b) monoidgentype set \<Rightarrow> ((('a,'b) groupgentype \<times> ('a,'b) groupgentype)) set \<Rightarrow> ('a, 'b) word set \<Rightarrow> ('a,'b) word set \<Rightarrow> bool"
  where
"lex_lift S r a b = (lex r (equiv_red S a) (equiv_red S b ))"

definition lexlift_set :: "('a,'b) monoidgentype set \<Rightarrow> (('a,'b) word set) set \<Rightarrow> (('a,'b) groupgentype \<times> ('a,'b) groupgentype) set \<Rightarrow> ((('a,'b) word set \<times> ('a,'b) word set)) set"
  where "lexlift_set S A r = {(a,b). a \<in> A \<and> b \<in> A \<and> lex_lift S r a b}"

definition nlengthwords :: "('a, 'b) word set \<Rightarrow> nat \<Rightarrow> ('a, 'b) word set"
  where
"nlengthwords S n = {w \<in> S. length w = n}"

definition allwords :: "('a, 'b) word set \<Rightarrow> nat \<Rightarrow> ('a, 'b) word set"
  where
"allwords S n = (\<Union>x \<in> Nats. nlengthwords S x)"


lemma well_order_words :
  assumes "well_order_on A r"
  shows "well_order_on \<llangle>A\<rrangle> (lex_set \<llangle>A\<rrangle> r)"
  unfolding well_order_on_def
sorry



