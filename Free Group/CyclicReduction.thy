theory CyclicReduction
imports "FreeGroupMain" "HOL.List"
begin

definition drop_last :: "'a list \<Rightarrow> 'a list"
where
"drop_last xs = (rev(tl(rev xs)))"

lemma length_drop:
"length xs \<ge> length (drop_last xs)"
proof-
  have "length (tl xs) \<le> length xs" by simp
  moreover have "length (rev xs) = length xs" by simp
  moreover then have "length (tl(rev xs)) \<le> length xs" by simp
  ultimately show ?thesis by (simp add: drop_last_def)
qed

lemma length_drop_inc:
"length(drop_last xs) < length (x#xs)"
  by (simp add: drop_last_def) 

function cyclic_reduced :: "('a,'b) word \<Rightarrow> bool"
  where
"cyclic_reduced [] = True" |
"cyclic_reduced (x#xs) = (if (xs \<noteq> []) 
                         then ((x \<noteq> inverse (last xs)) \<and> (cyclic_reduced (drop_last xs)))  
                         else True)"
  apply auto
  apply pat_completeness
  done
(*alternative defns for cyclic_reduced. These are not used in further lemmas*)
function cyclic_reduced1 :: "('a,'b) word \<Rightarrow> bool"
  where
"cyclic_reduced1 [] = True" |
"cyclic_reduced1 (x#xs) = (if xs\<noteq> [] then (if(reduced (x#xs) \<and> (x \<noteq> inverse (last xs))) then True else False)else True)"
  apply (meson list.exhaust)
  apply simp +
  done

definition cyc_red_condn :: "('a,'b) word \<Rightarrow> bool"
  where "cyc_red_condn wrd = ((last(rev wrd)) \<noteq> inverse (last wrd))"

definition cyc_red :: "('a,'b) word \<Rightarrow> bool"
  where "cyc_red wrd = (reduced wrd \<and> cyc_red_condn wrd)" 

lemma assumes "cyc_red (x#xs)" 
  shows "reduced (x#xs)"
  using assms cyc_red_def by auto

function cyclic_reduction :: "('a,'b) word \<Rightarrow> ('a,'b) word"
  where
"cyclic_reduction [] = []" |
"cyclic_reduction (x#xs) = (if xs = [] then [x] else (if (x = inverse (last xs)) then (cyclic_reduction (drop_last xs))
                            else ((cyclic_reduction xs)@[x])))"  

  using cyclic_reduced.cases 
  apply blast 
  apply simp 
  apply simp 
  by simp
termination
  apply (relation "measure(\<lambda>(xs).length xs)") 
  apply (simp add: length_drop_inc) 
  using length_drop_inc apply auto[1]
  apply simp 
  done 
  value "cyclic_reduction [((a\<^sub>1, a\<^sub>1), False), ((a\<^sub>1, a\<^sub>1), True), ((a\<^sub>1, a\<^sub>1), True), ((a\<^sub>1, a\<^sub>1), False), ((a\<^sub>1, a\<^sub>1), True),
       ((a\<^sub>1, a\<^sub>1), False)]"
(*-a,a,a,-a,a,-a*)

lemma assumes "normalized wrd"
  shows "normalization wrd = wrd"
  sorry

inductive_set group_spanset::"('a,'b) groupgentype set \<Rightarrow> ('a,'b) word set" ("\<llangle>_\<rrangle>")
  for S::"('a,'b) groupgentype set"
  where
"x \<in> S \<Longrightarrow> [x] \<in> \<llangle>S\<rrangle>"
|"x \<in> inver ` S \<Longrightarrow> [x] \<in> \<llangle>S\<rrangle>"
|"x \<in> S \<Longrightarrow> [y] \<in> \<llangle>S\<rrangle> \<Longrightarrow> [x]@[y] \<in> \<llangle>S\<rrangle>"

fun inv_list :: "('a,'b) word \<Rightarrow> ('a,'b) word"
  where 
"inv_list [] = []" |
"inv_list (x#xs) = inv_list xs@[inverse x]"
value "inv_list [((a\<^sub>1, a\<^sub>1), True), ((a\<^sub>1, a\<^sub>1), False), ((a\<^sub>1, a\<^sub>1), True)]"

definition conj_bool :: "('a,'b) groupgentype set \<Rightarrow> ('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool"
  where "conj_bool S x y = (\<exists>s.(s\<in>\<llangle>S\<rrangle>) \<and> y = s@x@(inv_list s) \<and> x \<in> \<llangle>S\<rrangle> \<and> y \<in> \<llangle>S\<rrangle>)"

definition conj_bool_eq :: "('a,'b) groupgentype set \<Rightarrow> ('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool"
  where "conj_bool_eq S xs ys = ((conj_bool S xs ys) \<or> (conj_bool S ys xs))"
                           
definition conj_class ::"('a,'b) groupgentype set \<Rightarrow> ('a,'b) word \<Rightarrow> ('a,'b) word set"
  where "conj_class S x = {y. conj_bool S x y}" 

definition cyclic_at_i :: "('a,'b) word \<Rightarrow> nat \<Rightarrow> ('a,'b) word"
  where
"cyclic_at_i x i = (drop i x)@(take i x)"

definition cyclicp_at_i :: "('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> nat \<Rightarrow> bool"
  where "cyclicp_at_i x y i = (cyclic_at_i x i = y)"

definition cyclicp :: "('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool"
  where "cyclicp x y = (\<exists>i. cyclicp_at_i x y i)"

lemma len_cycred:
  fixes "wrd"
  shows "length (cyclic_reduction wrd) \<le> length wrd"
proof(induction "length wrd" arbitrary: wrd rule:less_induct)
  case less
  show ?case
  proof(cases "wrd")
    case (Cons a wrd')
    have 1:"wrd' = [] \<Longrightarrow> ?thesis" using Cons by auto
    have 2:"wrd' \<noteq> [] \<Longrightarrow> a = inverse (last wrd')  \<Longrightarrow> ?thesis"  
    proof-
    assume A:"wrd' \<noteq> []"
    assume B:"a = inverse (last wrd')"
     have  cycl_eq:"cyclic_reduction (a#wrd') = cyclic_reduction (drop_last wrd')"
      using A B  Cons cyclic_reduction.simps(2)[of "a" "wrd'"] by simp
     have less_drp:"length (drop_last wrd') < length wrd" using length_drop Cons
       length_drop_inc by auto
     have "length (cyclic_reduction (drop_last wrd')) \<le> length (drop_last wrd')"
      using less[OF less_drp] .
     with less_drp cycl_eq show ?thesis using Cons by force
    qed
   have "wrd' \<noteq> [] \<Longrightarrow> a \<noteq> inverse (last wrd')  \<Longrightarrow> ?thesis"  
   proof-
   assume A:"wrd' \<noteq> []"
   assume B:"a \<noteq> inverse (last wrd')"
   have IH:"length wrd' < length wrd" using Cons by force
   have "length (cyclic_reduction wrd') \<le> length (wrd')" using less[OF IH] .
   moreover have "length (cyclic_reduction wrd) = length (cyclic_reduction wrd') + 1"
     using A B
     by (simp add: local.Cons)
   ultimately have "length (cyclic_reduction wrd) \<le> length (wrd') + 1" by simp
   then show ?thesis using IH by linarith
   qed
   then show ?thesis using 1 2 by argo
 qed(simp)
qed


lemma assumes "y = s@x@(inv_list s)" 
  shows "cyclic_reduction x = cyclic_reduction y"
  sorry

lemma conj_cyc:
  assumes "conj_bool S x y" "x\<noteq>[]"
  shows "cyclic_reduction x = cyclic_reduction y"
  using assms
proof(induction x)
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  have "conj_bool S (a#x) y" using local.Cons(2) by auto
  then have "\<exists>s.(s\<in>\<llangle>S\<rrangle>) \<and> y = s@(a#x)@(inv_list s) \<and> (a#x) \<in> \<llangle>S\<rrangle> \<and> y \<in> \<llangle>S\<rrangle>" using conj_bool_def by metis
  then obtain s where "s\<in>\<llangle>S\<rrangle> \<and> y = s@(a#x)@(inv_list s) \<and> (a#x) \<in> \<llangle>S\<rrangle> \<and> y \<in> \<llangle>S\<rrangle>" by auto
  then have "y = s@(a#x)@(inv_list s)" by simp 
  then show ?case sorry
qed

lemma assumes "cyclic_reduced1 xs" "wrd \<in> conj_class S xs" 
  shows "length(cyclic_reduction xs) \<le> length (wrd)"
proof-
  have "conj_bool S xs wrd" using conj_class_def[of S xs] using assms(2) by simp
  then have "cyclic_reduction wrd = cyclic_reduction xs" using conj_bool_def by (metis conj_cyc group_spanset.simps not_Cons_self2 snoc_eq_iff_butlast) 
  then show ?thesis using len_cycred by metis
qed

lemma assumes "conj_bool S x v" "conj_bool S y w"
  shows "conj_bool_eq S x y"
  sorry

lemma conj_conj:
  assumes "conj_class S x =  conj_class S y" "conj_class S x \<noteq>{}"
  shows "conj_bool_eq S x y"
proof-
  have 1: "{v. conj_bool S x v} = {w. conj_bool S y w}" using assms conj_class_def by auto
  then obtain v where "v \<in> {v. conj_bool S x v}" using assms conj_class_def by blast
  then have "(\<exists>s.(s\<in>\<llangle>S\<rrangle>) \<and> v = s@x@(inv_list s) \<and> x \<in> \<llangle>S\<rrangle> \<and> v \<in> \<llangle>S\<rrangle>)" using conj_bool_def by (metis mem_Collect_eq)
  then have a: "conj_bool S x v" using conj_bool_def by metis
  then obtain w where "w \<in> {w. conj_bool S y w}" using 1 assms by blast
  then have "(\<exists>t.(t\<in>\<llangle>S\<rrangle>) \<and> w = t@y@(inv_list t) \<and> y \<in> \<llangle>S\<rrangle> \<and> w \<in> \<llangle>S\<rrangle>)" using conj_bool_def by (metis mem_Collect_eq)
  then have b: "conj_bool S y w" using conj_bool_def by metis
  have "x = (inv_list s)@t@y@(inv_list t)@s" using assms 1 sorry   
  then show ?thesis sorry
  qed


lemma assumes "S \<noteq> {}"
  shows "conj_class S [] = {[]}"
proof (rule ccontr)
  assume assm :"\<not> (conj_class S [] = {[]})"
  then have "\<exists>y.(y \<noteq> []) \<and> y \<in> conj_class S []" using conj_class_def using conj_conj conj_class_def conj_bool_def by (metis (mono_tags, hide_lams) conj_bool_eq_def empty_Collect_eq is_singletonI' is_singleton_the_elem singleton_iff)
  then obtain y where 1: "(y \<noteq> []) \<and> y \<in> conj_class S []" using HOL.exE by auto
  then have "[] = y@[]@(inv_list y)" using conj_class_def conj_bool_def using Nil_is_append_conv mem_Collect_eq by (metis (no_types, lifting) group_spanset.simps snoc_eq_iff_butlast)
  then have 2: "y = []" by simp
  have 3: "y \<noteq> []" by (simp add: "1")
  then have "\<nexists>y.(y \<noteq> []) \<and> y \<in> conj_class S []" using 2 3 by auto
  then have "\<not>(\<not>(conj_class S [] = {[]}))" by (simp add: \<open>\<exists>y. y \<noteq> [] \<and> y \<in> conj_class S []\<close>)
  then show "False" using \<open>\<exists>y. y \<noteq> [] \<and> y \<in> conj_class S []\<close> by auto
qed


lemma conj_conjclass:
  assumes "conj_bool S x y"
  shows "conj_class S x = conj_class S y"
proof-
  have "\<exists>s.(s\<in>\<llangle>S\<rrangle>) \<and> y = s@x@(inv_list s) \<and> x \<in> \<llangle>S\<rrangle> \<and> y \<in> \<llangle>S\<rrangle>" using assms by (meson conj_bool_def)
  then show ?thesis sorry
qed
  
lemma assumes "\<not>(conj_bool S x y)" "x\<noteq>[]"
  shows "conj_class S x \<inter> conj_class S y = {}"
  sorry

lemma assumes "cyclic_reduced1 (x#xs)" 
  shows "reduced (x#xs)"
  using assms
proof(cases "xs =[]")
  case True
  then show ?thesis by simp
next
  case False
  then show ?thesis sorry   
qed

lemma "cyclic_reduced (cyclic_reduction (x#xs))"
proof(cases "(x#xs) = []")
  case True
  have "cyclic_reduction (x#xs) = []" by (simp add: True)
  have "cyclic_reduced (x#xs)" using True by simp
  then show ?thesis using True by auto
next
  case False
  then show ?thesis sorry
qed





  








