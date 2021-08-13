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

inductive_set group_spanset::"('a,'b) groupgentype set \<Rightarrow> ('a,'b) word set" ("\<llangle>_\<rrangle>")
  for S::"('a,'b) groupgentype set"
  where
"x \<in> S \<Longrightarrow> [x] \<in> \<llangle>S\<rrangle>"
|"x \<in> inver ` S \<Longrightarrow> [x] \<in> \<llangle>S\<rrangle>"
|"x \<in> S \<Longrightarrow> [y] \<in> \<llangle>S\<rrangle> \<Longrightarrow> [x]@[y] \<in> \<llangle>S\<rrangle>"

definition conj_bool :: "('a,'b) groupgentype set \<Rightarrow> ('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool"
  where "conj_bool S x y = (if (\<exists>s.(s\<in>\<llangle>S\<rrangle>) \<and> y = s@x@(inv_list s) \<and> x \<in> \<llangle>S\<rrangle> \<and> y \<in> \<llangle>S\<rrangle>)
                           then True else False)"

definition conj_class ::"('a,'b) groupgentype set \<Rightarrow> ('a,'b) word \<Rightarrow> ('a,'b) word set"
  where "conj_class S x = {y. conj_bool S x y}" 

definition conj_bool_eq :: "('a,'b) groupgentype set \<Rightarrow> ('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool"
  where "conj_bool_eq S xs ys = (if ((conj_bool S xs ys) \<or> (conj_bool S ys xs))then True else False)"

lemma len_cycred:
"length (cyclic_reduction wrd) \<le> length wrd" 
proof(induction wrd rule: cyclic_reduction.induct)
  case 1
  then show ?case by simp
next
  case (2 x xs)
  have "length (cyclic_reduction (drop_last xs)) \<le> length (drop_last xs)" using length_drop_inc sorry
  then show ?case sorry
qed

 









