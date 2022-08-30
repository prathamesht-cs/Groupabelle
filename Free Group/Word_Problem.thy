theory Word_Problem
imports FreeGroupMain Iter_Reduction_Results Generators Main 
begin

lemma word_problem_not_eq:
  assumes "x \<in> \<langle>S\<rangle>" and "y \<in> \<langle>S\<rangle>"
    and "\<not> (x ~ y)"
  shows "reln_tuple \<langle>S\<rangle> `` {x} \<noteq> reln_tuple \<langle>S\<rangle> `` {y} "
  using assms unfolding reln_tuple_def by blast

lemma word_problem_not_eq_id:
  assumes "x \<in> \<langle>S\<rangle>" 
    and "\<not> (x ~ [])"
  shows "reln_tuple \<langle>S\<rangle> `` {x} \<noteq> \<one>\<^bsub>(freegroup S)\<^esub> "
  using assms word_problem_not_eq[of "x" ] 
  by (metis freegroup_def freewords_on_def monoid.select_convs(2) words_on.intros(1))


lemma 
  assumes "x \<in> \<langle>S\<rangle>" "y \<in> \<langle>S\<rangle>"
  shows "reln_tuple \<langle>S\<rangle> `` {x @ y} = reln_tuple \<langle>S\<rangle> `` {x} \<otimes>\<^bsub>freegroup S\<^esub> reln_tuple \<langle>S\<rangle> `` {y} "
  using assms proj_append_wd[OF assms] sledgehammer
  by (simp add: freegroup_def)

lemma reln_tuple_eq:
  assumes "l \<in> \<langle>S\<rangle>" 
  shows "reln_tuple \<langle>S\<rangle> `` {l} = monoid.m_concat (freegroup S)  (map (\<lambda> x. (reln_tuple \<langle>S\<rangle> `` {[x]})) l)"
  using assms 
proof(induction l)
  case (Cons a l)
  let ?l =  "monoid.m_concat (freegroup S)  (map (\<lambda> x. (reln_tuple \<langle>S\<rangle> `` {[x]})) (l))"
  have "[a] \<in> \<langle>S\<rangle>" 
    using cons_span Cons freewords_on_def by blast
  have " (\<lambda> x. (reln_tuple \<langle>S\<rangle> `` {[x]})) a = reln_tuple \<langle>S\<rangle> `` {[a]}" by simp
  have "monoid.m_concat (freegroup S)  (map (\<lambda> x. (reln_tuple \<langle>S\<rangle> `` {[x]})) (a#l))
            =   reln_tuple \<langle>S\<rangle> `` {[a]} \<otimes>\<^bsub>freegroup S\<^esub> ?l"
    by simp
  moreover have "reln_tuple \<langle>S\<rangle> `` {l} = ?l" using Cons 
    using freewords_on_def span_cons by blast 
  ultimately have 1:"monoid.m_concat (freegroup S)  (map (\<lambda> x. (reln_tuple \<langle>S\<rangle> `` {[x]})) (a#l))
          = (reln_tuple \<langle>S\<rangle> `` {[a]}) \<otimes>\<^bsub>freegroup S\<^esub> (reln_tuple \<langle>S\<rangle> `` {l})"
    by argo
  hence 2:"... =  (reln_tuple \<langle>S\<rangle> `` {[a]@l})" using proj_append_wd Cons freegroup_def 
    by (metis \<open>[a] \<in> \<langle>S\<rangle>\<close> freewords_on_def monoid.select_convs(1) span_cons)
  hence 3:"... = (reln_tuple \<langle>S\<rangle> `` {a#l})" by auto
  then show ?case using 1 2 by argo
qed(simp add: freegroup_def)

lemma assumes "\<not> (l ~ [])" "l \<in> \<langle>S\<rangle>" 
  and "ls = map (\<lambda> x. (reln_tuple \<langle>S\<rangle> `` {[x]})) l"
shows "monoid.m_concat (freegroup S) ls \<noteq> \<one>\<^bsub>(freegroup S)\<^esub> "
  using assms word_problem_not_eq_id sorry  

  

lemma word_problem_eq:
  assumes "x \<in> \<langle>S\<rangle>" "y \<in> \<langle>S\<rangle>"
  shows "(reln_tuple \<langle>S\<rangle> `` {x}) = (reln_tuple \<langle>S\<rangle> `` {y}) 
          \<longleftrightarrow> iter (length x) reduce x = iter (length y) reduce y"
proof
  assume "reln_tuple \<langle>S\<rangle> `` {x} = reln_tuple \<langle>S\<rangle> `` {y}"
  hence "x ~ y" using assms 
    by (meson word_problem_not_eq)
  hence "cancels_eq x y" using assms reln_imp_cancels by blast
  thus "iter (length x) reduce x = iter (length y) reduce y" using cancels_imp_iter[of x y] by argo
next
  assume "iter (length x) reduce x = iter (length y) reduce y"
  hence "cancels_eq x y" using iter_imp_cancels[of x y] by argo
  hence "x ~ y" using assms 
    by (simp add: cancels_eq_imp_reln)
  thus "(reln_tuple \<langle>S\<rangle> `` {x}) = (reln_tuple \<langle>S\<rangle> `` {y})" using assms  
    by (metis (mono_tags, lifting) case_prodI equiv_class_eq mem_Collect_eq reln_equiv reln_tuple_def)
qed

lemma word_problem_neq:
assumes "x \<in> \<langle>S\<rangle>"
  and "(reln_tuple \<langle>S\<rangle> `` {x}) \<noteq> \<one>\<^bsub>freegroup S\<^esub>"
shows "iter (length x) reduce x \<noteq> []"
  using word_problem_eq assms freegroup_def freewords_on_def 
  by (metis iter.iter.simps(1) list.size(3) monoid.select_convs(2) words_on.intros(1))

lemma word_problem_notrel:
assumes "x \<in> \<langle>S\<rangle>"
  and "(reln_tuple \<langle>S\<rangle> `` {x}) \<noteq> \<one>\<^bsub>freegroup S\<^esub>"
shows "\<not> (iter (length x) reduce x ~ [])"
  using  assms freegroup_def freewords_on_def word_problem_neq 
    reduced.simps(1) reduced_cancel_eq reduced_iter_length reln_imp_cancels by metis
  
lemma assumes "x ~ y" "x \<in> \<langle>S\<rangle>" "y \<in> \<langle>S\<rangle>"
  shows "reln_tuple \<langle>S\<rangle> `` {x} = reln_tuple \<langle>S\<rangle> `` {y}"
  using assms unfolding reln_tuple_def using  cancels_imp_iter reln_imp_cancels reln_tuple_def word_problem_eq
  sorry


lemma "x ~ iter (length x) reduce x" 
  by (simp add: cancels_imp_rel iter_cancels_to)


end