theory Homomorphism_Eq
imports Main UniversalProperty
begin

definition (in group) hom_eq::"_ \<Rightarrow> _ \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> bool" 
  where
"hom_eq \<equiv> (\<lambda> G H f g. (((f \<in> hom G H) \<and> (g \<in> hom G H) \<and> (\<forall>x \<in> carrier G. f x = g x))))"

lemma (in group) assumes "group G" "group H" "hom_eq G H f g" "hom_eq G H g h"
  shows "hom_eq G H f h"
  using assms   group.hom_eq_def 
  by (smt (verit, ccfv_SIG))

lemma (in group) assumes "group G" "group H" "hom_eq G H f g" 
  shows "hom_eq G H g f"
  using assms   group.hom_eq_def 
  by (smt (verit, ccfv_SIG))

lemma (in group) assumes "group G" "group H" "f \<in> hom G H"
  shows "hom_eq G H f f"
  using assms   group.hom_eq_def 
  by metis

end