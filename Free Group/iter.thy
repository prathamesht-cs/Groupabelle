theory iter
imports Main
begin

primrec iter::"nat \<Rightarrow>('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)"
  where
"iter 0 f = (\<lambda> x. x)"
|"iter (Suc n) f = (\<lambda> x. f ((iter n f) x))"

(*Prove the following*)
lemma fixedpt_iteration:
  assumes "f x = x"
  shows "iter (n+1) f x = x"
  using assms
proof(induction n)
  case 0
  then show ?case by simp 
next
  case (Suc n)
  then show ?case by simp
qed

lemma iterative_fixed_pt:
  assumes "iter (n+1) f x = iter n f x" 
  shows "iter (k+(n+1)) f x = iter (k+n) f x"
  using assms
proof(induction k)
  case 0
  then show ?case 
    by force
next
  case (Suc m)
  have "iter (m + (n + 1)) f x = iter (Suc m + n) f x" by simp
  then show ?case using Suc.IH Suc.prems by fastforce
qed

end