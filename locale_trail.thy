theory locale_trail
imports Main
begin

definition nonempty::"'a list set"
  where
"nonempty = {xs . length xs > 1}"

definition appendlist where "appendlist x y = x@y" 
lemma assoc:"(xs@ys)@zs = xs@(ys@zs)"
  apply(induction xs)
   apply auto
  done


locale comm = 
  fixes S:: "'a set"
  and f::"'a \<Rightarrow> 'a \<Rightarrow>'a"
assumes "f (f x y) z = f x (f y z)"


interpretation random:comm "nonempty" "appendlist"
  apply(unfold_locales)
  apply(simp add:appendlist_def)
  done

end