theory group_class
imports Main
begin

class semigroup =
  fixes mult :: "'a \<Rightarrow> 'a  \<Rightarrow> 'a" (infixl "\<otimes>" 70)
  assumes assoc: "(x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"

class monoidl = semigroup +
  fixes neutral :: 'a ("e")
  assumes neutl: "e \<otimes> x = x"

class monoid = monoidl +
  assumes neutr: "x \<otimes> e = x"

class group = monoidl +
fixes inverse ::"'a \<Rightarrow> 'a" ("inv")
assumes invl: "(inv x) \<otimes> x = e"

lemma (in group) left_cancel: "x \<otimes> y = x \<otimes> z \<Longrightarrow> y = z"
proof-
assume "x \<otimes> y = x \<otimes> z"
then have "(inv x) \<otimes> (x \<otimes> y) = (inv x) \<otimes> (x \<otimes> z)" by simp
then have "((inv x) \<otimes> x) \<otimes> y = ((inv x) \<otimes> x) \<otimes> z" using assoc by simp
then show "y = z" using neutl and invl by simp
qed

(*
subclass (in group) monoid
proof-
fix x
from invl have "(inv x) \<otimes> x = e" by simp
then have "(inv x) \<otimes> (x \<otimes> e) = (inv x) \<otimes> x" using assoc [symmetric] and neutl and invl by simp
then have "x \<otimes> e = x" using left_cancel by simp
*)