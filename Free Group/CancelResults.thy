theory CancelResults
imports "FreeGroupMain" "CancelLemmas" "HOL-Proofs-Lambda.Commutation"
begin

(*1. Diamond*)

lemma diamond_cancel: 
  shows "diamond (\<lambda> x y. (cancels_to_1 x y) \<or> x = y)"
  unfolding  diamond_def cancels_to_1_def commute_def square_def 
  apply (rule allI, rule allI, rule impI, rule allI, rule impI)
proof-
  fix x y z :: "('a,'b) word"
  assume 1:"(\<exists>i. cancels_to_1_at i x y) \<or> x = y"
  assume 2:"(\<exists>i. cancels_to_1_at i x z) \<or> x = z"
  show "\<exists>u. ((\<exists>i. cancels_to_1_at i y u) \<or> y = u) \<and> ((\<exists>i. cancels_to_1_at i z u) \<or> z = u)"
  proof(cases "x = y \<or> x = z")
    case True
    then have "(\<exists>i. cancels_to_1_at i y z) \<or> (\<exists>i. cancels_to_1_at i z y) \<or> y = z " using 1 2 by blast
  then show ?thesis by blast
  next
    case False
    have 3: "(\<exists>i. cancels_to_1_at i x y) \<and> (\<exists>j. cancels_to_1_at j x z)" using 1 2 False by blast
    obtain i where "cancels_to_1_at i x y" using 3 by auto
    obtain j where "cancels_to_1_at j x z" using 3 by auto
  then show ?thesis 
    proof(cases "y = z")
      case True
    then show ?thesis by auto
    next
      case False
      then show ?thesis
      proof(cases "i \<in> {j, j + 1} \<or> j \<in> {i, i+1}")
        case True
        have a: "y \<noteq> z"  by (simp add: False)
      then show ?thesis
        proof(cases "i = j")
          case True
          have y: "y = cancel_at i x" using cancels_to_1_at_def using \<open>cancels_to_1_at i x y\<close> by auto
          have z: "z = cancel_at i x" using cancels_to_1_at_def True using \<open>cancels_to_1_at j x z\<close> by auto
          have cont: "y = z" using y z by simp
        then show ?thesis using a by auto 
        next
          case False
          then have ij: "i = j + 1 \<or> j = i + 1" using True by blast
          have xi: "inverse (x!i) = (x!(1+i))" using cancels_to_1_at_def \<open>cancels_to_1_at i x y\<close> by auto
          have xj: "inverse (x!j) = (x!(1+j))" using cancels_to_1_at_def \<open>cancels_to_1_at j x z\<close> by auto
        then show ?thesis
          proof(cases "i = 1 + j")
            case True
            have xij: "((nth x j) = (nth x (2+j)))" using True xi xj inverse_of_inverse by (metis add_2_eq_Suc plus_1_eq_Suc)
            have y1: "y = cancel_at (j+1) x" by (metis True \<open>cancels_to_1_at i x y\<close> add.commute cancels_to_1_at_def)
            have z1: "z = cancel_at j x" using cancels_to_1_at_def \<open>cancels_to_1_at j x z\<close> by (simp add: cancels_to_1_at_def)
            have contr1: "y = z" using y1 z1 a1 z1 xij by (smt (z3) True \<open>cancels_to_1_at i x y\<close> a2 add.commute cancel_at_def cancels_to_1_at_def group_cancel.add1 nat_1_add_1 zero_le)
          show ?thesis using a contr1 by auto
          next
            case False
            have "j = i + 1" using False ij by auto
            then have xji: "((nth x i) = (nth x (2+i)))" by (metis Suc_1 add.commute add_Suc_right inverse_of_inverse plus_1_eq_Suc xi xj)
            have y2: "y = cancel_at i x" using cancels_to_1_at_def \<open>cancels_to_1_at i x y\<close> by auto
            have z2: "z = cancel_at (i+1) x" using xji cancels_to_1_at_def \<open>cancels_to_1_at j x z\<close> by (simp add: cancels_to_1_at_def \<open>j = i + 1\<close>)
            have contr2: "y = z" using y2 z2 a2 z2 xji  by (smt (verit) \<open>cancels_to_1_at j x z\<close> \<open>j = i + 1\<close> a1 add.left_commute cancel_at_def cancels_to_1_at_def le_add2 le_add_same_cancel2 nat_1_add_1)
          then show ?thesis using a contr2 by auto
          qed
        qed
      next
        case False
        then have ij: " \<not> (i \<in> {j, j + 1} \<or> j \<in> {i, i + 1})" by auto
        have xi: "inverse (x!i) = (x!(1+i))" using cancels_to_1_at_def \<open>cancels_to_1_at i x y\<close> by auto
        have xj: "inverse (x!j) = (x!(1+j))" using cancels_to_1_at_def \<open>cancels_to_1_at j x z\<close> by auto
        then show ?thesis
        proof(cases "i \<le> j")
          case True
           then have l: "i + 1 < j"  by (metis False discrete insert_iff le_neq_implies_less)
          then have j1: "i + 1 < j + 1" by linarith
          have i0: "i\<ge>0" by simp
          have j0: "j \<ge> 0"  by simp
          then have j20: "j - 2 \<ge> 0" by simp
          have z: "z = cancel_at j x" using \<open>cancels_to_1_at j x z\<close> cancels_to_1_at_def by auto
          have y: "y = cancel_at i x"  using \<open>cancels_to_1_at i x y\<close> cancels_to_1_at_def by auto
          have il: "1 + i < length x" using  \<open>cancels_to_1_at i x y\<close> by (simp add: cancels_to_1_at_def)
          have m: "1 + j  < length x" using \<open>cancels_to_1_at j x z\<close> cancels_to_1_at_def by (simp add: cancels_to_1_at_def)
          then have jl: "j + 1 < length x" by auto
          then have "i + 1 + 2 < length x" using l  by linarith
          then have zz: "i + 1 < length x - 2" by simp
          have "length x - 2 = length (cancel_at i x)" using cancel_at_length[of "i" "x"] il i0 by presburger
          then have "length x - 2 = length y" using y by simp
          then have "j + 1 < length y + 2" using jl  by linarith
          then have j2y: "(j - 2) + 1 < length y" using l by linarith
          have "length x - 2 = length (cancel_at j x)" using cancel_at_length[of "j" "x"]  jl j0 by metis
          then have "length x - 2 = length z" using z by simp
          then have iz: "i + 1 < length z" using zz  by simp
          have j: "j < length x" using m by linarith
          then have n: "cancel_at i (cancel_at j x) = cancel_at (j-2) (cancel_at i x)" using cancel_order l m by (metis add.commute)
          then have eq: "cancel_at i z = cancel_at (j-2) y" using \<open>cancels_to_1_at j x z\<close> \<open>cancels_to_1_at i x y\<close> cancels_to_1_at_def by (simp add: cancels_to_1_at_def)
          have take: "take j z = take j x" using take_assoc cancel_at_def l m by (metis \<open>cancels_to_1_at j x z\<close> add.commute cancels_to_1_at_def eq_imp_le)
          then have o: "(nth x i) = (nth z i)" using l i0 by (metis add_lessD1 nth_take)
          have p: "(nth x (i+1)) = (nth z (i+1))" using l i0 take takenth by (metis True order.trans)
          then have "inverse (nth z i) = (nth x (i+1))" using xi o by (smt (z3) add.commute) 
          then have "inverse (nth z i) = (nth z (i+1))" using p by (smt (z3))
          then have inv1: "inverse (nth z i) = (nth z (1+i))" by simp
          have zeq: "(cancel_at i z) = cancel_at i z" by simp
          have zu: "cancels_to_1_at i z (cancel_at i z)"  using i0 iz inv1 zeq unfolding cancels_to_1_at_def by linarith
          have "y = cancel_at i x" using  \<open>cancels_to_1_at i x y\<close> cancels_to_1_at_def by (simp add: cancels_to_1_at_def)
          then have q: "(nth x j) = (nth y (j - 2))" using cancel_atnth l j by blast
          have r: "(nth x (j + 1)) = (nth y ((j - 2) + 1))"  using cancel_atnth j1 m by (smt (verit) \<open>y = cancel_at i x\<close> add.commute comm diff_add_inverse diff_diff_left diff_is_0_eq' l le_add2 nat_1_add_1 nat_less_le zero_less_diff)
          have s: "inverse (nth y (j - 2)) = (nth x (j + 1))" using xj q  by auto
          then have inv2:"inverse (nth y (j - 2)) = (nth y ((j - 2) + 1))" using r  by fastforce
          have yeq: "cancel_at (j - 2) y = cancel_at (j - 2) y" by simp
          have yu: "cancels_to_1_at (j - 2) y (cancel_at (j - 2) y)" using j20 j2y  inv2 yeq unfolding cancels_to_1_at_def by auto
          then show ?thesis using yu zu eq by auto
        next
          case False
          then have j1i: "j + 1 < i" using ij by (metis discrete insertCI leI le_neq_implies_less)
          then have j1i1: "j + 1 < i + 1" by linarith
          have i0: "i\<ge>0" by simp
          then have i20: "i - 2 \<ge> 0" by simp
          have j0: "j \<ge> 0"  by simp
          have z: "z = cancel_at j x" using \<open>cancels_to_1_at j x z\<close> cancels_to_1_at_def by auto
          have y: "y = cancel_at i x"  using \<open>cancels_to_1_at i x y\<close> cancels_to_1_at_def by auto
          have jl: "1 + j  < length x" using \<open>cancels_to_1_at j x z\<close> cancels_to_1_at_def by (simp add: cancels_to_1_at_def)
          have il: "1 + i < length x" using  \<open>cancels_to_1_at i x y\<close> by (simp add: cancels_to_1_at_def)
          have "length x - 2 = length (cancel_at j x)" using cancel_at_length[of "j" "x"] jl j0 by presburger
          then have  "length x = length (cancel_at j x) + 2" using jl by linarith
          then have "i + 1 < (length z) + 2" using il i0 z  by auto
          then have i2z: "(i - 2) + 1 < length z" using j1i by linarith
          have "length x - 2 = length (cancel_at i x)" using cancel_at_length[of "i" "x"] il i0 by presburger
          then have xy: "length x - 2 = length y" using y  by simp
          have "j + 1 + 2 < length x" using j1i il  by linarith
          then have "j + 1 < length x - 2" using jl  by linarith
          then have jy: "j + 1 < length y" using xy by simp
          have "cancel_at j (cancel_at i x) = cancel_at (i-2) (cancel_at j x)" using j1i il cancel_order by auto
          then have eq: "cancel_at j y = cancel_at (i-2) z" using y z by simp
          have take: "take i x = take i y" using take_assoc cancel_at_def j1i by (metis add_diff_inverse_nat diff_add_inverse diff_add_inverse2 diff_le_self less_imp_diff_less less_nat_zero_code y zero_less_diff)
          have nth: "(nth x j) = (nth y j)" using takenth i0 j1i1 add_less_imp_less_right take by blast
          have nth1: "(nth x (j+1)) = (nth y (j+1))" using takenth i0 j1i1 j1i take by auto
          have "inverse (nth y j) = (nth x (j+1))" using xj nth by fastforce
          then have invj: "inverse (nth y j) = (nth y (j+1))" using nth1 by (smt (z3))
          have yu:  "cancels_to_1_at j y (cancel_at j y)" using j0 jy invj cancels_to_1_at_def by fastforce
          have nthi: "(nth x i) = (nth z (i - 2))" using z j1i  il cancel_atnth by (metis trans_le_add2 verit_comp_simplify1(3))
          have nthi1: "(nth x (i+1)) = (nth z ((i - 2) + 1))"  using z j1i1 il by (metis Nat.add_diff_assoc2 add.commute add_lessD1 cancel_atnth discrete j1i nat_1_add_1)
          then have "inverse (nth z (i - 2)) = (nth x (i + 1))" using xi nthi by fastforce
          then have invi: "inverse (nth z (i - 2)) = (nth z ((i - 2) + 1))" using nthi1 by (smt (z3))
          have zu: "cancels_to_1_at (i - 2) z (cancel_at (i - 2) z)" using i20 i2z invi cancels_to_1_at_def by (metis add.commute)
          then show ?thesis using eq yu zu by auto
        qed
      qed
    qed
  qed
qed

(*2. Uniqueness of cancels_to*)

lemma cancels_to_reduced :
  assumes "i\<ge>0" "(i+1) <length x" "cancels_to x y"  "cancels_to x z" "reduced y" "reduced z" 
  shows "y = z"
  using assms
  unfolding cancels_to_def
  sorry  
  

(*3. Uniqueness of cancel_eq*) 
lemma "cancels_eq x y \<Longrightarrow> reduced x \<Longrightarrow> reduced y \<Longrightarrow> x = y" sorry 

end
