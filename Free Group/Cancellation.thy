theory Cancellation
imports "FreeGroupMain" 
begin

definition cancel_at :: "nat \<Rightarrow> ('a,'b) word \<Rightarrow> ('a,'b) word"
  where "cancel_at i l = take i l @ drop (2+i) l"

definition cancels_to_1_at ::  "nat \<Rightarrow> ('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool"
where "cancels_to_1_at i l1 l2 = (0\<le>i \<and> (1+i) < length l1
                              \<and> (inverse (l1 ! i) = (l1 ! (1 + i)))
                              \<and> (l2 = cancel_at i l1))"

definition cancels_to_1 :: "('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool"
  where "cancels_to_1 l1 l2 = (\<exists>i. cancels_to_1_at i l1 l2)"

definition cancels_to  :: "('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool"
  where "cancels_to = (cancels_to_1)^**"

definition cancels_eq::"('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool"
  where
"cancels_eq = (\<lambda> wrd1 wrd2. cancels_to wrd1 wrd2 \<or> cancels_to wrd2 wrd1)^**"

end

