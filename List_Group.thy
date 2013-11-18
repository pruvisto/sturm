(*  Title:      List_RemAdjDups.thy
    Author:     Manuel Eberl <eberlm@in.tum.de>

    Provides a "rem_adj_dups" function for lists, which "merges" all equal adjacent
    elements in the given list, i.e. rem_adj_dups [1,2,2,3,3,3,2,2] = [1,2,3,2]
*)
theory List_RemAdjDups
imports List
begin

fun rem_adj_dups :: "'a list \<Rightarrow> 'a list" where
"rem_adj_dups [] = []" |
"rem_adj_dups [x] = [x]" |
"rem_adj_dups (x#y#xs) = (if x = y then rem_adj_dups (x#xs) else x # rem_adj_dups(y#xs))"


lemma rem_adj_dups_append_two: 
    "rem_adj_dups (xs @ [x,y]) = rem_adj_dups (xs @ [x]) @ (if x = y then [] else [y])"
  by (induction xs rule: rem_adj_dups.induct, simp_all)

lemma rem_adj_dups_rev[simp]: "rem_adj_dups (rev xs) = rev (rem_adj_dups xs)"
  by (induction xs rule: rem_adj_dups.induct, simp_all add: rem_adj_dups_append_two)

lemma rem_adj_dups_length[simp]: "length (rem_adj_dups xs) \<le> length xs"
  by (induction xs rule: rem_adj_dups.induct, auto)

lemma rem_adj_dups_length_ge1[simp]: "xs \<noteq> [] \<Longrightarrow> length (rem_adj_dups xs) \<ge> Suc 0"
  by (induction xs rule: rem_adj_dups.induct, simp_all)

lemma rem_adj_dups_Nil_iff[simp]: "rem_adj_dups xs = [] \<longleftrightarrow> xs = []"
  by (induction xs rule: rem_adj_dups.induct, simp_all)

lemma rem_adj_dups_set[simp]: "set (rem_adj_dups xs) = set xs"
  by (induction xs rule: rem_adj_dups.induct, simp_all)

lemma rem_adj_dups_Cons_alt[simp]: "x # tl (rem_adj_dups (x # xs)) = rem_adj_dups (x # xs)"
    by (induction xs rule: rem_adj_dups.induct, auto)

lemma rem_adj_dups_distinct: "distinct xs \<Longrightarrow> rem_adj_dups xs = xs"
    by (induction xs rule: rem_adj_dups.induct, simp_all)

lemma rem_adj_dups_append: 
  "rem_adj_dups (xs\<^sub>1 @ x # xs\<^sub>2) = rem_adj_dups (xs\<^sub>1 @ [x]) @ tl (rem_adj_dups (x # xs\<^sub>2))"
  by (induction xs\<^sub>1 rule: rem_adj_dups.induct, simp_all)

lemma rem_adj_dups_singleton:
  "rem_adj_dups xs = [x] \<Longrightarrow> xs = replicate (length xs) x"
  by (induction xs rule: rem_adj_dups.induct, auto split: split_if_asm)


lemma rem_adj_dups_map_injective:
  assumes "inj f"
  shows "rem_adj_dups (map f xs) = map f (rem_adj_dups xs)"
  by (induction xs rule: rem_adj_dups.induct, 
      auto simp add: injD[OF assms])

lemma rem_adj_dups_sorted: "sorted xs \<Longrightarrow> sorted (rem_adj_dups xs)"
  by (induction xs rule: rem_adj_dups.induct, 
      simp_all split: split_if_asm add: sorted_Cons)

end