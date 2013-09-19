(*  Title:      ListGroup.thy
    Author:     Manuel Eberl <eberlm@in.tum.de>

    Provides a "group" function for lists, which "merges" all equal adjacent
    elements in the given list, i.e. group [1,2,2,3,3,3,2,2] = [1,2,3,2]
*)
theory List_Group
imports List
begin

fun group :: "'a list \<Rightarrow> 'a list" where
"group [] = []" |
"group [x] = [x]" |
"group (x#y#xs) = (if x = y then group (x#xs) else x # group(y#xs))"


lemma group_append_two: 
    "group (xs @ [x,y]) = group (xs @ [x]) @ (if x = y then [] else [y])"
  by (induction xs rule: group.induct, simp_all)

lemma group_rev[simp]: "group (rev xs) = rev (group xs)"
  by (induction xs rule: group.induct, simp_all add: group_append_two)

lemma group_length[simp]: "length (group xs) \<le> length xs"
  by (induction xs rule: group.induct, auto)

lemma group_length_ge1[simp]: "xs \<noteq> [] \<Longrightarrow> length (group xs) \<ge> Suc 0"
  by (induction xs rule: group.induct, simp_all)

lemma group_Nil_iff[simp]: "group xs = [] \<longleftrightarrow> xs = []"
  by (induction xs rule: group.induct, simp_all)

lemma group_set[simp]: "set (group xs) = set xs"
  by (induction xs rule: group.induct, simp_all)

lemma group_Cons_alt[simp]: "x # tl (group (x # xs)) = group (x # xs)"
    by (induction xs rule: group.induct, auto)

lemma group_distinct: "distinct xs \<Longrightarrow> group xs = xs"
    by (induction xs rule: group.induct, simp_all)

lemma group_append: 
  "group (xs\<^sub>1 @ x # xs\<^sub>2) = group (xs\<^sub>1 @ [x]) @ tl (group (x # xs\<^sub>2))"
  by (induction xs\<^sub>1 rule: group.induct, simp_all)

lemma group_singleton:
  "group xs = [x] \<Longrightarrow> xs = replicate (length xs) x"
  by (induction xs rule: group.induct, auto split: split_if_asm)


lemma group_map_injective:
  assumes "inj f"
  shows "group (map f xs) = map f (group xs)"
  by (induction xs rule: group.induct, 
      auto simp add: injD[OF assms])

lemma group_sorted: "sorted xs \<Longrightarrow> sorted (group xs)"
  by (induction xs rule: group.induct, 
      simp_all split: split_if_asm add: sorted_Cons)

end