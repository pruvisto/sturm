(*  Title:      ListGroup.thy
    Author:     Manuel Eberl <eberlm@in.tum.de>

    Provides a "group" function for lists, which "merges" all equal adjacent
    elements in the given list, i.e. group [1,2,2,3,3,3,2,2] = [1,2,3,2]
*)
theory ListGroup
imports List
begin

fun group where
"group [] = []" |
"group [x] = [x]" |
"group (x#y#xs) = (if x = y then group (x#xs) else x # group(y#xs))"

lemma group_append_two_same[simp]: "group (xs @ [x,x]) = group (xs @ [x])"
  by (induction xs rule: group.induct, simp_all)

lemma group_append_two_different[simp]: 
  "x \<noteq> y \<Longrightarrow> group (xs @ [x,y]) = group (xs @ [x]) @ [y]"
  by (induction xs rule: group.induct, simp_all)

lemma group_rev[simp]: "group (rev xs) = rev (group xs)"
  by (induction xs rule: group.induct, simp_all)

lemma group_length[simp]: "length (group xs) \<le> length xs"
  by (induction xs rule: group.induct, auto)

lemma group_length_ge1[simp]: "xs \<noteq> [] \<Longrightarrow> length xs \<ge> Suc 0"
  by (induction xs rule: group.induct, simp_all)

lemma group_Nil_iff[simp]: "group xs = [] \<longleftrightarrow> xs = []"
  by (induction xs rule: group.induct, simp_all)

lemma group_set[simp]: "set (group xs) = set xs"
  by (induction xs rule: group.induct, simp_all)

lemma group_Cons_alt[simp]: "x # tl (group (x # xs)) = group (x # xs)"
    by (induction xs rule: group.induct, auto)

lemma group_append: 
  "group (xs\<^isub>1 @ x # xs\<^isub>2) = group (xs\<^isub>1 @ [x]) @ tl (group (x # xs\<^isub>2))"
  by (induction xs\<^isub>1 rule: group.induct, simp_all)

end