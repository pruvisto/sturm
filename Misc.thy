theory Misc
imports Main
begin

section {* Diverse *}

lemma div_diff:
  fixes a :: "'a::ring_div"
  assumes "q dvd a" "q dvd b"
  shows "a div q - b div q = (a - b) div q"
proof-
  from assms have "a div q + (-b div q) = (a + (-b)) div q" by simp
  thus ?thesis by (simp add: assms dvd_neg_div algebra_simps)
qed

end