theory Misc
imports "~~/src/HOL/Library/Poly_Deriv"
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

lemma sgn_real_cases[case_names neg 0 pos]:
  "\<lbrakk>sgn (x :: real) = -1 \<Longrightarrow> x < 0 \<Longrightarrow> P; 
    sgn x = 0 \<Longrightarrow> x = 0 \<Longrightarrow> P;
    sgn x = 1 \<Longrightarrow> x > 0 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  unfolding sgn_real_def by (cases "x = 0", simp, cases "x > 0", simp_all)

end