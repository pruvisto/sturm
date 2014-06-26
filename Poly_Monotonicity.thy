theory Poly_Monotonicity
imports "~~/src/HOL/Library/Poly_Deriv"
begin

lemma poly_deriv_ge_0:
  fixes p :: "real poly"
  defines "p' \<equiv> pderiv p"
  assumes "a \<le> b" and "\<And>x. x \<in> {a<..<b} \<Longrightarrow> poly p' x \<ge> 0"
  shows "poly p a \<le> poly p b"
proof (cases "a < b")
  assume "a < b"
  from poly_MVT[OF this] obtain \<xi> 
    where "\<xi> \<in> {a<..<b}" and "poly p b - poly p a = (b - a) * poly p' \<xi>" 
    by (auto simp: p'_def)
  with assms have "poly p b - poly p a \<ge> 0" by simp
  thus ?thesis by simp
qed (insert assms, simp)

lemma poly_deriv_ge_0':
  fixes p :: "real poly"
  defines "p' \<equiv> pderiv p"
  assumes "a < b" and "p' \<noteq> 0" and "\<And>x. x \<in> {a<..<b} \<Longrightarrow> poly p' x \<ge> 0"
  shows "poly p a < poly p b"
proof (rule ccontr)
  assume "\<not>(poly p a < poly p b)"
  moreover from assms have "poly p a \<le> poly p b" using poly_deriv_ge_0 by simp
  ultimately have eq: "poly p a = poly p b" by simp
  have interval_const: "\<And>x. x \<in> {a..b} \<Longrightarrow> poly p x = poly p a"
  proof-
    fix x assume x: "x \<in> {a..b}"
    with assms(4) have "poly p x \<ge> poly p a" "poly p x \<le> poly  p b"
      by (intro poly_deriv_ge_0, simp, simp add: p'_def)+
    with eq show "poly p x = poly p a" by auto
  qed

  have deriv_0: "\<And>x. x \<in> {a<..<b} \<Longrightarrow> poly p' x = 0"
  proof (intro ballI DERIV_local_const)
    fix x assume x: "x \<in> {a<..<b}"
    hence px: "poly p x = poly p a" by (intro interval_const) simp
    show "(poly p has_real_derivative poly p' x) (at x)" unfolding p'_def by (rule poly_DERIV)
    let ?m = "(a + b) / 2" and ?d = "(b - a) / 2"
    from x and `a < b` show "?d - abs (x - ?m) > 0" by (simp add: field_simps abs_real_def)
    show "\<forall>y. \<bar>x - y\<bar> < ?d - \<bar>x - ?m\<bar> \<longrightarrow> poly p x = poly p y"
    proof (intro allI impI)
      fix y assume "\<bar>x - y\<bar> < ?d - \<bar>x - ?m\<bar>"
      hence "y \<in> {a<..<b}" by (simp add: field_simps abs_real_def split: split_if_asm)
      hence "poly p y = poly p a" by (intro interval_const) simp
      with px show "poly p x = poly p y" by simp
    qed
  qed
  from `a < b` have "\<not>finite {a<..<b}" by (rule dense_linorder_class.infinite_Ioo)
  moreover from deriv_0 have "{a<..<b} \<subseteq> {x. poly p' x = 0}" by blast
  ultimately have "\<not>finite {x. poly p' x = 0}" using finite_subset by blast
  hence "p' = 0" using poly_roots_finite by blast
  with `p' \<noteq> 0` show False by contradiction
qed

lemma pderiv_ge_0_imp_mono:
    "(\<forall>x. poly (pderiv p) x \<ge> (0::real)) \<Longrightarrow> mono (poly p) "
  by (intro monoI poly_deriv_ge_0) auto

lemma pderiv_ge_0_imp_strict_mono:
    "pderiv p \<noteq> 0 \<Longrightarrow> (\<forall>x. poly (pderiv p) x \<ge> (0::real)) \<Longrightarrow> strict_mono (poly p) "
  by (intro strict_monoI poly_deriv_ge_0') auto  

end
