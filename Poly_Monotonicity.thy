theory Poly_Monotonicity
imports "~~/src/HOL/Library/Poly_Deriv" "Lib/Misc_Polynomial"
begin

section {* Additional monotonicity notions *}

subsection{* Monotonicity on a set *}

definition mono_on where
  "mono_on f A  \<longleftrightarrow> (\<forall>x y. x \<in> A \<longrightarrow> y \<in> A \<longrightarrow> x \<le> y \<longrightarrow> f x \<le> f y)"

lemma mono_onI:
  assumes "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
  shows "mono_on f A"
  using assms unfolding mono_on_def by simp

lemma mono_onD:
  assumes "mono_on f A"
  shows "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
  using assms unfolding mono_on_def by simp

lemma mono_on_subset: "mono_on f B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> mono_on f A"
  by (blast intro: mono_onI dest: mono_onD)

lemma mono_on_UNIV[simp]: "mono_on f UNIV = mono f"
  unfolding mono_on_def mono_def by simp


subsection{* Strict monotonicity on a set *}

definition strict_mono_on where
  "strict_mono_on f A  \<longleftrightarrow> (\<forall>x y. x \<in> A \<longrightarrow> y \<in> A \<longrightarrow> x < y \<longrightarrow> f x < f y)"

lemma strict_mono_onI:
  assumes "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x < y \<Longrightarrow> f x < f y"
  shows "strict_mono_on f A"
  using assms unfolding strict_mono_on_def by simp

lemma strict_mono_onD:
  assumes "strict_mono_on f A"
  shows "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x < y \<Longrightarrow> f x < f y"
  using assms unfolding strict_mono_on_def by simp

lemma strict_mono_on_subset: "strict_mono_on f B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> strict_mono_on f A"
  by (blast intro: strict_mono_onI dest: strict_mono_onD)

lemma strict_mono_on_UNIV[simp]: "strict_mono_on f UNIV = strict_mono f"
  unfolding strict_mono_on_def strict_mono_def by simp

subsection{* Monotonically decreasing *}

definition mono_dec where
  "mono_dec f \<longleftrightarrow> (\<forall>x y. x \<le> y \<longrightarrow> f x \<ge> f y)"

definition strict_mono_dec where
  "strict_mono_dec f \<longleftrightarrow> (\<forall>x y. x < y \<longrightarrow> f x > f y)"

lemma mono_dec_mono_conv:
  fixes f :: "_ \<Rightarrow> ('a :: ordered_ab_group_add)"
  shows "mono_dec f \<longleftrightarrow> mono (\<lambda>x. -f x)"
  unfolding mono_def mono_dec_def by simp

lemma strict_mono_dec_strict_mono_conv:
  fixes f :: "_ \<Rightarrow> ('a :: ordered_ab_group_add)"
  shows "strict_mono_dec f \<longleftrightarrow> strict_mono (\<lambda>x. -f x)"
  unfolding strict_mono_def strict_mono_dec_def by simp


subsection{* Monotonically decreasing on a set *}

definition mono_dec_on where
  "mono_dec_on f A  \<longleftrightarrow> (\<forall>x y. x \<in> A \<longrightarrow> y \<in> A \<longrightarrow> x \<le> y \<longrightarrow> f x \<ge> f y)"

lemma mono_dec_onI:
  assumes "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<ge> f y"
  shows "mono_dec_on f A"
  using assms unfolding mono_dec_on_def by simp

lemma mono_dec_onD:
  assumes "mono_dec_on f A"
  shows "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<ge> f y"
  using assms unfolding mono_dec_on_def by simp

lemma mono_dec_on_subset: "mono_dec_on f B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> mono_dec_on f A"
  by (blast intro: mono_dec_onI dest: mono_dec_onD)

lemma mono_dec_on_mono_on_conv:
  fixes f :: "_ \<Rightarrow> ('a :: ordered_ab_group_add)"
  shows "mono_dec_on f A \<longleftrightarrow> mono_on (\<lambda>x. -f x) A"
  unfolding mono_on_def mono_dec_on_def by simp

lemma mono_dec_on_UNIV[simp]:
    "mono_dec_on f UNIV = mono_dec f"
  unfolding mono_dec_on_def mono_dec_def by simp

subsection {* Strictly monotonically decreasing on a set *}

definition strict_mono_dec_on where
  "strict_mono_dec_on f A  \<longleftrightarrow> (\<forall>x y. x \<in> A \<longrightarrow> y \<in> A \<longrightarrow> x < y \<longrightarrow> f x > f y)"

lemma strict_mono_dec_onI:
  assumes "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x < y \<Longrightarrow> f x > f y"
  shows "strict_mono_dec_on f A"
  using assms unfolding strict_mono_dec_on_def by simp

lemma strict_mono_dec_onD:
  assumes "strict_mono_dec_on f A"
  shows "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x < y \<Longrightarrow> f x > f y"
  using assms unfolding strict_mono_dec_on_def by simp

lemma strict_mono_dec_on_subset: "strict_mono_dec_on f B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> strict_mono_dec_on f A"
  by (blast intro: strict_mono_dec_onI dest: strict_mono_dec_onD)

lemma strict_mono_dec_on_strict_mono_on_conv:
  fixes f :: "_ \<Rightarrow> ('a :: ordered_ab_group_add)"
  shows "strict_mono_dec_on f A \<longleftrightarrow> strict_mono_on (\<lambda>x. -f x) A"
  unfolding strict_mono_on_def strict_mono_dec_on_def by simp

lemma strict_mono_dec_on_UNIV[simp]: "strict_mono_dec_on f UNIV = strict_mono_dec f"
  unfolding strict_mono_dec_on_def strict_mono_dec_def by simp

section {* Monotonicity of polynomials *}

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

lemma pderiv_ge_0_imp_mono_on:
  assumes "connected A" "\<forall>x\<in>A. poly (pderiv p) x \<ge> (0::real)"
  shows "mono_on (poly p) A"
proof (rule mono_onI)
  fix x y assume "x \<in> A" "y \<in> A" "x \<le> y"
  with `connected A` have "{x<..<y} \<subseteq> A" by (intro connected_contains_Ioo)
  with `x \<le> y` and assms(2) show "poly p x \<le> poly p y"
    by (intro poly_deriv_ge_0) auto
qed

lemma pderiv_ge_0_imp_strict_mono_on:
  assumes "connected A" "pderiv p \<noteq> 0" "\<forall>x\<in>A. poly (pderiv p) x \<ge> (0::real)"
  shows "strict_mono_on (poly p) A"
proof (rule strict_mono_onI)
  fix x y assume "x \<in> A" "y \<in> A" "x < y"
  with `connected A` have "{x<..<y} \<subseteq> A" by (intro connected_contains_Ioo)
  with `x < y` and assms(2,3) show "poly p x < poly p y"
    by (intro poly_deriv_ge_0') auto
qed

lemma pderiv_ge_0_imp_mono:
    "(\<forall>x. poly (pderiv p) x \<ge> (0::real)) \<Longrightarrow> mono (poly p) "
  by (intro monoI poly_deriv_ge_0) auto

lemma pderiv_ge_0_imp_strict_mono:
    "pderiv p \<noteq> 0 \<Longrightarrow> (\<forall>x. poly (pderiv p) x \<ge> (0::real)) \<Longrightarrow> strict_mono (poly p) "
  by (intro strict_monoI poly_deriv_ge_0') auto

lemma pderiv_le_0_imp_mono_dec_on:
    "connected A \<Longrightarrow> (\<forall>x\<in>A. poly (pderiv p) x \<le> (0::real)) \<Longrightarrow> mono_dec_on (poly p) A"
  apply (subst mono_dec_on_mono_on_conv, subst poly_minus[symmetric])
  apply (intro pderiv_ge_0_imp_mono_on)
  apply (simp_all add: pderiv_minus)
  done

lemma pderiv_ge_0_imp_strict_mono_dec_on:
    "connected A \<Longrightarrow> pderiv p \<noteq> 0 \<Longrightarrow> (\<forall>x\<in>A. poly (pderiv p) x \<le> (0::real)) \<Longrightarrow> strict_mono_dec_on (poly p) A"
  apply (subst strict_mono_dec_on_strict_mono_on_conv, subst poly_minus[symmetric])
  apply (intro pderiv_ge_0_imp_strict_mono_on)
  apply (simp_all add: pderiv_minus)
  done

lemma pderiv_le_0_imp_mono_dec:
    "(\<forall>x. poly (pderiv p) x \<le> (0::real)) \<Longrightarrow> mono_dec (poly p) "
  apply (subst mono_dec_mono_conv, subst poly_minus[symmetric])
  apply (intro pderiv_ge_0_imp_mono)
  apply (simp add: pderiv_minus)
  done

lemma pderiv_ge_0_imp_strict_mono_dec:
    "pderiv p \<noteq> 0 \<Longrightarrow> (\<forall>x. poly (pderiv p) x \<le> (0::real)) \<Longrightarrow> strict_mono_dec (poly p) "
  apply (subst strict_mono_dec_strict_mono_conv, subst poly_minus[symmetric])
  apply (intro pderiv_ge_0_imp_strict_mono)
  apply (simp_all add: pderiv_minus)
  done

end
