theory Misc_Polynomial
imports "~~/src/HOL/Library/Poly_Deriv" Misc Misc_Analysis
begin

section {* General simplification lemmas *}

lemma degree_power_eq:
  "(p::('a::idom) poly) \<noteq> 0 \<Longrightarrow> degree (p^n) = n * degree p"
  by (induction n, simp_all add: degree_mult_eq)

lemma poly_altdef: "poly p (x::real) = (\<Sum>i\<le>degree p. coeff p i * x ^ i)"
proof (induction p rule: pCons_induct)
  case (pCons a p)
    show ?case
    proof (cases "p = 0")
      case False
      let ?p' = "pCons a p"
      note poly_pCons[of a p x]
      also note pCons.IH
      also have "a + x * (\<Sum>i\<le>degree p. coeff p i * x ^ i) = 
                 coeff ?p' 0 * x^0 + (\<Sum>i\<le>degree p. coeff ?p' (Suc i) * x^Suc i)" 
          by (simp add: field_simps setsum_right_distrib coeff_pCons)
      also note setsum_atMost_Suc_shift[symmetric]
      also note degree_pCons_eq[OF `p \<noteq> 0`, of a, symmetric]
      finally show ?thesis .
   qed simp
qed simp

lemma pderiv_div:
  assumes [simp]: "q dvd p" "q \<noteq> 0"
  shows "pderiv (p div q) = (q * pderiv p - p * pderiv q) div (q * q)"
        "q*q dvd (q * pderiv p - p * pderiv q)"
proof-
  note pderiv_mult[of q "p div q"]
  also have "q * (p div q) = p" by (simp add: dvd_mult_div_cancel)
  finally have "q * pderiv (p div q) = q * pderiv p div q - p * pderiv q div q"
      by (simp add: algebra_simps dvd_div_mult[symmetric]) 
  also have "... = (q * pderiv p - p * pderiv q) div q"
      by (rule div_diff, simp_all)
  finally have A: "pderiv (p div q) * q div q = 
                   (q * pderiv p - p * pderiv q) div q div q" 
      by (simp add: algebra_simps)
  thus "pderiv (p div q) = (q * pderiv p - p * pderiv q) div (q * q)" 
        by (simp add: algebra_simps poly_div_mult_right) 
  from assms obtain r where "p = q * r" unfolding dvd_def by blast
  hence "q * pderiv p - p * pderiv q = (q * q) * pderiv r" 
      by (simp add: algebra_simps pderiv_mult)
  thus "q*q dvd (q * pderiv p - p * pderiv q)" by simp
qed


section {* Divisibility of polynomials *}

text {*
  Two polynomials that are coprime have no common roots.
*}
lemma coprime_imp_no_common_roots:
  assumes "coprime p q"
  shows "\<And>x. \<not>(poly p x = 0 \<and> poly q x = 0)"
proof(clarify)
  fix x assume "poly p x = 0" "poly q x = 0"
  hence "[:-x,1:] dvd p" "[:-x,1:] dvd q" 
      by (simp_all add: poly_eq_0_iff_dvd)
  hence "[:-x,1:] dvd gcd p q" by simp
  hence "poly (gcd p q) x = 0" by (simp add: poly_eq_0_iff_dvd)
  moreover from assms have "poly (gcd p q) x = 1" by simp
  ultimately show False by simp
qed

text {*
  Dividing two polynomials by their gcd makes them coprime.
*}
lemma div_gcd_coprime_poly:
  assumes "(p :: ('a::field) poly) \<noteq> 0 \<or> q \<noteq> 0" 
  defines [simp]: "d \<equiv> gcd p q"
  shows "coprime (p div d) (q div d)"
proof-
  let ?d' = "gcd (p div d) (q div d)"
  from assms have [simp]: "d \<noteq> 0" by simp
  {
    fix r assume "r dvd (p div d)" "r dvd (q div d)"
    then obtain s t where "p div d = r * s" "q div d = r * t"
        unfolding dvd_def by auto
    hence "d * (p div d) = d * (r * s)" "d * (q div d) = d * (r * t)" by simp_all
    hence A: "p = s * (r * d)" "q = t * (r * d)"
        by (auto simp add: algebra_simps dvd_mult_div_cancel)
    have "r * d dvd p" "r * d dvd q" by (subst A, rule dvd_triv_right)+
    hence "d * r dvd d * 1" by (simp add: algebra_simps)
    hence "r dvd 1" using `d \<noteq> 0` by (subst (asm) dvd_mult_cancel_left, auto)
  }
  hence A: "?d' dvd 1" by simp
  from assms(1) have "p div d \<noteq> 0 \<or> q div d \<noteq> 0" by (auto simp: dvd_div_eq_mult)
  hence B: "coeff ?d' (degree ?d') = coeff 1 (degree 1)"
      using poly_gcd_monic[of "p div d" "q div d"] by simp
  from poly_dvd_antisym[OF B A one_dvd] show ?thesis .
qed

lemma poly_div:
  assumes "poly q x \<noteq> 0" and "q dvd p"
  shows "poly (p div q) x = poly p x / poly q x"
proof-
  from assms have [simp]: "q \<noteq> 0" by force
  have "poly q x * poly (p div q) x = poly (q * (p div q)) x" by simp
  also have "q * (p div q) = p" 
      using assms by (simp add: div_mult_swap) 
  finally show "poly (p div q) x = poly p x / poly q x" 
      using assms by (simp add: field_simps)
qed


text {*
  A function that gives witnesses for Bezout's lemma for polynomials.
*}
function bezw_poly where
  "bezw_poly (p::('a::field) poly) q = 
      (if q = 0 then ([:inverse (coeff p (degree p)):], 0)
                else (case bezw_poly q (p mod q) of 
                        (r,s) \<Rightarrow> (s, r - s * (p div q))))"
by (pat_completeness, simp_all)
termination by (relation "measure (\<lambda>(x, y). if y = 0 then 0 else Suc (degree y))")
               (auto dest: degree_mod_less)
declare bezw_poly.simps[simp del]

text {*
  Bezout's lemma for polynomials.
*}
lemma bezout_poly:
  "gcd p q = fst (bezw_poly p q) * p + snd (bezw_poly p q) * q"
proof (induction p q rule: gcd_poly.induct)
  case (goal1 p)
    show ?case by (subst bezw_poly.simps, simp add: gcd_poly.simps(1))
next
  case (goal2 q p)
    let ?b = "bezw_poly q (p mod q)"
    let ?b' = "bezw_poly p q"
    
    from goal2 have b'_b: "fst ?b' = snd ?b" 
                          "snd ?b' = fst ?b - snd ?b * (p div q)"
        by (subst bezw_poly.simps, simp split: prod.split)+
    hence "fst ?b' * p + snd ?b' * q =
                snd ?b * p + (fst ?b - snd ?b * (p div q)) * q" by simp
    also have "... = fst ?b * q + snd ?b * (p - p div q * q)" 
        by (simp add: algebra_simps) 
    also have "p - p div q * q = p mod q" 
        using mod_div_equality[of p q] by (simp add: algebra_simps)
    also have "fst ?b * q + snd ?b * (p mod q) = gcd q (p mod q)"
        using goal2 by simp
    also have "... = gcd p q"
        using goal2 by (subst gcd_poly.simps(2)[of q p], simp_all)
    finally show ?case ..
qed

lemma bezout_poly': "\<exists>r s. gcd (p::('a::field) poly) q = r*p+s*q"
    using bezout_poly by blast


(* TODO: make this less ugly *)
lemma poly_div_gcd_squarefree_aux:
  assumes "pderiv (p::('a::real_normed_field) poly) \<noteq> 0"
  defines "d \<equiv> gcd p (pderiv p)"
  shows "coprime (p div d) (pderiv (p div d))" and
        "\<And>x. poly (p div d) x = 0 \<longleftrightarrow> poly p x = 0"
proof-
  from bezout_poly' obtain r s where rs: "d = r * p + s * pderiv p" 
      unfolding d_def by blast
  def t \<equiv> "p div d" 
  def [simp]: p' \<equiv> "pderiv p"
  def [simp]: d' \<equiv> "pderiv d"
  def u \<equiv> "p' div d"
  have A: "p = t * d" and B: "p' = u * d" 
      by (simp_all add: t_def u_def dvd_mult_div_cancel d_def algebra_simps)
  from poly_squarefree_decomp[OF assms(1) A B[unfolded p'_def] rs]
      show "\<And>x. poly (p div d) x = 0 \<longleftrightarrow> poly p x = 0" by (auto simp: t_def)

  from rs have C: "s*t*d' = d * (1 - r*t - s*pderiv t)" 
      by (simp add: A B algebra_simps pderiv_mult)
  from assms have [simp]: "p \<noteq> 0" "d \<noteq> 0" "t \<noteq> 0" 
      by (force, force, subst (asm) A, force)

  have "\<And>x. \<lbrakk>x dvd t; x dvd (pderiv t)\<rbrakk> \<Longrightarrow> x dvd 1"
  proof-
    fix x assume "x dvd t" "x dvd (pderiv t)"
    then obtain v w where vw: 
        "t = x*v" "pderiv t = x*w" unfolding dvd_def by blast
    def [simp]: x' \<equiv> "pderiv x" and [simp]: v' \<equiv> "pderiv v"
    from vw have "x*v' + v*x' = x*w" by (simp add: pderiv_mult)
    hence "v*x' = x*(w - v')" by (simp add: algebra_simps)
    hence "x dvd v*pderiv x" by simp
    then obtain y where y: "v*x' = x*y" unfolding dvd_def by force
    from `t \<noteq> 0` and vw have "x \<noteq> 0" by simp

    have x_pow_n_dvd_d: "\<And>n. x^n dvd d"
    proof-
      fix n show "x ^ n dvd d"
      proof (induction n, simp, rename_tac n, case_tac n)
        fix n assume "n = (0::nat)"
        from vw and C have "d = x*(d*r*v + d*s*w + s*v*d')" 
            by (simp add: algebra_simps)
        with `n = 0` show "x^Suc n dvd d" by (force intro: dvdI)
      next
        fix n n' assume IH: "x^n dvd d" and "n = Suc n'"
        hence [simp]: "Suc n' = n" "x * x^n' = x^n" by simp_all
        def c \<equiv> "[:of_nat n:] :: 'a poly"
        from pderiv_power_Suc[of x n']
            have [simp]: "pderiv (x^n) = c*x^n' * x'" unfolding c_def 
            by (simp add: real_eq_of_nat)

        from IH obtain z where d: "d = x^n * z" unfolding dvd_def by blast
        def [simp]: z' \<equiv> "pderiv z"
        from d `d \<noteq> 0` have "x^n \<noteq> 0" "z \<noteq> 0" by force+
        from C d have "x^n*z = z*r*v*x^Suc n + z*s*c*x^n*(v*x') +
                          s*v*z'*x^Suc n + s*z*(v*x')*x^n + s*z*v'*x^Suc n"
            by (simp add: algebra_simps vw pderiv_mult)
        also have "... = x^n*(x * (z*r*v + z*s*c*y + s*v*z' + s*z*y + s*z*v'))"
            by (simp only: y, simp add: algebra_simps)
        finally have "z = x*(z*r*v+z*s*c*y+s*v*z'+s*z*y+s*z*v')"
             using `x^n \<noteq> 0` by force
        hence "x dvd z" by (metis dvd_triv_left) 
        with d show "x^Suc n dvd d" by simp
     qed
   qed

   have "degree x = 0" 
   proof (cases "degree x", simp)
     case (Suc n)
       hence "x \<noteq> 0" by auto
       with Suc have "degree (x ^ (Suc (degree d))) > degree d" 
           by (subst degree_power_eq, simp_all)
       moreover from x_pow_n_dvd_d[of "Suc (degree d)"] and `d \<noteq> 0`
           have "degree (x^Suc (degree d)) \<le> degree d" 
                by (simp add: dvd_imp_degree_le)
       ultimately show ?thesis by simp
    qed
    then obtain c where [simp]: "x = [:c:]" by (cases x, simp split: split_if_asm)
    moreover from `x \<noteq> 0` have "c \<noteq> 0" by simp
    ultimately show "x dvd 1" using dvdI[of 1 x "[:inverse c:]"] 
        by (simp add: one_poly_def)
  qed

  thus "coprime t (pderiv t)"
      by (force intro: poly_gcd_unique[of 1 t "pderiv t"])
qed

text {*
  Dividing a polynomial by its gcd with its derivative yields 
  a squarefree polynomial with the same roots.
*}
lemma poly_div_gcd_squarefree:
  assumes "(p :: ('a::real_normed_field) poly) \<noteq> 0"
  defines "d \<equiv> gcd p (pderiv p)"
  shows "coprime (p div d) (pderiv (p div d))" (is ?A) and
        "\<And>x. poly (p div d) x = 0 \<longleftrightarrow> poly p x = 0" (is "\<And>x. ?B x")
proof-
  have "?A \<and> (\<forall>x. ?B x)"
  proof (cases "pderiv p = 0")
    case False
      from poly_div_gcd_squarefree_aux[OF this] show ?thesis
          unfolding d_def by auto
  next
    case True
      then obtain c where [simp]: "p = [:c:]" using pderiv_iszero by blast
      from assms(1) have "c \<noteq> 0" by simp
      from True have "d = smult (inverse c) p"
          by (simp add: d_def gcd_poly.simps(1))
      hence "p div d = [:c:]" using `c \<noteq> 0` 
          by (simp add: div_smult_right assms(1) one_poly_def[symmetric]) 
      thus ?thesis using `c \<noteq> 0`
        by (simp add: gcd_poly.simps(1) one_poly_def)   
  qed
  thus ?A and "\<And>x. ?B x" by simp_all
qed



section {* Sign changes of a polynomial *}

text {*
  If a polynomial has different signs at a position, it has a root inbetween.
*}
lemma poly_different_sign_imp_root:
  assumes "a < b" and "sgn (poly p a) \<noteq> sgn (poly p (b::real))"
  shows "\<exists>x. a \<le> x \<and> x \<le> b \<and> poly p x = 0"
proof (cases "poly p a = 0 \<or> poly p b = 0")
  case True
    thus ?thesis using assms(1) 
        by (elim disjE, rule_tac exI[of _ a], simp,
                        rule_tac exI[of _ b], simp)
next
  case False
    hence [simp]: "poly p a \<noteq> 0" "poly p b \<noteq> 0" by simp_all
    show ?thesis
    proof (cases "poly p a < 0")
      case True
        hence "sgn (poly p a) = -1" by simp
        with assms True have "poly p b > 0"
            by (auto simp: sgn_real_def split: split_if_asm)
        from poly_IVT_pos[OF `a < b` True this] guess x ..
        thus ?thesis by (intro exI[of _ x], simp)
    next
      case False
        hence "poly p a > 0" by (simp add: not_less less_eq_real_def)
        hence "sgn (poly p a) = 1"  by simp
        with assms False have "poly p b < 0"
            by (auto simp: sgn_real_def not_less 
                           less_eq_real_def split: split_if_asm)
        from poly_IVT_neg[OF `a < b` `poly p a > 0` this] guess x ..
        thus ?thesis by (intro exI[of _ x], simp)
    qed
qed

lemma no_roots_inbetween_imp_same_sign:
  assumes "a < b" "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> poly p x \<noteq> (0::real)"
  shows "sgn (poly p a) = sgn (poly p b)"
proof (rule ccontr)
  assume "sgn (poly p a) \<noteq> sgn (poly p b)"
  from  poly_different_sign_imp_root[OF `a < b` this] guess x ..
  thus False using assms(2) by auto
qed



section {* Limits of polynomials *}

lemma poly_neighbourhood_without_roots:
  assumes "(p :: real poly) \<noteq> 0"
  shows "eventually (\<lambda>x. poly p x \<noteq> 0) (at x\<^sub>0)"
proof (subst eventually_at, subst dist_real_def)
  {fix \<epsilon> :: real assume "\<epsilon> > 0"
  have fin: "finite {x. \<bar>x-x\<^sub>0\<bar> < \<epsilon> \<and> x \<noteq> x\<^sub>0 \<and> poly p x = 0}"
      using poly_roots_finite[OF assms] by simp
  with `\<epsilon> > 0`have "\<exists>\<delta>>0. \<delta>\<le>\<epsilon> \<and> (\<forall>x. \<bar>x-x\<^sub>0\<bar> < \<delta> \<and> x \<noteq> x\<^sub>0 \<longrightarrow> poly p x \<noteq> 0)"
  proof (induction "card {x. \<bar>x-x\<^sub>0\<bar> < \<epsilon> \<and> x \<noteq> x\<^sub>0 \<and> poly p x = 0}" 
         arbitrary: \<epsilon> rule: less_induct)
  case (less \<epsilon>)
  let ?A = "{x. \<bar>x - x\<^sub>0\<bar> < \<epsilon> \<and> x \<noteq> x\<^sub>0 \<and> poly p x = 0}"
  show ?case
    proof (cases "card ?A")
    case 0
      hence "?A = {}" using less by auto
      thus ?thesis using less(2) by (rule_tac exI[of _ \<epsilon>], auto)
    next
    case (Suc _)
      with less(3) have "{x. \<bar>x - x\<^sub>0\<bar> < \<epsilon> \<and> x \<noteq> x\<^sub>0 \<and> poly p x = 0} \<noteq> {}" by force
      then obtain x where x_props: "\<bar>x - x\<^sub>0\<bar> < \<epsilon>" "x \<noteq> x\<^sub>0" "poly p x = 0" by blast
      def \<epsilon>' \<equiv> "\<bar>x - x\<^sub>0\<bar> / 2"
      have "\<epsilon>' > 0" "\<epsilon>' < \<epsilon>" unfolding \<epsilon>'_def using x_props by simp_all
      from x_props(1,2) and `\<epsilon> > 0`
          have "x \<notin> {x'. \<bar>x' - x\<^sub>0\<bar> < \<epsilon>' \<and> x' \<noteq> x\<^sub>0 \<and> poly p x' = 0}" (is "_ \<notin> ?B")
          by (auto simp: \<epsilon>'_def)
      moreover from x_props 
          have "x \<in> {x. \<bar>x - x\<^sub>0\<bar> < \<epsilon> \<and> x \<noteq> x\<^sub>0 \<and> poly p x = 0}" by blast
      ultimately have "?B \<subset> ?A" by auto
      hence "card ?B < card ?A" "finite ?B" 
          by (rule psubset_card_mono[OF less(3)], 
              blast intro: finite_subset[OF _ less(3)])
      from less(1)[OF this(1) `\<epsilon>' > 0` this(2)]
          show ?thesis using `\<epsilon>' < \<epsilon>` by force
    qed
  qed}
  from this[of 1] 
    show "\<exists>d>0. \<forall>x\<in>UNIV. x \<noteq> x\<^sub>0 \<and> \<bar>x - x\<^sub>0\<bar> < d \<longrightarrow> poly p x \<noteq> 0" by auto
qed


lemma poly_neighbourhood_same_sign:
  assumes "poly p (x\<^sub>0 :: real) \<noteq> 0"
  shows "eventually (\<lambda>x. sgn (poly p x) = sgn (poly p x\<^sub>0)) (at x\<^sub>0)"
proof (rule eventually_mono)
  have cont: "isCont (\<lambda>x. sgn (poly p x)) x\<^sub>0"
      by (rule isCont_sgn, rule poly_isCont, rule assms)
  thus "eventually (\<lambda>x. \<bar>sgn (poly p x) - sgn (poly p x\<^sub>0)\<bar> < 1) (at x\<^sub>0)"
      by (auto simp: isCont_def tendsto_iff dist_real_def)
qed (auto simp add: sgn_real_def)

lemma poly_lhopital:
  assumes "poly p (x::real) = 0" "poly q x = 0" "q \<noteq> 0"
  assumes "(\<lambda>x. poly (pderiv p) x / poly (pderiv q) x) -- x --> y"
  shows "(\<lambda>x. poly p x / poly q x) -- x --> y"
using assms
proof (rule_tac lhopital)
  have "isCont (poly p) x" "isCont (poly q) x" by simp_all
  with assms(1,2) show "poly p -- x --> 0" "poly q -- x --> 0" 
       by (simp_all add: isCont_def)
  from `q \<noteq> 0` and `poly q x = 0` have "pderiv q \<noteq> 0"
      by (auto dest: pderiv_iszero)
  from poly_neighbourhood_without_roots[OF this]
      show "eventually (\<lambda>x. poly (pderiv q) x \<noteq> 0) (at x)" .
qed (auto intro: poly_DERIV poly_neighbourhood_without_roots)


lemma poly_roots_bounds:
  assumes "p \<noteq> 0" 
  obtains l u
  where "l \<le> (u :: real)"
    and "poly p l \<noteq> 0"
    and "poly p u \<noteq> 0"
    and "{x. x > l \<and> x \<le> u \<and> poly p x = 0 } = {x. poly p x = 0}"
    and "\<And>x. x \<le> l \<Longrightarrow> sgn (poly p x) = sgn (poly p l)"
    and "\<And>x. x \<ge> u \<Longrightarrow> sgn (poly p x) = sgn (poly p u)"
proof
  from assms have "finite {x. poly p x = 0}" (is "finite ?roots")
      using poly_roots_finite by fast
  let ?roots' = "insert 0 ?roots"

  def l \<equiv> "Min ?roots' - 1"
  def u \<equiv> "Max ?roots' + 1"

  from `finite ?roots` have A: "finite ?roots'" "?roots' \<noteq> {}" by auto
  from min_max.Inf_le_Sup[OF A] 
      show "l \<le> u" unfolding l_def u_def by simp
  from Min_le[OF A(1)] have l_props: "\<And>x. x\<le>l \<Longrightarrow> poly p x \<noteq> 0"
      by (fastforce simp: l_def)
  from Max_ge[OF A(1)] have u_props: "\<And>x. x\<ge>u \<Longrightarrow> poly p x \<noteq> 0"
      by (fastforce simp: u_def)
  from l_props u_props show [simp]: "poly p l \<noteq> 0" "poly p u \<noteq> 0" by auto

  from l_props have "\<And>x. poly p x = 0 \<Longrightarrow> x > l" by (metis not_le)
  moreover from u_props have "\<And>x. poly p x = 0 \<Longrightarrow> x \<le> u" by (metis linear)
  ultimately show "{x. x > l \<and> x \<le> u \<and> poly p x = 0} = ?roots" by auto

  {
    fix x assume A: "x < l" "sgn (poly p x) \<noteq> sgn (poly p l)"
    with poly_IVT_pos[OF A(1), of p] poly_IVT_neg[OF A(1), of p] A(2) 
        have False by (auto split: split_if_asm
                         simp: sgn_real_def l_props not_less less_eq_real_def)
  }
  thus "\<And>x. x \<le> l \<Longrightarrow> sgn (poly p x) = sgn (poly p l)"
      by (case_tac "x = l", auto simp: less_eq_real_def)
      
  {
    fix x assume A: "x > u" "sgn (poly p x) \<noteq> sgn (poly p u)"
    with u_props poly_IVT_neg[OF A(1), of p] poly_IVT_pos[OF A(1), of p] A(2) 
        have False by (auto split: split_if_asm
                         simp: sgn_real_def l_props not_less less_eq_real_def)
  }
  thus "\<And>x. x \<ge> u \<Longrightarrow> sgn (poly p x) = sgn (poly p u)"
      by (case_tac "x = u", auto simp: less_eq_real_def)
qed



definition poly_inf :: "('a::real_normed_vector) poly \<Rightarrow> 'a" where 
  "poly_inf p \<equiv> sgn (coeff p (degree p))"
definition poly_neg_inf :: "('a::real_normed_vector) poly \<Rightarrow> 'a" where 
  "poly_neg_inf p \<equiv> if even (degree p) then sgn (coeff p (degree p))
                                       else -sgn (coeff p (degree p))"
lemma poly_inf_0_iff[simp]: 
    "poly_inf p = 0 \<longleftrightarrow> p = 0" "poly_neg_inf p = 0 \<longleftrightarrow> p = 0"
    by (auto simp: poly_inf_def poly_neg_inf_def sgn_zero_iff) 

lemma poly_inf_mult[simp]: 
  fixes p :: "('a::real_normed_field) poly"
  shows "poly_inf (p*q) = poly_inf p * poly_inf q"
        "poly_neg_inf (p*q) = poly_neg_inf p * poly_neg_inf q"
unfolding poly_inf_def poly_neg_inf_def
by ((cases "p = 0 \<or> q = 0",auto simp: sgn_zero_iff
         degree_mult_eq[of p q] coeff_mult_degree_sum sgn_mult)[])+

 
lemma poly_neq_0_at_infinity:
  assumes "(p :: real poly) \<noteq> 0"
  shows "eventually (\<lambda>x. poly p x \<noteq> 0) at_infinity"
proof-
  from poly_roots_bounds[OF assms] guess l u .
  note lu_props = this
  def b \<equiv> "max (-l) u"
  show ?thesis
  proof (subst eventually_at_infinity, rule exI[of _ b], clarsimp)
    fix x assume A: "\<bar>x\<bar> \<ge> b" and B: "poly p x = 0"
    show False
    proof (cases "x \<ge> 0")
      case True
        with A have "x \<ge> u" unfolding b_def by simp
        with lu_props(3, 6) show False by (metis sgn_zero_iff B)
    next
      case False
        with A have "x \<le> l" unfolding b_def by simp
        with lu_props(2, 5) show False by (metis sgn_zero_iff B)
    qed
  qed
qed


lemma x_pow_n_limit: 
  assumes "n \<ge> 1"
  shows "LIM (x::real) at_top. x^n :> at_top"
proof (simp only: filterlim_at_top eventually_at_top_linorder, clarify)
  fix b :: real
  let ?x\<^sub>0 = "max b 1"
  show "\<exists>x\<^sub>0. \<forall>x\<ge>x\<^sub>0. x ^ n \<ge> b"
  proof (rule exI[of _ ?x\<^sub>0], clarify)
    fix x assume "x \<ge> max b 1"
    have "b \<le> ?x\<^sub>0" by simp
    also from power_increasing[OF assms, of ?x\<^sub>0] 
        have "... \<le> ?x\<^sub>0 ^ n" by simp
    also from power_mono[OF `x \<ge> ?x\<^sub>0`] have "... \<le> x ^ n" by simp
    finally show "b \<le> x ^ n" .
  qed
qed

lemma x_pow_n_limit_at_top: 
  assumes "n \<ge> 1"
  shows "LIM (x::real) at_top. x^n :> at_top"
proof (simp only: filterlim_at_top eventually_at_top_linorder, clarify)
  fix b :: real
  let ?x\<^sub>0 = "max b 1"
  show "\<exists>x\<^sub>0. \<forall>x\<ge>x\<^sub>0. x ^ n \<ge> b"
  proof (rule exI[of _ ?x\<^sub>0], clarify)
    fix x assume "x \<ge> max b 1"
    have "b \<le> ?x\<^sub>0" by simp
    also from power_increasing[OF assms, of ?x\<^sub>0] 
        have "... \<le> ?x\<^sub>0 ^ n" by simp
    also from power_mono[OF `x \<ge> ?x\<^sub>0`] have "... \<le> x ^ n" by simp
    finally show "b \<le> x ^ n" .
  qed
qed

lemma x_pow_n_limit_at_bot[intro]: 
  assumes "n \<ge> 1"
  shows "even n \<Longrightarrow> LIM (x::real) at_bot. x^n :> at_top"
    and "odd n \<Longrightarrow> LIM (x::real) at_bot. x^n :> at_bot"
proof-
  assume "even n"
  show "LIM (x::real) at_bot. x^n :> at_top"
  proof (subst filterlim_cong, rule refl, rule refl)
    from `even n` show "eventually (\<lambda>x::real. x^n = (-x)^n) at_bot" 
        by (simp add: neg_power_if)
    show "LIM (x::real) at_bot. (-x)^n :> at_top" using assms
        by (simp add: filterlim_at_bot_mirror x_pow_n_limit_at_top)
  qed
next
  assume "odd n"
  show "LIM (x::real) at_bot. x^n :> at_bot"
  proof (subst filterlim_cong, rule refl, rule refl)
    from `odd n` show "eventually (\<lambda>x::real. x^n = -((-x)^n)) at_bot" 
        by (simp add: neg_power_if)
    show "LIM (x::real) at_bot. -((-x)^n) :> at_bot" using assms
        by (simp add: filterlim_at_bot_mirror filterlim_uminus_at_bot 
                      x_pow_n_limit_at_top)
  qed
qed



lemma poly_limit_aux:
  fixes p :: "real poly"
  defines "n \<equiv> degree p"
  shows "((\<lambda>x. poly p x / x ^ n) ---> coeff p n) at_infinity"
proof (subst filterlim_cong, rule refl, rule refl)
  show "eventually (\<lambda>x. poly p x / x^n = (\<Sum>i\<le>n. coeff p i / x^(n-i))) 
            at_infinity"
  proof (rule eventually_mono, clarify)
    show "eventually (\<lambda>x::real. x \<noteq> 0) at_infinity"
        by (simp add: eventually_at_infinity, rule exI[of _ 1], auto)
    fix x :: real assume [simp]: "x \<noteq> 0"
    show "poly p x / x ^ n = (\<Sum>i\<le>n. coeff p i / x ^ (n - i))"
        by (simp add: n_def setsum_divide_distrib power_diff poly_altdef)
  qed

  let ?a = "\<lambda>i. if i = n then coeff p n else 0"
  have "\<forall>i\<in>{..n}. ((\<lambda>x. coeff p i / x ^ (n - i)) ---> ?a i) at_infinity"
  proof
    fix i assume "i \<in> {..n}"
    hence "i \<le> n" by simp
    show "((\<lambda>x. coeff p i / x ^ (n - i)) ---> ?a i) at_infinity"
    proof (cases "i = n")
      case True 
        thus ?thesis by (intro tendstoI, subst eventually_at_infinity,
                         intro exI[of _ 1], simp add: dist_real_def)
    next
      case False
        hence "n - i > 0" using `i \<le> n` by simp
        from tendsto_inverse_0 and divide_real_def[of 1]
            have "((\<lambda>x. 1 / x :: real) ---> 0) at_infinity" by simp
        from tendsto_power[OF this, of "n - i"]
            have "((\<lambda>x::real. 1 / x ^ (n - i)) ---> 0) at_infinity" 
                using `n - i > 0` by (simp add: power_0_left power_one_over)
        from tendsto_mult_right_zero[OF this, of "coeff p i"]
            have "((\<lambda>x. coeff p i / x ^ (n - i)) ---> 0) at_infinity"
                by (simp add: field_simps)
        thus ?thesis using False by simp
    qed
  qed
  hence "((\<lambda>x. \<Sum>i\<le>n. coeff p i / x^(n-i)) ---> (\<Sum>i\<le>n. ?a i)) at_infinity"
      by (force intro: tendsto_setsum)
  also have "(\<Sum>i\<le>n. ?a i) = coeff p n" by (subst setsum_delta, simp_all)
  finally show "((\<lambda>x. \<Sum>i\<le>n. coeff p i / x^(n-i)) ---> coeff p n) at_infinity" .
qed



lemma poly_at_top_at_top:
  fixes p :: "real poly"
  assumes "degree p \<ge> 1" "coeff p (degree p) > 0"
  shows "LIM x at_top. poly p x :> at_top"
proof-
  let ?n = "degree p"
  def f \<equiv> "\<lambda>x::real. poly p x / x^?n" and g \<equiv> "\<lambda>x::real. x ^ ?n"

  from poly_limit_aux have "(f ---> coeff p (degree p)) at_top"
      using tendsto_mono at_top_le_at_infinity unfolding f_def by blast
  moreover from x_pow_n_limit_at_top assms 
      have "LIM x at_top. g x :> at_top" by (simp add: g_def)
  ultimately have "LIM x at_top. f x * g x :> at_top"
      using filterlim_tendsto_pos_mult_at_top assms by simp
  also have "eventually (\<lambda>x. f x * g x = poly p x) at_top"
      unfolding f_def g_def
      by (subst eventually_at_top_linorder, rule exI[of _ 1],
          simp add: poly_altdef field_simps setsum_right_distrib power_diff)
  note filterlim_cong[OF refl refl this]
  finally show ?thesis .
qed

lemma poly_at_bot_at_top:
  fixes p :: "real poly"
  assumes "degree p \<ge> 1" "coeff p (degree p) < 0"
  shows "LIM x at_top. poly p x :> at_bot"
proof-
  from poly_at_top_at_top[of "-p"] and assms 
      have "LIM x at_top. -poly p x :> at_top" by simp
  thus ?thesis by (simp add: filterlim_uminus_at_bot)
qed

lemma poly_lim_inf:
  "eventually (\<lambda>x::real. sgn (poly p x) = poly_inf p) at_top"
proof (cases "degree p \<ge> 1")
  case False
    hence "degree p = 0" by simp
    then obtain c where "p = [:c:]" by (cases p, auto split: split_if_asm)
    thus ?thesis
        by (simp add: eventually_at_top_linorder poly_inf_def)
next
  case True
    note deg = this
    let ?lc = "coeff p (degree p)"
    from True have "?lc \<noteq> 0" by force
    show ?thesis
    proof (cases "?lc > 0")
      case True
        from poly_at_top_at_top[OF deg this]
          obtain x\<^sub>0 where "\<And>x. x \<ge> x\<^sub>0 \<Longrightarrow> poly p x \<ge> 1"
              by (fastforce simp: filterlim_at_top 
                      eventually_at_top_linorder less_eq_real_def) 
        hence "\<And>x. x \<ge> x\<^sub>0 \<Longrightarrow> sgn (poly p x) = 1" by force
        thus ?thesis by (simp only: eventually_at_top_linorder poly_inf_def, 
                             intro exI[of _ x\<^sub>0], simp add: True)
    next
      case False
        hence "?lc < 0" using `?lc \<noteq> 0` by linarith
        from poly_at_bot_at_top[OF deg this]
          obtain x\<^sub>0 where "\<And>x. x \<ge> x\<^sub>0 \<Longrightarrow> poly p x \<le> -1"
              by (fastforce simp: filterlim_at_bot 
                      eventually_at_top_linorder less_eq_real_def) 
        hence "\<And>x. x \<ge> x\<^sub>0 \<Longrightarrow> sgn (poly p x) = -1" by force
        thus ?thesis by (simp only: eventually_at_top_linorder poly_inf_def, 
                             intro exI[of _ x\<^sub>0], simp add: `?lc < 0`)
    qed
qed

lemma poly_at_top_or_bot_at_bot:
  fixes p :: "real poly"
  assumes "degree p \<ge> 1" "coeff p (degree p) > 0"
  shows "LIM x at_bot. poly p x :> (if even (degree p) then at_top else at_bot)"
proof-
  let ?n = "degree p"
  def f \<equiv> "\<lambda>x::real. poly p x / x ^ ?n" and g \<equiv> "\<lambda>x::real. x ^ ?n"
  
  from poly_limit_aux have "(f ---> coeff p (degree p)) at_bot"
      using tendsto_mono at_bot_le_at_infinity by (force simp: f_def)
  moreover from x_pow_n_limit_at_bot assms
      have "LIM x at_bot. g x :> (if even (degree p) then at_top else at_bot)"
      by (simp add: g_def split: split_if_asm)
  ultimately have "LIM x at_bot. f x * g x :> 
                      (if even ?n then at_top else at_bot)"
      by (auto simp: assms intro: filterlim_tendsto_pos_mult_at_top 
                                  filterlim_tendsto_pos_mult_at_bot)
  also have "eventually (\<lambda>x. f x * g x = poly p x) at_bot"
      unfolding f_def g_def
      by (subst eventually_at_bot_linorder, rule exI[of _ "-1"],
          simp add: poly_altdef field_simps setsum_right_distrib power_diff)
  note filterlim_cong[OF refl refl this]
  finally show ?thesis .
qed


lemma poly_at_bot_or_top_at_bot:
  fixes p :: "real poly"
  assumes "degree p \<ge> 1" "coeff p (degree p) < 0"
  shows "LIM x at_bot. poly p x :> (if even (degree p) then at_bot else at_top)"
proof-
  from poly_at_top_or_bot_at_bot[of "-p"] and assms 
      have "LIM x at_bot. -poly p x :> 
                (if even (degree p) then at_top else at_bot)" by simp
  thus ?thesis by (auto simp: filterlim_uminus_at_bot)
qed

lemma poly_lim_neg_inf:
  "eventually (\<lambda>x::real. sgn (poly p x) = poly_neg_inf p) at_bot"
proof (cases "degree p \<ge> 1")
  case False
    hence "degree p = 0" by simp
    then obtain c where "p = [:c:]" by (cases p, auto split: split_if_asm)
    thus ?thesis
        by (simp add: eventually_at_bot_linorder poly_neg_inf_def)
next
  case True
    note deg = this
    let ?lc = "coeff p (degree p)"
    from True have "?lc \<noteq> 0" by force
    show ?thesis
    proof (cases "?lc > 0")
      case True
        note lc_pos = this
        show ?thesis
        proof (cases "even (degree p)")
          case True
            from poly_at_top_or_bot_at_bot[OF deg lc_pos] and True
              obtain x\<^sub>0 where "\<And>x. x \<le> x\<^sub>0 \<Longrightarrow> poly p x \<ge> 1"
                by (fastforce simp add: filterlim_at_top filterlim_at_bot
                        eventually_at_bot_linorder less_eq_real_def)
                hence "\<And>x. x \<le> x\<^sub>0 \<Longrightarrow> sgn (poly p x) = 1" by force
              thus ?thesis 
                by (simp add: True eventually_at_bot_linorder poly_neg_inf_def, 
                    intro exI[of _ x\<^sub>0], simp add: lc_pos)
       next
          case False
            from poly_at_top_or_bot_at_bot[OF deg lc_pos] and False
              obtain x\<^sub>0 where "\<And>x. x \<le> x\<^sub>0 \<Longrightarrow> poly p x \<le> -1"
                by (fastforce simp add: filterlim_at_bot filterlim_at_bot
                        eventually_at_bot_linorder less_eq_real_def)
                hence "\<And>x. x \<le> x\<^sub>0 \<Longrightarrow> sgn (poly p x) = -1" by force
              thus ?thesis 
                by (simp add: False eventually_at_bot_linorder poly_neg_inf_def, 
                              intro exI[of _ x\<^sub>0], simp add: lc_pos)
      qed
    next
      case False
        hence lc_neg: "?lc < 0" using `?lc \<noteq> 0` by linarith
        show ?thesis
        proof (cases "even (degree p)")
          case True
            with poly_at_bot_or_top_at_bot[OF deg lc_neg]
              obtain x\<^sub>0 where "\<And>x. x \<le> x\<^sub>0 \<Longrightarrow> poly p x \<le> -1"
                  by (fastforce simp: filterlim_at_bot 
                          eventually_at_bot_linorder less_eq_real_def) 
              hence "\<And>x. x \<le> x\<^sub>0 \<Longrightarrow> sgn (poly p x) = -1" by force
              thus ?thesis 
                by (simp only: True eventually_at_bot_linorder poly_neg_inf_def, 
                               intro exI[of _ x\<^sub>0], simp add: lc_neg)
        next
          case False
            with poly_at_bot_or_top_at_bot[OF deg lc_neg]
              obtain x\<^sub>0 where "\<And>x. x \<le> x\<^sub>0 \<Longrightarrow> poly p x \<ge> 1"
                  by (fastforce simp: filterlim_at_top 
                          eventually_at_bot_linorder less_eq_real_def) 
              hence "\<And>x. x \<le> x\<^sub>0 \<Longrightarrow> sgn (poly p x) = 1" by force
              thus ?thesis 
                by (simp only: False eventually_at_bot_linorder poly_neg_inf_def, 
                               intro exI[of _ x\<^sub>0], simp add: lc_neg)
        qed
    qed
qed





section {* Sturm chain-specific stuff *}

lemma polys_inf_sign_thresholds:
  assumes "finite (ps :: real poly set)"
  obtains l u
  where "l \<le> u"
    and "\<And>p. \<lbrakk>p \<in> ps; p \<noteq> 0\<rbrakk> \<Longrightarrow> 
              {x. l < x \<and> x \<le> u \<and> poly p x = 0} = {x. poly p x = 0}"
    and "\<And>p x. \<lbrakk>p \<in> ps; x \<ge> u\<rbrakk> \<Longrightarrow> sgn (poly p x) = poly_inf p"
    and "\<And>p x. \<lbrakk>p \<in> ps; x \<le> l\<rbrakk> \<Longrightarrow> sgn (poly p x) = poly_neg_inf p"
proof-
  case goal1
  have "\<exists>l u. l \<le> u \<and> (\<forall>p x. p \<in> ps \<and> x \<ge> u \<longrightarrow> sgn (poly p x) = poly_inf p) \<and>
              (\<forall>p x. p \<in> ps \<and> x \<le> l \<longrightarrow> sgn (poly p x) = poly_neg_inf p)"
      (is "\<exists>l u. ?P ps l u")
  proof (induction rule: finite_subset_induct[OF assms(1), where A = UNIV], simp)
    case goal1
      show ?case by (intro exI[of _ 42], simp)
  next
    case (goal2 p ps)
      from goal2(4) obtain l u where lu_props: "?P ps l u" by blast
      from poly_lim_inf obtain u' 
          where u'_props: "\<forall>x\<ge>u'. sgn (poly p x) = poly_inf p"
          by (force simp add: eventually_at_top_linorder)
      from poly_lim_neg_inf obtain l' 
          where l'_props: "\<forall>x\<le>l'. sgn (poly p x) = poly_neg_inf p"
          by (force simp add: eventually_at_bot_linorder)
      show ?case
          by (rule exI[of _ "min l l'"], rule exI[of _ "max u u'"],
              insert lu_props l'_props u'_props, auto)
  qed
  then obtain l u where lu_props: "l \<le> u"
        "\<And>p x. p \<in> ps \<Longrightarrow> u \<le> x \<Longrightarrow> sgn (poly p x) = poly_inf p"
        "\<And>p x. p \<in> ps \<Longrightarrow> x \<le> l \<Longrightarrow> sgn (poly p x) = poly_neg_inf p" by blast
  moreover {
    fix p x assume A: "p \<in> ps" "p \<noteq> 0" "poly p x = 0"
    from A have "l < x" "x < u" 
        by (auto simp: not_le[symmetric] dest: lu_props(2,3))
  }
  note A = this
  have "\<And>p. p \<in> ps \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> 
                 {x. l < x \<and> x \<le> u \<and> poly p x = 0} = {x. poly p x = 0}" 
      by (auto dest: A)

  from goal1[OF lu_props(1) this lu_props(2,3)] show thesis .
qed


end
