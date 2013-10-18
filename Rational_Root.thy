theory Scratch
imports Main Real "~~/src/HOL/Library/Polynomial" Misc_Polynomial
begin

lemma floor_int: "x \<in> \<int> \<Longrightarrow> real (floor x) = x"
proof-
  assume "x \<in> \<int>" then obtain x' :: int where "x = real x'" 
      using Ints_cases unfolding real_of_int_def by blast
  thus ?thesis by simp
qed

lemma rational_roots_aux:
  fixes p :: "real poly" and c :: int and d :: int
  assumes d_nonzero: "d \<noteq> 0" and coprime: "coprime c d"
  assumes int_coeffs: "\<And>n. coeff p n \<in> \<int>"
  assumes zero: "poly p (c/d) = 0"
  defines [simp]: "n \<equiv> degree p"
  defines "a\<^sub>0 \<equiv> \<lfloor>coeff p 0\<rfloor>" and "a\<^sub>n \<equiv> \<lfloor>coeff p n\<rfloor>"
  shows "c dvd a\<^sub>0 \<and> d dvd a\<^sub>n"
proof (cases "n \<ge> 1")
  case False
    hence "p = [:coeff p 0:]" by (cases p, simp split: split_if_asm)
    hence "p = [:a\<^sub>0:]" unfolding a\<^sub>0_def by (simp add: floor_int[OF int_coeffs])
    with `poly p (c/d) = 0` have "a\<^sub>0 = 0" "a\<^sub>n = 0" by (simp_all add: a\<^sub>n_def)
    thus ?thesis by simp
next
  case True
    from int_coeffs have [simp]: "\<And>i. real \<lfloor>coeff p i\<rfloor> = coeff p i"
        by (simp add: floor_int)
    from int_coeffs have [simp]: 
        "coeff p 0 = real a\<^sub>0" "coeff p (degree p) = real a\<^sub>n"
        unfolding a\<^sub>0_def a\<^sub>n_def by simp_all

    from `poly p (c/d) = 0` have "0 = (\<Sum>i=0..n. coeff p i * (c/d) ^ i)"
        using poly_altdef by (simp add: atLeast0AtMost)
    hence "-coeff p 0 = (\<Sum>i=1..n. coeff p i * (c/d)^i)"
        by (subst (asm) setsum_head_Suc, simp_all)
    hence "-coeff p 0 * d^n = (\<Sum>i=1..n. coeff p i * (c/d)^i * d^n)"
        by (metis (no_types) setsum_left_distrib)
    also from `d \<noteq> 0` have "... = (\<Sum>i=1..n. coeff p i * c^i * d^(n - i))" 
        by (simp add: power_divide power_diff)
    also have "... = (\<Sum>i=1..n. coeff p i * (c^1 * c^(i - 1)) * d^(n - i))"
        by (subst power_add[symmetric], simp)
    also have "... = c * (\<Sum>i=1..n. coeff p i * c^(i - 1) * d^(n - i))"
        by (simp add: setsum_right_distrib field_simps)
    also have "... = c * (\<Sum>i=1..n. \<lfloor>coeff p i\<rfloor> * c^(i - 1) * d^(n - i))" by simp
    finally have "-a\<^sub>0 * d^n = c * (\<Sum>i=1..n. \<lfloor>coeff p i\<rfloor> * c^(i - 1) * d^(n - i))"
        by (subst real_of_int_inject[symmetric], simp)
    hence "c dvd a\<^sub>0 * d^n"  by (subst dvd_minus_iff[symmetric], force)
    with coprime have "c dvd a\<^sub>0" 
        by (blast dest: coprime_dvd_mult_int coprime_exp_int)

    from `poly p (c/d) = 0` have "0 = (\<Sum>i=0..n. coeff p i * (c/d) ^ i)"
        using poly_altdef by (simp add: atLeast0AtMost)
    also from `n \<ge> 1` have "n = Suc (n - 1)" by simp
    finally have "-coeff p n * (c/d)^n = (\<Sum>i=0..n - 1. coeff p i * (c/d)^i)"
        using `n \<ge> 1` by (subst (asm) setsum_cl_ivl_Suc, 
                          simp only: `n = Suc (n - 1)`[symmetric], simp)
    hence "-coeff p n * (c/d)^n * d^n = (\<Sum>i=0..n - 1. coeff p i * (c/d)^i) * d^n"
        by simp
    with `d \<noteq> 0` have "-coeff p n * c^n = (\<Sum>i=0..n - 1. coeff p i * (c/d)^i*d^n)"
        using `d \<noteq> 0` by (simp add: setsum_right_distrib field_simps power_divide)
    also from `d \<noteq> 0` have "... = (\<Sum>i=0..n - 1. coeff p i * c^i * d^(n - i))" 
        by (simp add: power_divide power_diff)
    also {
      fix i assume "i \<in> {0..n - 1}"
      with `n \<ge> 1` have "1 + (n - i - 1) = n - i" by simp
      have "d^(n - i) = d^1 * d^(n - i - 1)"
          by (simp only: power_add[symmetric]`1 + (n - i - 1) = n - i`)
      hence "d^(n - i) = d * d^(n - i - 1)" by simp
    }
    hence "... = d * (\<Sum>i=0..n - 1. coeff p i * c^i * d^(n - i - 1))"
        by (simp add: setsum_right_distrib field_simps)
    also have "... = d * (\<Sum>i=0..n - 1. \<lfloor>coeff p i\<rfloor> * c^i * d^(n - i - 1))" by simp
    finally have "-a\<^sub>n * c^n = d * (\<Sum>i=0..n - 1. \<lfloor>coeff p i\<rfloor> * c^i * d^(n - i - 1))"
        by (subst real_of_int_inject[symmetric], simp)
    hence "d dvd a\<^sub>n * c^n"  by (subst dvd_minus_iff[symmetric], force)
    with coprime have "d dvd a\<^sub>n"
        by (subst (asm) gcd_int.commute, 
            blast dest: coprime_dvd_mult_int coprime_exp_int)

    from `c dvd a\<^sub>0` and `d dvd a\<^sub>n` show ?thesis ..
qed

lemma Rats_int_div_intE:
  assumes "x \<in> \<rat>" obtains m :: int and n :: int 
      where "x = m / n" and "n > 0" and "coprime m n"
proof-
  case goal1
  from `x \<in> \<rat>` obtain c ::nat and d :: nat 
      where c_d_facts: "\<bar>x\<bar> = c / d" "d \<noteq> 0" "coprime c d"
      by (elim Rats_abs_nat_div_natE, simp)
  def c' \<equiv> "if x \<ge> 0 then int c else -int c" and d' \<equiv> "int d"
  with c_d_facts have "x = c' / d'" "d' > 0" "coprime c' d'"
      by (cases "x \<ge> 0", auto simp: less_eq_real_def transfer_int_nat_gcd)
  with goal1 show ?thesis .
qed


text {*
  If @{term p} is a real polynomial with integer coefficients, 
  all its rational roots are, written in lowest terms, of the form @{term c/d} 
  where @{term c} divides the polynomial's constant part and @{term d} divides 
  the leading coefficient.
*}
lemma rational_roots:
  fixes p :: "real poly" and x :: real
  assumes int_coeffs: "\<And>n. coeff p n \<in> \<int>"
  assumes zero: "poly p x = 0" and rat: "x \<in> \<rat>"
  defines [simp]: "n \<equiv> degree p"
  defines "a\<^sub>0 \<equiv> \<lfloor>coeff p 0\<rfloor>" and "a\<^sub>n \<equiv> \<lfloor>coeff p n\<rfloor>"
  obtains c :: int and d :: int where "x = c / d" and "d > 0" and "coprime c d" and
                                      "c dvd a\<^sub>0" and "d dvd a\<^sub>n"
proof-
  case goal1
  from `x \<in> \<rat>` obtain c :: int and d :: int
      where "x = c / d" and "d > 0" and "coprime c d" 
      by (blast elim: Rats_int_div_intE)
  with assms have "c dvd a\<^sub>0 \<and> d dvd a\<^sub>n" unfolding a\<^sub>0_def a\<^sub>n_def n_def
      by (intro rational_roots_aux, simp_all)
  with `x = c / d` and `d > 0` and `coprime c d` show ?thesis using goal1 by blast
qed

text {*
  If @{term p} is a real polynomial with integer coefficients whose 
  leading coefficient is 1, all its rational roots must be integers and 
  divide its constant part.
*}
lemma integral_roots:
  fixes p :: "real poly" and x :: real
  assumes int_coeffs: "\<And>n. coeff p n \<in> \<int>"
  assumes zero: "poly p x = 0" and rat: "x \<in> \<rat>"
  assumes normed: "coeff p (degree p) = 1"
  defines [simp]: "n \<equiv> degree p"
  defines "a\<^sub>0 \<equiv> \<lfloor>coeff p 0\<rfloor>"
  shows "x \<in> \<int>" and "\<lfloor>x\<rfloor> dvd a\<^sub>0"
proof-
  from normed obtain c :: int where "x = c" and "c dvd a\<^sub>0" unfolding a\<^sub>0_def
      by (rule_tac rational_roots[OF int_coeffs zero rat], simp)
  moreover from this show "x \<in> \<int>" by simp
  ultimately show "\<lfloor>x\<rfloor> dvd a\<^sub>0" by (simp add: floor_int)
qed



definition divisors :: "int \<Rightarrow> int set" where
"divisors x = {d. d dvd x}"

lemma divisors_code[code]: "divisors x = 
      (if x = 0 then UNIV else set [d \<leftarrow> [-\<bar>x\<bar>..\<bar>x\<bar>]. d dvd x])"
unfolding divisors_def by (cases "x = 0", simp, auto dest: dvd_imp_le_int)


function rat_roots :: "real poly \<Rightarrow> real set" where
"rat_roots p =
  (if p = 0 then UNIV
   else (let a\<^sub>0 = \<lfloor>coeff p 0\<rfloor> :: int; a\<^sub>n = \<lfloor>coeff p (degree p)\<rfloor> :: int
         in  if a\<^sub>0 = 0 then
           rat_roots (p div [:0,1:])
         else
           {c/d |c d. c \<in> divisors a\<^sub>0 \<and> d \<in> divisors a\<^sub>n \<and> poly p (c/d) = 0}))"
by (pat_completeness, auto)
termination
proof (relation "measure degree", simp, clarify)
  fix p :: "real poly" assume "p \<noteq> 0" "\<lfloor>coeff p 0\<rfloor> = 0"
  have int_coeffs: "\<And>i. coeff p i \<in> \<int>" sorry
  with `\<lfloor>coeff p 0\<rfloor> = 0`  have "coeff p 0 = 0" 
      by (-, subst floor_int[symmetric], simp_all)
  hence "poly p 0 = 0"  by (induction p, simp_all)
  hence [simp]:"[:0,1:] dvd p" by (simp add: dvd_iff_poly_eq_0)
  hence "p div [:0,1:] * [:0,1:] = p" 
      by (subst dvd_div_mult_self, simp_all)
  with `p \<noteq> 0` have [simp]: "p div [:0,1:] \<noteq> 0" by force

  have "degree p = degree (p div [:0,1:] * [:0,1:])"
      by (subst dvd_div_mult_self, simp_all)
  also have "... = degree (p div [:0,1:]) + 1"
      by (subst degree_mult_eq, simp_all)
  finally have "degree (p div [:0,1:]) < degree p" by simp
  thus "(p div [:0,1:], p) \<in> measure degree" by simp
qed



end