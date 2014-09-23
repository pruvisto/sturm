header {* Example usage of the ``sturm'' method *}
(* Author: Manuel Eberl <eberlm@in.tum.de> *)
theory Sturm_Ex
imports "../Sturm"
begin

text {*
  In this section, we give a variety of statements about real polynomials that can b
  proven by the \emph{sturm} method.
*}

lemma "\<forall>x::real. x^2 + 1 \<noteq> 0" by sturm

lemma "(x::real)^2 + 1 \<noteq> 0" by sturm

lemma "(x::real) > 1 \<Longrightarrow> x^3 > 1" by sturm

lemma "\<forall>x::real. x*x \<noteq> -1" by sturm

schematic_lemma A:
  "card {x::real. -0.010831 < x \<and> x < 0.010831 \<and> 
      1/120*x^5 + 1/24 * x^4 +1/6*x^3 - 49/16777216*x^2 - 17/2097152*x = 0} = ?n" by sturm

lemma "card {x::real. x^3 + x = 2*x^2 \<and> x^3 - 6*x^2 + 11*x = 6} = 1"  by sturm

lemma "mono (\<lambda>x::real. x^3)" by sturm
lemma "inj (\<lambda>x::real. x^3)" by sturm
lemma "\<forall>(x::real) y. x \<noteq> y \<longrightarrow> x^3 \<noteq> y^3" by sturm
lemma "(x::real) < y \<Longrightarrow> -(x^3) > -(y^3)" by sturm


lemma "strict_mono (\<lambda>x::real. x^7/7 - 14/5*x^5 + 3*x^4 + 49/3*x^3 - 42*x^2 + 36*x - 13)" by sturm

lemma "\<exists>x::real. -x*x + 9 - 4 > 0" by sturm
lemma "\<exists>x::real. -x*x + 9 - 4 \<ge> 0" by sturm

schematic_lemma "card {x::real. x^3 + x = 2*x^2 \<or> x^3 - 6*x^2 + 11*x = 6} = ?n" by sturm


lemma
  "card {x::real. -0.010831 < x \<and> x < 0.010831 \<and> 
     poly [:0, -17/2097152, -49/16777216, 1/6, 1/24, 1/120:] x = 0} = 3"
  by sturm

lemma "\<forall>x::real. x*x \<noteq> 0 \<or> x*x - 1 \<noteq> 2*x" by sturm
lemma "\<exists>x::real. x*x - 9 = 0 \<and> x+3 = 0" by sturm

lemma "\<bar>x - 3 :: real\<bar> < 2 \<Longrightarrow> 5 + 6*x - x^2 > 0" by sturm

lemma "(x::real)*x+1 \<noteq> 0 \<and> (x^2+1)*(x^2+2) \<noteq> 0" by sturm

text {* nonstrict inequalities *}
lemma "x^6 - 4*x^5 + 7*x^4 - 12*x^3 + 12*x^2 \<ge> (0 :: real)" by sturm
lemma "-33062500 + 30187500*x - 10743125*x^2 + 1793250*x^3 - 116475*x^4 -
            3240*x^5 + 661*x^6 - 6*x^7 - x^8 \<le> (0 :: real)" by sturm
lemma "x \<ge> -0.5 \<Longrightarrow> x \<le> 1 \<Longrightarrow> x^3 - 5*x^2 + x + 3 \<ge> (0::real)" by sturm
lemma "x \<ge> (4::real) \<Longrightarrow> x^3 \<ge> 4*x^2" by sturm
lemma "x \<ge> 40 \<Longrightarrow> x \<le> 44 \<Longrightarrow> x^2 - 84*x + 1760 \<le> (0::real)" by sturm

lemma "1296 - 3528*x^2 + 3409*x^4 - 1444*x^6 + 294*x^8 - 28*x^10 + x^12 \<ge> (0 :: real)" by sturm
lemma "x \<ge> -2 \<Longrightarrow> 1296 - 3528*x^2 + 3409*x^4 - 1444*x^6 + 294*x^8 - 28*x^10 + x^12 \<ge> (0 :: real)" by sturm
lemma "x \<le> 2 \<Longrightarrow> 1296 - 3528*x^2 + 3409*x^4 - 1444*x^6 + 294*x^8 - 28*x^10 + x^12 \<ge> (0 :: real)" by sturm
lemma "x > -2 \<Longrightarrow> 1296 - 3528*x^2 + 3409*x^4 - 1444*x^6 + 294*x^8 - 28*x^10 + x^12 \<ge> (0 :: real)" by sturm
lemma "x < 2 \<Longrightarrow> 1296 - 3528*x^2 + 3409*x^4 - 1444*x^6 + 294*x^8 - 28*x^10 + x^12 \<ge> (0 :: real)" by sturm
lemma "x \<ge> -2 \<Longrightarrow> x \<le> 2 \<Longrightarrow> 1296 - 3528*x^2 + 3409*x^4 - 1444*x^6 + 294*x^8 - 28*x^10 + x^12 \<ge> (0 :: real)" by sturm
lemma "x > -2 \<Longrightarrow> x \<le> 2 \<Longrightarrow> 1296 - 3528*x^2 + 3409*x^4 - 1444*x^6 + 294*x^8 - 28*x^10 + x^12 \<ge> (0 :: real)" by sturm
lemma "x \<ge> -2 \<Longrightarrow> x < 2 \<Longrightarrow> 1296 - 3528*x^2 + 3409*x^4 - 1444*x^6 + 294*x^8 - 28*x^10 + x^12 \<ge> (0 :: real)" by sturm
lemma "x > -2 \<Longrightarrow> x < 2 \<Longrightarrow> 1296 - 3528*x^2 + 3409*x^4 - 1444*x^6 + 294*x^8 - 28*x^10 + x^12 \<ge> (0 :: real)" by sturm

lemma "\<exists>x::real. 1 - x*x > 0" by sturm
lemma "\<exists>x::real \<ge> -1. 1 - x*x > 0" by sturm
lemma "\<exists>x::real > -1. 1 - x*x > 0" by sturm
lemma "\<exists>x::real < 1. 1 - x*x > 0" by sturm
lemma "\<exists>x::real \<le> 1. 1 - x*x > 0" by sturm
lemma "\<exists>x::real. x \<ge> -1 \<and> x \<le> 1 \<and> 1 - x*x > 0" by sturm
lemma "\<exists>x::real. x > -1 \<and> x \<le> 1 \<and> 1 - x*x > 0" by sturm
lemma "\<exists>x::real. x \<ge> -1 \<and> x < 1 \<and> 1 - x*x > 0" by sturm
lemma "\<exists>x::real. x > -1 \<and> x < 1 \<and> 1 - x*x > 0" by sturm
lemma "\<exists>x::real. x \<ge> 0 \<and> x \<le> 0 \<and> 1 - x*x > 0" by sturm


text{*3 examples related to continued fraction approximants to exp: LCP*}
lemma fixes x::real
shows "-7.29347719 \<le> x \<Longrightarrow> 0 < x^5 + 30*x^4 + 420*x^3 + 3360*x^2 + 15120*x + 30240"
by sturm

lemma fixes x::real
shows "0 < x^6 + 42*x^5 + 840*x^4 + 10080*x^3 + 75600*x\<^sup>2 + 332640*x + 665280"
by sturm

schematic_lemma "card {x::real. x^7 + 56*x^6 + 1512*x^5 + 25200*x^4 + 277200*x^3 + 1995840*x^2 + 8648640*x = -17297280} = ?n" 
by sturm

lemma "inj_on (\<lambda>x::real. x^2) {0..1}" by sturm
lemma "inj_on (\<lambda>x::real. x^2) {0<..1}" by sturm
lemma "inj_on (\<lambda>x::real. x^2) {0..<1}" by sturm
lemma "inj_on (\<lambda>x::real. x^2) {0<..<1}" by sturm
lemma "inj_on (\<lambda>x::real. x^2) {0..}" by sturm
lemma "inj_on (\<lambda>x::real. x^2) {0<..}" by sturm
lemma "inj_on (\<lambda>x::real. x^2) {..0}" by sturm
lemma "inj_on (\<lambda>x::real. x^2) {..<0}" by sturm
lemma "inj (\<lambda>x::real. x^3)" by sturm

end
