header {* The ``sturm'' proof method *}

(* Author: Manuel Eberl <eberlm@in.tum.de> *)
theory Sturm_Method
imports Sturm_Theorem Poly_Monotonicity "~~/src/HOL/Library/Code_Target_Numeral"
begin

subsection {* Preliminary lemmas *}

text {*
  In this subsection, we prove lemmas that reduce root counting and
  related statements to simple, computable expressions using the 
  @{term "count_roots"} function family.
*}

lemma poly_card_roots_less_leq:
  "card {x. a < x \<and> x \<le> b \<and> poly p x = 0} = count_roots_between p a b"
  by (simp add: count_roots_between_correct)

lemma poly_card_roots_leq_leq:
  "card {x. a \<le> x \<and> x \<le> b \<and> poly p x = 0} = 
       ( count_roots_between p a b + 
      (if (a \<le> b \<and> poly p a = 0 \<and> p \<noteq> 0) \<or> (a = b \<and> p = 0) then 1 else 0))"
proof (cases "(a \<le> b \<and> poly p a = 0 \<and> p \<noteq> 0) \<or> (a = b \<and> p = 0)")
  case False
    note False' = this
    thus ?thesis
    proof (cases "p = 0")
      case False
        with False' have "poly p a \<noteq> 0 \<or> a > b" by auto
        hence "{x. a \<le> x \<and> x \<le> b \<and> poly p x = 0} = 
               {x. a < x \<and> x \<le> b \<and> poly p x = 0}"
        by (auto simp: less_eq_real_def)
        thus ?thesis using poly_card_roots_less_leq assms False' 
            by (auto split: split_if_asm)
    next
      case True
        have "{x. a \<le> x \<and> x \<le> b} = {a..b}"
             "{x. a < x \<and> x \<le> b} = {a<..b}" by auto
        with True False have "card {x. a < x \<and> x \<le> b} = 0" "card {x. a \<le> x \<and> x \<le> b} = 0"
          by (auto simp add: card_eq_0_iff infinite_Ioc infinite_Icc)
        with True False show ?thesis
            using count_roots_between_correct by (simp add: )
    qed
next
  case True
    note True' = this
    have fin: "finite {x. a \<le> x \<and> x \<le> b \<and> poly p x = 0}" 
    proof (cases "p = 0")
      case True
        with True' have "a = b" by simp
        hence "{x. a \<le> x \<and> x \<le> b \<and> poly p x = 0} = {b}" using True by auto
        thus ?thesis by simp
    next
      case False
        from poly_roots_finite[OF this] show ?thesis by fast
    qed
    with True have "{x. a \<le> x \<and> x \<le> b \<and> poly p x = 0} =
        insert a {x. a < x \<and> x \<le> b \<and> poly p x = 0}" by auto
    hence "card {x. a \<le> x \<and> x \<le> b \<and> poly p x = 0} =
           Suc (card {x. a < x \<and> x \<le> b \<and> poly p x = 0})" using fin by force
    thus ?thesis using True count_roots_between_correct by simp
qed

lemma poly_card_roots_less_less:
  "card {x. a < x \<and> x < b \<and> poly p x = 0} = 
      ( count_roots_between p a b -
              (if poly p b = 0 \<and> a < b \<and> p \<noteq> 0 then 1 else 0))"
proof (cases "poly p b = 0 \<and> a < b \<and> p \<noteq> 0")
  case False
    note False' = this
    show ?thesis
    proof (cases "p = 0")
      case True
        have [simp]: "{x. a < x \<and> x < b} = {a<..<b}"
                     "{x. a < x \<and> x \<le> b} = {a<..b}" by auto
        with True False have "card {x. a < x \<and> x \<le> b} = 0" "card {x. a < x \<and> x < b} = 0"
          by (auto simp add: card_eq_0_iff infinite_Ioo infinite_Ioc)
        with True False' assms show ?thesis 
            by (auto simp: count_roots_between_correct)
    next
      case False
        with False' have "{x. a < x \<and> x < b \<and> poly p x = 0} = 
                          {x. a < x \<and> x \<le> b \<and> poly p x = 0}"
          by (auto simp: less_eq_real_def)
      thus ?thesis using poly_card_roots_less_leq assms False by auto
  qed
next
  case True
    with poly_roots_finite
        have fin: "finite {x. a < x \<and> x < b \<and> poly p x = 0}" by fast
    from True have "{x. a < x \<and> x \<le> b \<and> poly p x = 0} =
        insert b {x. a < x \<and> x < b \<and> poly p x = 0}" by auto
    hence "Suc (card {x. a < x \<and> x < b \<and> poly p x = 0}) =
           card {x. a < x \<and> x \<le> b \<and> poly p x = 0}" using fin by force
    also note count_roots_between_correct[symmetric]
    finally show ?thesis using True by simp
qed

lemma poly_card_roots_leq_less:
  "card {x::real. a \<le> x \<and> x < b \<and> poly p x = 0} =
      ( count_roots_between p a b +
      (if p \<noteq> 0 \<and> a < b \<and> poly p a = 0 then 1 else 0) -
      (if p \<noteq> 0 \<and> a < b \<and> poly p b = 0 then 1 else 0))"
proof (cases "p = 0 \<or> a \<ge> b")
  case True
    note True' = this
    show ?thesis
    proof (cases "a \<ge> b")
      case False
        hence "{x. a < x \<and> x \<le> b} = {a<..b}"
              "{x. a \<le> x \<and> x < b} = {a..<b}" by auto
        with True False have "card {x. a < x \<and> x \<le> b} = 0" "card {x. a \<le> x \<and> x < b} = 0"
          by (auto simp add: card_eq_0_iff infinite_Ico infinite_Ioc)
        with False True' show ?thesis 
            by (simp add: count_roots_between_correct)
    next
      case True
        with True' have "{x. a \<le> x \<and> x < b \<and> poly p x = 0} = 
                          {x. a < x \<and> x \<le> b \<and> poly p x = 0}"
          by (auto simp: less_eq_real_def)
      thus ?thesis using poly_card_roots_less_leq True by simp
  qed
next
  case False
    let ?A = "{x. a \<le> x \<and> x < b \<and> poly p x = 0}"
    let ?B = "{x. a < x \<and> x \<le> b \<and> poly p x = 0}"
    let ?C = "{x. x = b \<and> poly p x = 0}"
    let ?D = "{x. x = a \<and> poly p a = 0}"
    have CD_if: "?C = (if poly p b = 0 then {b} else {})"
                "?D = (if poly p a = 0 then {a} else {})" by auto
    from False poly_roots_finite 
        have [simp]: "finite ?A" "finite ?B" "finite ?C" "finite ?D"
            by (fast, fast, simp_all)
    
    from False have "?A = (?B \<union> ?D) - ?C" by (auto simp: less_eq_real_def)
    with False have "card ?A = card ?B + (if poly p a = 0 then 1 else 0) -
                       (if poly p b = 0 then 1 else 0)" by (auto simp: CD_if)
    also note count_roots_between_correct[symmetric]
    finally show ?thesis using False by simp
qed

lemma poly_card_roots:
  "card {x::real. poly p x = 0} = count_roots p"
  using assms count_roots_correct by simp

lemma poly_no_roots:
  "(\<forall>x. poly p x \<noteq> 0) \<longleftrightarrow> ( p \<noteq> 0 \<and> count_roots p = 0)"
    by (auto simp: count_roots_correct dest: poly_roots_finite)

lemma poly_pos:
  "(\<forall>x. poly p x > 0) \<longleftrightarrow> ( 
        p \<noteq> 0 \<and> poly_inf p = 1 \<and> count_roots p = 0)"
  by (simp only: Let_def poly_pos poly_no_roots, blast)


lemma poly_card_roots_greater:
  "card {x::real. x > a \<and> poly p x = 0} = count_roots_above p a"
  using assms count_roots_above_correct by simp

lemma poly_card_roots_leq:
  "card {x::real. x \<le> a \<and> poly p x = 0} = count_roots_below p a"
  using assms  count_roots_below_correct by simp

lemma poly_card_roots_geq:
  "card {x::real. x \<ge> a \<and> poly p x = 0} = (
      count_roots_above p a + (if poly p a = 0 \<and> p \<noteq> 0 then 1 else 0))"
proof (cases "poly p a = 0 \<and> p \<noteq> 0")
  case False
    hence "card {x. x \<ge> a \<and> poly p x = 0} = card {x. x > a \<and> poly p x = 0}"
    proof (cases rule: disjE)
      assume "p = 0"
      have "\<not>finite {a<..<a+1}"
        by (metis infinite_Ioo less_add_one) 
      moreover have "{a<..<a+1} \<subseteq> {x. x \<ge> a \<and> poly p x = 0}"
                    "{a<..<a+1} \<subseteq> {x. x > a \<and> poly p x = 0}" 
          using `p = 0` by auto
      ultimately have "\<not>finite {x. x \<ge> a \<and> poly p x = 0}" 
                     "\<not>finite {x. x > a \<and> poly p x = 0}" 
          by (auto dest: finite_subset[of "{a<..<a+1}"])
      thus ?thesis by simp
    next
      assume "poly p a \<noteq> 0"
      hence "{x. x \<ge> a \<and> poly p x = 0} = {x. x > a \<and> poly p x = 0}" 
          by (auto simp: less_eq_real_def)
      thus ?thesis by simp
    qed auto
    thus ?thesis using assms False 
        by (auto intro: poly_card_roots_greater)
next
  case True
    hence "finite {x. x > a \<and> poly p x = 0}" using poly_roots_finite by force
    moreover have "{x. x \<ge> a \<and> poly p x = 0} = 
                       insert a {x. x > a \<and> poly p x = 0}" using True by auto
    ultimately have "card {x. x \<ge> a \<and> poly p x = 0} = 
                         Suc (card {x. x > a \<and> poly p x = 0})"
        using card_insert_disjoint by auto
    thus ?thesis using assms True by (auto intro: poly_card_roots_greater)
qed

lemma poly_card_roots_less:
  "card {x::real. x < a \<and> poly p x = 0} =
       (count_roots_below p a - (if poly p a = 0 \<and> p \<noteq> 0 then 1 else 0))"
proof (cases "poly p a = 0 \<and> p \<noteq> 0")
  case False
    hence "card {x. x < a \<and> poly p x = 0} = card {x. x \<le> a \<and> poly p x = 0}"
    proof (cases rule: disjE)
      assume "p = 0"
      have "\<not>finite {a - 1<..<a}" 
        by (metis infinite_Ioo diff_add_cancel less_add_one) 
      moreover have "{a - 1<..<a} \<subseteq> {x. x \<le> a \<and> poly p x = 0}"
                    "{a - 1<..<a} \<subseteq> {x. x < a \<and> poly p x = 0}" 
          using `p = 0` by auto
      ultimately have "\<not>finite {x. x \<le> a \<and> poly p x = 0}" 
                     "\<not>finite {x. x < a \<and> poly p x = 0}" 
          by (auto dest: finite_subset[of "{a - 1<..<a}"])
      thus ?thesis by simp
    next
      assume "poly p a \<noteq> 0"
      hence "{x. x < a \<and> poly p x = 0} = {x. x \<le> a \<and> poly p x = 0}" 
          by (auto simp: less_eq_real_def)
      thus ?thesis by simp
    qed auto
    thus ?thesis using assms False 
        by (auto intro: poly_card_roots_leq)
next
  case True
    hence "finite {x. x < a \<and> poly p x = 0}" using poly_roots_finite by force
    moreover have "{x. x \<le> a \<and> poly p x = 0} = 
                       insert a {x. x < a \<and> poly p x = 0}" using True by auto
    ultimately have "Suc (card {x. x < a \<and> poly p x = 0}) =
                     (card {x. x \<le> a \<and> poly p x = 0})"
        using card_insert_disjoint by auto
    also note count_roots_below_correct[symmetric]
    finally show ?thesis using assms True by simp
qed


lemma poly_no_roots_less_leq:
  "(\<forall>x. a < x \<and> x \<le> b \<longrightarrow> poly p x \<noteq> 0) \<longleftrightarrow>
   ((a \<ge> b \<or> (p \<noteq> 0 \<and> count_roots_between p a b = 0)))"
  by (auto simp: count_roots_between_correct card_eq_0_iff not_le 
           dest: poly_roots_finite)

lemma poly_pos_between_less_leq:
  "(\<forall>x. a < x \<and> x \<le> b \<longrightarrow> poly p x > 0) \<longleftrightarrow>
   ((a \<ge> b \<or> (p \<noteq> 0 \<and> poly p b > 0 \<and> count_roots_between p a b = 0)))"
  by (simp only: poly_pos_between_less_leq Let_def 
                 poly_no_roots_less_leq, blast)


lemma poly_no_roots_leq_leq:
  "(\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> poly p x \<noteq> 0) \<longleftrightarrow>
   ((a > b \<or> (p \<noteq> 0 \<and> poly p a \<noteq> 0 \<and> count_roots_between p a b = 0)))"
apply (intro iffI)
apply (force simp add: count_roots_between_correct card_eq_0_iff)
apply (elim conjE disjE, simp, intro allI)
apply (rename_tac x, case_tac "x = a")
apply (auto simp add: count_roots_between_correct card_eq_0_iff
            dest: poly_roots_finite)
done

lemma poly_pos_between_leq_leq:
  "(\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> poly p x > 0) \<longleftrightarrow> 
   ((a > b \<or> (p \<noteq> 0 \<and> poly p a > 0 \<and> 
                count_roots_between p a b = 0)))"
by (simp only: poly_pos_between_leq_leq Let_def poly_no_roots_leq_leq, force)



lemma poly_no_roots_less_less:
  "(\<forall>x. a < x \<and> x < b \<longrightarrow> poly p x \<noteq> 0) \<longleftrightarrow> 
   ((a \<ge> b \<or> p \<noteq> 0 \<and> count_roots_between p a b = 
       (if poly p b = 0 then 1 else 0)))"
proof
  case goal1
    note A = this
    thus ?case
    proof (cases "a \<ge> b", simp)
      case goal1
      with A have [simp]: "p \<noteq> 0" using dense[of a b] by auto
      have B: "{x. a < x \<and> x \<le> b \<and> poly p x = 0} =
                {x. a < x \<and> x < b \<and> poly p x = 0} \<union>
                (if poly p b = 0 then {b} else {})" using goal1 by auto
      have "count_roots_between p a b =
                 card {x. a < x \<and> x < b \<and> poly p x = 0} +
                (if poly p b = 0 then 1 else 0)"
         by (subst count_roots_between_correct, subst B, subst card_Un_disjoint, 
             rule finite_subset[OF _ poly_roots_finite], blast, simp_all)
      also from A have "{x. a < x \<and> x < b \<and> poly p x = 0} = {}" by simp
      finally show ?thesis by auto
    qed
next
  case goal2
    hence "card {x. a < x \<and> x < b \<and> poly p x = 0} = 0"
        by (subst poly_card_roots_less_less, auto simp: count_roots_between_def)
    thus ?case using goal2
        by (cases "p = 0", simp, subst (asm) card_eq_0_iff, 
            auto dest: poly_roots_finite)
qed

lemma poly_pos_between_less_less:
  "(\<forall>x. a < x \<and> x < b \<longrightarrow> poly p x > 0) \<longleftrightarrow>
   ((a \<ge> b \<or> (p \<noteq> 0 \<and> poly p ((a+b)/2) > 0 \<and> 
       count_roots_between p a b = (if poly p b = 0 then 1 else 0))))"
  by (simp only: poly_pos_between_less_less Let_def 
                 poly_no_roots_less_less, blast)

lemma poly_no_roots_leq_less:
  "(\<forall>x. a \<le> x \<and> x < b \<longrightarrow> poly p x \<noteq> 0) \<longleftrightarrow>
   ((a \<ge> b \<or> p \<noteq> 0 \<and> poly p a \<noteq> 0 \<and> count_roots_between p a b = 
       (if a < b \<and> poly p b = 0 then 1 else 0)))"
proof
  case goal1
    hence "\<forall>x. a < x \<and> x < b \<longrightarrow> poly p x \<noteq> 0" by simp
    thus ?case using goal1 by (subst (asm) poly_no_roots_less_less, auto)
next
  case goal2
    hence "(b \<le> a \<or> p \<noteq> 0 \<and> count_roots_between p a b = 
               (if poly p b = 0 then 1 else 0))" by auto
    thus ?case using goal2 unfolding Let_def
        by (subst (asm) poly_no_roots_less_less[symmetric, unfolded Let_def], 
        auto split: split_if_asm simp: less_eq_real_def) 
qed

lemma poly_pos_between_leq_less:
  "(\<forall>x. a \<le> x \<and> x < b \<longrightarrow> poly p x > 0) \<longleftrightarrow> 
   ((a \<ge> b \<or> (p \<noteq> 0 \<and> poly p a > 0 \<and> count_roots_between p a b = 
        (if a < b \<and> poly p b = 0 then 1 else 0))))"
 by (simp only: poly_pos_between_leq_less Let_def 
                poly_no_roots_leq_less, force)


lemma poly_no_roots_greater:
  "(\<forall>x. x > a \<longrightarrow> poly p x \<noteq> 0) \<longleftrightarrow>
       ((p \<noteq> 0 \<and> count_roots_above p a = 0))"
proof-
  have "\<forall>x. \<not> a < x \<Longrightarrow> False" by (metis gt_ex)
  thus ?thesis by (auto simp: count_roots_above_correct card_eq_0_iff
                        intro: poly_roots_finite )
qed

lemma poly_pos_greater:
  "(\<forall>x. x > a \<longrightarrow> poly p x > 0) \<longleftrightarrow> (
       p \<noteq> 0 \<and> poly_inf p = 1 \<and> count_roots_above p a = 0)"
  unfolding Let_def
  by (subst poly_pos_greater, subst poly_no_roots_greater, force)

lemma poly_no_roots_leq:
  "(\<forall>x. x \<le> a \<longrightarrow> poly p x \<noteq> 0) \<longleftrightarrow> 
       ( (p \<noteq> 0 \<and> count_roots_below p a = 0))"
    by (auto simp: Let_def count_roots_below_correct card_eq_0_iff
             intro: poly_roots_finite)

lemma poly_pos_leq:
  "(\<forall>x. x \<le> a \<longrightarrow> poly p x > 0) \<longleftrightarrow> 
   ( p \<noteq> 0 \<and> poly_neg_inf p = 1 \<and> count_roots_below p a = 0)"
  by (simp only: poly_pos_leq Let_def poly_no_roots_leq, blast)



lemma poly_no_roots_geq:
  "(\<forall>x. x \<ge> a \<longrightarrow> poly p x \<noteq> 0) \<longleftrightarrow>
       ( (p \<noteq> 0 \<and> poly p a \<noteq> 0 \<and> count_roots_above p a = 0))"
proof
  case goal1
  hence "\<forall>x>a. poly p x \<noteq> 0" by simp
  thus ?case using goal1 by (subst (asm) poly_no_roots_greater, auto)
next
  case goal2
  hence "(p \<noteq> 0 \<and> count_roots_above p a = 0)" by simp
  thus ?case using goal2 
      by (subst (asm) poly_no_roots_greater[symmetric, unfolded Let_def], 
          auto simp: less_eq_real_def)
qed

lemma poly_pos_geq:
  "(\<forall>x. x \<ge> a \<longrightarrow> poly p x > 0) \<longleftrightarrow>
   (p \<noteq> 0 \<and> poly_inf p = 1 \<and> poly p a \<noteq> 0 \<and> count_roots_above p a = 0)"
  by (simp only: poly_pos_geq Let_def poly_no_roots_geq, blast)

lemma poly_no_roots_less:
  "(\<forall>x. x < a \<longrightarrow> poly p x \<noteq> 0) \<longleftrightarrow>
       ((p \<noteq> 0 \<and> count_roots_below p a = (if poly p a = 0 then 1 else 0)))"
proof
  case goal1
  hence "{x. x \<le> a \<and> poly p x = 0} = (if poly p a = 0 then {a} else {})"
      by (auto simp: less_eq_real_def)
  moreover have "\<forall>x. \<not> x < a \<Longrightarrow> False" by (metis lt_ex)
  ultimately show ?case using goal1 by (auto simp: count_roots_below_correct)
next
  case goal2
  have A: "{x. x \<le> a \<and> poly p x = 0} = {x. x < a \<and> poly p x = 0} \<union> 
            (if poly p a = 0 then {a} else {})" by (auto simp: less_eq_real_def)
  have "count_roots_below p a = card {x. x < a \<and> poly p x = 0} +
            (if poly p a = 0 then 1 else 0)" using goal2
      by (subst count_roots_below_correct, subst A, subst card_Un_disjoint,
          auto intro: poly_roots_finite)
  with goal2 have "card {x. x < a \<and> poly p x = 0} = 0" by simp
  thus ?case using goal2
      by (subst (asm) card_eq_0_iff, auto intro: poly_roots_finite)
qed

lemma poly_pos_less:
  "(\<forall>x. x < a \<longrightarrow> poly p x > 0) \<longleftrightarrow>
   (p \<noteq> 0 \<and> poly_neg_inf p = 1 \<and> count_roots_below p a = 
       (if poly p a = 0 then 1 else 0))"
  by (simp only: poly_pos_less Let_def poly_no_roots_less, blast)



subsection {* Nonnegativity *}

lemma sturm_nonneg_betweenI_aux:
  assumes "(p :: real poly) \<noteq> 0"
  assumes hd_a: "hd xs \<le> a" and last_b: "last xs \<ge> b" and not_empty: "xs \<noteq> []"
  assumes sorted: "sorted xs"
  assumes roots_1: "\<And>i. i < length xs - 1 \<Longrightarrow> card {x\<in>{xs!i<..xs!Suc i}. poly p x = 0} = 1"
  assumes xs_pos: "\<And>x. x \<in> set xs \<Longrightarrow> poly p x > 0"
  assumes x_in_bound: "x > a" "x \<le> b"
  shows "poly p x \<ge> 0"
proof (cases "length xs = 1")
  assume "length xs = 1"
  with x_in_bound hd_a last_b have "a = b" by (cases xs) auto
  moreover from x_in_bound have "a < b" by simp
  ultimately have False by simp
  thus ?thesis ..
next
  assume "length xs \<noteq> 1"
  with not_empty have len: "length xs > 1" by (cases xs) auto
  from hd_a last_b x_in_bound have "x > hd xs" "x \<le> last xs" by simp_all
  from not_empty sorted len this have "\<exists>i < length xs - 1. x \<in> {xs!i<..xs ! Suc i}"
  proof (induction xs rule: list_nonempty_induct)
    case (cons y xs)
    show ?case
    proof (cases "x \<le> xs ! 0")
      assume "x \<le> xs ! 0"
      with cons show ?thesis by (intro exI[of _ 0]) auto
    next
      assume A: "\<not>(x \<le> xs ! 0)"
      with cons have "x > hd xs" by (subst hd_conv_nth) auto
      moreover {
        assume "\<not>(length xs > 1)"
        with cons.prems obtain z where "xs = [z]" by (cases xs) simp_all
        with cons.prems and A have False by auto
      }
      hence "length xs > 1" by blast
      ultimately have "\<exists>i<length xs - 1. x \<in> {xs ! i<..xs ! Suc i}" using cons.prems
        by (intro cons.IH) (auto simp: sorted_Cons)
      then guess i by (elim exE conjE)
      thus ?thesis by (intro exI[of _ "Suc i"]) auto
    qed
  qed simp
  then guess i by (elim exE conjE)
  note i_props = this
  let ?I = "{xs ! i<..xs ! Suc i}"
  from i_props have i_props': "poly p (xs!i) > 0" "poly p (xs!Suc i) > 0" by (auto intro: xs_pos)

  have card_1: "card {x\<in>?I. poly p x = 0} = 1" by (intro roots_1 i_props)
  hence "{x\<in>?I. poly p x = 0} \<noteq> {}" by (intro notI) (simp only: card_empty)
  then obtain x0 where "x0 \<in> ?I" "poly p x0 = 0" by blast
  moreover from i_props' and `poly p x0 = 0` have "x0 \<noteq> xs ! Suc i" by auto
  ultimately have x0_props: "x0 > xs!i" "x0 < xs!Suc i" "poly p x0 = 0" by auto

  have fin: "finite {x\<in>?I. poly p x = 0}"
    by (rule finite_subset[OF _ poly_roots_finite[OF `p \<noteq> 0`]]) auto
  with card_1 x0_props have "card ({x\<in>?I. poly p x = 0} - {x0}) = 0"
    by (subst card_Diff_singleton) auto
  hence "{x\<in>?I. poly p x = 0} - {x0} = {}"
    by (subst (asm) card_eq_0_iff) (auto intro: finite_subset[OF _ fin])
  hence only_root: "\<And>x. x \<in> ?I \<Longrightarrow> poly p x = 0 \<Longrightarrow> x = x0" by blast

  {
    assume neg: "poly p x < 0"
    with i_props and i_props' have "\<exists>\<xi>. \<xi> \<ge> xs!i \<and> \<xi> \<le> x \<and> poly p \<xi> = 0"
      by (intro poly_different_sign_imp_root) auto
    then guess \<xi>1 by (elim exE conjE)
    note \<xi>1_props = this
    with i_props' have "\<xi>1 \<noteq> xs ! i" by auto
    with \<xi>1_props and i_props have "\<xi>1 \<in> ?I" "poly p \<xi>1 = 0" by auto
    hence "\<xi>1 = x0" by (intro only_root) auto
    with `\<xi>1 \<le> x` have "x0 \<le> x" by simp
    moreover from i_props' neg have "x \<noteq> xs ! Suc i" by auto
    with i_props i_props' neg have "\<exists>\<xi>. \<xi> \<ge> x \<and> \<xi> \<le> xs ! Suc i \<and> poly p \<xi> = 0"
      by (intro poly_different_sign_imp_root) auto
    then guess \<xi>2 by (elim exE conjE)
    with i_props have "\<xi>2 \<in> ?I" "poly p \<xi>2 = 0" by auto
    hence "\<xi>2 = x0" by (intro only_root) auto
    with `\<xi>2 \<ge> x` have "x0 \<ge> x" by simp
    ultimately have "x = x0" by simp
    with neg and x0_props have False by simp
  }
  thus "poly p x \<ge> 0" by (subst not_less[symmetric]) blast
qed

primrec nat_all_less :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" where
  "nat_all_less p 0 = True"
| "nat_all_less p (Suc n) = (p n \<and> nat_all_less p n)"

lemma nat_all_less_correct: "nat_all_less p n = (\<forall>k<n. p k)"
proof (induction n)
  case (Suc n)
  show ?case
  proof
    assume A: "nat_all_less p (Suc n)"
    {
      fix k assume "k < Suc n"
      with A and Suc.IH have "p k" by (cases "k = n") auto
    }
    thus "\<forall>k<Suc n. p k" by blast
  next
    assume "\<forall>k<Suc n. p k"
    with Suc.IH show "nat_all_less p (Suc n)" by auto
  qed
qed simp

definition "poly_nonneg_witness_between p xs a b \<equiv> 
  hd xs \<le> a \<and> last xs \<ge> b \<and> xs \<noteq> [] \<and> sorted xs \<and> 
    nat_all_less (\<lambda>i. count_roots_between p (xs ! i) (xs ! Suc i) = 1) (length xs - 1) \<and>
    list_all (\<lambda>x. poly p x > 0) xs"

lemma sturm_nonneg_betweenI_aux2:
  assumes "poly_nonneg_witness_between p xs a b" "x > a" "x \<le> b"
  shows "poly p x \<ge> 0"
proof (cases "p = 0")
  assume "p \<noteq> 0"
  show ?thesis
  proof (rule sturm_nonneg_betweenI_aux[OF `p \<noteq> 0` _ _ _ _ _ _ assms(2,3)])
    fix i assume i: "i < length xs - 1"
    have "{x \<in> {xs ! i<..xs ! Suc i}. poly p x = 0} = 
              {x. xs ! i < x \<and> x \<le> xs ! Suc i \<and> poly p x = 0}" by auto
    also have "card ... = count_roots_between p (xs ! i) (xs ! Suc i)"
      by (rule count_roots_between_correct[symmetric])
    also from assms(1) and i have "... = 1" unfolding poly_nonneg_witness_between_def
      by (auto simp: nat_all_less_correct)
    finally show "card {x \<in> {xs ! i<..xs ! Suc i}. poly p x = 0} = 1" .
  qed (insert assms, auto simp: list_all_iff poly_nonneg_witness_between_def)
qed simp_all

definition "poly_nonneg_witness_above p xs a \<equiv>
  let b = last xs; ps = sturm_squarefree p
  in  hd xs = a \<and> a \<le> b \<and> xs \<noteq> [] \<and> sorted xs \<and> (sign_changes ps a - sign_changes_inf ps) =
      (sign_changes ps a - sign_changes ps b) \<and>
      nat_all_less (\<lambda>i. sign_changes ps (xs ! i) - sign_changes ps (xs ! Suc i) = 1) (length xs - 1) \<and>
      list_all (\<lambda>x. poly p x > 0) xs"

lemma sturm_nonneg_aboveI_aux:
  assumes "poly_nonneg_witness_above p xs a" "x > a"
  shows "poly p x \<ge> 0"
proof (cases "p = 0")
  assume "p \<noteq> 0"
  show ?thesis
  proof (cases "x \<le> last xs")
    assume A: "x \<le> last xs"
    from assms `p \<noteq> 0` have "poly_nonneg_witness_between p xs a (last xs)"
    unfolding poly_nonneg_witness_above_def poly_nonneg_witness_between_def
      by (auto simp: Let_def count_roots_between_def nat_all_less_correct intro!: sorted_nth_mono)
    from assms(2) this A show "poly p x \<ge> 0" by (intro sturm_nonneg_betweenI_aux2) auto
  next
    let ?I = "{hd xs<..last xs}"
    from assms and `p \<noteq> 0` have [simp]: "hd xs = a"
      unfolding poly_nonneg_witness_above_def Let_def by simp
    from assms and `p \<noteq> 0` have "count_roots_above p a = count_roots_between p (hd xs) (last xs)"
      unfolding poly_nonneg_witness_above_def count_roots_above_def count_roots_between_def Let_def
      by (auto simp add: count_roots_between_def count_roots_above_def Let_def)
    hence "card {x. x \<in> ?I \<and> poly p x = 0} = card {x. x > a \<and> poly p x = 0}"
      by (simp add: count_roots_above_correct count_roots_between_correct)
    hence roots[symmetric]: "{x. x \<in> ?I \<and> poly p x = 0} = {x. x > a \<and> poly p x = 0}"
      by (intro card_subset_eq) (auto intro!: poly_roots_finite `p \<noteq> 0`)

    assume A: "\<not>(x \<le> last xs)"
    hence "x > last xs" by auto
    from assms have "a \<le> last xs" unfolding poly_nonneg_witness_above_def Let_def by simp
    with A and assms have "{t. t > last xs \<and> t \<le> x \<and> poly p t = 0} \<subseteq> {t. t > a \<and> poly p t = 0}" 
      by (auto simp: not_le)
    also note roots
    finally have "\<forall>xa. xa > last xs \<and> xa \<le> x \<longrightarrow> poly p xa \<noteq> 0" by auto
    moreover from assms have B: "poly p (last xs) > 0"
      unfolding poly_nonneg_witness_above_def Let_def by (auto simp: list_all_iff)
    ultimately have "\<And>t. t \<ge> last xs \<Longrightarrow> t \<le> x \<Longrightarrow> poly p t \<noteq> 0"
      by (case_tac "t = last xs") auto
    with A have "sgn (poly p (last xs)) = sgn (poly p x)"
      by (intro no_roots_inbetween_imp_same_sign') auto
    with B show "poly p x \<ge> 0" by (auto simp: sgn_real_def split: split_if_asm)    
  qed
qed simp

definition "poly_nonneg_witness_below p xs b \<equiv>
  let a = hd xs; ps = sturm_squarefree p
  in  b = last xs \<and> a \<le> b \<and> xs \<noteq> [] \<and> sorted xs \<and> (sign_changes_neg_inf ps - sign_changes ps b) =
      (sign_changes ps a - sign_changes ps b) \<and>
      nat_all_less (\<lambda>i. sign_changes ps (xs ! i) - sign_changes ps (xs ! Suc i) = 1) (length xs - 1) \<and>
      list_all (\<lambda>x. poly p x > 0) xs"

lemma sturm_nonneg_belowI_aux:
  assumes "poly_nonneg_witness_below p xs b" "x \<le> b"
  shows "poly p x \<ge> 0"
proof (cases "p = 0")
  assume "p \<noteq> 0"
  show ?thesis
  proof (cases "x > hd xs")
    assume A: "x > hd xs"
    from assms `p \<noteq> 0` have "poly_nonneg_witness_between p xs (hd xs) b"
      unfolding poly_nonneg_witness_below_def poly_nonneg_witness_between_def
      by (auto simp: Let_def count_roots_between_def nat_all_less_correct intro!: sorted_nth_mono)
    from assms(2) this A show "poly p x \<ge> 0" by (intro sturm_nonneg_betweenI_aux2) auto
  next
    let ?I = "{hd xs<..last xs}"
    from assms and `p \<noteq> 0` have [simp]: "last xs = b"
      unfolding poly_nonneg_witness_below_def Let_def by simp
    from assms and `p \<noteq> 0` have "count_roots_below p b = count_roots_between p (hd xs) (last xs)"
      unfolding poly_nonneg_witness_below_def count_roots_below_def count_roots_between_def Let_def
      by (auto simp add: count_roots_between_def count_roots_below_def Let_def)
    hence "card {x. x \<in> ?I \<and> poly p x = 0} = card {x. x \<le> b \<and> poly p x = 0}"
      by (simp add: count_roots_below_correct count_roots_between_correct)
    hence roots[symmetric]: "{x. x \<in> ?I \<and> poly p x = 0} = {x. x \<le> b \<and> poly p x = 0}"
      by (intro card_subset_eq) (auto intro!: poly_roots_finite `p \<noteq> 0`)

    assume A: "\<not>(x > hd xs)"
    hence "x \<le> hd xs" by auto
    from assms have "b \<ge> hd xs" unfolding poly_nonneg_witness_below_def Let_def by simp
    with A and assms have "{t. t \<le> hd xs \<and> t \<ge> x \<and> poly p t = 0} \<subseteq> {t. t \<le> b \<and> poly p t = 0}" 
      by (auto simp: not_le)
    also note roots
    finally have "\<forall>xa. xa \<le> hd xs \<and> xa \<ge> x \<longrightarrow> poly p xa \<noteq> 0" by auto
    with A have "sgn (poly p x) = sgn (poly p (hd xs))"
      by (intro no_roots_inbetween_imp_same_sign') auto
    moreover from assms have "poly p (hd xs) > 0"
      unfolding poly_nonneg_witness_below_def Let_def by (auto simp: list_all_iff)
    ultimately show "poly p x \<ge> 0" by (auto simp: sgn_real_def split: split_if_asm)
  qed
qed simp

definition "poly_nonneg_witness p xs \<equiv>
  let a = hd xs; b = last xs; ps = sturm_squarefree p
  in  a \<le> b \<and> xs \<noteq> [] \<and> sorted xs \<and> (sign_changes_neg_inf ps - sign_changes_inf ps) =
      (sign_changes ps a - sign_changes ps b) \<and>
      nat_all_less (\<lambda>i. sign_changes ps (xs ! i) - sign_changes ps (xs ! Suc i) = 1) (length xs - 1) \<and>
      list_all (\<lambda>x. poly p x > 0) xs"

lemma sturm_nonnegI_aux:
  assumes "poly_nonneg_witness p xs"
  shows "poly p x \<ge> 0"
proof (cases "p = 0")
  assume "p \<noteq> 0"
  show ?thesis
  proof (cases "x \<in> {hd xs<..last xs}")
    assume A: "x \<in> {hd xs<..last xs}"
    from assms `p \<noteq> 0` have "poly_nonneg_witness_between p xs (hd xs) (last xs)"
    unfolding poly_nonneg_witness_def poly_nonneg_witness_between_def
      by (auto simp: Let_def count_roots_between_def nat_all_less_correct intro!: sorted_nth_mono)
    from this and A show "poly p x \<ge> 0" by (intro sturm_nonneg_betweenI_aux2) auto
  next
    let ?I = "{hd xs<..last xs}"
    from assms and `p \<noteq> 0` have "count_roots p = count_roots_between p (hd xs) (last xs)"
      by (simp add: count_roots_def count_roots_between_def poly_nonneg_witness_def Let_def)
    hence "card {x. x \<in> ?I \<and> poly p x = 0} = card {x. poly p x = 0}"
      by (simp add: count_roots_correct count_roots_between_correct)
    hence roots[symmetric]: "{x. x \<in> ?I \<and> poly p x = 0} = {x. poly p x = 0}"
      by (intro card_subset_eq) (auto intro!: poly_roots_finite `p \<noteq> 0`)

    assume A: "x \<notin> {hd xs<..last xs}"
    show ?thesis
    proof (cases "x \<le> hd xs")
      assume B: "x \<le> hd xs"
      have "{t. t \<ge> x \<and> t \<le> hd xs \<and> poly p t = 0} \<subseteq> {t. poly p t = 0}" by blast
      also note roots
      finally have "\<forall>xa. x \<le> xa \<and> xa \<le> hd xs \<longrightarrow> poly p xa \<noteq> 0" by auto
      with B have "sgn (poly p x) = sgn (poly p (hd xs))"
        by (intro no_roots_inbetween_imp_same_sign') auto
      moreover from assms have "poly p (hd xs) > 0" 
        unfolding poly_nonneg_witness_def Let_def by (auto simp: list_all_iff)
      ultimately show "poly p x \<ge> 0" by (auto simp: sgn_real_def split: split_if_asm)
    next
      assume "\<not>(x \<le> hd xs)"
      with A have B: "x > last xs" by simp
      have "{t. t > last xs \<and> t \<le> x \<and> poly p t = 0} \<subseteq> {t. poly p t = 0}" by blast
      also note roots
      finally have "\<forall>xa. last xs < xa \<and> xa \<le> x \<longrightarrow> poly p xa \<noteq> 0" by auto
      moreover from assms have C: "poly p (last xs) > 0"
        unfolding poly_nonneg_witness_def Let_def by (auto simp: list_all_iff)
      ultimately have "\<forall>xa. last xs \<le> xa \<and> xa \<le> x \<longrightarrow> poly p xa \<noteq> 0"
        by (intro allI, rename_tac xa, case_tac "xa = last xs") auto
      with B have "sgn (poly p (last xs)) = sgn (poly p x)"
        by (intro no_roots_inbetween_imp_same_sign') auto
      with C show "poly p x \<ge> 0"  by (auto simp: sgn_real_def split: split_if_asm)
    qed
  qed
qed simp

definition "sturm_nonneg_witness p xs \<equiv> p = 0 \<or> poly_nonneg_witness p xs"

definition "sturm_nonneg_witness_above p xs a \<equiv> p = 0 \<or> 
  (let ps = sturm_squarefree p 
   in  hd xs \<ge> a \<and> xs \<noteq> [] \<and> sorted xs \<and> poly p a \<ge> 0 \<and>
       nat_all_less (\<lambda>i. sign_changes ps (xs ! i) - sign_changes ps (xs ! Suc i) = 1) (length xs - 1) \<and>
       sign_changes ps a - sign_changes ps (hd xs) = 0 \<and>
       sign_changes_inf ps = sign_changes ps (last xs) \<and>
       list_all (\<lambda>x. poly p x > 0) xs)"

definition "sturm_nonneg_witness_below p xs b \<equiv> p = 0 \<or> 
  (let ps = sturm_squarefree p 
   in  last xs \<le> b \<and> xs \<noteq> [] \<and> sorted xs \<and> poly p b \<ge> 0 \<and>
       nat_all_less (\<lambda>i. sign_changes ps (xs ! i) - sign_changes ps (xs ! Suc i) = 1) (length xs - 1) \<and>
       sign_changes ps (last xs) - sign_changes ps b = 
         (if poly p b = 0 \<and> last xs < b then 1 else 0) \<and>
       sign_changes_neg_inf ps = sign_changes ps (hd xs) \<and>
       list_all (\<lambda>x. poly p x > 0) xs)"

definition "sturm_nonneg_witness_between p xs a b \<equiv> p = 0 \<or> 
  (let ps = sturm_squarefree p 
   in  hd xs \<ge> a \<and> last xs \<le> b \<and> xs \<noteq> [] \<and> sorted xs \<and> poly p a \<ge> 0 \<and> poly p b \<ge> 0 \<and>
       nat_all_less (\<lambda>i. sign_changes ps (xs ! i) - sign_changes ps (xs ! Suc i) = 1) (length xs - 1) \<and>
       sign_changes ps a - sign_changes ps (hd xs) = 0 \<and>
       sign_changes ps (last xs) - sign_changes ps b = 
         (if poly p b = 0 \<and> last xs < b then 1 else 0) \<and>
       list_all (\<lambda>x. poly p x > 0) xs)"


lemma sturm_nonnegI: "sturm_nonneg_witness p xs \<Longrightarrow> \<forall>x. poly p x \<ge> 0"
  unfolding sturm_nonneg_witness_def
  by (auto intro: sturm_nonnegI_aux)

lemma sorted_hd_le_last: "xs \<noteq> [] \<Longrightarrow> sorted xs \<Longrightarrow> hd xs \<le> last xs"
  by (induction xs) (auto simp: sorted_Cons)

lemma sturm_nonneg_above_geqI:
  assumes "sturm_nonneg_witness_above p xs a"
  shows "\<forall>x. x \<ge> a \<longrightarrow> poly p x \<ge> 0"
proof (cases "p = 0")
  assume [simp]: "p \<noteq> 0"
  from assms have "poly p a \<ge> 0"
    unfolding sturm_nonneg_witness_above_def Let_def by auto
  moreover have "\<forall>x. x > a \<longrightarrow> poly p x \<ge> 0"
  proof (intro allI impI)
    fix x assume "x > a"
    show "poly p x \<ge> 0"
    proof (cases "x > hd xs")
      case False
      from assms have "\<forall>x. x > a \<and> x \<le> hd xs \<longrightarrow> poly p x \<noteq> 0"
        unfolding sturm_nonneg_witness_above_def Let_def
        by (subst poly_no_roots_less_leq) (auto simp: count_roots_between_def)
      with `x > a` have "\<And>t. t \<ge> x \<Longrightarrow> t \<le> hd xs \<Longrightarrow> poly p t \<noteq> 0" by auto
      with False have "sgn (poly p x) = sgn (poly p (hd xs))"
        by (intro no_roots_inbetween_imp_same_sign') auto
      with assms show ?thesis
        by (auto simp: sturm_nonneg_witness_above_def Let_def list_all_iff sgn_real_def 
                 split: split_if_asm)
    next
      case True
      from assms have "poly_nonneg_witness_above p xs (hd xs)"
        unfolding sturm_nonneg_witness_above_def poly_nonneg_witness_above_def 
        by (auto simp: Let_def sorted_nth_mono nat_all_less_correct intro!: sorted_hd_le_last)
      with True and `x > hd xs` show ?thesis by (intro sturm_nonneg_aboveI_aux)
    qed
  qed
  ultimately show ?thesis by (intro allI, rename_tac x, case_tac "x = a") auto
qed simp

lemma sturm_nonneg_above_greaterI:
    "sturm_nonneg_witness_above p xs a \<Longrightarrow> \<forall>x. x > a \<longrightarrow> poly p x \<ge> 0"
  by (drule sturm_nonneg_above_geqI) auto

lemma sturm_nonneg_below_leqI:
  assumes "sturm_nonneg_witness_below p xs b"
  shows "\<forall>x. x \<le> b \<longrightarrow> poly p x \<ge> 0"
proof (cases "p = 0")
  assume [simp]: "p \<noteq> 0"
  from assms have "poly p b \<ge> 0"
    unfolding sturm_nonneg_witness_below_def Let_def by auto
  moreover have "\<forall>x. x < b \<longrightarrow> poly p x \<ge> 0"
  proof (intro allI impI)
    fix x assume "x < b"
    show "poly p x \<ge> 0"
    proof (cases "x \<le> last xs")
      case False
      from assms have "\<forall>x. x > last xs \<and> x < b \<longrightarrow> poly p x \<noteq> 0"
        unfolding sturm_nonneg_witness_below_def Let_def
        by (subst poly_no_roots_less_less) (auto simp: count_roots_between_def)
      with `x < b` have "\<And>t. t \<le> x \<Longrightarrow> t > last xs \<Longrightarrow> poly p t \<noteq> 0" by auto
      moreover from assms have B: "poly p (last xs) > 0"
        by (auto simp: sturm_nonneg_witness_below_def Let_def list_all_iff sgn_real_def 
                 split: split_if_asm)
      ultimately have "\<And>t. t \<le> x \<Longrightarrow> t \<ge> last xs \<Longrightarrow> poly p t \<noteq> 0"
        by (case_tac "t = last xs") auto
      hence "sgn (poly p (last xs)) = sgn (poly p x)" using False
        by (intro no_roots_inbetween_imp_same_sign') auto
      with B show ?thesis by (auto simp: sgn_real_def split: split_if_asm)
    next
      case True
      from assms have "poly_nonneg_witness_below p xs (last xs)"
        unfolding sturm_nonneg_witness_below_def poly_nonneg_witness_below_def 
        by (auto simp: Let_def nat_all_less_correct intro!: sorted_hd_le_last)
      with True and `x \<le> last xs` show ?thesis by (intro sturm_nonneg_belowI_aux)
    qed
  qed
  ultimately show ?thesis by (intro allI, rename_tac x, case_tac "x = b") auto
qed simp

lemma sturm_nonneg_below_lessI:
    "sturm_nonneg_witness_below p xs b \<Longrightarrow> \<forall>x. x < b \<longrightarrow> poly p x \<ge> 0"
  by (drule sturm_nonneg_below_leqI) auto


lemma sturm_nonneg_between_leq_leqI: 
  assumes "sturm_nonneg_witness_between p xs a b"
  shows "\<forall>x. (x \<ge> a \<and> x \<le> b) \<longrightarrow> poly p x \<ge> 0"
proof (cases "p = 0")
  assume [simp]: "p \<noteq> 0"
  from assms have "poly p a \<ge> 0" "poly p b \<ge> 0"
    unfolding sturm_nonneg_witness_between_def Let_def by auto
  moreover have "\<forall>x. (x > a \<and> x < b) \<longrightarrow> poly p x \<ge> 0"
  proof (intro allI impI, elim conjE)
    fix x assume "x > a" "x < b"
    show "poly p x \<ge> 0"
    proof (cases "x > hd xs")
      case False
      from assms have "\<forall>x. x > a \<and> x \<le> hd xs \<longrightarrow> poly p x \<noteq> 0"
        unfolding sturm_nonneg_witness_between_def Let_def
        by (subst poly_no_roots_less_leq) (auto simp: count_roots_between_def)
      with `x > a` have "\<And>t. t \<ge> x \<Longrightarrow> t \<le> hd xs \<Longrightarrow> poly p t \<noteq> 0" by auto
      with False have "sgn (poly p x) = sgn (poly p (hd xs))"
        by (intro no_roots_inbetween_imp_same_sign') auto
      with assms show ?thesis
        by (auto simp: sturm_nonneg_witness_between_def Let_def list_all_iff sgn_real_def 
                 split: split_if_asm)
    next
      case True
      show "poly p x \<ge> 0"
      proof (cases "x \<le> last xs")
        case False
        from assms have "(if poly p b = 0 \<and> last xs < b then 1 else 0) = 
                             count_roots_between p (last xs) b"
          unfolding sturm_nonneg_witness_between_def Let_def by (auto simp: count_roots_between_def) 
        also have "... = card {x. x > last xs \<and> x \<le> b \<and> poly p x = 0}"
          by (rule count_roots_between_correct)
        also have "{x. x > last xs \<and> x \<le> b \<and> poly p x = 0} =
                   {x. x > last xs \<and> x < b \<and> poly p x = 0} \<union>
                   (if poly p b = 0 \<and> last xs < b then {b} else {})" (is "?A = ?B \<union> ?C")
          using assms unfolding sturm_nonneg_witness_between_def Let_def 
          by (auto simp: less_eq_real_def)
        also have "card ... = card ?B + card ?C"
          by (intro card_Un_disjoint)
             (auto intro: finite_subset[OF _ poly_roots_finite[OF `p \<noteq> 0`]])
        also have "card ?C = (if poly p b = 0 \<and> last xs < b then 1 else 0)" by auto
        finally have "card {x. last xs < x \<and> x < b \<and> poly p x = 0} = 0" by auto
        hence "{x. last xs < x \<and> x < b \<and> poly p x = 0} = {}"
          by (subst card_0_eq[symmetric])
             (auto intro!: finite_subset[OF _ poly_roots_finite[OF `p \<noteq> 0`]])
        moreover from assms have A: "poly p (last xs) > 0"
          by (auto simp: sturm_nonneg_witness_between_def Let_def list_all_iff)
        ultimately have "\<And>t. t \<ge> last xs \<Longrightarrow> t \<le> x \<Longrightarrow> poly p t \<noteq> 0" using `x < b`
          by (case_tac "t = last xs") auto
        with False have "sgn (poly p (last xs)) = sgn (poly p x)"
          by (intro no_roots_inbetween_imp_same_sign') auto
        with assms and A show ?thesis by (auto simp: sgn_real_def split: split_if_asm)
      next
        case True
        from assms have "poly_nonneg_witness_between p xs (hd xs) (last xs)"
          unfolding sturm_nonneg_witness_between_def poly_nonneg_witness_between_def 
          by (auto simp: count_roots_between_def Let_def sorted_nth_mono nat_all_less_correct)
        with True and `x > hd xs` show ?thesis by (intro sturm_nonneg_betweenI_aux2)
      qed
    qed
  qed
  ultimately show ?thesis by (intro allI, rename_tac x, case_tac "x = a \<or> x = b") auto
qed simp

lemma sturm_nonneg_between_less_leqI: 
    "sturm_nonneg_witness_between p xs a b \<Longrightarrow> \<forall>x. (x > a \<and> x \<le> b) \<longrightarrow> poly p x \<ge> 0"
  by (drule sturm_nonneg_between_leq_leqI) auto

lemma sturm_nonneg_between_leq_lessI: 
    "sturm_nonneg_witness_between p xs a b \<Longrightarrow> \<forall>x. (x \<ge> a \<and> x < b) \<longrightarrow> poly p x \<ge> 0"
  by (drule sturm_nonneg_between_leq_leqI) auto

lemma sturm_nonneg_between_less_lessI: 
    "sturm_nonneg_witness_between p xs a b \<Longrightarrow> \<forall>x. (x > a \<and> x < b) \<longrightarrow> poly p x \<ge> 0"
  by (drule sturm_nonneg_between_leq_leqI) auto


text {* 
  Note that the above_geq / below_leq versions imply the above_greater / below_less versions.
  We can just shift the witnesses to the left / right by some epsilon. *)
*}
definition sturm_not_nonneg_witness :: "real poly \<Rightarrow> real \<Rightarrow> bool" where
  "sturm_not_nonneg_witness p x \<longleftrightarrow> poly p x < 0"

definition sturm_not_nonneg_witness_above :: "real poly \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "sturm_not_nonneg_witness_above p x a \<longleftrightarrow> x > a \<and> poly p x < 0"

definition sturm_not_nonneg_witness_below :: "real poly \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "sturm_not_nonneg_witness_below p x a \<longleftrightarrow> x < a \<and> poly p x < 0"

definition sturm_not_nonneg_witness_between :: "real poly \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "sturm_not_nonneg_witness_between p x a b \<longleftrightarrow> x > a \<and> x < b \<and> poly p x < 0"

text {* 
  This is required so that the case of a = b also works. Shifting by an epsilon is not possible 
  in this case. 
*}
definition sturm_not_nonneg_witness_between_leq_leq :: "real poly \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "sturm_not_nonneg_witness_between_leq_leq p x a b \<longleftrightarrow> x \<ge> a \<and> x \<le> b \<and> poly p x < 0"

lemma sturm_not_nonnegI:
    "sturm_not_nonneg_witness p x \<Longrightarrow> \<not>(\<forall>x::real. poly p x \<ge> 0)"
  by (auto simp: not_le sturm_not_nonneg_witness_def)

lemma sturm_not_nonneg_above_geqI:
    "sturm_not_nonneg_witness_above p x a \<Longrightarrow> \<not>(\<forall>x::real \<ge> a. poly p x \<ge> 0)"
  by (auto simp: not_le sturm_not_nonneg_witness_above_def intro!: exI[of _ x])

lemma sturm_not_nonneg_above_greaterI:
    "sturm_not_nonneg_witness_above p x a \<Longrightarrow> \<not>(\<forall>x::real > a. poly p x \<ge> 0)"
  by (auto simp: not_le sturm_not_nonneg_witness_above_def intro!: exI[of _ x])

lemma sturm_not_nonneg_below_leqI:
    "sturm_not_nonneg_witness_below p x a \<Longrightarrow> \<not>(\<forall>x::real \<le> a. poly p x \<ge> 0)"
  by (auto simp: not_le sturm_not_nonneg_witness_below_def intro!: exI[of _ x])

lemma sturm_not_nonneg_below_lessI:
    "sturm_not_nonneg_witness_below p x a \<Longrightarrow> \<not>(\<forall>x::real < a. poly p x \<ge> 0)"
  by (auto simp: not_le sturm_not_nonneg_witness_below_def intro!: exI[of _ x])

lemma sturm_not_nonneg_between_less_lessI:
    "sturm_not_nonneg_witness_between p x a b \<Longrightarrow> \<not>(\<forall>x::real. x > a \<and> x < b \<longrightarrow> poly p x \<ge> 0)" 
  by (auto simp: not_le sturm_not_nonneg_witness_between_def intro!: exI[of _ x])

lemma sturm_not_nonneg_between_less_leqI:
    "sturm_not_nonneg_witness_between p x a b \<Longrightarrow> \<not>(\<forall>x::real. x > a \<and> x \<le> b \<longrightarrow> poly p x \<ge> 0)" 
  by (auto simp: not_le sturm_not_nonneg_witness_between_def intro!: exI[of _ x])

lemma sturm_not_nonneg_between_leq_lessI:
    "sturm_not_nonneg_witness_between p x a b \<Longrightarrow> \<not>(\<forall>x::real. x \<ge> a \<and> x < b \<longrightarrow> poly p x \<ge> 0)" 
  by (auto simp: not_le sturm_not_nonneg_witness_between_def intro!: exI[of _ x])

lemma sturm_not_nonneg_between_leq_leqI:
    "sturm_not_nonneg_witness_between_leq_leq p x a b \<Longrightarrow> \<not>(\<forall>x::real. x \<ge> a \<and> x \<le> b \<longrightarrow> poly p x \<ge> 0)" 
  by (auto simp: not_le sturm_not_nonneg_witness_between_leq_leq_def intro!: exI[of _ x])


definition "sturm_mono_witness (p :: real poly) xs \<equiv> sturm_nonneg_witness (pderiv p) xs"
definition "sturm_mono_witness_above (p :: real poly) xs a \<equiv> sturm_nonneg_witness_above (pderiv p) xs a"
definition "sturm_mono_witness_below (p :: real poly) xs a \<equiv> sturm_nonneg_witness_below (pderiv p) xs a"
definition "sturm_mono_witness_between (p :: real poly) xs a b \<equiv> sturm_nonneg_witness_between (pderiv p) xs a b"

lemma sturm_monoI:
    "sturm_mono_witness p xs \<Longrightarrow> mono (poly p)"
  unfolding sturm_mono_witness_def
  by (intro pderiv_ge_0_imp_mono sturm_nonnegI)
lemma sturm_mono_above_geqI:
    "sturm_mono_witness_above p xs a \<Longrightarrow> mono_on (poly p) {a..}"
  unfolding sturm_mono_witness_above_def using sturm_nonneg_above_geqI
  by (intro pderiv_ge_0_imp_mono_on) simp_all
lemma sturm_mono_above_greaterI:
    "sturm_mono_witness_above p xs a \<Longrightarrow> mono_on (poly p) {a<..}"
  unfolding sturm_mono_witness_above_def using sturm_nonneg_above_greaterI
  by (intro pderiv_ge_0_imp_mono_on) simp_all
lemma sturm_mono_below_leqI:
    "sturm_mono_witness_below p xs a \<Longrightarrow> mono_on (poly p) {..a}"
  unfolding sturm_mono_witness_below_def using sturm_nonneg_below_leqI
  by (intro pderiv_ge_0_imp_mono_on) simp_all
lemma sturm_mono_below_lessI:
    "sturm_mono_witness_below p xs a \<Longrightarrow> mono_on (poly p) {..<a}"
  unfolding sturm_mono_witness_below_def using sturm_nonneg_below_lessI
  by (intro pderiv_ge_0_imp_mono_on) simp_all
lemma sturm_mono_between_leq_leqI:
    "sturm_mono_witness_between p xs a b \<Longrightarrow> mono_on (poly p) {a..b}"
  unfolding sturm_mono_witness_between_def using sturm_nonneg_between_leq_leqI
  by (intro pderiv_ge_0_imp_mono_on) simp_all
lemma sturm_mono_between_less_leqI:
    "sturm_mono_witness_between p xs a b \<Longrightarrow> mono_on (poly p) {a<..b}"
  unfolding sturm_mono_witness_between_def using sturm_nonneg_between_less_leqI
  by (intro pderiv_ge_0_imp_mono_on) simp_all
lemma sturm_mono_between_leq_lessI:
    "sturm_mono_witness_between p xs a b \<Longrightarrow> mono_on (poly p) {a..<b}"
  unfolding sturm_mono_witness_between_def using sturm_nonneg_between_leq_lessI
  by (intro pderiv_ge_0_imp_mono_on) simp_all
lemma sturm_mono_between_less_lessI:
    "sturm_mono_witness_between p xs a b \<Longrightarrow> mono_on (poly p) {a<..<b}"
  unfolding sturm_mono_witness_between_def using sturm_nonneg_between_less_lessI
  by (intro pderiv_ge_0_imp_mono_on) simp_all


definition "sturm_strict_mono_witness (p :: real poly) xs \<equiv>
                let p' = pderiv p in p' \<noteq> 0 \<and> sturm_nonneg_witness p' xs"
definition "sturm_strict_mono_witness_above (p :: real poly) xs a \<equiv>
                let p' = pderiv p in p' \<noteq> 0 \<and> sturm_nonneg_witness_above p' xs a"
definition "sturm_strict_mono_witness_below (p :: real poly) xs a \<equiv>
                let p' = pderiv p in p' \<noteq> 0 \<and> sturm_nonneg_witness_below p' xs a"
definition "sturm_strict_mono_witness_between (p :: real poly) xs a b \<equiv>
                let p' = pderiv p in p' \<noteq> 0 \<and> sturm_nonneg_witness_between p' xs a b"

lemma sturm_strict_monoI:
    "sturm_strict_mono_witness p xs \<Longrightarrow> strict_mono (poly p)"
  unfolding sturm_strict_mono_witness_def
  by (intro pderiv_ge_0_imp_strict_mono sturm_nonnegI) (auto simp: Let_def)
lemma sturm_strict_mono_above_geqI:
    "sturm_strict_mono_witness_above p xs a \<Longrightarrow> strict_mono_on (poly p) {a..}"
  unfolding sturm_strict_mono_witness_above_def using sturm_nonneg_above_geqI
  by (intro pderiv_ge_0_imp_strict_mono_on) (auto simp add: Let_def)
lemma sturm_strict_mono_above_greaterI:
    "sturm_strict_mono_witness_above p xs a \<Longrightarrow> strict_mono_on (poly p) {a<..}"
  unfolding sturm_strict_mono_witness_above_def using sturm_nonneg_above_greaterI
  by (intro pderiv_ge_0_imp_strict_mono_on) (auto simp add: Let_def)
lemma sturm_strict_mono_below_leqI:
    "sturm_strict_mono_witness_below p xs a \<Longrightarrow> strict_mono_on (poly p) {..a}"
  unfolding sturm_strict_mono_witness_below_def using sturm_nonneg_below_leqI
  by (intro pderiv_ge_0_imp_strict_mono_on) (auto simp add: Let_def)
lemma sturm_strict_mono_below_lessI:
    "sturm_strict_mono_witness_below p xs a \<Longrightarrow> strict_mono_on (poly p) {..<a}"
  unfolding sturm_strict_mono_witness_below_def using sturm_nonneg_below_lessI
  by (intro pderiv_ge_0_imp_strict_mono_on) (auto simp add: Let_def)
lemma sturm_strict_mono_between_leq_leqI:
    "sturm_strict_mono_witness_between p xs a b \<Longrightarrow> strict_mono_on (poly p) {a..b}"
  unfolding sturm_strict_mono_witness_between_def using sturm_nonneg_between_leq_leqI
  by (intro pderiv_ge_0_imp_strict_mono_on) (auto simp add: Let_def)
lemma sturm_strict_mono_between_less_leqI:
    "sturm_strict_mono_witness_between p xs a b \<Longrightarrow> strict_mono_on (poly p) {a<..b}"
  unfolding sturm_strict_mono_witness_between_def using sturm_nonneg_between_less_leqI
  by (intro pderiv_ge_0_imp_strict_mono_on) (auto simp add: Let_def)
lemma sturm_strict_mono_between_leq_lessI:
    "sturm_strict_mono_witness_between p xs a b \<Longrightarrow> strict_mono_on (poly p) {a..<b}"
  unfolding sturm_strict_mono_witness_between_def using sturm_nonneg_between_leq_lessI
  by (intro pderiv_ge_0_imp_strict_mono_on) (auto simp add: Let_def)
lemma sturm_strict_mono_between_less_lessI:
    "sturm_strict_mono_witness_between p xs a b \<Longrightarrow> strict_mono_on (poly p) {a<..<b}"
  unfolding sturm_strict_mono_witness_between_def using sturm_nonneg_between_less_lessI
  by (intro pderiv_ge_0_imp_strict_mono_on) (auto simp add: Let_def)



lemma sturm_inj_onI_aux:
  fixes p :: "real poly"
  assumes "strict_mono_on (poly p) A \<or> strict_mono_on (poly (-p)) A"
  shows "inj_on (poly p) A"
proof (rule inj_onI)
  fix x y assume "x \<in> A" "y \<in> A" "poly p x = poly p y"
  with assms show "x = y"
    by (cases x y rule: linorder_cases) (force dest: strict_mono_onD)+
qed

definition "sturm_inj_witness (p :: real poly) xs \<equiv>
               let p' = pderiv p in p' \<noteq> 0 \<and> (sturm_nonneg_witness p' xs \<or> sturm_nonneg_witness (-p') xs)"
definition "sturm_inj_witness_above (p :: real poly) xs a \<equiv>
               let p' = pderiv p in p' \<noteq> 0 \<and> 
                 (sturm_nonneg_witness_above p' xs a \<or> sturm_nonneg_witness_above (-p') xs a)"
definition "sturm_inj_witness_below (p :: real poly) xs a \<equiv>
               let p' = pderiv p in p' \<noteq> 0 \<and> 
                 (sturm_nonneg_witness_below p' xs a \<or> sturm_nonneg_witness_below (-p') xs a)"
definition "sturm_inj_witness_between (p :: real poly) xs a b \<equiv>
               let p' = pderiv p in p' \<noteq> 0 \<and> 
                 (sturm_nonneg_witness_between p' xs a b \<or> sturm_nonneg_witness_between (-p') xs a b)"

lemma sturm_injI:
  "sturm_inj_witness p xs \<Longrightarrow> inj (poly p)"
unfolding sturm_inj_witness_def Let_def
apply (elim disjE conjE)
apply (rule sturm_inj_onI_aux, rule disjI1, simp, rule sturm_strict_monoI, simp add: sturm_strict_mono_witness_def)
apply (rule sturm_inj_onI_aux, rule disjI2, simp, rule sturm_strict_monoI, simp add: sturm_strict_mono_witness_def pderiv_minus)
done

lemma sturm_inj_above_geqI:
  "sturm_inj_witness_above p xs a \<Longrightarrow> inj_on (poly p) {a..}"
unfolding sturm_inj_witness_above_def Let_def
apply (elim disjE conjE)
apply (rule sturm_inj_onI_aux, rule disjI1, rule sturm_strict_mono_above_geqI, simp add: sturm_strict_mono_witness_above_def)
apply (rule sturm_inj_onI_aux, rule disjI2, rule sturm_strict_mono_above_geqI, simp add: sturm_strict_mono_witness_above_def pderiv_minus)
done
lemma sturm_inj_above_greaterI:
    "sturm_inj_witness_above p xs a \<Longrightarrow> inj_on (poly p) {a<..}"
  by (erule subset_inj_on[OF sturm_inj_above_geqI]) auto

lemma sturm_inj_below_leqI:
  "sturm_inj_witness_below p xs a \<Longrightarrow> inj_on (poly p) {..a}"
unfolding sturm_inj_witness_below_def Let_def
apply (elim disjE conjE)
apply (rule sturm_inj_onI_aux, rule disjI1, rule sturm_strict_mono_below_leqI, simp add: sturm_strict_mono_witness_below_def)
apply (rule sturm_inj_onI_aux, rule disjI2, rule sturm_strict_mono_below_leqI, simp add: sturm_strict_mono_witness_below_def pderiv_minus)
done
lemma sturm_inj_below_lessI:
    "sturm_inj_witness_below p xs a \<Longrightarrow> inj_on (poly p) {..<a}"
  by (erule subset_inj_on[OF sturm_inj_below_leqI]) auto

lemma sturm_inj_between_leq_leqI:
  "sturm_inj_witness_between p xs a b \<Longrightarrow> inj_on (poly p) {a..b}"
unfolding sturm_inj_witness_between_def Let_def
apply (elim disjE conjE)
apply (rule sturm_inj_onI_aux, rule disjI1, rule sturm_strict_mono_between_leq_leqI, simp add: sturm_strict_mono_witness_between_def)
apply (rule sturm_inj_onI_aux, rule disjI2, rule sturm_strict_mono_between_leq_leqI, simp add: sturm_strict_mono_witness_between_def pderiv_minus)
done
lemma sturm_inj_between_less_leqI:
  "sturm_inj_witness_between p xs a b \<Longrightarrow> inj_on (poly p) {a<..b}"
  by (erule subset_inj_on[OF sturm_inj_between_leq_leqI]) auto
lemma sturm_inj_between_leq_lessI:
  "sturm_inj_witness_between p xs a b \<Longrightarrow> inj_on (poly p) {a..<b}"
  by (erule subset_inj_on[OF sturm_inj_between_leq_leqI]) auto
lemma sturm_inj_between_less_lessI:
  "sturm_inj_witness_between p xs a b \<Longrightarrow> inj_on (poly p) {a<..<b}"
  by (erule subset_inj_on[OF sturm_inj_between_leq_leqI]) auto




lemmas sturm_card_substs = poly_card_roots poly_card_roots_less_leq 
    poly_card_roots_leq_less poly_card_roots_less_less poly_card_roots_leq_leq
    poly_card_roots_less poly_card_roots_leq poly_card_roots_greater
    poly_card_roots_geq 

lemmas sturm_prop_substs = poly_no_roots poly_no_roots_less_leq 
    poly_no_roots_leq_leq poly_no_roots_less_less poly_no_roots_leq_less
    poly_no_roots_leq poly_no_roots_less poly_no_roots_geq 
    poly_no_roots_greater
    poly_pos poly_pos_greater poly_pos_geq poly_pos_less poly_pos_leq
    poly_pos_between_leq_less poly_pos_between_less_leq
    poly_pos_between_leq_leq poly_pos_between_less_less

lemmas sturm_nonneg_intros = sturm_nonnegI sturm_nonneg_above_geqI sturm_nonneg_above_greaterI
    sturm_nonneg_below_leqI sturm_nonneg_below_lessI sturm_nonneg_between_leq_leqI 
    sturm_nonneg_between_leq_lessI sturm_nonneg_between_less_leqI sturm_nonneg_between_less_lessI
    sturm_monoI sturm_mono_above_geqI sturm_mono_above_greaterI sturm_mono_below_leqI 
    sturm_mono_below_lessI sturm_mono_between_leq_leqI sturm_mono_between_less_leqI 
    sturm_mono_between_leq_lessI sturm_mono_between_less_lessI sturm_strict_monoI
    sturm_strict_mono_above_geqI sturm_strict_mono_above_greaterI sturm_strict_mono_below_leqI
    sturm_strict_mono_below_lessI sturm_strict_mono_between_leq_leqI 
    sturm_strict_mono_between_leq_lessI sturm_strict_mono_between_less_leqI
    sturm_strict_mono_between_less_lessI sturm_injI sturm_inj_above_geqI
    sturm_inj_above_greaterI sturm_inj_below_leqI sturm_inj_below_lessI
    sturm_inj_between_leq_leqI sturm_inj_between_leq_lessI sturm_inj_between_less_leqI
    sturm_inj_between_less_lessI

lemmas sturm_not_nonneg_intros = sturm_not_nonnegI sturm_not_nonneg_above_geqI 
    sturm_not_nonneg_above_greaterI sturm_not_nonneg_below_leqI sturm_not_nonneg_below_lessI
    sturm_not_nonneg_between_leq_leqI sturm_not_nonneg_between_leq_lessI 
    sturm_not_nonneg_between_less_leqI sturm_not_nonneg_between_less_lessI 



subsection {* Reification *}

text {*
  This subsection defines a number of equations to automatically convert 
  statements about roots of polynomials into a canonical form so that they 
  can be proven using the above substitutions.
*}

definition "PR_TAG x \<equiv> x"

lemma sturm_id_PR_prio0:
  "{x::real. P x} = {x::real. (PR_TAG P) x}"
  "(\<forall>x::real. f x < g x) = (\<forall>x::real. PR_TAG (\<lambda>x. f x < g x) x)"
  "(\<forall>x::real. f x \<le> g x) = (\<forall>x::real. PR_TAG (\<lambda>x. f x \<le> g x) x)"
  "(\<forall>x::real. P x) = (\<forall>x::real. \<not>(PR_TAG (\<lambda>x. \<not>P x)) x)"
  "(\<exists>x::real. f x < g x) = (\<not>(\<forall>x::real. PR_TAG (\<lambda>x. (f x :: real) \<ge> g x) x))"
  "(\<exists>x::real. f x \<le> g x) = (\<not>(\<forall>x::real. PR_TAG (\<lambda>x. (f x :: real) > g x) x))"
  "(\<exists>x::real. P x) = (\<not>(\<forall>x::real. \<not>(PR_TAG (\<lambda>x. P x)) x))"
  by (simp_all add: PR_TAG_def not_less not_le)

lemma sturm_id_PR_prio1:
  fixes f :: "real \<Rightarrow> real"
  shows
  "{x::real. x < a \<and> P x} = {x::real. x < a \<and> (PR_TAG P) x}"
  "{x::real. x \<le> a \<and> P x} = {x::real. x \<le> a \<and> (PR_TAG P) x}"
  "{x::real. x \<ge> b \<and> P x} = {x::real. x \<ge> b \<and> (PR_TAG P) x}"
  "{x::real. x > b \<and> P x} = {x::real. x > b \<and> (PR_TAG P) x}"
  "(\<forall>x::real < a. f x < g x) = (\<forall>x::real < a. PR_TAG (\<lambda>x. f x < g x) x)"
  "(\<forall>x::real \<le> a. f x < g x) = (\<forall>x::real \<le> a. PR_TAG (\<lambda>x. f x < g x) x)"
  "(\<forall>x::real > a. f x < g x) = (\<forall>x::real > a. PR_TAG (\<lambda>x. f x < g x) x)"
  "(\<forall>x::real \<ge> a. f x < g x) = (\<forall>x::real \<ge> a. PR_TAG (\<lambda>x. f x < g x) x)"
  "(\<forall>x::real < a. f x \<le> g x) = (\<forall>x::real < a. PR_TAG (\<lambda>x. f x \<le> g x) x)"
  "(\<forall>x::real \<le> a. f x \<le> g x) = (\<forall>x::real \<le> a. PR_TAG (\<lambda>x. f x \<le> g x) x)"
  "(\<forall>x::real > a. f x \<le> g x) = (\<forall>x::real > a. PR_TAG (\<lambda>x. f x \<le> g x) x)"
  "(\<forall>x::real \<ge> a. f x \<le> g x) = (\<forall>x::real \<ge> a. PR_TAG (\<lambda>x. f x \<le> g x) x)"
  "(\<forall>x::real < a. P x) = (\<forall>x::real < a. \<not>(PR_TAG (\<lambda>x. \<not>P x)) x)"
  "(\<forall>x::real > a. P x) = (\<forall>x::real > a. \<not>(PR_TAG (\<lambda>x. \<not>P x)) x)"
  "(\<forall>x::real \<le> a. P x) = (\<forall>x::real \<le> a. \<not>(PR_TAG (\<lambda>x. \<not>P x)) x)"
  "(\<forall>x::real \<ge> a. P x) = (\<forall>x::real \<ge> a. \<not>(PR_TAG (\<lambda>x. \<not>P x)) x)"

  "(\<exists>x::real < a. f x < g x) = (\<not>(\<forall>x::real < a. PR_TAG (\<lambda>x. f x \<ge> g x) x))"
  "(\<exists>x::real \<le> a. f x < g x) = (\<not>(\<forall>x::real \<le> a. PR_TAG (\<lambda>x. f x \<ge> g x) x))"
  "(\<exists>x::real > a. f x < g x) = (\<not>(\<forall>x::real > a. PR_TAG (\<lambda>x. f x \<ge> g x) x))"
  "(\<exists>x::real \<ge> a. f x < g x) = (\<not>(\<forall>x::real \<ge> a. PR_TAG (\<lambda>x. f x \<ge> g x) x))"
  "(\<exists>x::real < a. f x \<le> g x) = (\<not>(\<forall>x::real < a. PR_TAG (\<lambda>x. f x > g x) x))"
  "(\<exists>x::real \<le> a. f x \<le> g x) = (\<not>(\<forall>x::real \<le> a. PR_TAG (\<lambda>x. f x > g x) x))"
  "(\<exists>x::real > a. f x \<le> g x) = (\<not>(\<forall>x::real > a. PR_TAG (\<lambda>x. f x > g x) x))"
  "(\<exists>x::real \<ge> a. f x \<le> g x) = (\<not>(\<forall>x::real \<ge> a. PR_TAG (\<lambda>x. f x > g x) x))"
  "(\<exists>x::real < a. P x) = (\<not>(\<forall>x::real < a. \<not>(PR_TAG (\<lambda>x. P x)) x))"
  "(\<exists>x::real > a. P x) = (\<not>(\<forall>x::real > a. \<not>(PR_TAG (\<lambda>x. P x)) x))"
  "(\<exists>x::real \<le> a. P x) = (\<not>(\<forall>x::real \<le> a. \<not>(PR_TAG (\<lambda>x. P x)) x))"
  "(\<exists>x::real \<ge> a. P x) = (\<not>(\<forall>x::real \<ge> a. \<not>(PR_TAG (\<lambda>x. P x)) x))"
  by (simp_all add: PR_TAG_def not_less not_le)

lemma sturm_id_PR_prio2:
  fixes f :: "real \<Rightarrow> real"
  shows
  "{x::real. x > a \<and> x \<le> b \<and> P x} = 
       {x::real. x > a \<and> x \<le> b \<and> PR_TAG P x}"
  "{x::real. x \<ge> a \<and> x \<le> b \<and> P x} = 
       {x::real. x \<ge> a \<and> x \<le> b \<and> PR_TAG P x}"
  "{x::real. x \<ge> a \<and> x < b \<and> P x} = 
       {x::real. x \<ge> a \<and> x < b \<and> PR_TAG P x}"
  "{x::real. x > a \<and> x < b \<and> P x} = 
       {x::real. x > a \<and> x < b \<and> PR_TAG P x}"
  "(\<forall>x::real. a < x \<and> x \<le> b \<longrightarrow> f x < g x) = 
       (\<forall>x::real. a < x \<and> x \<le> b \<longrightarrow> PR_TAG (\<lambda>x. f x < g x) x)"
  "(\<forall>x::real. a \<le> x \<and> x \<le> b \<longrightarrow> f x < g x) = 
       (\<forall>x::real. a \<le> x \<and> x \<le> b \<longrightarrow> PR_TAG (\<lambda>x. f x < g x) x)"
  "(\<forall>x::real. a < x \<and> x < b \<longrightarrow> f x < g x) = 
       (\<forall>x::real. a < x \<and> x < b \<longrightarrow> PR_TAG (\<lambda>x. f x < g x) x)"
  "(\<forall>x::real. a \<le> x \<and> x < b \<longrightarrow> f x < g x) = 
       (\<forall>x::real. a \<le> x \<and> x < b \<longrightarrow> PR_TAG (\<lambda>x. f x < g x) x)"
  "(\<forall>x::real. a < x \<and> x \<le> b \<longrightarrow> f x \<le> g x) = 
       (\<forall>x::real. a < x \<and> x \<le> b \<longrightarrow> PR_TAG (\<lambda>x. f x \<le> g x) x)"
  "(\<forall>x::real. a \<le> x \<and> x \<le> b \<longrightarrow> f x \<le> g x) = 
       (\<forall>x::real. a \<le> x \<and> x \<le> b \<longrightarrow> PR_TAG (\<lambda>x. f x \<le> g x) x)"
  "(\<forall>x::real. a < x \<and> x < b \<longrightarrow> f x \<le> g x) = 
       (\<forall>x::real. a < x \<and> x < b \<longrightarrow> PR_TAG (\<lambda>x. f x \<le> g x) x)"
  "(\<forall>x::real. a \<le> x \<and> x < b \<longrightarrow> f x \<le> g x) = 
       (\<forall>x::real. a \<le> x \<and> x < b \<longrightarrow> PR_TAG (\<lambda>x. f x \<le> g x) x)"
  "(\<forall>x::real. a < x \<and> x \<le> b \<longrightarrow> P x) = 
       (\<forall>x::real. a < x \<and> x \<le> b \<longrightarrow> \<not>(PR_TAG (\<lambda>x. \<not>P x)) x)"
  "(\<forall>x::real. a \<le> x \<and> x \<le> b \<longrightarrow> P x) = 
       (\<forall>x::real. a \<le> x \<and> x \<le> b \<longrightarrow> \<not>(PR_TAG (\<lambda>x. \<not>P x)) x)"
  "(\<forall>x::real. a \<le> x \<and> x < b \<longrightarrow> P x) = 
       (\<forall>x::real. a \<le> x \<and> x < b \<longrightarrow> \<not>(PR_TAG (\<lambda>x. \<not>P x)) x)"
  "(\<forall>x::real. a < x \<and> x < b \<longrightarrow> P x) = 
       (\<forall>x::real. a < x \<and> x < b \<longrightarrow> \<not>(PR_TAG (\<lambda>x. \<not>P x)) x)"
  "(\<exists>x::real. a < x \<and> x \<le> b \<and> f x < g x) = 
       (\<not>(\<forall>x::real. a < x \<and> x \<le> b \<longrightarrow> PR_TAG (\<lambda>x. f x \<ge> g x) x))"
  "(\<exists>x::real. a \<le> x \<and> x \<le> b \<and> f x < g x) = 
       (\<not>(\<forall>x::real. a \<le> x \<and> x \<le> b \<longrightarrow> PR_TAG (\<lambda>x. f x \<ge> g x) x))"
  "(\<exists>x::real. a < x \<and> x < b \<and> f x < g x) = 
       (\<not>(\<forall>x::real. a < x \<and> x < b \<longrightarrow> PR_TAG (\<lambda>x. f x \<ge> g x) x))"
  "(\<exists>x::real. a \<le> x \<and> x < b \<and> f x < g x) = 
       (\<not>(\<forall>x::real. a \<le> x \<and> x < b \<longrightarrow> PR_TAG (\<lambda>x. f x \<ge> g x) x))"
  "(\<exists>x::real. a < x \<and> x \<le> b \<and> f x \<le> g x) = 
       (\<not>(\<forall>x::real. a < x \<and> x \<le> b \<longrightarrow> PR_TAG (\<lambda>x. f x > g x) x))"
  "(\<exists>x::real. a \<le> x \<and> x \<le> b \<and> f x \<le> g x) = 
       (\<not>(\<forall>x::real. a \<le> x \<and> x \<le> b \<longrightarrow> PR_TAG (\<lambda>x. f x > g x) x))"
  "(\<exists>x::real. a < x \<and> x < b \<and> f x \<le> g x) = 
       (\<not>(\<forall>x::real. a < x \<and> x < b \<longrightarrow> PR_TAG (\<lambda>x. f x > g x) x))"
  "(\<exists>x::real. a \<le> x \<and> x < b \<and> f x \<le> g x) = 
       (\<not>(\<forall>x::real. a \<le> x \<and> x < b \<longrightarrow> PR_TAG (\<lambda>x. f x > g x) x))"
  "(\<exists>x::real. a < x \<and> x \<le> b \<and> P x) = 
       (\<not>(\<forall>x::real. a < x \<and> x \<le> b \<longrightarrow> \<not>(PR_TAG (\<lambda>x. P x)) x))"
  "(\<exists>x::real. a \<le> x \<and> x \<le> b \<and> P x) = 
       (\<not>(\<forall>x::real. a \<le> x \<and> x \<le> b \<longrightarrow> \<not>(PR_TAG (\<lambda>x. P x)) x))"
  "(\<exists>x::real. a \<le> x \<and> x < b \<and> P x) = 
       (\<not>(\<forall>x::real. a \<le> x \<and> x < b \<longrightarrow> \<not>(PR_TAG (\<lambda>x. P x)) x))"
  "(\<exists>x::real. a < x \<and> x < b \<and> P x) = 
       (\<not>(\<forall>x::real. a < x \<and> x < b \<longrightarrow> \<not>(PR_TAG (\<lambda>x. P x)) x))"
  by (simp_all add: PR_TAG_def not_less not_le)

lemma sturm_id_PR_prio3:
  "mono (P :: real \<Rightarrow> real) = mono (PR_TAG P)"
  "mono_on (P :: real \<Rightarrow> real) = mono_on (PR_TAG P)"
  "strict_mono P = strict_mono (PR_TAG P)"
  "strict_mono_on P = strict_mono_on (PR_TAG P)"
  "mono_dec P = mono (PR_TAG (\<lambda>x. -P x))"
  "mono_dec_on P = mono_on (PR_TAG (\<lambda>x. -P x))"
  "strict_mono_dec P = strict_mono (PR_TAG (\<lambda>x. -P x))"
  "strict_mono_dec_on P = strict_mono_on (PR_TAG (\<lambda>x. -P x))"
  "inj_on P = inj_on (PR_TAG P)"
  by (auto simp: PR_TAG_def mono_dec_mono_conv strict_mono_dec_strict_mono_conv
                 mono_dec_on_mono_on_conv strict_mono_dec_on_strict_mono_on_conv)


lemma PR_TAG_intro_prio0:
  fixes P :: "real \<Rightarrow> bool" and f :: "real \<Rightarrow> real"
  shows
  "PR_TAG P = P' \<Longrightarrow> PR_TAG (\<lambda>x. \<not>(\<not>P x)) = P'"
  "\<lbrakk>PR_TAG P = (\<lambda>x. poly p x = 0); PR_TAG Q = (\<lambda>x. poly q x = 0)\<rbrakk>
       \<Longrightarrow> PR_TAG (\<lambda>x. P x \<and> Q x) = (\<lambda>x. poly (gcd p q) x = 0)" and
  "\<lbrakk>PR_TAG P = (\<lambda>x. poly p x = 0); PR_TAG Q = (\<lambda>x. poly q x = 0)\<rbrakk>
       \<Longrightarrow> PR_TAG (\<lambda>x. P x \<or> Q x) = (\<lambda>x. poly (p*q) x = 0)" and

  "\<lbrakk>PR_TAG f = (\<lambda>x. poly p x); PR_TAG g = (\<lambda>x. poly q x)\<rbrakk>
       \<Longrightarrow> PR_TAG (\<lambda>x. f x = g x) = (\<lambda>x. poly (p-q) x = 0)"
  "\<lbrakk>PR_TAG f = (\<lambda>x. poly p x); PR_TAG g = (\<lambda>x. poly q x)\<rbrakk>
       \<Longrightarrow> PR_TAG (\<lambda>x. f x \<noteq> g x) = (\<lambda>x. poly (p-q) x \<noteq> 0)"
  "\<lbrakk>PR_TAG f = (\<lambda>x. poly p x); PR_TAG g = (\<lambda>x. poly q x)\<rbrakk>
       \<Longrightarrow> PR_TAG (\<lambda>x. f x < g x) = (\<lambda>x. poly (q-p) x > 0)"
  "\<lbrakk>PR_TAG f = (\<lambda>x. poly p x); PR_TAG g = (\<lambda>x. poly q x)\<rbrakk>
       \<Longrightarrow> PR_TAG (\<lambda>x. f x \<le> g x) = (\<lambda>x. poly (q-p) x \<ge> 0)"

  "PR_TAG f = (\<lambda>x. poly p x) \<Longrightarrow> PR_TAG (\<lambda>x. -f x) = (\<lambda>x. poly (-p) x)"
  "\<lbrakk>PR_TAG f = (\<lambda>x. poly p x); PR_TAG g = (\<lambda>x. poly q x)\<rbrakk>
       \<Longrightarrow> PR_TAG (\<lambda>x. f x + g x) = (\<lambda>x. poly (p+q) x)"
  "\<lbrakk>PR_TAG f = (\<lambda>x. poly p x); PR_TAG g = (\<lambda>x. poly q x)\<rbrakk>
       \<Longrightarrow> PR_TAG (\<lambda>x. f x - g x) = (\<lambda>x. poly (p-q) x)"
  "\<lbrakk>PR_TAG f = (\<lambda>x. poly p x); PR_TAG g = (\<lambda>x. poly q x)\<rbrakk>
       \<Longrightarrow> PR_TAG (\<lambda>x. f x * g x) = (\<lambda>x. poly (p*q) x)"
  "PR_TAG f = (\<lambda>x. poly p x) \<Longrightarrow> PR_TAG (\<lambda>x. (f x)^n) = (\<lambda>x. poly (p^n) x)"
  "PR_TAG (\<lambda>x. poly p x :: real) = (\<lambda>x. poly p x)"
  "PR_TAG (\<lambda>x. x::real) = (\<lambda>x. poly [:0,1:] x)"
  "PR_TAG (\<lambda>x. a::real) = (\<lambda>x. poly [:a:] x)"
  by (simp_all add: PR_TAG_def poly_eq_0_iff_dvd field_simps)


lemma PR_TAG_intro_prio1:
  fixes f :: "real \<Rightarrow> real"
  shows
  "PR_TAG f = (\<lambda>x. poly p x) \<Longrightarrow> PR_TAG (\<lambda>x. f x = 0) = (\<lambda>x. poly p x = 0)"
  "PR_TAG f = (\<lambda>x. poly p x) \<Longrightarrow> PR_TAG (\<lambda>x. f x \<noteq> 0) = (\<lambda>x. poly p x \<noteq> 0)"
  "PR_TAG f = (\<lambda>x. poly p x) \<Longrightarrow> PR_TAG (\<lambda>x. 0 = f x) = (\<lambda>x. poly p x = 0)"
  "PR_TAG f = (\<lambda>x. poly p x) \<Longrightarrow> PR_TAG (\<lambda>x. 0 \<noteq> f x) = (\<lambda>x. poly p x \<noteq> 0)"
  "PR_TAG f = (\<lambda>x. poly p x) \<Longrightarrow> PR_TAG (\<lambda>x. f x \<ge> 0) = (\<lambda>x. poly p x \<ge> 0)"
  "PR_TAG f = (\<lambda>x. poly p x) \<Longrightarrow> PR_TAG (\<lambda>x. f x > 0) = (\<lambda>x. poly p x > 0)"
  "PR_TAG f = (\<lambda>x. poly p x) \<Longrightarrow> PR_TAG (\<lambda>x. f x \<le> 0) = (\<lambda>x. poly (-p) x \<ge> 0)"
  "PR_TAG f = (\<lambda>x. poly p x) \<Longrightarrow> PR_TAG (\<lambda>x. f x < 0) = (\<lambda>x. poly (-p) x > 0)"
  "PR_TAG f = (\<lambda>x. poly p x) \<Longrightarrow> 
       PR_TAG (\<lambda>x. 0 \<le> f x) = (\<lambda>x. poly (-p) x \<le> 0)"
  "PR_TAG f = (\<lambda>x. poly p x) \<Longrightarrow> 
       PR_TAG (\<lambda>x. 0 < f x) = (\<lambda>x. poly (-p) x < 0)"
  "PR_TAG f = (\<lambda>x. poly p x) 
       \<Longrightarrow> PR_TAG (\<lambda>x. a * f x) = (\<lambda>x. poly (smult a p) x)"
  "PR_TAG f = (\<lambda>x. poly p x) 
       \<Longrightarrow> PR_TAG (\<lambda>x. f x * a) = (\<lambda>x. poly (smult a p) x)"
  "PR_TAG f = (\<lambda>x. poly p x) 
       \<Longrightarrow> PR_TAG (\<lambda>x. f x / a) = (\<lambda>x. poly (smult (inverse a) p) x)"
  "PR_TAG (\<lambda>x. x^n :: real) = (\<lambda>x. poly (monom 1 n) x)"
using assms by (simp_all add: PR_TAG_def field_simps poly_monom)

lemma PR_TAG_intro_prio2:
  "PR_TAG (\<lambda>x. 1 / b) = (\<lambda>x. inverse b)"
  "PR_TAG (\<lambda>x. a / b) = (\<lambda>x. a / b)"
  "PR_TAG (\<lambda>x. a / b * x^n :: real) = (\<lambda>x. poly (monom (a/b) n) x)"
  "PR_TAG (\<lambda>x. x^n * a / b :: real) = (\<lambda>x. poly (monom (a/b) n) x)"
  "PR_TAG (\<lambda>x. a * x^n :: real) = (\<lambda>x. poly (monom a n) x)"
  "PR_TAG (\<lambda>x. x^n * a :: real) = (\<lambda>x. poly (monom a n) x)"
  "PR_TAG (\<lambda>x. x^n / a :: real) = (\<lambda>x. poly (monom (inverse a) n) x)"
(* TODO: can this be done more efficiently? I should think so. *)
  "PR_TAG (\<lambda>x. f x^(Suc (Suc 0)) :: real) = (\<lambda>x. poly p x)
       \<Longrightarrow> PR_TAG (\<lambda>x. f x * f x :: real) = (\<lambda>x. poly p x)"
  "PR_TAG (\<lambda>x. (f x)^Suc n :: real) = (\<lambda>x. poly p x)
       \<Longrightarrow> PR_TAG (\<lambda>x. (f x)^n * f x :: real) = (\<lambda>x. poly p x)"
  "PR_TAG (\<lambda>x. (f x)^Suc n :: real) = (\<lambda>x. poly p x)
       \<Longrightarrow> PR_TAG (\<lambda>x. f x * (f x)^n :: real) = (\<lambda>x. poly p x)"
  "PR_TAG (\<lambda>x. (f x)^(m+n) :: real) = (\<lambda>x. poly p x)
       \<Longrightarrow> PR_TAG (\<lambda>x. (f x)^m * (f x)^n :: real) = (\<lambda>x. poly p x)"
using assms by (simp_all add: PR_TAG_def field_simps poly_monom power_add)

lemma sturm_meta_spec: "(\<And>x::real. P x) \<Longrightarrow> P x" by simp
lemma sturm_imp_conv: 
  "(a < x \<longrightarrow> x < b \<longrightarrow> c) \<longleftrightarrow> (a < x \<and> x < b \<longrightarrow> c)"
  "(a \<le> x \<longrightarrow> x < b \<longrightarrow> c) \<longleftrightarrow> (a \<le> x \<and> x < b \<longrightarrow> c)"
  "(a < x \<longrightarrow> x \<le> b \<longrightarrow> c) \<longleftrightarrow> (a < x \<and> x \<le> b \<longrightarrow> c)"
  "(a \<le> x \<longrightarrow> x \<le> b \<longrightarrow> c) \<longleftrightarrow> (a \<le> x \<and> x \<le> b \<longrightarrow> c)"
  "(x < b \<longrightarrow> a < x \<longrightarrow> c) \<longleftrightarrow> (a < x \<and> x < b \<longrightarrow> c)"
  "(x < b \<longrightarrow> a \<le> x \<longrightarrow> c) \<longleftrightarrow> (a \<le> x \<and> x < b \<longrightarrow> c)"
  "(x \<le> b \<longrightarrow> a < x \<longrightarrow> c) \<longleftrightarrow> (a < x \<and> x \<le> b \<longrightarrow> c)"
  "(x \<le> b \<longrightarrow> a \<le> x \<longrightarrow> c) \<longleftrightarrow> (a \<le> x \<and> x \<le> b \<longrightarrow> c)"
  by (auto simp: abs_less_iff abs_le_iff)

lemma sturm_preprocess:
  "x \<in> {a..} \<longleftrightarrow> x \<ge> a"
  "x \<in> {a<..} \<longleftrightarrow> x > a"
  "x \<in> {..b} \<longleftrightarrow> x \<le> b"
  "x \<in> {..<b} \<longleftrightarrow> x < b"
  "x \<in> {a..b} \<longleftrightarrow> x \<ge> a \<and> x \<le> b"
  "x \<in> {a<..b} \<longleftrightarrow> x > a \<and> x \<le> b"
  "x \<in> {a..<b} \<longleftrightarrow> x \<ge> a \<and> x < b"
  "x \<in> {a<..<b} \<longleftrightarrow> x > a \<and> x < b"
  "(abs x < a) \<longleftrightarrow> (-a < x \<and> x < (a::real))"
  "(abs (x - a) < b) \<longleftrightarrow> (a - b < x \<and> x < (a::real) + b)"
  "(abs (a - x) < b) \<longleftrightarrow> (a - b < x \<and> x < (a::real) + b)"
  "(abs x \<le> a) \<longleftrightarrow> (-a \<le> x \<and> x \<le> (a::real))"
  "(abs (x - a) \<le> b) \<longleftrightarrow> (a - b \<le> x \<and> x \<le> (a::real) + b)"
  "(abs (a - x) \<le> b) \<longleftrightarrow> (a - b \<le> x \<and> x \<le> (a::real) + b)"
  "(\<forall>x\<in>A. P x) \<longleftrightarrow> (\<forall>x. x \<in> A \<longrightarrow> P x)"
  "(\<forall>y x. x \<le> y \<longrightarrow> Q x y) \<longleftrightarrow> (\<forall>x y. x \<le> y \<longrightarrow> Q x y)"
  "(\<forall>y x. x < y \<longrightarrow> Q x y) \<longleftrightarrow> (\<forall>x y. x < y \<longrightarrow> Q x y)"
  "(\<forall>x y. x \<noteq> y \<longrightarrow> f x \<noteq> f y) \<longleftrightarrow> inj f"
  "(\<forall>x y. x \<le> y \<longrightarrow> f x \<le> f y) \<longleftrightarrow> mono f"
  "(\<forall>x y. x < y \<longrightarrow> f x < f y) \<longleftrightarrow> strict_mono f"
  "(\<forall>x y. x \<le> y \<longrightarrow> f x \<ge> f y) \<longleftrightarrow> mono_dec f"
  "(\<forall>x y. x < y \<longrightarrow> f x > f y) \<longleftrightarrow> strict_mono_dec f"
  by (auto simp: mono_def strict_mono_def mono_dec_def strict_mono_dec_def inj_on_def)

definition pow_aux :: "real poly \<Rightarrow> nat \<Rightarrow> real poly" where "pow_aux \<equiv> op ^"
definition term_of_rpoly_aux :: "real poly \<Rightarrow> _" where "term_of_rpoly_aux = Code_Evaluation.term_of"
definition term_of_nat_aux :: "nat \<Rightarrow> _" where "term_of_nat_aux = Code_Evaluation.term_of"
definition zero_aux :: "real poly" where "zero_aux = Groups.zero"

subsection {* Setup for the ``sturm'' method *}

ML_file "rat_polynomial.ML"
ML_file "rat_sturm.ML"
ML_file "sturm.ML"

method_setup sturm = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (Sturm.sturm_tac ctxt false))
*}

hide_const pow_aux term_of_rpoly_aux term_of_nat_aux zero_aux

schematic_lemma A:
  "card {x::real. -0.010831 < x \<and> x < 0.010831 \<and> 
      1/120*x^5 + 1/24 * x^4 +1/6*x^3 - 49/16777216*x^2 - 17/2097152*x = 0} = ?n" by sturm

end

