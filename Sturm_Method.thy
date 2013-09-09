theory Sturm_Method
imports Sturm
begin

section {* Setup for the sturm method *}

lemma poly_card_roots_less_leq:
  "card {x. a < x \<and> x \<le> b \<and> poly p x = 0} = count_roots_between p a b"
  by (simp add: count_roots_between_correct)

lemma poly_card_roots_leq_leq:
  "card {x. a \<le> x \<and> x \<le> b \<and> poly p x = 0} = count_roots_between p a b + 
      (if (a \<le> b \<and> poly p a = 0 \<and> p \<noteq> 0) \<or> (a = b \<and> p = 0) then 1 else 0)"
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
        with True False show ?thesis
            using count_roots_between_correct 
            by (simp add: real_interval_card_eq)
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
  "card {x. a < x \<and> x < b \<and> poly p x = 0} = count_roots_between p a b -
              (if poly p b = 0 \<and> a < b \<and> p \<noteq> 0 then 1 else 0)"
proof (cases "poly p b = 0 \<and> a < b \<and> p \<noteq> 0")
  case False
    note False' = this
    show ?thesis
    proof (cases "p = 0")
      case True
        have [simp]: "{x. a < x \<and> x < b} = {a<..<b}"
                     "{x. a < x \<and> x \<le> b} = {a<..b}" by auto
        from True False' assms show ?thesis 
            by (auto simp: count_roots_between_correct real_interval_card_eq)
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
      count_roots_between p a b +
      (if p \<noteq> 0 \<and> a < b \<and> poly p a = 0 then 1 else 0) -
      (if p \<noteq> 0 \<and> a < b \<and> poly p b = 0 then 1 else 0)"
proof (cases "p = 0 \<or> a \<ge> b")
  case True
    note True' = this
    show ?thesis
    proof (cases "a \<ge> b")
      case False
        hence "{x. a < x \<and> x \<le> b} = {a<..b}"
              "{x. a \<le> x \<and> x < b} = {a..<b}" by auto
        with False True' show ?thesis 
            by (simp add: count_roots_between_correct real_interval_card_eq)
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
  "(\<forall>x. poly p x \<noteq> 0) \<longleftrightarrow> p \<noteq> 0 \<and> count_roots p = 0"
    by (auto simp: count_roots_correct dest: poly_roots_finite)


lemma poly_card_roots_greater:
  "card {x::real. x > a \<and> poly p x = 0} = count_roots_above p a"
  using assms count_roots_above_correct by simp

lemma poly_card_roots_leq:
  "card {x::real. x \<le> a \<and> poly p x = 0} = count_roots_below p a"
  using assms  count_roots_below_correct by simp

lemma poly_card_roots_geq:
  "card {x::real. x \<ge> a \<and> poly p x = 0} = 
      count_roots_above p a + (if poly p a = 0 \<and> p \<noteq> 0 then 1 else 0)"
proof (cases "poly p a = 0 \<and> p \<noteq> 0")
  case False
    hence "card {x. x \<ge> a \<and> poly p x = 0} = card {x. x > a \<and> poly p x = 0}"
    proof (cases rule: disjE)
      assume "p = 0"
      have "\<not>finite {a<..<a+1}" using real_infinite_interval by simp
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
       count_roots_below p a - (if poly p a = 0 \<and> p \<noteq> 0 then 1 else 0)"
proof (cases "poly p a = 0 \<and> p \<noteq> 0")
  case False
    hence "card {x. x < a \<and> poly p x = 0} = card {x. x \<le> a \<and> poly p x = 0}"
    proof (cases rule: disjE)
      assume "p = 0"
      have "\<not>finite {a - 1<..<a}" using real_infinite_interval by simp
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
   (a \<ge> b \<or> (p \<noteq> 0 \<and> count_roots_between p a b = 0))"
  by (auto simp: count_roots_between_correct card_eq_0_iff not_le 
           intro: poly_roots_finite)

lemma poly_no_roots_leq_leq:
  "(\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> poly p x \<noteq> 0) \<longleftrightarrow>
   (a > b \<or> (p \<noteq> 0 \<and> poly p a \<noteq> 0 \<and> count_roots_between p a b = 0))"
apply (intro iffI)
apply (force simp add: count_roots_between_correct card_eq_0_iff)
apply (elim conjE disjE, simp, intro allI)
apply (rename_tac x, case_tac "x = a")
apply (auto simp add: count_roots_between_correct card_eq_0_iff
            intro: poly_roots_finite)
done

lemma poly_no_roots_less_less:
  "(\<forall>x. a < x \<and> x < b \<longrightarrow> poly p x \<noteq> 0) \<longleftrightarrow>
   (a \<ge> b \<or> p \<noteq> 0 \<and> count_roots_between p a b = (if poly p b = 0 then 1 else 0))"
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
            auto intro: poly_roots_finite)
qed


lemma poly_no_roots_leq_less:
  "(\<forall>x. a \<le> x \<and> x < b \<longrightarrow> poly p x \<noteq> 0) \<longleftrightarrow> 
   (a \<ge> b \<or> p \<noteq> 0 \<and> poly p a \<noteq> 0 \<and> count_roots_between p a b = 
       (if a < b \<and> poly p b = 0 then 1 else 0))"
proof
  case goal1
    hence "\<forall>x. a < x \<and> x < b \<longrightarrow> poly p x \<noteq> 0" by simp
    thus ?case using goal1 by (subst (asm) poly_no_roots_less_less, auto)
next
  case goal2
    hence "(b \<le> a \<or> p \<noteq> 0 \<and> count_roots_between p a b = 
               (if poly p b = 0 then 1 else 0))" by auto
    thus ?case using goal2 by (subst (asm) poly_no_roots_less_less[symmetric], 
        auto split: split_if_asm simp: less_eq_real_def) 
qed

lemma poly_no_roots_greater:
  "(\<forall>x. x > a \<longrightarrow> poly p x \<noteq> 0) \<longleftrightarrow> (p \<noteq> 0 \<and> count_roots_above p a = 0)"
proof-
  have "\<forall>x. \<not> a < x \<Longrightarrow> False" by (metis gt_ex)
  thus ?thesis by (auto simp: count_roots_above_correct card_eq_0_iff
                        intro: poly_roots_finite )
qed

lemma poly_no_roots_leq:
  "(\<forall>x. x \<le> a \<longrightarrow> poly p x \<noteq> 0) \<longleftrightarrow> (p \<noteq> 0 \<and> count_roots_below p a = 0)"
    by (auto simp: count_roots_below_correct card_eq_0_iff
             intro: poly_roots_finite )

lemma poly_no_roots_geq:
  "(\<forall>x. x \<ge> a \<longrightarrow> poly p x \<noteq> 0) \<longleftrightarrow>
       (p \<noteq> 0 \<and> poly p a \<noteq> 0 \<and> count_roots_above p a = 0)"
proof
  case goal1
  hence "\<forall>x>a. poly p x \<noteq> 0" by simp
  thus ?case using goal1 by (subst (asm) poly_no_roots_greater, auto)
next
  case goal2
  hence "(p \<noteq> 0 \<and> count_roots_above p a = 0)" by simp
  thus ?case using goal2 
      by (subst (asm) poly_no_roots_greater[symmetric], 
          auto simp: less_eq_real_def)
qed

lemma poly_no_roots_less:
  "(\<forall>x. x < a \<longrightarrow> poly p x \<noteq> 0) \<longleftrightarrow>
       (p \<noteq> 0 \<and> count_roots_below p a = (if poly p a = 0 then 1 else 0))"
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

lemmas sturm_card_substs = poly_card_roots poly_card_roots_less_leq 
    poly_card_roots_leq_less poly_card_roots_less_less poly_card_roots_leq_leq
    poly_card_roots_less poly_card_roots_leq poly_card_roots_greater
    poly_card_roots_geq 

lemmas sturm_prop_substs = poly_no_roots poly_no_roots_less_leq 
    poly_no_roots_leq_leq poly_no_roots_less_less poly_no_roots_leq_less
    poly_no_roots_leq poly_no_roots_less poly_no_roots_geq poly_no_roots_greater


ML_file "sturm.ML"

method_setup sturm = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (Sturm.sturm_tac ctxt))
*}

schematic_lemma "card {x::real. x \<ge> 0 \<and> poly [:0, 0, 1:] x = 0} = ?n" by sturm

lemma "card {x::real. poly [:1,0,1:] x = 0} = 0" by sturm

lemma "\<forall>x::real. poly [:1,0,1:] x \<noteq> 0" by sturm

lemma  "\<forall>x::real. 1 < x \<and> x < 2 \<longrightarrow> poly [:0, -17/2097152, -49/16777216, 
                  1/6, 1/24, 1/120:] x \<noteq> 0" by sturm

schematic_lemma A:
  "card {x::real. -0.010831 < x \<and> x < 0.010831 \<and> 
     poly [:0, -17/2097152, -49/16777216, 1/6, 1/24, 1/120:] x = 0} = ?n"
by sturm

end