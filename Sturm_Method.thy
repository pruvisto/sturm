theory Sturm_Method
imports Sturm "~~/src/HOL/Library/LaTeXsugar" "~~/src/HOL/Library/OptionalSugar"
begin

section {* Setup for the sturm method *}

lemma poly_card_roots_less_leq:
  "count_roots_between p a b = n \<Longrightarrow> 
       card {x. a < x \<and> x \<le> b \<and> poly p x = 0} = n"
  by (simp add: count_roots_between_correct)

lemma poly_card_roots_leq_leq:
  assumes "Suc (count_roots_between p a b) = 
      (if (a \<le> b \<and> poly p a = 0 \<and> p \<noteq> 0) \<or> (a = b \<and> p = 0) then n else Suc n)"
  shows "card {x. a \<le> x \<and> x \<le> b \<and> poly p x = 0} = n"
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
        have [simp]: "{x. a \<le> x \<and> x \<le> b} = {a..b}"
                     "{x. a < x \<and> x \<le> b} = {a<..b}" by auto
        from False True assms have "count_roots_between 0 a b = n" 
            by (auto split: split_if_asm)
        also note count_roots_between_correct
        finally show ?thesis using True False
            by (auto simp: real_interval_card_eq)
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
    also have "... = n"
        using True count_roots_between_correct assms by auto
    finally show ?thesis .
qed

lemma poly_card_roots_less_less:
  assumes "count_roots_between p a b = 
      (if poly p b = 0 \<and> a < b \<and> p \<noteq> 0 then Suc n else n)"
  shows "card {x. a < x \<and> x < b \<and> poly p x = 0} = n"
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
    also have "count_roots_between p a b = Suc n" using assms True by simp
    finally show ?thesis by simp
qed

lemma poly_card_roots_leq_less:
  assumes "Suc (count_roots_between p a b) = 
      (if p = 0 \<or> a \<ge> b then Suc 0
         else (if poly p a = 0 then 0 else Suc 0) + 
              (if poly p b = 0 then Suc 0 else 0)) + n"
  shows "card {x::real. a \<le> x \<and> x < b \<and> poly p x = 0} = n"
proof (cases "p = 0 \<or> a \<ge> b")
  case True
    note True' = this
    show ?thesis
    proof (cases "a \<ge> b")
      case False
        have [simp]: "{x. a < x \<and> x \<le> b} = {a<..b}"
                     "{x. a \<le> x \<and> x < b} = {a..<b}" by auto
        from False True' assms show ?thesis 
            by (auto simp: count_roots_between_correct real_interval_card_eq)
    next
      case True
        with True' have "{x. a \<le> x \<and> x < b \<and> poly p x = 0} = 
                          {x. a < x \<and> x \<le> b \<and> poly p x = 0}"
          by (auto simp: less_eq_real_def)
      thus ?thesis using poly_card_roots_less_leq assms True by auto
  qed
next
  case False
    let ?A = "{x. a \<le> x \<and> x < b \<and> poly p x = 0}"
    let ?B = "{x. a < x \<and> x \<le> b \<and> poly p x = 0}"
    let ?C = "{x. x = b \<and> poly p x = 0}"
    let ?D = "{x. x = a \<and> poly p a = 0}"
    from False have A: "?C \<subseteq> ?B" and B: "(?B-?C) \<inter> ?D = {}" by auto
    have CD_if: "?C = (if poly p b = 0 then {b} else {})"
                "?D = (if poly p a = 0 then {a} else {})" by auto
    from False poly_roots_finite 
        have [simp]: "finite ?A" "finite ?B" "finite ?C" "finite ?D"
            by (fast, fast, simp_all)
    from False have C: "?A = (?B \<union> ?D) - ?C" by (auto simp: less_eq_real_def)
    from False have "?C \<subseteq> ?B \<union> ?D" "?B \<inter> ?D = {}" by auto

    from count_roots_between_correct
        have "Suc (count_roots_between p a b) = Suc (card ?B)" by simp
    also note assms
    finally have "Suc (card ?B) = n + (if poly p a = 0 then 0 else Suc 0) +
                      (if poly p b = 0 then Suc 0 else 0)" using False by simp
    hence "n = Suc (card ?B) - (if poly p a = 0 then 0 else Suc 0) - 
               (if poly p b = 0 then Suc 0 else 0)" by (auto simp: field_simps)
    also have "... = card ?B + card ?D - card ?C" by (auto simp: CD_if)
    also have "... = card ?A"
        by (rule sym, subst C, subst card_Diff_subset, simp, fact,
                subst card_Un_disjoint, simp, simp, fact, rule refl)
    finally show ?thesis ..
qed

lemma poly_card_roots:
  assumes "count_roots p = n"
  shows "card {x::real. poly p x = 0} = n"
  using assms count_roots_correct by simp

lemma poly_no_roots:
  assumes "p \<noteq> 0 \<and> count_roots p = 0"
  shows "\<forall>x. poly p x \<noteq> 0"
proof-
  from assms have "finite {x. poly p x = 0}" using poly_roots_finite ..
  with assms have "{x. poly p x = 0} = {}" 
      by (simp add: card_eq_0_iff count_roots_correct)
  thus ?thesis by simp
qed


lemma poly_card_roots_greater:
  assumes "count_roots_above p a = n"
  shows "card {x::real. x > a \<and> poly p x = 0} = n"
  using assms  count_roots_above_correct by simp

lemma poly_card_roots_leq:
  assumes "count_roots_below p a = n"
  shows "card {x::real. x \<le> a \<and> poly p x = 0} = n"
  using assms  count_roots_below_correct by simp

lemma poly_card_roots_geq:
  assumes "Suc (count_roots_above p a) = 
      (if poly p a = 0 \<and> p \<noteq> 0 then n else Suc n)"
  shows "card {x::real. x \<ge> a \<and> poly p x = 0} = n"
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
  assumes "count_roots_below p a = 
      (if poly p a = 0 \<and> p \<noteq> 0 then Suc n else n)"
  shows "card {x::real. x < a \<and> poly p x = 0} = n"
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
    also from assms True have "card {x. x \<le> a \<and> poly p x = 0} = Suc n"
        by (intro poly_card_roots_leq, simp)
    finally show ?thesis by simp
qed



lemma poly_no_roots_less_leq:
  assumes "p \<noteq> 0 \<and> count_roots_between p a b = 0"
  shows "\<forall>x. a < x \<and> x \<le> b \<longrightarrow> poly p x \<noteq> 0"
proof-
  from assms have "finite {x. poly p x = 0}" using poly_roots_finite ..
  with assms
      have "{x. a < x \<and> x \<le> b \<and> poly p x = 0} = {}"
      by (auto simp add: card_eq_0_iff count_roots_between_correct
               intro: poly_card_roots_less_leq)
  thus ?thesis by simp
qed

lemma poly_no_roots_leq_leq:
  assumes "p \<noteq> 0 \<and> poly p a \<noteq> 0 \<and> count_roots_between p a b = 0"
  shows "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> poly p x \<noteq> 0"
proof-
  from assms have "\<forall>x. a < x \<and> x \<le> b \<longrightarrow> poly p x \<noteq> 0"
      by (intro poly_no_roots_less_leq, simp_all)
  with assms show ?thesis 
      by (intro allI, rename_tac x, case_tac "x = a", auto) 
qed

lemma poly_no_roots_less_less:
  assumes "p \<noteq> 0 \<and> count_roots_between p a b = 
                       (if a < b \<and> poly p b = 0 then 1 else 0)"
  shows "\<forall>x. a < x \<and> x < b \<longrightarrow> poly p x \<noteq> 0"
proof (cases "a < b \<and> poly p b = 0")
  case False
    with assms have "p \<noteq> 0 \<and> count_roots_between p a b = 0" by simp
    from poly_no_roots_less_leq[OF this] show ?thesis
        by (intro allI, rename_tac x, case_tac "x = b", simp_all)
next
  case True
    from assms have fin: "finite {x. poly p x = 0}" using poly_roots_finite ..
    hence fin': "finite {x. a < x \<and> x < b \<and> poly p x = 0}"
        by (force intro: finite_subset)
    from True assms have "1 = card {x. a < x \<and> x \<le> b \<and> poly p x = 0}" 
        (is "1 = card ?S") by (simp add: count_roots_between_correct)
    also have "?S = insert b {x. a < x \<and> x < b \<and> poly p x = 0}" 
        using assms True by auto
    also have "card ... = Suc (card {x. a < x \<and> x < b \<and> poly p x = 0})"
        by (subst card_insert_disjoint, 
            force intro: finite_subset fin, simp_all)
    finally have "{x. a < x \<and> x < b \<and> poly p x = 0} = {}" using fin' by simp
    thus ?thesis by simp
qed


lemma poly_no_roots_leq_less:
  assumes "p \<noteq> 0 \<and> poly p a \<noteq> 0 \<and> count_roots_between p a b = 
                       (if a < b \<and> poly p b = 0 then 1 else 0)"
  shows "\<forall>x. a \<le> x \<and> x < b \<longrightarrow> poly p x \<noteq> 0"
proof-
  from assms have "p \<noteq> 0 \<and> count_roots_between p a b =
                       (if a < b \<and> poly p b = 0 then 1 else 0)" by simp
  from poly_no_roots_less_less[OF this] and assms show ?thesis
      by (intro allI, rename_tac x, case_tac "x = a", simp_all)
qed

lemma poly_no_roots_greater:
  assumes "p \<noteq> 0 \<and> count_roots_above p a = 0"
  shows "\<forall>x. x > a \<longrightarrow> poly p x \<noteq> 0"
proof-
  from assms have "finite {x. poly p x = 0}" using poly_roots_finite ..
  with assms
      have "{x. x > a \<and> poly p x = 0} = {}"
      by (auto simp add: card_eq_0_iff count_roots_above_correct
               intro: poly_card_roots_less_leq)
  thus ?thesis by simp
qed

lemma poly_no_roots_leq:
  assumes "p \<noteq> 0 \<and> count_roots_below p a = 0"
  shows "\<forall>x. x \<le> a \<longrightarrow> poly p x \<noteq> 0"
proof-
  from assms have "finite {x. poly p x = 0}" using poly_roots_finite ..
  with assms
      have "{x. x \<le> a \<and> poly p x = 0} = {}"
      by (auto simp add: card_eq_0_iff count_roots_below_correct
               intro: poly_card_roots_less_leq)
  thus ?thesis by simp
qed

lemma poly_no_roots_geq:
  assumes "p \<noteq> 0 \<and> poly p a \<noteq> 0 \<and> 
               count_roots_above p a = 0"
  shows "\<forall>x. x \<ge> a \<longrightarrow> poly p x \<noteq> 0"
proof (clarify)
  fix x assume "x \<ge> a" "poly p x = 0"
  moreover with assms have "x \<noteq> a" by auto
  ultimately have "x > a" by simp
  with assms and poly_no_roots_greater have "poly p x \<noteq> 0" by auto
  thus False using `poly p x = 0` by contradiction
qed

lemma poly_no_roots_less:
  assumes "p \<noteq> 0 \<and> count_roots_below p a = (if poly p a = 0 then 1 else 0)"
  shows "\<forall>x. x < a \<longrightarrow> poly p x \<noteq> 0"
proof (cases "poly p a = 0")
  case False
    thus ?thesis using assms poly_no_roots_leq
        by (intro allI, rename_tac x, case_tac "x = a", auto)
next
  case True
    from assms have fin: "finite {x. poly p x = 0}" using poly_roots_finite ..
    hence fin: "finite {x. x < a \<and> poly p x = 0}" by simp
    from assms and True have "1 = count_roots_below p a" by simp
    also have "... = card {x. x \<le> a \<and> poly p x = 0}" 
         using count_roots_below_correct .
    also from True 
        have "{x. x \<le> a \<and> poly p x = 0} = insert a {x. x < a \<and> poly p x = 0}"
        by auto
    also have "card ... = Suc (card {x. x < a \<and> poly p x = 0})"
        using card_insert_disjoint[OF fin] by simp
    finally have "card {x. x < a \<and> poly p x = 0} = 0" by simp
    with fin have "{x. x < a \<and> poly p x = 0} = {}" by simp
    thus ?thesis by blast
qed


lemmas sturm_intros = poly_card_roots poly_card_roots_less_leq 
    poly_card_roots_leq_less poly_card_roots_less_less poly_card_roots_leq_leq
    poly_card_roots_less poly_card_roots_leq poly_card_roots_greater
    poly_card_roots_geq poly_no_roots poly_no_roots_less_leq 
    poly_no_roots_leq_leq poly_no_roots_less_less poly_no_roots_leq_less
    poly_no_roots_leq poly_no_roots_less poly_no_roots_geq poly_no_roots_greater

ML {*

fun pretty_thm ctxt thm =
Syntax.pretty_term ctxt (prop_of thm)

  fun sturm_instantiate_tac ctxt thm =
    let val concl = concl_of thm
        val prems = prems_of thm
        val vars = Term.add_vars concl []
        val thy = Proof_Context.theory_of ctxt
    in if length vars = 1 then
          let val a = hd prems |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst
              val (idxname,_) = hd vars
              val (SOME n) = Code_Evaluation.dynamic_value thy a
              val n' = HOLogic.dest_nat n
              val thm' = read_instantiate ctxt [(idxname, Int.toString n')] thm
           in Seq.single thm'
           end
        else
          Seq.single thm
    end;
    

*}

method_setup sturm = {*
let
  fun sturm_conv thy = Code_Runtime.static_holds_conv thy
  [@{const_name count_roots_between}, @{const_name count_roots},
   @{const_name count_roots_above},@{const_name count_roots_below},
   @{const_name Trueprop}, @{const_name Rat.of_int}, 
   @{const_name Power.power_class.power},
   @{const_name Num.nat_of_num}]
in
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD' (
      fn i =>
        resolve_tac @{thms sturm_intros} 1
        THEN sturm_instantiate_tac ctxt
        THEN CONVERSION (sturm_conv (Proof_Context.theory_of ctxt)) 1
(*        THEN rtac TrueI 1*)
))
end
*} "decide how many roots a polynomial has"

lemma "\<forall>x::real. poly [:1,0,1:] x \<noteq> 0" by sturm

lemma  "\<forall>x::real. 1 < x \<and> x < 2 \<longrightarrow> poly [:0, -17/2097152, -49/16777216, 
                  1/6, 1/24, 1/120:] x \<noteq> 0" by sturm


schematic_lemma A:
  "card {x::real. -0.010831 < x \<and> x < 0.010831 \<and> 
     poly [:0, -17/2097152, -49/16777216, 1/6, 1/24, 1/120:] x = 0} = ?n"
by sturm

end