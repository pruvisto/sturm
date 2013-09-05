theory Sturm
imports "~~/src/HOL/Library/Poly_Deriv" SturmLibrary
begin

locale quasi_sturm_seq =
  fixes ps :: "(real poly) list"
  assumes last_ps_sgn_const[simp]: 
      "\<And>x y. sgn (poly (last ps) x) = sgn (poly (last ps) y)"
  assumes ps_not_Nil[simp]: "ps \<noteq> []"
  assumes signs: "\<And>i x. \<lbrakk>i < length ps - 2; poly (ps ! (i+1)) x = 0\<rbrakk>
                     \<Longrightarrow> (poly (ps ! (i+2)) x) * (poly (ps ! i) x) < 0"
begin

  lemma (in -) sturm_adjacent_root_aux:
    assumes "i < length (ps :: real poly list) - 1"
    assumes "poly (ps ! i) x = 0" and "poly (ps ! (i + 1)) x = 0"
    assumes "\<And>i x. \<lbrakk>i < length ps - 2; poly (ps ! (i+1)) x = 0\<rbrakk>
                     \<Longrightarrow> sgn (poly (ps ! (i+2)) x) = - sgn (poly (ps ! i) x)"
    shows "\<forall>j\<le>i+1. poly (ps ! j) x = 0"
  using assms
  proof (induction i)
    case 0 thus ?case by (clarsimp, rename_tac j, case_tac j, simp_all)
  next
    case (Suc i)
      from Suc.prems(1,2) 
          have "sgn (poly (ps ! (i + 2)) x) = - sgn (poly (ps ! i) x)"
          by (intro assms(4)) simp_all
      with Suc.prems(3) have "poly (ps ! i) x = 0" by (simp add: sgn_zero_iff)
      with Suc.prems have "\<forall>j\<le>i+1. poly (ps ! j) x = 0"
          by (intro Suc.IH, simp_all)
      with Suc.prems(3) show ?case
        by (clarsimp, rename_tac j, case_tac "j = Suc (Suc i)", simp_all)
  qed


end

lemma [simp]: "\<not>quasi_sturm_seq []" by (simp add: quasi_sturm_seq_def)

lemma quasi_sturm_seq_Cons:
  assumes "quasi_sturm_seq (p#ps)" and "ps \<noteq> []"
  shows "quasi_sturm_seq ps"
proof (unfold_locales)
  show "ps \<noteq> []" by fact
next
  from assms(1) interpret quasi_sturm_seq "p#ps" .
  fix x y
  from last_ps_sgn_const and `ps \<noteq> []` 
      show "sgn (poly (last ps) x) = sgn (poly (last ps) y)" by simp_all
next
  from assms(1) interpret quasi_sturm_seq "p#ps" .
  fix i x
  assume "i < length ps - 2" and "poly (ps ! (i+1)) x = 0"
  with signs[of "i+1"] 
      show "poly (ps ! (i+2)) x * poly (ps ! i) x < 0" by simp
qed

  

locale sturm_seq = quasi_sturm_seq + 
  fixes p :: "real poly"
  assumes hd_ps_p[simp]: "hd ps = p"
  assumes length_ps_ge_2[simp]: "length ps \<ge> 2"
  assumes deriv: "\<And>x\<^isub>0. poly p x\<^isub>0 = 0 \<Longrightarrow> 
      eventually (\<lambda>x. sgn (poly (ps!1) x) = 
                      sgn (x - x\<^isub>0) * sgn (poly p x)) (at x\<^isub>0)"
begin

  lemma quasi_sturm_seq: "quasi_sturm_seq ps" ..

  lemma ps_first_two:
    obtains q ps' where "ps = p # q # ps'"
    using hd_ps_p length_ps_ge_2
      by (cases ps, simp, clarsimp, rename_tac ps', case_tac ps', auto)

  lemma ps_first: "ps ! 0 = p" by (rule ps_first_two, simp)

end


definition no_adjacent_roots where
"no_adjacent_roots ps = (\<forall>i x. i < length ps - 1 \<longrightarrow> 
    poly (ps!i) x = 0 \<longrightarrow> poly (ps!(i+1)) x = 0 \<longrightarrow> False)"

lemma no_adjacent_rootsI[intro]:
  assumes "\<And>i x. i < length ps - 1 \<Longrightarrow> 
               poly (ps!i) x = 0 \<Longrightarrow> poly (ps!(i+1)) x = 0 \<Longrightarrow> False"
  shows "no_adjacent_roots ps"
  using assms unfolding no_adjacent_roots_def by force

lemma no_adjacent_rootsD[dest]:
  assumes "no_adjacent_roots ps"
  assumes "i < length ps - 1" "poly (ps!i) x = 0" "poly (ps!(i+1)) x = 0"
  shows False
  using assms unfolding no_adjacent_roots_def by force

lemma [simp]: "length ps < 2 \<Longrightarrow> no_adjacent_roots ps"
  unfolding no_adjacent_roots_def by simp

lemma no_adjacent_roots_distrib[dest]:
  assumes "no_adjacent_roots (ps\<^isub>1 @ ps\<^isub>2)"
  shows "no_adjacent_roots ps\<^isub>1" and "no_adjacent_roots ps\<^isub>2"
proof-
  let ?ps = "ps\<^isub>1 @ ps\<^isub>2"
  show "no_adjacent_roots ps\<^isub>1"
  proof
    case (goal1 i x)
      from goal1 have "?ps ! i = ps\<^isub>1 ! i" "?ps ! (i+1) = ps\<^isub>1 ! (i+1)" 
          by (auto simp: nth_append)
      with goal1 have "poly (?ps ! i) x = 0" and
                      "poly (?ps ! (i+1)) x = 0" by simp_all
      from goal1 and no_adjacent_rootsD[OF assms _ this] show False by force
  qed

  show "no_adjacent_roots ps\<^isub>2"
  proof
    case (goal1 i x)
      let ?l = "length ps\<^isub>1"
      from goal1 have "?ps ! (?l + i) = ps\<^isub>2 ! i" "?ps ! (?l+i+1) = ps\<^isub>2 ! (i+1)" 
          by (auto simp: nth_append)
      with goal1 have "poly (?ps ! (?l+i)) x = 0" and
                      "poly (?ps ! (?l+i+1)) x = 0" by simp_all
      from goal1 and no_adjacent_rootsD[OF assms _ this] show False by force
  qed
qed


locale sturm_seq_squarefree = sturm_seq +
  assumes p_squarefree: "\<And>x. \<not>(poly p x = 0 \<and> poly (ps!1) x = 0)"
begin
end



definition sign_changes where
"sign_changes ps (x::real) = 
    length (group (filter (\<lambda>x. x \<noteq> 0) (map (\<lambda>p. sgn (poly p x)) ps))) - 1"

lemma sign_changes_distrib:
  "poly p x \<noteq> 0 \<Longrightarrow> 
      sign_changes (ps\<^isub>1 @ [p] @ ps\<^isub>2) x = 
      sign_changes (ps\<^isub>1 @ [p]) x + sign_changes ([p] @ ps\<^isub>2) x"
  by (simp add: sign_changes_def sgn_zero_iff, subst group_append, simp)

lemma same_signs_imp_same_sign_changes:
  assumes "\<forall>p \<in> set ps. sgn (poly p x) = sgn (poly p y)"
  shows "sign_changes ps x = sign_changes ps y"
proof-
  from assms have A: "map (\<lambda>p. sgn (poly p x)) ps = map (\<lambda>p. sgn (poly p y)) ps"
     by (induction ps, simp_all)
  show ?thesis unfolding sign_changes_def by (simp add: A)
qed

lemma sign_changes_sturm_triple:
  assumes "poly p x \<noteq> 0" and "sgn (poly r x) = - sgn (poly p x)"
  shows "sign_changes [p,q,r] x = 1"
unfolding sign_changes_def
apply (insert assms)
apply (cases "poly p x" rule: sgn_real_cases)
apply (cases "poly q x" rule: sgn_real_cases, simp_all add: sgn_zero_iff) []
apply (cases "poly q x" rule: sgn_real_cases, simp_all add: sgn_zero_iff) []
apply (cases "poly q x" rule: sgn_real_cases, simp_all add: sgn_zero_iff) []
done


definition sign_changes_inf where
"sign_changes_inf ps = 
    length (group (filter (\<lambda>x. x \<noteq> 0) (map poly_inf ps))) - 1"

definition sign_changes_neg_inf where
"sign_changes_neg_inf ps = 
    length (group (filter (\<lambda>x. x \<noteq> 0) (map poly_neg_inf ps))) - 1"



fun split_sign_changes where
"split_sign_changes [p] x = [[p]]" |
"split_sign_changes [p,q] x = [[p,q]]" |
"split_sign_changes (p#q#r#ps) x =
    (if poly p x \<noteq> 0 \<and> poly q x = 0 then 
       [p,q,r] # split_sign_changes (r#ps) x
     else
       [p,q] # split_sign_changes (q#r#ps) x)"

lemma (in quasi_sturm_seq) split_sign_changes_subset[dest]:
  "ps' \<in> set (split_sign_changes ps x) \<Longrightarrow> set ps' \<subseteq> set ps"
apply (insert ps_not_Nil)
apply (induction ps x rule: split_sign_changes.induct)
apply (simp, simp, rename_tac p q r ps x, 
       case_tac "poly p x \<noteq> 0 \<and> poly q x = 0", auto)
done

lemma (in quasi_sturm_seq) split_sign_changes_induct:
  "\<lbrakk>\<And>p x. P [p] x; \<And>p q x. quasi_sturm_seq [p,q] \<Longrightarrow> P [p,q] x;
    \<And>p q r ps x. quasi_sturm_seq (p#q#r#ps) \<Longrightarrow>
       \<lbrakk>poly p x \<noteq> 0 \<Longrightarrow> poly q x = 0 \<Longrightarrow> P (r#ps) x; 
        poly q x \<noteq> 0 \<Longrightarrow> P (q#r#ps) x;
        poly p x = 0 \<Longrightarrow> P (q#r#ps) x\<rbrakk> 
           \<Longrightarrow> P (p#q#r#ps) x\<rbrakk> \<Longrightarrow> P ps x"
proof-
  case goal1
  have "quasi_sturm_seq ps" ..
  with goal1 show ?thesis
  proof (induction ps x rule: split_sign_changes.induct)
    case (goal3 p q r ps x)
      show ?case
      proof (rule goal3(5)[OF goal3(6)])
        assume A: "poly p x \<noteq> 0" "poly q x = 0"
        from goal3(6) have "quasi_sturm_seq (r#ps)" 
            by (force dest: quasi_sturm_seq_Cons)
        with goal3 A show "P (r # ps) x" by blast
      next
        assume A: "poly q x \<noteq> 0"
        from goal3(6) have "quasi_sturm_seq (q#r#ps)"
            by (force dest: quasi_sturm_seq_Cons)
        with goal3 A show "P (q # r # ps) x" by blast
      next
        assume A: "poly p x = 0"
        from goal3(6) have "quasi_sturm_seq (q#r#ps)"
            by (force dest: quasi_sturm_seq_Cons)
        with goal3 A show "P (q # r # ps) x" by blast
      qed
  qed simp_all  
qed



lemma (in quasi_sturm_seq) split_sign_changes_correct:
  assumes "poly (hd ps) x\<^isub>0 \<noteq> 0"
  defines "sign_changes' \<equiv> \<lambda>ps x. 
               \<Sum>ps'\<leftarrow>split_sign_changes ps x. sign_changes ps' x"
  shows "sign_changes' ps x\<^isub>0 = sign_changes ps x\<^isub>0"
using assms(1)
proof (induction x\<^isub>0 rule: split_sign_changes_induct)
case (goal3 p q r ps x\<^isub>0)
  hence "poly p x\<^isub>0 \<noteq> 0" by simp
  note IH = goal3(2,3,4)
  show ?case
  proof (cases "poly q x\<^isub>0 = 0")
    case True
      from goal3 interpret quasi_sturm_seq "p#q#r#ps" by simp
      from signs[of 0] and True have 
           sgn_r_x0: "poly r x\<^isub>0 * poly p x\<^isub>0 < 0" by simp
      with goal3 have "poly r x\<^isub>0 \<noteq> 0" by force
      from sign_changes_distrib[OF this, of "[p,q]" ps]
        have "sign_changes (p#q#r#ps) x\<^isub>0 =
                  sign_changes ([p, q, r]) x\<^isub>0 + sign_changes (r # ps) x\<^isub>0" by simp
      also have "sign_changes (r#ps) x\<^isub>0 = sign_changes' (r#ps) x\<^isub>0"
          using `poly q x\<^isub>0 = 0` `poly p x\<^isub>0 \<noteq> 0` goal3(5)`poly r x\<^isub>0 \<noteq> 0`
          by (intro IH(1)[symmetric], simp_all)
      finally show ?thesis unfolding sign_changes'_def 
          using True `poly p x\<^isub>0 \<noteq> 0` by simp
  next
    case False
      from sign_changes_distrib[OF this, of "[p]" "r#ps"]
          have "sign_changes (p#q#r#ps) x\<^isub>0 = 
                  sign_changes ([p,q]) x\<^isub>0 + sign_changes (q#r#ps) x\<^isub>0" by simp
      also have "sign_changes (q#r#ps) x\<^isub>0 = sign_changes' (q#r#ps) x\<^isub>0"
          using `poly q x\<^isub>0 \<noteq> 0` `poly p x\<^isub>0 \<noteq> 0` goal3(5)
          by (intro IH(2)[symmetric], simp_all)
      finally show ?thesis unfolding sign_changes'_def 
          using False by simp
    qed
qed (simp_all add: sign_changes_def sign_changes'_def)



lemma (in quasi_sturm_seq) split_sign_changes_correct_nbh:
  assumes "poly (hd ps) x\<^isub>0 \<noteq> 0"
  defines "sign_changes' \<equiv> \<lambda>x\<^isub>0 ps x. 
               \<Sum>ps'\<leftarrow>split_sign_changes ps x\<^isub>0. sign_changes ps' x"
  shows "eventually (\<lambda>x. sign_changes' x\<^isub>0 ps x = sign_changes ps x) (at x\<^isub>0)"
proof (rule eventually_mono)
  case goal1
  let ?ps_nz = "{p \<in> set ps. poly p x\<^isub>0 \<noteq> 0}"
  show "eventually (\<lambda>x. \<forall>p\<in>?ps_nz. sgn (poly p x) = sgn (poly p x\<^isub>0)) (at x\<^isub>0)"
      by (rule eventually_Ball_finite, auto intro: poly_neighbourhood_same_sign)

  show "\<forall>x. (\<forall>p\<in>{p \<in> set ps. poly p x\<^isub>0 \<noteq> 0}. sgn (poly p x) = sgn (poly p x\<^isub>0)) \<longrightarrow>
        sign_changes' x\<^isub>0 ps x = sign_changes ps x"
  proof (clarify)
    fix x assume nbh: "\<forall>p\<in>?ps_nz. sgn (poly p x) = sgn (poly p x\<^isub>0)"
    thus "sign_changes' x\<^isub>0 ps x = sign_changes ps x" using assms(1)
    proof (induction x\<^isub>0 rule: split_sign_changes_induct)
    case (goal3 p q r ps x\<^isub>0)
      hence "poly p x\<^isub>0 \<noteq> 0" by simp
      note IH = goal3(2,3,4)
      show ?case
      proof (cases "poly q x\<^isub>0 = 0")
        case True
          from goal3 interpret quasi_sturm_seq "p#q#r#ps" by simp
          from signs[of 0] and True have 
               sgn_r_x0: "poly r x\<^isub>0 * poly p x\<^isub>0 < 0" by simp
          with goal3 have "poly r x\<^isub>0 \<noteq> 0" by force
          with nbh goal3(5) have "poly r x \<noteq> 0" by (auto simp: sgn_zero_iff)
          from sign_changes_distrib[OF this, of "[p,q]" ps]
            have "sign_changes (p#q#r#ps) x =
                      sign_changes ([p, q, r]) x + sign_changes (r # ps) x" by simp
          also have "sign_changes (r#ps) x = sign_changes' x\<^isub>0 (r#ps) x"
              using `poly q x\<^isub>0 = 0` nbh `poly p x\<^isub>0 \<noteq> 0` goal3(5)`poly r x\<^isub>0 \<noteq> 0`
              by (intro IH(1)[symmetric], simp_all)
          finally show ?thesis unfolding sign_changes'_def 
              using True `poly p x\<^isub>0 \<noteq> 0`by simp
      next
        case False
          with nbh goal3(5) have "poly q x \<noteq> 0" by (auto simp: sgn_zero_iff)
          from sign_changes_distrib[OF this, of "[p]" "r#ps"]
              have "sign_changes (p#q#r#ps) x = 
                      sign_changes ([p,q]) x + sign_changes (q#r#ps) x" by simp
          also have "sign_changes (q#r#ps) x = sign_changes' x\<^isub>0 (q#r#ps) x"
              using `poly q x\<^isub>0 \<noteq> 0` nbh `poly p x\<^isub>0 \<noteq> 0` goal3(5)
              by (intro IH(2)[symmetric], simp_all)
          finally show ?thesis unfolding sign_changes'_def 
              using False by simp
        qed
    qed (simp_all add: sign_changes_def sign_changes'_def)
  qed
qed



lemma (in quasi_sturm_seq) hd_nonzero_imp_sign_changes_const_aux:
  assumes "poly (hd ps) x\<^isub>0 \<noteq> 0" and "ps' \<in> set (split_sign_changes ps x\<^isub>0)"
  shows "eventually (\<lambda>x. sign_changes ps' x = sign_changes ps' x\<^isub>0) (at x\<^isub>0)"
using assms
proof (induction x\<^isub>0 rule: split_sign_changes_induct)
  case (goal1 p x)
    thus ?case by (simp add: sign_changes_def)
next
  case (goal2 p q x\<^isub>0)
    hence [simp]: "ps' = [p,q]" by simp
    from goal2 have "poly p x\<^isub>0 \<noteq> 0" by simp
    from goal2(1) interpret quasi_sturm_seq "[p,q]" .
    from poly_neighbourhood_same_sign[OF `poly p x\<^isub>0 \<noteq> 0`]
        have "eventually (\<lambda>x. sgn (poly p x) = sgn (poly p x\<^isub>0)) (at x\<^isub>0)" .
    moreover from last_ps_sgn_const
        have sgn_q: "\<And>x. sgn (poly q x) = sgn (poly q x\<^isub>0)" by simp
    ultimately have A:  "eventually (\<lambda>x. \<forall>p\<in>set[p,q]. sgn (poly p x) = 
                           sgn (poly p x\<^isub>0)) (at x\<^isub>0)" by simp
    thus ?case by (force intro: eventually_mono[OF _ A] 
                                same_signs_imp_same_sign_changes)
next
  case (goal3 p q r ps'' x\<^isub>0)
    hence p_not_0: "poly p x\<^isub>0 \<noteq> 0" by simp
    note sturm = goal3(1)
    note IH = goal3(2,3)
    note ps''_props = goal3(6)
    show ?case
    proof (cases "poly q x\<^isub>0 = 0")
      case True
        note q_0 = this
        from sturm interpret quasi_sturm_seq "p#q#r#ps''" .
        from signs[of 0] and q_0 
            have signs': "poly r x\<^isub>0 * poly p x\<^isub>0 < 0" by simp
        with p_not_0 have r_not_0: "poly r x\<^isub>0 \<noteq> 0" by force
        show ?thesis
        proof (cases "ps' \<in> set (split_sign_changes (r # ps'') x\<^isub>0)")
          case True
            show ?thesis by (rule IH(1), fact, fact, simp add: r_not_0, fact)
        next
          case False
            with ps''_props p_not_0 q_0 have ps'_props: "ps' = [p,q,r]" by simp
            from signs[of 0] and q_0 
                have sgn_r: "poly r x\<^isub>0 * poly p x\<^isub>0 < 0" by simp
            from p_not_0 sgn_r
              have A: "eventually (\<lambda>x. sgn (poly p x) = sgn (poly p x\<^isub>0) \<and>
                                     sgn (poly r x) = sgn (poly r x\<^isub>0)) (at x\<^isub>0)"
                  by (intro eventually_conj poly_neighbourhood_same_sign, 
                      simp_all add: r_not_0)
            show ?thesis
            proof (rule eventually_mono[OF _ A], clarify,
                   subst ps'_props, subst sign_changes_sturm_triple)
              fix x assume A: "sgn (poly p x) = sgn (poly p x\<^isub>0)"
                       and B: "sgn (poly r x) = sgn (poly r x\<^isub>0)"
              have prod_neg: "\<And>a (b::real). \<lbrakk>a>0; b>0; a*b<0\<rbrakk> \<Longrightarrow> False"
                             "\<And>a (b::real). \<lbrakk>a<0; b<0; a*b<0\<rbrakk> \<Longrightarrow> False"
                  by (drule mult_pos_pos, simp, simp, 
                      drule mult_neg_neg, simp, simp)
              from A and `poly p x\<^isub>0 \<noteq> 0` show "poly p x \<noteq> 0" 
                  by (force simp: sgn_zero_iff)

              with sgn_r p_not_0 r_not_0 A B
                  have "poly r x * poly p x < 0" "poly r x \<noteq> 0"
                  by (metis sgn_less sgn_times, metis sgn_0_0)
              with sgn_r show sgn_r': "sgn (poly r x) = - sgn (poly p x)"
                  apply (simp add: sgn_real_def not_le not_less 
                             split: split_if_asm, intro conjI impI)
                  using prod_neg[of "poly r x" "poly p x"] apply force+
                  done

              show "1 = sign_changes ps' x\<^isub>0"
                  by (subst ps'_props, subst sign_changes_sturm_triple, 
                      fact, metis A B sgn_r', simp)
            qed
        qed
    next
      case False
        note q_not_0 = this
        show ?thesis
        proof (cases "ps' \<in> set (split_sign_changes (q # r # ps'') x\<^isub>0)")
          case True
            show ?thesis by (rule IH(2), fact, simp add: q_not_0, fact)
        next
          case False
            with ps''_props and q_not_0 have "ps' = [p, q]" by simp
            hence [simp]: "\<forall>p\<in>set ps'. poly p x\<^isub>0 \<noteq> 0" 
                using q_not_0 p_not_0 by simp
            show ?thesis
            proof (rule eventually_mono, clarify)
              fix x assume "\<forall>p\<in>set ps'. sgn (poly p x) = sgn (poly p x\<^isub>0)"
              thus "sign_changes ps' x = sign_changes ps' x\<^isub>0"
                  by (rule same_signs_imp_same_sign_changes)
            next
              show "eventually (\<lambda>x. \<forall>p\<in>set ps'. 
                        sgn (poly p x) = sgn (poly p x\<^isub>0)) (at x\<^isub>0)"
                  by (force intro: eventually_Ball_finite 
                                   poly_neighbourhood_same_sign)
            qed
    qed
  qed
qed


lemma (in quasi_sturm_seq) hd_nonzero_imp_sign_changes_const:
  assumes "poly (hd ps) x\<^isub>0 \<noteq> 0"
  shows "eventually (\<lambda>x. sign_changes ps x = sign_changes ps x\<^isub>0) (at x\<^isub>0)"
proof-
  let ?pss = "split_sign_changes ps x\<^isub>0"
  let ?f = "\<lambda>pss x. \<Sum>ps'\<leftarrow>pss. sign_changes ps' x"
  {
    fix pss assume "\<And>ps'. ps'\<in>set pss \<Longrightarrow> 
        eventually (\<lambda>x. sign_changes ps' x = sign_changes ps' x\<^isub>0) (at x\<^isub>0)"
    hence "eventually (\<lambda>x. ?f pss x = ?f pss x\<^isub>0) (at x\<^isub>0)"
    proof (induction pss)
      case (Cons ps' pss)
        have "\<forall>x. ?f pss x = ?f pss x\<^isub>0 \<and> sign_changes ps' x = sign_changes ps' x\<^isub>0 
                      \<longrightarrow> ?f (ps'#pss) x = ?f (ps'#pss) x\<^isub>0" by simp
        note A = eventually_mono[OF this eventually_conj]
        show ?case by (rule A, simp_all add: Cons)
    qed simp
  }
  note A = this[of ?pss]
  have B: "eventually (\<lambda>x. ?f ?pss x = ?f ?pss x\<^isub>0) (at x\<^isub>0)"
      by (rule A, rule hd_nonzero_imp_sign_changes_const_aux[OF assms], simp)
  note C = split_sign_changes_correct_nbh[OF assms]
  note D = split_sign_changes_correct[OF assms]
  note E = eventually_conj[OF B C]
  show ?thesis by (rule eventually_mono[OF _ E], auto simp: D)
qed

hide_fact quasi_sturm_seq.hd_nonzero_imp_sign_changes_const_aux

lemma (in sturm_seq) p_nonzero_imp_sign_changes_const:
  "poly p x\<^isub>0 \<noteq> 0 \<Longrightarrow> 
       eventually (\<lambda>x. sign_changes ps x = sign_changes ps x\<^isub>0) (at x\<^isub>0)"
  using hd_nonzero_imp_sign_changes_const by simp


lemma (in sturm_seq_squarefree) p_zero:
  assumes "poly p x\<^isub>0 = 0" "p \<noteq> 0"
  shows "eventually (\<lambda>x. sign_changes ps x = 
      sign_changes ps x\<^isub>0 + (if x<x\<^isub>0 then 1 else 0)) (at x\<^isub>0)"
proof-
  from ps_first_two obtain q ps' where [simp]: "ps = p#q#ps'" .
  hence "ps!1 = q" by simp
  have "eventually (\<lambda>x. x \<noteq> x\<^isub>0) (at x\<^isub>0)"
      by (simp add: eventually_at, rule exI[of _ 1], simp)
  moreover from p_squarefree and assms(1) have "poly q x\<^isub>0 \<noteq> 0" by simp
  {
      have A: "quasi_sturm_seq ps" ..
      with quasi_sturm_seq_Cons[of p "q#ps'"]
          interpret quasi_sturm_seq "q#ps'" by simp
      from `poly q x\<^isub>0 \<noteq> 0` have "eventually (\<lambda>x. sign_changes (q#ps') x = 
                                     sign_changes (q#ps') x\<^isub>0) (at x\<^isub>0)"
      using hd_nonzero_imp_sign_changes_const[where x\<^isub>0=x\<^isub>0] by simp
  }   
  moreover note poly_neighbourhood_without_roots[OF assms(2)] deriv[OF assms(1)]
  ultimately
      have A: "eventually (\<lambda>x. x \<noteq> x\<^isub>0 \<and> poly p x \<noteq> 0 \<and>
                   sgn (poly (ps!1) x) = sgn (x - x\<^isub>0)*sgn(poly p x) \<and>
                   sign_changes (q#ps') x = sign_changes (q#ps') x\<^isub>0) (at x\<^isub>0)" 
          by (simp only: `ps!1 = q`, intro eventually_conj)
  show ?thesis
  proof (rule eventually_mono[OF _ A], clarify)
    case (goal1 x)
    hence "poly q x \<noteq> 0" and q_sgn: "sgn (poly q x) = 
              (if x < x\<^isub>0 then -sgn (poly p x) else sgn (poly p x))"
        by (auto simp add: sgn_real_def split: split_if_asm)
    from sign_changes_distrib[OF `poly q x \<noteq> 0`, of "[p]" ps']
        have "sign_changes ps x = sign_changes [p,q] x + sign_changes (q#ps') x"
            by simp
    also from q_sgn and `poly p x \<noteq> 0` 
        have "sign_changes [p,q] x = (if x<x\<^isub>0 then 1 else 0)"
        by (simp add: sign_changes_def sgn_zero_iff split: split_if_asm)
    also note goal1(4)
    also from assms(1) have "sign_changes (q#ps') x\<^isub>0 = sign_changes ps x\<^isub>0"
        by (simp add: sign_changes_def)
    finally show ?case by simp
  qed
qed
    

lemma real_nat_one_half[dest]:
  "(n::nat) = (m::nat) - 1/2 \<Longrightarrow> False"
  "(n::nat) = (m::nat) + 1/2 \<Longrightarrow> False"
proof-
  assume "(n::nat) = (m::nat) - 1/2" 
  hence "2*(n - m) = 1" by linarith 
  thus False by simp
next
  assume "(n::nat) = (m::nat) + 1/2" 
  hence "2*(n - m) = 1" by linarith 
  thus False by simp
qed

lemma natfun_eq_in_ivl:
  assumes "a \<le> b"
  assumes "\<forall>x::real. a \<le> x \<and> x \<le> b \<longrightarrow> eventually (\<lambda>\<xi>. f \<xi> = (f x::nat)) (at x)"
  shows "f a = f b"
proof-
  have cont: "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> isCont f x"
  proof (clarify, simp add: isCont_def, rule tendstoI, simp add: dist_real_def)
    fix \<epsilon> :: real and x :: real assume "\<epsilon> > 0" and  "a \<le> x" "x \<le> b"
    with assms have A: "eventually (\<lambda>\<xi>. f \<xi> = (f x::nat)) (at x)" by simp
    show "eventually (\<lambda>\<xi>. \<bar>real (f \<xi>) - real (f x)\<bar> < \<epsilon>) (at x)"
        by (rule eventually_mono[OF _ A], simp add: `\<epsilon> > 0`)
  qed

  {
    def y \<equiv> "f a + 1/2"
    assume "f a < f b"
    hence "f a \<le> y" "y \<le> f b" by (simp_all add: y_def)
    with IVT[OF this `a \<le> b` cont] have False by (auto simp: y_def)
  }
  moreover
  {
    def y \<equiv> "f a - 1/2"
    assume "f a > f b"
    hence "f b \<le> y" "y \<le> f a" by (simp_all add: y_def)
    with IVT2[OF this `a \<le> b` cont] have False by (auto simp: y_def)
  }
  ultimately show "f a = f b" by force
qed

lemma count_roots_between_aux:
  assumes "a \<le> b"
  assumes "\<forall>x::real. a < x \<and> x \<le> b \<longrightarrow> eventually (\<lambda>\<xi>. f \<xi> = (f x::nat)) (at x)"
  shows "\<forall>x. a < x \<and> x \<le> b \<longrightarrow> f x = f b"
proof (clarify)
  fix x assume "x > a" "x \<le> b"
  with assms have "\<forall>x'. x \<le> x' \<and> x' \<le> b \<longrightarrow> 
                       eventually (\<lambda>\<xi>. f \<xi> = f x') (at x')" by auto
  from natfun_eq_in_ivl[OF `x \<le> b` this] show "f x = f b" .
qed
  

lemma (in sturm_seq_squarefree) count_roots_between:
  assumes [simp]: "p \<noteq> 0" "a \<le> b"
  shows "sign_changes ps a - sign_changes ps b = 
             card {x. x > a \<and> x \<le> b \<and> poly p x = 0}"
proof-
  have "sign_changes ps a - int (sign_changes ps b) = 
             card {x. x > a \<and> x \<le> b \<and> poly p x = 0}" using `a \<le> b`
  proof (induction "card {x. x > a \<and> x \<le> b \<and> poly p x = 0}" arbitrary: a b
             rule: less_induct)
    case (less a b)
      show ?case
      proof (cases "\<exists>x. a < x \<and> x \<le> b \<and> poly p x = 0")
        case False
          hence no_roots: "{x. a < x \<and> x \<le> b \<and> poly p x = 0} = {}" 
              (is "?roots=_") by auto
          hence card_roots: "card ?roots = (0::int)" by (subst no_roots, simp)
          show ?thesis
          proof (simp only: card_roots eq_iff_diff_eq_0[symmetric] int_int_eq, 
                 cases "poly p a = 0")
            case False
              with no_roots show "sign_changes ps a = sign_changes ps b"
                  by (force intro: natfun_eq_in_ivl `a \<le> b` 
                                   p_nonzero_imp_sign_changes_const)
          next
            case True
              have A: "\<forall>x. a < x \<and> x \<le> b \<longrightarrow> sign_changes ps x = sign_changes ps b"
                  apply (rule count_roots_between_aux, fact, clarify)
                  apply (rule p_nonzero_imp_sign_changes_const)
                  apply (insert False, simp)
                  done
              have "eventually (\<lambda>x. x > a \<longrightarrow> 
                        sign_changes ps x = sign_changes ps a) (at a)"
                  apply (rule eventually_mono) defer
                  apply (rule p_zero[OF `poly p a = 0` `p \<noteq> 0`], force)
                  done
              then obtain \<delta> where \<delta>_props:
                  "\<delta> > 0" "\<forall>x. x > a \<and> x < a+\<delta> \<longrightarrow> 
                                   sign_changes ps x = sign_changes ps a"
                  by (auto simp: eventually_at dist_real_def)

              show "sign_changes ps a = sign_changes ps b"
              proof (cases "a = b")
                case False
                  def x \<equiv> "min (a+\<delta>/2) b"
                  with False have "a < x" "x < a+\<delta>" "x \<le> b"
                     using `\<delta> > 0` `a \<le> b` by simp_all
                  from \<delta>_props `a < x` `x < a+\<delta>` 
                      have "sign_changes ps a = sign_changes ps x" by simp
                  also from A `a < x` `x \<le> b` have "... = sign_changes ps b"
                      by blast
                  finally show ?thesis .
              qed simp
          qed

      next
        case True
          from poly_roots_finite[OF assms(1)]
            have fin: "finite {x. x > a \<and> x \<le> b \<and> poly p x = 0}" 
            by (force intro: finite_subset)
          from True have "{x. x > a \<and> x \<le> b \<and> poly p x = 0} \<noteq> {}" by blast
          with fin have card_greater_0:
              "card {x. x > a \<and> x \<le> b \<and> poly p x = 0} > 0" by fastforce
              
          def x \<equiv> "Min {x. x > a \<and> x \<le> b \<and> poly p x = 0}"
          from Min_in[OF fin] and True
              have x_props: "x > a" "x \<le> b" "poly p x = 0" 
              unfolding x_def by blast+
          from Min_le[OF fin] x_props 
              have x_le: "\<And>x'. \<lbrakk>x' > a; x' \<le> b; poly p x' = 0\<rbrakk> \<Longrightarrow> x \<le> x'"
              unfolding x_def by simp

          have left: "{x'. a < x' \<and> x' \<le> x \<and> poly p x' = 0} = {x}"
              using x_props x_le by force
          hence [simp]: "card {x'. a < x' \<and> x' \<le> x \<and> poly p x' = 0} = 1" by simp

          from p_zero[OF `poly p x = 0` `p \<noteq> 0`, 
              unfolded eventually_at dist_real_def] guess \<epsilon> ..
          hence \<epsilon>_props: "\<epsilon> > 0"
              "\<forall>x'. x' \<noteq> x \<and> \<bar>x' - x\<bar> < \<epsilon> \<longrightarrow> 
                   sign_changes ps x' = sign_changes ps x + 
                       (if x' < x then 1 else 0)" by auto
          def x' \<equiv> "max (x - \<epsilon> / 2) a"
          have "\<bar>x' - x\<bar> < \<epsilon>" using `\<epsilon> > 0` x_props by (simp add: x'_def)
          hence "sign_changes ps x' = 
              (if x' < x then sign_changes ps x + 1 else sign_changes ps x)"
              using \<epsilon>_props(2) by (cases "x' = x", simp, force)
          hence "sign_changes ps x' - sign_changes ps x = 1"
              unfolding x'_def using x_props `\<epsilon> > 0` by simp

          also have "x \<notin> {x''. a < x'' \<and> x'' \<le> x' \<and> poly p x'' = 0}"
              unfolding x'_def using `\<epsilon> > 0` by force
          with left have "{x''. a < x'' \<and> x'' \<le> x' \<and> poly p x'' = 0} = {}"
              by force
          with less(1)[of a x'] have "sign_changes ps x' = sign_changes ps a"
              unfolding x'_def `\<epsilon> > 0` by (force simp: card_greater_0)

          finally have signs_left: 
              "sign_changes ps a - int (sign_changes ps x) = 1" by simp

          have "{x. x > a \<and> x \<le> b \<and> poly p x = 0} = 
                {x'. a < x' \<and> x' \<le> x \<and> poly p x' = 0} \<union>
                {x'. x < x' \<and> x' \<le> b \<and> poly p x' = 0}" using x_props by auto
          also note left
          finally have A: "card {x'. x < x' \<and> x' \<le> b \<and> poly p x' = 0} + 1 = 
              card {x. a < x \<and> x \<le> b \<and> poly p x = 0}" using fin by simp
          hence "card {x'. x < x' \<and> x' \<le> b \<and> poly p x' = 0} < 
                 card {x. a < x \<and> x \<le> b \<and> poly p x = 0}" by simp
          from less(1)[OF this x_props(2)] and A
              have signs_right: "sign_changes ps x - int (sign_changes ps b) + 1 =
                  card {x'. x' > a \<and> x' \<le> b \<and> poly p x' = 0}" by simp
          
          from signs_left and signs_right show ?thesis by simp
        qed
  qed
  thus ?thesis by simp
qed


lemma (in sturm_seq_squarefree) count_roots:
  assumes "p \<noteq> 0"
  shows "sign_changes_neg_inf ps - sign_changes_inf ps = 
             card {x. poly p x = 0}"
proof-
  from poly_roots_bounds[OF assms] guess l\<^isub>1 u\<^isub>1 .
  note lu\<^isub>1_props = this

  have "finite (set ps)" by simp
  from polys_inf_sign_thresholds[OF this] guess l\<^isub>2 u\<^isub>2 .
  note lu\<^isub>2_props = this

  let ?l = "min l\<^isub>1 l\<^isub>2" and ?u = "max u\<^isub>1 u\<^isub>2"
  from lu\<^isub>1_props lu\<^isub>2_props 
    have "map (\<lambda>p. sgn (poly p ?l)) ps = map poly_neg_inf ps"
         "map (\<lambda>p. sgn (poly p ?u)) ps = map poly_inf ps" by auto
  hence "sign_changes_neg_inf ps - sign_changes_inf ps =
             sign_changes ps ?l - sign_changes ps ?u"
      by (simp_all only: sign_changes_def sign_changes_inf_def 
                         sign_changes_neg_inf_def)
  also from count_roots_between[OF assms] lu\<^isub>1_props lu\<^isub>2_props
      have "... =  card {x. ?l < x \<and> x \<le> ?u \<and> poly p x = 0}" by simp
  also have "{x. ?l < x \<and> x \<le> ?u \<and> poly p x = 0} = {x. poly p x = 0}"
      using lu\<^isub>1_props by (auto simp: sgn_zero_iff 
                               intro: min_max.less_infI1 min_max.le_supI1)
  finally show ?thesis .
qed






lemma degree_mod_less': "degree q \<noteq> 0 \<Longrightarrow> degree (p mod q) < degree q"
  using assms degree_mod_less by force

function sturm_aux where
"sturm_aux p q = (if degree q = 0 then [p,q] else p # sturm_aux q (-(p mod q)))"
  by (pat_completeness, simp_all)
termination by (relation "measure (degree \<circ> snd)", 
                simp_all add: o_def degree_mod_less')

declare sturm_aux.simps[simp del]

definition sturm where "sturm p = sturm_aux p (pderiv p)"

lemma [simp]: "sturm_aux p q = [] \<longleftrightarrow> False"
    by (induction p q rule: sturm_aux.induct, subst sturm_aux.simps, auto)

lemma [simp]: "sturm p = [] \<longleftrightarrow> False" unfolding sturm_def by simp

lemma [simp]: "hd (sturm p) = p"
  unfolding sturm_def by (subst sturm_aux.simps, simp)

lemma [simp]: "length (sturm p) \<ge> 2"
proof-
  {fix q have "length (sturm_aux p q) \<ge> 2"
           by (induction p q rule: sturm_aux.induct, subst sturm_aux.simps, simp)
  }
  thus ?thesis unfolding sturm_def .
qed

lemma [simp]: "degree (last (sturm p)) = 0"
proof-
  {fix q have "degree (last (sturm_aux p q)) = 0"
           by (induction p q rule: sturm_aux.induct, subst sturm_aux.simps, simp)
  }
  thus ?thesis unfolding sturm_def .
qed

lemma [simp]: "sturm_aux p q ! 0 = p"
    by (subst sturm_aux.simps, simp)
lemma [simp]: "sturm_aux p q ! Suc 0 = q"
    by (subst sturm_aux.simps, simp)

lemma [simp]: "sturm p ! 0 = p" 
    unfolding sturm_def by simp
lemma [simp]: "sturm p ! Suc 0 = pderiv p" 
    unfolding sturm_def by simp

lemma sturm_indices:
  assumes "i < length (sturm p) - 2"
  shows "sturm p!(i+2) = -(sturm p!i mod sturm p!(i+1))"
proof-
 {fix ps q
  have "\<lbrakk>ps = sturm_aux p q; i < length ps - 2\<rbrakk>
            \<Longrightarrow> ps!(i+2) = -(ps!i mod ps!(i+1))"
  proof (induction p q arbitrary: ps i rule: sturm_aux.induct)
    case (goal1 p q)
      show ?case
      proof (cases "i = 0")
        case False
          then obtain i' where [simp]: "i = Suc i'" by (cases i, simp_all)
          hence "length ps \<ge> 4" using goal1 by simp
          with goal1(2) have deg: "degree q \<noteq> 0" 
              by (subst (asm) sturm_aux.simps, simp split: split_if_asm)
          with goal1(2) obtain ps' where [simp]: "ps = p # ps'" 
              by (subst (asm) sturm_aux.simps, simp)
          with goal1(2) deg have ps': "ps' = sturm_aux q (-(p mod q))"
              by (subst (asm) sturm_aux.simps, simp)
          from `length ps \<ge> 4` and `ps = p # ps'`goal1(3) False
              have "i - 1 < length ps' - 2" by simp
          from goal1(1)[OF deg ps' this]
              show ?thesis by simp
      next
        case True
          with goal1(3) have "length ps \<ge> 3" by simp
          with goal1(2) have "degree q \<noteq> 0"
              by (subst (asm) sturm_aux.simps, simp split: split_if_asm)
          with goal1(2) have [simp]: "sturm_aux p q ! Suc (Suc 0) = -(p mod q)"
              by (subst sturm_aux.simps, simp)
          from True have "ps!i = p" "ps!(i+1) = q" "ps!(i+2) = -(p mod q)" 
              by (simp_all add: goal1(2))
          thus ?thesis by simp
      qed
    qed}
  from this[OF sturm_def assms] show ?thesis .
qed

lemma sturm_aux_gcd: "r \<in> set (sturm_aux p q) \<Longrightarrow> gcd p q dvd r"
proof (induction p q rule: sturm_aux.induct)
  case (goal1 p q)
    show ?case
    proof (cases "r = p")
      case False
        with goal1(2) have r: "r \<in> set (sturm_aux q (-(p mod q)))" 
          by (subst (asm) sturm_aux.simps, simp split: split_if_asm,
              subst sturm_aux.simps, simp)
        show ?thesis
        proof (cases "degree q = 0")
          case False
            hence "q \<noteq> 0" by force
            from goal1(1)[OF False r] show ?thesis 
                by (subst gcd_poly.simps(2)[OF `q \<noteq> 0`], simp)
        next
          case True
            with goal1(2) and `r \<noteq> p` have "r = q"
                by (subst (asm) sturm_aux.simps, simp)
            thus ?thesis by simp
        qed
    qed simp
qed

lemma sturm_gcd: "r \<in> set (sturm p) \<Longrightarrow> gcd p (pderiv p) dvd r"
    unfolding sturm_def by (rule sturm_aux_gcd)

lemma sturm_adjacent_root_propagate_left:
  assumes "i < length (sturm (p :: real poly)) - 1"
  assumes "poly (sturm p ! i) x = 0"
      and "poly (sturm p ! (i + 1)) x = 0"
  shows "\<forall>j\<le>i+1. poly (sturm p ! j) x = 0"
using assms(2)
proof (intro sturm_adjacent_root_aux[OF assms(1,2,3)])
  case (goal1 i x)
    let ?p = "sturm p ! i"
    let ?q = "sturm p ! (i + 1)"
    let ?r = "sturm p ! (i + 2)"
    from sturm_indices[OF goal1(2)] have "?p = ?p div ?q * ?q - ?r" 
        by (simp add: mod_div_equality)
    hence "poly ?p x = poly (?p div ?q * ?q - ?r) x" by simp
    hence "poly ?p x = -poly ?r x" using goal1(3) by simp
    thus ?case by (simp add: sgn_minus)
qed

lemma sturm_adjacent_root_not_squarefree:
  assumes "i < length (sturm (p :: real poly)) - 1"
          "poly (sturm p ! i) x = 0" "poly (sturm p ! (i + 1)) x = 0"
  shows "\<not>rsquarefree p"
proof-
  from sturm_adjacent_root_propagate_left[OF assms]
      have "poly p x = 0" "poly (pderiv p) x = 0" by auto
  thus ?thesis by (auto simp: rsquarefree_roots)
qed


lemma sturm_seq_sturm[simp]: 
   assumes "rsquarefree p"
   shows "sturm_seq_squarefree (sturm p) p"
proof
  show "sturm p \<noteq> []" by simp
  show "hd (sturm p) = p" by simp
  show "length (sturm p) \<ge> 2" by simp
  from assms show "\<And>x. \<not>(poly p x = 0 \<and> poly (sturm p ! 1) x = 0)"
      by (simp add: rsquarefree_roots)
next
  fix x :: real and y :: real
  have "degree (last (sturm p)) = 0" by simp
  then obtain c where "last (sturm p) = [:c:]" 
      by (cases "last (sturm p)", simp split: split_if_asm)
  thus "\<And>x y. sgn (poly (last (sturm p)) x) =
            sgn (poly (last (sturm p)) y)" by simp
next
  fix x\<^isub>0 assume p_0: "poly p x\<^isub>0 = 0"
  def q \<equiv> "pderiv p"
  from assms have "p \<noteq> 0" by (simp add: rsquarefree_def)
  from assms and p_0 have q_not_0: "poly q x\<^isub>0 \<noteq> 0"
      by (simp add: rsquarefree_roots q_def)
  have A: "eventually (\<lambda>x. poly p x \<noteq> 0 \<and> 
               sgn (poly q x) = sgn (poly q x\<^isub>0)) (at x\<^isub>0)"
      using `p \<noteq> 0` q_not_0  by (intro poly_neighbourhood_same_sign 
                                 poly_neighbourhood_without_roots eventually_conj)
  then obtain \<epsilon> where \<epsilon>_props: "\<epsilon> > 0" "\<forall>x. x \<noteq> x\<^isub>0 \<and> \<bar>x - x\<^isub>0\<bar> < \<epsilon> \<longrightarrow> 
      poly p x \<noteq> 0 \<and> sgn (poly q x) = sgn (poly q x\<^isub>0)"
      by (auto simp: eventually_at dist_real_def)
  show "eventually (\<lambda>x. sgn (poly (sturm p ! 1) x) = 
            sgn (x - x\<^isub>0) * sgn (poly p x)) (at x\<^isub>0)"
  proof (simp add: eventually_at dist_real_def, rule exI[of _ \<epsilon>],
         intro conjI, fact `\<epsilon> > 0`, clarify)
    fix x assume "x \<noteq> x\<^isub>0" "\<bar>x - x\<^isub>0\<bar> < \<epsilon>"
    with \<epsilon>_props have [simp]: "sgn (poly (pderiv p) x) = sgn (poly q x\<^isub>0)"
        by (simp add: q_def)
    show "sgn (poly (pderiv p) x) = sgn (x - x\<^isub>0) * sgn (poly p x)"
    proof (cases "x \<ge> x\<^isub>0")
      case True
        with `x \<noteq> x\<^isub>0` have "x > x\<^isub>0" by simp
        from poly_MVT[OF this, of p] guess \<xi> ..
        with `\<bar>x - x\<^isub>0\<bar> < \<epsilon>` `poly p x\<^isub>0 = 0` `x > x\<^isub>0`
        have "\<bar>\<xi> - x\<^isub>0\<bar> < \<epsilon>" "poly p x = (x - x\<^isub>0) * poly q \<xi>" 
            by (auto simp add: q_def) 
        moreover with \<epsilon>_props have "sgn (poly (pderiv p) \<xi>) = 
            sgn (poly q x\<^isub>0)" by (auto simp: q_def)
        ultimately show ?thesis using True `x \<noteq> x\<^isub>0` 
            by (auto simp add: q_def sgn_mult)
    next
      case False
        hence "x < x\<^isub>0" by simp
        from poly_MVT[OF this, of p] guess \<xi> ..
        with `\<bar>x - x\<^isub>0\<bar> < \<epsilon>` `poly p x\<^isub>0 = 0` `x < x\<^isub>0`
        have "\<bar>\<xi> - x\<^isub>0\<bar> < \<epsilon>" "poly p x = (x - x\<^isub>0) * poly q \<xi>" 
            by (auto simp add: q_def field_simps) 
        moreover with \<epsilon>_props have "sgn (poly (pderiv p) \<xi>) = 
            sgn (poly q x\<^isub>0)" by (auto simp: q_def)
        ultimately show ?thesis using False `x \<noteq> x\<^isub>0` 
            by (auto simp add: q_def sgn_mult) 
    qed
  qed

next
  fix i x
  assume A: "i < length (sturm p) - 2" and B: "poly (sturm p ! (i+1)) x = 0"
  from sturm_indices[OF A] 
      have "sturm p ! (i+2) = - (sturm p ! i mod sturm p ! (i+1))"
           (is "?r = - (?p mod ?q)") .
  hence "-?r = ?p mod ?q" by simp
  with mod_div_equality[of ?p ?q] have "?p div ?q * ?q - ?r = ?p" by simp
  hence "poly (?p div ?q) x * poly ?q x - poly ?r x = poly ?p x"
      by (metis poly_diff poly_mult)
  with B have C: "poly ?r x = -poly ?p x" by simp
  moreover have sqr_pos: "\<And>x::real. x \<noteq> 0 \<Longrightarrow> x * x > 0" apply (case_tac "x \<ge> 0")
      by (simp_all add: mult_pos_pos mult_neg_neg)
  from sturm_adjacent_root_not_squarefree[of i p] assms A B C
      have "poly ?p x * poly ?p x > 0" by (force intro: sqr_pos)
  ultimately show "poly ?r x * poly ?p x < 0" by simp
qed



definition sturm_squarefree where
  "sturm_squarefree p = sturm (p div (gcd p (pderiv p)))"

lemma sturm_squarefree_not_Nil[simp]: "sturm_squarefree p \<noteq> []"
  by (simp add: sturm_squarefree_def)



lemma sturm_seq_squarefree:
  assumes [simp]: "p \<noteq> 0"
  defines [simp]: "p' \<equiv> p div gcd p (pderiv p)"
  shows "sturm_seq_squarefree (sturm_squarefree p) p'"
proof
  have "rsquarefree p'" 
  proof (subst rsquarefree_roots, clarify)
    fix x assume "poly p' x = 0" "poly (pderiv p') x = 0"
    hence "[:-x,1:] dvd gcd p' (pderiv p')" by (simp add: poly_eq_0_iff_dvd)
    also from poly_div_gcd_squarefree(1)[OF assms(1)]
        have "gcd p' (pderiv p') = 1" by simp
    finally show False by (simp add: poly_eq_0_iff_dvd[symmetric])
  qed

  from sturm_seq_sturm[OF `rsquarefree p'`] 
      interpret sturm_seq: sturm_seq_squarefree "sturm_squarefree p" p' 
      by (simp add: sturm_squarefree_def)

  show "\<And>x y. sgn (poly (last (sturm_squarefree p)) x) = 
      sgn (poly (last (sturm_squarefree p)) y)" by simp
  show "sturm_squarefree p \<noteq> []" by simp
  show "hd (sturm_squarefree p) = p'" by (simp add: sturm_squarefree_def)
  show "length (sturm_squarefree p) \<ge> 2" by simp

  have [simp]: "sturm_squarefree p ! 0 = p'" 
               "sturm_squarefree p ! Suc 0 = pderiv p'" 
      by (simp_all add: sturm_squarefree_def) 

  from `rsquarefree p'` 
      show "\<And>x. \<not> (poly p' x = 0 \<and> poly (sturm_squarefree p ! 1) x = 0)"
      by (simp add: rsquarefree_roots)

  from sturm_seq.signs show "\<And>i x. \<lbrakk>i < length (sturm_squarefree p) - 2;
                                 poly (sturm_squarefree p ! (i + 1)) x = 0\<rbrakk>
                                 \<Longrightarrow> poly (sturm_squarefree p ! (i + 2)) x *
                                         poly (sturm_squarefree p ! i) x < 0" .

  from sturm_seq.deriv show "\<And>x\<^isub>0. poly p' x\<^isub>0 = 0 \<Longrightarrow>
         eventually (\<lambda>x. sgn (poly (sturm_squarefree p ! 1) x) =
                         sgn (x - x\<^isub>0) * sgn (poly p' x)) (at x\<^isub>0)" .
qed



definition count_roots_between where
"count_roots_between p a b = (if a \<le> b \<and> p \<noteq> 0 then 
  (let ps = sturm_squarefree p
    in sign_changes ps a - sign_changes ps b) else 0)"

definition count_roots where
"count_roots p = (if p = 0 then 0 else
  (let ps = sturm_squarefree p
    in sign_changes_neg_inf ps - sign_changes_inf ps))"


lemma count_roots_between_correct:
  "count_roots_between p a b = card {x. a < x \<and> x \<le> b \<and> poly p x = 0}"
proof (cases "p \<noteq> 0 \<and> a \<le> b")
  case False
    note False' = this
    hence "card {x. a < x \<and> x \<le> b \<and> poly p x = 0} = 0"
    proof (cases "a < b")
      case True
        with False have [simp]: "p = 0" by simp
        have subset: "{a<..<b} \<subseteq> {x. a < x \<and> x \<le> b \<and> poly p x = 0}" by auto
        from real_infinite_interval[OF True] have "\<not>finite {a<..<b}" .
        hence "\<not>finite {x. a < x \<and> x \<le> b \<and> poly p x = 0}"
            using finite_subset[OF subset] by blast
        thus ?thesis by simp
    next
      case False
        with False' show ?thesis by (auto simp: not_less card_eq_0_iff)
    qed
    thus ?thesis unfolding count_roots_between_def Let_def using False by auto
next
  case True
  hence "p \<noteq> 0" "a \<le> b" by simp_all
  def p' \<equiv> "p div (gcd p (pderiv p))"
  from poly_div_gcd_squarefree(1)[OF `p \<noteq> 0`] have "p' \<noteq> 0"
      unfolding p'_def by clarsimp

  from sturm_seq_squarefree[OF `p \<noteq> 0`]
      interpret sturm_seq_squarefree "sturm_squarefree p" p'
      unfolding p'_def .
  from poly_roots_finite[OF `p' \<noteq> 0`] 
      have "finite {x. a < x \<and> x \<le> b \<and> poly p' x = 0}" by fast
  have "count_roots_between p a b = card {x. a < x \<and> x \<le> b \<and> poly p' x = 0}"
      unfolding count_roots_between_def Let_def
      using True count_roots_between[OF `p' \<noteq> 0` `a \<le> b`] by simp
  also from poly_div_gcd_squarefree(2)[OF `p \<noteq> 0`]
      have "{x. a < x \<and> x \<le> b \<and> poly p' x = 0} = 
            {x. a < x \<and> x \<le> b \<and> poly p x = 0}" unfolding p'_def by blast
  finally show ?thesis .
qed

lemma count_roots_correct:
  fixes p :: "real poly"
  shows "count_roots p = card {x. poly p x = 0}" (is "_ = card ?S")
proof (cases "p = 0")
  case True
    with real_infinite_interval[of 0 1] finite_subset[of "{0<..<1}" ?S]
        have "\<not>finite {x. poly p x = 0}" by force
    thus ?thesis by (simp add: count_roots_def True)
next
  case False
  def p' \<equiv> "p div (gcd p (pderiv p))"
  from poly_div_gcd_squarefree(1)[OF `p \<noteq> 0`] have "p' \<noteq> 0"
      unfolding p'_def by clarsimp

  from sturm_seq_squarefree[OF `p \<noteq> 0`]
      interpret sturm_seq_squarefree "sturm_squarefree p" p'
      unfolding p'_def .
  from count_roots[OF `p' \<noteq> 0`]
      have "count_roots p = card {x. poly p' x = 0}"
      unfolding count_roots_def Let_def by (simp add: `p \<noteq> 0`)
  also from poly_div_gcd_squarefree(2)[OF `p \<noteq> 0`]
      have "{x. poly p' x = 0} = {x. poly p x = 0}" unfolding p'_def by blast
  finally show ?thesis .
qed


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

lemmas sturm_intros = poly_card_roots poly_card_roots_less_leq 
    poly_card_roots_leq_less poly_card_roots_less_less poly_card_roots_leq_leq

method_setup sturm = {*
let
  fun sturm_conv thy = Code_Runtime.static_holds_conv thy
  [@{const_name count_roots_between}, @{const_name count_roots},
   @{const_name Trueprop}, @{const_name Rat.of_int}, 
   @{const_name Power.power_class.power},
   @{const_name Num.nat_of_num}]
in
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD' (
      fn i =>
        resolve_tac @{thms sturm_intros} 1
        THEN CONVERSION (sturm_conv (Proof_Context.theory_of ctxt)) 1
        THEN rtac TrueI 1
))
end
*} "decide how many roots a polynomial has"

lemma example:
  "card {x::real. -0.010831 < x \<and> x < 0.010831 \<and> 
     poly [:0, -17/2097152, -49/16777216, 1/6, 1/24, 1/120:] x = 0} = 3"
 by sturm


end