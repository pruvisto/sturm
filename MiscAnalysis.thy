theory MiscAnalysis
imports Limits
begin

lemma real_infinite_interval:
  assumes "a < (b::real)"
  shows "\<not>finite {a<..<b}"
proof
  assume "finite {a<..<b}"
  {
    fix S assume fin: "finite (S::real set)" and "\<exists>l u. l < u \<and> S = {l<..<u}"
    from this(2) have "\<not>finite S"
    proof (induction rule: finite_psubset_induct[OF fin])
      case (goal1 S)
        then obtain l u where "l < u" and [simp]: "S = {l<..<u}" by blast
        def S' \<equiv> "{l<..<l + (u-l)/3}"
        have "(l+u)/2 \<in> S" "(l+u)/2 \<notin> S'" unfolding S'_def using `l < u`
            by (simp_all add: field_simps)
        hence "S \<noteq> S'" by blast
        hence "S' \<subset> S" unfolding S'_def by (auto simp: field_simps)
        moreover have "\<exists>l' u'. l' < u' \<and> S' = {l'<..<u'}" using `l < u`
            by (rule_tac exI[of _ l], rule_tac exI[of _ "l+(u-l)/3"], 
                simp add: S'_def)
        ultimately have "\<not>finite S'" by (intro goal1(2), simp_all)
        thus ?case using `S' \<subset> S` using finite_subset by blast
    qed
  }
  from this[OF `finite {a<..<b}`] have "\<not> finite {a<..<b}" using assms by blast
  thus False using `finite {a<..<b}` by contradiction
qed

lemma real_interval_card_eq:
  "card {a<..<b::real} = 0"
  "card {a<..b::real} = 0"
  "card {a..<b::real} = 0"
  "card {a..b::real} = (if a = b then 1 else 0)"
proof-
  show "card {a<..<b} = 0"
      by (cases "a < b", simp_all add: real_infinite_interval)
  have "{a<..<b} \<subseteq> {a<..b}" by auto
  from finite_subset[OF this] show "card {a<..b::real} = 0"
      by (cases "a < b", auto simp: real_infinite_interval card_eq_0_iff) 
  have "{a<..<b} \<subseteq> {a..<b}" by auto
  from finite_subset[OF this] show "card {a..<b::real} = 0"
      by (cases "a < b", auto simp: real_infinite_interval card_eq_0_iff) 
  have "{a<..<b} \<subseteq> {a..b}" by auto
  from finite_subset[OF this] 
      show "card {a..b::real} = (if a = b then 1 else 0)"
      by (cases "a < b", auto simp: real_infinite_interval card_eq_0_iff)
qed


end
