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

lemma isContI_real:
  assumes "\<And>\<epsilon>. \<epsilon>>0 \<Longrightarrow> \<exists>\<delta>>0. \<forall>x. \<bar>x - x\<^isub>0\<bar> < \<delta> \<longrightarrow> \<bar>f x - f x\<^isub>0\<bar> < (\<epsilon> :: real)"
  shows "isCont f (x\<^isub>0 :: real)"
unfolding isCont_def tendsto_def
proof (clarify)
  fix S assume "open S" and "f x\<^isub>0 \<in> S"
  then obtain \<epsilon> where \<epsilon>_props: "\<epsilon> > 0" "\<forall>y. \<bar>y - f x\<^isub>0\<bar> < \<epsilon> \<longrightarrow> y \<in> S"
      by (force simp: dist_real_def open_dist)
  with assms obtain \<delta> where "\<delta> > 0" and "\<forall>x. \<bar>x - x\<^isub>0\<bar> < \<delta> \<longrightarrow> \<bar>f x - f x\<^isub>0\<bar> < \<epsilon>"
      by blast
  hence "\<forall>x. x \<noteq> x\<^isub>0 \<and> dist x x\<^isub>0 < \<delta> \<longrightarrow> f x \<in> S" 
      using \<epsilon>_props unfolding dist_real_def by blast
  with `\<delta> > 0` show "eventually (\<lambda>x. f x \<in> S) (at x\<^isub>0)"
    unfolding eventually_at by blast
qed

lemma isContE_real:
  assumes "isCont f (x\<^isub>0 :: real)" and [simp]: "\<epsilon> > 0"
  obtains \<delta> where "\<delta> > 0" and "\<forall>x. \<bar>x - x\<^isub>0\<bar> < \<delta> \<longrightarrow> \<bar>f x - f x\<^isub>0\<bar> < (\<epsilon> :: real)"
proof-
  case goal1
  let ?S = "{f x\<^isub>0 - \<epsilon><..<f x\<^isub>0 + \<epsilon>}"
  from `\<epsilon> > 0` have [simp]: "open ?S" "f x\<^isub>0 \<in> ?S" by auto
  with assms(1) obtain \<delta> where "\<delta> > 0" and 
      A: "\<forall>x. x \<noteq> x\<^isub>0 \<and> dist x x\<^isub>0 < \<delta> \<longrightarrow> f x \<in> ?S" 
      unfolding isCont_def tendsto_def eventually_at by fast
  {
    fix x assume "\<bar>x - x\<^isub>0\<bar> < \<delta>"
    with A have "f x \<in> ?S" unfolding dist_real_def by (cases "x = x\<^isub>0", simp_all)
    hence "\<bar>f x - f x\<^isub>0\<bar> < \<epsilon>" by (cases "f x - f x\<^isub>0 \<ge> 0", simp_all)
  }
  thus ?case by (rule_tac goal1, rule_tac `\<delta> > 0`, blast)
qed

lemma isContE_real_nat:
  assumes "isCont (f :: real \<Rightarrow> nat) x\<^isub>0"
  obtains \<delta> where "\<delta> > 0" and "\<forall>x. \<bar>x - x\<^isub>0\<bar> < \<delta> \<longrightarrow> f x = f x\<^isub>0"
proof-
  case goal1
  have "(1/2 :: real) > 0" by simp
  from isContE_real[OF assms this] guess \<delta> .
  note \<delta>_props = this
  {
    fix x assume "\<bar>x - x\<^isub>0\<bar> < \<delta>"
    with \<delta>_props have "\<bar>real (f x) - real (f x\<^isub>0)\<bar> < 1 / 2" by blast
    also have "\<bar>real (f x) - real (f x\<^isub>0)\<bar> = real \<bar>int (f x) - int (f x\<^isub>0)\<bar>"
        by (metis real_of_int_abs real_of_int_diff real_of_int_of_nat_eq) 
    finally have A: "real \<bar>int (f x) - int (f x\<^isub>0)\<bar> < 1 / 2" .
    have "f x = f x\<^isub>0"  
    proof (cases "\<bar>int (f x) - int (f x\<^isub>0)\<bar> \<ge> 1")
      case True
        hence "\<bar>int (f x) - int (f x\<^isub>0)\<bar> \<ge> 1/2" by linarith
        thus ?thesis using A by simp
    qed simp
  }
  thus thesis by (rule_tac goal1, rule_tac `\<delta> > 0`, blast)
qed 
  

lemma isCont_equal_neighbourhood:
  fixes f :: "real \<Rightarrow> real"
  assumes "\<delta> > 0" and "isCont f x\<^isub>0" and "\<forall>x. \<bar>x - x\<^isub>0\<bar> < \<delta> \<longrightarrow> f x = g x"
  shows "isCont g x\<^isub>0"
proof (rule isContI_real)
  case (goal1 \<epsilon>)
    from assms have [simp]: "f x\<^isub>0 = g x\<^isub>0" by simp
    from isContE_real[OF assms(2) `\<epsilon> > 0`] guess \<delta>' .
    note \<delta>'_props = this
    {
      fix x assume "\<bar>x - x\<^isub>0\<bar> < min \<delta> \<delta>'"
      with \<delta>'_props have "\<bar>f x - f x\<^isub>0\<bar> < \<epsilon>" by force
      moreover from assms(3) and `\<bar>x - x\<^isub>0\<bar> < min \<delta> \<delta>'` have "f x = g x" by force
      ultimately have "\<bar>g x - g x\<^isub>0\<bar> < \<epsilon>" by simp
    }
    moreover from `\<delta> > 0` `\<delta>' > 0` have "min \<delta> \<delta>' > 0" by simp
    ultimately show ?case by blast
qed

lemma isCont_const_neighbourhood:
  fixes f :: "real \<Rightarrow> real"
  assumes "\<delta> > 0" "\<forall>x. \<bar>x - x\<^isub>0\<bar> < \<delta> \<longrightarrow> f x = f x\<^isub>0"
  shows "isCont f x\<^isub>0"
  by (rule isCont_equal_neighbourhood[where g = f and f = "\<lambda>_. f x\<^isub>0"],
      rule assms(1), simp, metis assms(2))

end