
signature STURM =
sig
  val sturm_conv : Proof.context -> conv
  val sturm_tac :  Proof.context -> bool -> int -> tactic
end;

structure Sturm : STURM =
struct

  val deps = [@{const_name count_roots_between}, @{const_name count_roots},
     @{const_name count_roots_above},@{const_name count_roots_below},
     @{const_name Trueprop}, @{const_name Rat.of_int}, @{const_name Rat.Fract},
     @{const_name Power.power_class.power},
     @{const_name Real.ord_real_inst.less_eq_real},
     @{const_name Real.ord_real_inst.less_real},
     @{const_name Real.plus_real_inst.plus_real},
     @{const_name Real.times_real_inst.times_real},
     @{const_name Real.inverse_real_inst.divide_real},
     @{const_name Real.uminus_real_inst.uminus_real},
     @{const_name Num.nat_of_num},
     @{const_name Polynomial.monom},
     @{const_name Polynomial.plus_poly_inst.plus_poly},
     @{const_name Polynomial.times_poly_inst.times_poly},
     @{const_name Sturm_Method.poly_nonneg_witness_between},
     @{const_name Sturm_Method.poly_nonneg_witness_above},
     @{const_name Sturm_Method.poly_nonneg_witness_below},
     @{const_name Sturm_Method.poly_nonneg_witness},
     @{const_name Sturm_Method.sturm_nonneg_witness_between},
     @{const_name Sturm_Method.sturm_nonneg_witness_above},
     @{const_name Sturm_Method.sturm_nonneg_witness_below},
     @{const_name Sturm_Method.sturm_nonneg_witness},
     @{const_name Sturm_Method.sturm_mono_witness},
     @{const_name Sturm_Method.sturm_strict_mono_witness},
     @{const_name Sturm_Method.sturm_not_nonneg_witness},
     @{const_name Sturm_Method.sturm_not_nonneg_witness_above},
     @{const_name Sturm_Method.sturm_not_nonneg_witness_below},
     @{const_name Sturm_Method.sturm_not_nonneg_witness_between},
     @{const_name Sturm_Method.sturm_not_nonneg_witness_between_leq_leq}];

(*  val sturm_conv = Code_Runtime.static_holds_conv
    {ctxt = @{context}, consts = deps};*)
  fun sturm_conv ctxt = Code_Runtime.dynamic_holds_conv ctxt;

(*  val eval_term = Code_Evaluation.static_value
      {Ts = [], ctxt = @{context}, consts = deps};*)
  fun eval_term ctxt = Code_Evaluation.dynamic_value ctxt;

  val sturm_id_thmss = [@{thms sturm_id_PR_prio3}, @{thms sturm_id_PR_prio2}, 
                        @{thms sturm_id_PR_prio1}, @{thms sturm_id_PR_prio0}]
  val sturm_PR_tag_intro_thmss = [@{thms PR_TAG_intro_prio2}, @{thms PR_TAG_intro_prio1}, @{thms PR_TAG_intro_prio0}]

  fun extract_PR_tags (t as (Const (@{const_name PR_TAG}, _) $ _)) acc = t :: acc
    | extract_PR_tags (s $ t) acc = extract_PR_tags s (extract_PR_tags t acc)
    | extract_PR_tags (Abs (_,_,t)) acc = extract_PR_tags t acc
    | extract_PR_tags _ acc = acc
    
  fun sturm_nonneg_witness_tac ctxt thm =
    let val thy = Proof_Context.theory_of ctxt
        val prop = case prems_of thm of p :: _ => p | _ => concl_of thm
        val prop = case prop of Const (@{const_name Pure.prop}, _) $ prop => prop
                                | _ => prop
        val prop = case prop of Const (@{const_name Pure.conjunction}, _) $ 
                                    (Const (@{const_name Pure.term}, _) $ _) $ prop => prop
                                 | _ => prop
        val (witness_pred, p :: v :: args) = prop |> HOLogic.dest_Trueprop |> strip_comb
        val p = case eval_term ctxt p of
                  SOME p => p
                | NONE => raise (TERM ("Could not evaluate polynomial.", [p]))
        val args = map (fn x => case eval_term ctxt x of
                                  SOME x => x
                                | NONE => raise (TERM ("Could not evaluate bound.", [x]))) args
        val witness_pred = fst (dest_Const witness_pred)
        val witness = 
          if witness_pred = "Sturm_Method.sturm_nonneg_witness" then
            Rat_Sturm.poly_nonneg_witness p
          else if witness_pred = "Sturm_Method.sturm_nonneg_witness_above" then
            Rat_Sturm.poly_nonneg_witness_above p (nth args 0)
          else if witness_pred = "Sturm_Method.sturm_nonneg_witness_below" then
            Rat_Sturm.poly_nonneg_witness_below p (nth args 0)
          else if witness_pred = "Sturm_Method.sturm_nonneg_witness_between" then
            Rat_Sturm.poly_nonneg_witness_between p (nth args 0, nth args 1)
          else if witness_pred = "Sturm_Method.sturm_mono_witness" then
            Rat_Sturm.poly_mono_witness p false
          else if witness_pred = "Sturm_Method.sturm_strict_mono_witness" then
            Rat_Sturm.poly_mono_witness p true
          else 
            NONE
    in 
      case witness of 
        SOME w => Seq.single 
                    (Drule.instantiate_normalize ([], [(cterm_of thy v, cterm_of thy w)]) thm)
      | NONE => Seq.empty
    end;

  fun sturm_not_nonneg_witness_tac ctxt thm =
    let val thy = Proof_Context.theory_of ctxt
        val prop = case prems_of thm of p :: _ => p | _ => concl_of thm
        val prop = case prop of Const (@{const_name Pure.prop}, _) $ prop => prop
                                | _ => prop
        val prop = case prop of Const (@{const_name Pure.conjunction}, _) $ 
                                    (Const (@{const_name Pure.term}, _) $ _) $ prop => prop
                                 | _ => prop
        val (witness_pred, p :: v :: args) = prop |> HOLogic.dest_Trueprop |> strip_comb
        val p = case Code_Evaluation.dynamic_value ctxt p of
                  SOME p => p
                | NONE => raise (TERM ("Could not evaluate polynomial.", [p]))
        val witness_pred = fst (dest_Const witness_pred)
        val witness = 
          if witness_pred = "Sturm_Method.sturm_not_nonneg_witness" then
            Rat_Sturm.poly_not_nonneg_witness p
          else if witness_pred = "Sturm_Method.sturm_not_nonneg_witness_above" then
            Rat_Sturm.poly_not_nonneg_witness_above p (nth args 0)
          else if witness_pred = "Sturm_Method.sturm_not_nonneg_witness_below" then
            Rat_Sturm.poly_not_nonneg_witness_below p (nth args 0)
          else if witness_pred = "Sturm_Method.sturm_not_nonneg_witness_between" orelse
                  witness_pred = "Sturm_Method.sturm_not_nonneg_witness_between_leq_leq" then
            Rat_Sturm.poly_not_nonneg_witness_between p (nth args 0, nth args 1)
          else
            NONE
    in 
      case witness of 
        SOME w => Seq.single 
                    (Drule.instantiate_normalize ([], [(cterm_of thy v, cterm_of thy w)]) thm)
      | NONE => Seq.empty
    end;
    

  fun sturm_preprocess_tac ctxt i =
    let val thy = Proof_Context.theory_of ctxt
        fun subst_tac thms = EqSubst.eqsubst_tac ctxt [1] thms i
        fun process_PR_tag_tac thm =
          let val trms = extract_PR_tags (prop_of thm) []
              fun tac trm = 
                let val subst = Thm.reflexive (cterm_of thy trm) RS @{thm HOL.meta_eq_to_obj_eq}
                    val subst = subst RS @{thm "HOL.trans"}
                    val subst = subst RS @{thm "HOL.ssubst"}
                in  TRY (rtac subst i
                    THEN REPEAT_ALL_NEW (FIRST' (map (fn thms => 
                             DETERM o resolve_tac thms) sturm_PR_tag_intro_thmss)) i)
                end;
          in  EVERY (map tac trms) thm
          end;
    in  FIRST (map subst_tac sturm_id_thmss)
        THEN REPEAT (subst_tac @{thms HOL.nnf_simps(1,2,5) not_less not_le})
        THEN process_PR_tag_tac
        THEN TRY (REPEAT (subst_tac @{thms HOL.nnf_simps(1,2,5) not_less not_le}))
    end;

  fun find_sturm_card_eq_thm ctxt s =
    let val thy = Proof_Context.theory_of ctxt
        fun matches thm =
          case concl_of thm of
            Const (@{const_name Trueprop}, _) $ (Const (@{const_name HOL.eq}, _) $ 
                (Const (@{const_name Finite_Set.card}, _) $ s') $ _)
              => Pattern.matches thy (s',s)
          | _ => 
              let val _ = Output.urgent_message ("Warning: invalid theorem in " ^
                          "sturm_card_eq_substs: \n" ^ Pretty.string_of (
                            Syntax.pretty_term ctxt (concl_of thm)));
               in false
              end
        val thm = find_first matches @{thms sturm_card_substs};
    in
        thm
    end;

  fun sturm_card_eq_instantiate_tac ctxt _ thm =
    let val prop = case prems_of thm of p :: _ => p | _ => concl_of thm
        val prop = case prop of Const (@{const_name Pure.prop}, _) $ prop => prop
                                | _ => prop
        val prop = case prop of Const (@{const_name Pure.conjunction}, _) $ 
                                    (Const (@{const_name Pure.term}, _) $ _) $ prop => prop
                                 | _ => prop
        val (lhs,rhs) = prop |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
        val vars = Term.add_vars rhs []
    in case vars of
          [v] => let val (idxname,ty) = v
                      val n = Code_Evaluation.dynamic_value ctxt lhs  (* FIXME prefer static converson? *)
                  in case n of
                     NONE => Seq.empty
                   | SOME n => (* TODO: Ugly hack. *)
                       let val n' = (if ty = @{typ nat} then "" else "%_. ") ^ Int.toString (snd (HOLogic.dest_number n))
                       in  Seq.single (Rule_Insts.read_instantiate ctxt [(idxname, n')] [] thm)
                       end
                  end
        | _ => Seq.single thm
    end;
    

  fun sturm_card_eq_tac ctxt i thm =
    let val prop = case prems_of thm of p :: _ => p | _ => concl_of thm
        val prop = case prop of Const (@{const_name Pure.prop}, _) $ prop => prop
                                | _ => prop
        val prop = case prop of Const (@{const_name Pure.conjunction}, _) $ 
                                    (Const (@{const_name Pure.term}, _) $ _) $ prop => prop
                                 | _ => prop
        val s = case prop of
                        Const (@{const_name Trueprop}, _) $
                        (Const (@{const_name HOL.eq}, _) $ 
                          (Const (@{const_name Finite_Set.card}, _) $ s) $ _)
                        => s;
        val thm' = find_sturm_card_eq_thm ctxt s
    in  case thm' of
          NONE => Seq.empty
        |  SOME thm'' => (EqSubst.eqsubst_tac ctxt [1] [thm''] i
                          THEN sturm_card_eq_instantiate_tac ctxt i) thm
    end;

  fun find_sturm_prop_thm ctxt prop =
    let val thy = Proof_Context.theory_of ctxt
        fun matches thm =
          case concl_of thm of
            Const (@{const_name Trueprop}, _) $ (Const (@{const_name HOL.eq}, _) $ prop' $ _)
              => Pattern.matches thy (prop',prop)
          | _ => 
              let val _ = Output.urgent_message ("Warning: invalid theorem in " ^
                          "sturm_prop_substs: \n" ^ Pretty.string_of (
                            Syntax.pretty_term ctxt (concl_of thm)));
               in false
              end
        val thm = find_first matches @{thms sturm_prop_substs};
    in
        thm
    end;

  fun sturm_prop_tac ctxt i thm =
    let val prop = case prems_of thm of p :: _ => p | _ => concl_of thm
        val prop = case prop of Const (@{const_name Pure.prop}, _) $ prop => prop
                               | _ => prop
        val prop = case prop of Const (@{const_name Pure.conjunction}, _) $ 
                                    (Const (@{const_name Pure.term}, _) $ _) $ prop => prop
                               | _ => prop
        val prop = case prop of Const (@{const_name Trueprop}, _) $ prop => prop
                              | _ => prop
        val prop = case prop of Const (@{const_name Not}, _) $ p => p
                              | _ => prop
        val thm' = find_sturm_prop_thm ctxt prop
    in  case thm' of
          NONE => Seq.empty
        | SOME thm' => EqSubst.eqsubst_tac ctxt [1] [thm'] i thm
    end;

  fun sturm_main_tac ctxt keep_goal i thm =
    let val prop = case prems_of thm of p :: _ => p | _ => concl_of thm
        val prop = case prop of Const (@{const_name Pure.prop}, _) $ prop => prop
                               | _  => prop
        val prop = case prop of Const (@{const_name Pure.conjunction}, _) $ 
                                    (Const (@{const_name Pure.term}, _) $ _) $ prop => prop
                                 | _ => prop
        val tac = case prop of
                Const (@{const_name Trueprop}, _) $
                  (Const (@{const_name HOL.eq}, _) $ 
                    (Const (@{const_name Finite_Set.card}, _) $ _) $ _) 
                  => sturm_card_eq_tac
              | _ => sturm_prop_tac;
    in  ((tac ctxt i
         THEN CONVERSION (sturm_conv ctxt) i
         THEN rtac @{thm TrueI} i
        ) ORELSE (if keep_goal then all_tac else no_tac)) thm
    end;

    fun convert_meta_spec_tac ctxt i thm =
      let val prem = term_of (cprem_of thm i)
          val frees = Term.add_frees prem []
      in case frees of
           [_] => let val prem' = Logic.close_form prem
                    val goal = Logic.mk_implies (prem', prem)
                    val rule = Goal.prove ctxt [] [] goal (fn _ => 
                                   dtac @{thm sturm_meta_spec} i THEN atac i)
                in  rtac rule i thm
                end
         | _ => Seq.empty
      end
      
    fun sturm_nonneg_tac ctxt i =
        DETERM (resolve_tac @{thms sturm_nonneg_intros} i)
        THEN sturm_nonneg_witness_tac ctxt      
        THEN CONVERSION (sturm_conv ctxt) i
        THEN rtac @{thm TrueI} i

    fun sturm_not_nonneg_tac ctxt i =
        DETERM (resolve_tac @{thms sturm_not_nonneg_intros} i)
        THEN sturm_not_nonneg_witness_tac ctxt
        THEN  CONVERSION (sturm_conv ctxt) i
        THEN rtac @{thm TrueI} i

    fun sturm_tac ctxt keep_goal = SELECT_GOAL
       (prune_params_tac ctxt
        THEN TRY (Object_Logic.full_atomize_tac ctxt 1)
        THEN REPEAT (EqSubst.eqsubst_tac ctxt [1] @{thms sturm_imp_conv} 1)
        THEN TRY (convert_meta_spec_tac ctxt 1)
        THEN TRY (Object_Logic.full_atomize_tac ctxt 1)
        THEN sturm_preprocess_tac ctxt 1
        THEN (sturm_nonneg_tac ctxt 1 ORELSE sturm_not_nonneg_tac ctxt 1 
                  ORELSE sturm_main_tac ctxt keep_goal 1)) 

end;
