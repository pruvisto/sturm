
signature STURM =
sig
  val sturm_conv : conv
  val sturm_tac :  Proof.context -> int -> tactic
  val setup : cterm -> (Proof.context -> Method.method) * cterm
end;

structure Sturm : STURM =
struct

  val sturm_conv = Code_Runtime.static_holds_conv @{theory}
    [@{const_name count_roots_between}, @{const_name count_roots},
     @{const_name count_roots_above},@{const_name count_roots_below},
     @{const_name Trueprop}, @{const_name Rat.of_int}, 
     @{const_name Power.power_class.power},
     @{const_name Real.ord_real_inst.less_eq_real},
     @{const_name Real.ord_real_inst.less_real},
     @{const_name Num.nat_of_num}]

  fun find_sturm_card_eq_thm ctxt s =
    let val thy = Proof_Context.theory_of ctxt
        fun matches thm =
          case concl_of thm of
            Const ("HOL.Trueprop", _) $ (Const ("HOL.eq", _) $ 
                (Const ("Finite_Set.card", _) $ s') $ _)
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

  fun sturm_card_eq_instantiate_tac ctxt i thm =
    let val prop = case prems_of thm of p :: _ => p | _ => concl_of thm
        val prop = case prop of Const ("prop", _) $ prop => prop
                                | _ => prop
        val prop = case prop of Const ("Pure.conjunction", _) $ 
                                    (Const ("Pure.term", _) $ _) $ prop => prop
                                 | _ => prop
        val (lhs,rhs) = prop |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
        val thy = Proof_Context.theory_of ctxt
        val vars = Term.add_vars rhs []
    in case vars of
          [v] => let val (idxname,_) = v
                      val n = Code_Evaluation.dynamic_value thy lhs
                  in case n of
                     NONE => Seq.empty
                   | SOME n => Seq.single (read_instantiate ctxt 
                                  [(idxname, Int.toString (HOLogic.dest_nat n))] thm)
                  end
        | _ => Seq.single thm
    end;
    

  fun sturm_card_eq_tac ctxt i thm =
    let val prop = concl_of thm
        val prop = case prop of Const ("prop", _) $ prop => prop
                                | _ => prop
        val prop = case prop of Const ("Pure.conjunction", _) $ 
                                    (Const ("Pure.term", _) $ _) $ prop => prop
                                 | _ => prop
        val (s,rhs) = case prop of
                        Const ("HOL.Trueprop", _) $
                        (Const ("HOL.eq", _) $ 
                          (Const ("Finite_Set.card", _) $ s) $ rhs)
                        => (s, rhs);
        val thm' = find_sturm_card_eq_thm ctxt s
    in  case thm' of
          NONE => error ""
        |  SOME thm'' => (EqSubst.eqsubst_tac ctxt [1] [thm''] i
                          THEN sturm_card_eq_instantiate_tac ctxt i) thm
    end;

  fun find_sturm_prop_thm ctxt prop =
    let val thy = Proof_Context.theory_of ctxt
        fun matches thm =
          case concl_of thm of
            Const ("HOL.Trueprop", _) $ (Const ("HOL.eq", _) $ prop' $ _)
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
    let val prop = concl_of thm
        val prop = case prop of Const ("prop", _) $ prop => prop
                                 | _ => prop
        val prop = case prop of Const ("Pure.conjunction", _) $ 
                                    (Const ("Pure.term", _) $ _) $ prop => prop
                                 | _ => prop
        val prop = case prop of Const ("HOL.Trueprop", _) $ prop => prop
                                 | _ => prop
        val thm' = find_sturm_prop_thm ctxt prop
    in  case thm' of
          NONE => Seq.empty
        | SOME thm' => EqSubst.eqsubst_tac ctxt [1] [thm'] i thm
    end;

  fun sturm_tac ctxt i thm =
    let val thy = Proof_Context.theory_of ctxt
        val prop = concl_of thm
        val prop = case prop of Const ("prop", _) $ prop => prop
                               | _  => prop
        val prop = case prop of Const ("Pure.conjunction", _) $ 
                                    (Const ("Pure.term", _) $ _) $ prop => prop
                                 | _ => prop
        val tac = case prop of
                Const ("HOL.Trueprop", _) $
                  (Const ("HOL.eq", _) $ 
                    (Const ("Finite_Set.card", _) $ s) $ rhs) 
                  => sturm_card_eq_tac
              | _ => sturm_prop_tac;
    in  (tac ctxt i
         THEN CONVERSION sturm_conv i
         THEN rtac @{thm TrueI} i
        ) thm
    end;

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

  val setup = Scan.succeed (fn ctxt => SIMPLE_METHOD' (sturm_tac ctxt))
end;
