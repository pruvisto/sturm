
open Rat_Polynomial;

signature RAT_STURM =
sig
  val sturm : pol -> pol -> pol list
  val sturmd : pol -> pol list
  val sturm_count : pol list -> int
  val sturm_count_between : pol list -> rat * rat -> int
  
  val isolate_roots_between : pol -> rat * rat -> rat list
  val isolate_roots_greater : pol -> rat -> rat list
  val isolate_roots_leq : pol -> rat -> rat list
  val isolate_roots : pol -> rat list
  
  val poly_nonneg_witness_between : term -> term * term -> term option
  val poly_nonneg_witness_above : term -> term -> term option
  val poly_nonneg_witness_below : term -> term -> term option
  val poly_nonneg_witness : term -> term option
  val poly_mono_witness : term -> bool -> term option
end;

structure Rat_Sturm : RAT_STURM =
struct

(* Sturm chains *)

fun sturm p q = 
  let fun sturm' p [] ps = p::ps 
        | sturm' p q ps = sturm' q (pscale (pmod p q) (~1,1)) (p::ps) 
  in  rev (sturm' p q []) 
  end;

fun sturmd [] = [[], []]
  | sturmd p = 
  let val q = pderiv p
      val d = pgcd p q
  in sturm (pdiv p d) (pdiv q d)
  end;

fun count_sign_changes xs = 
  let fun f x (s,n) = if s=0 orelse s=x then (x,n) else if x=0 then (s,n) else (x,n+1)
  in  snd (fold f xs (0,0))
  end;

fun sturm_count ps = 
  count_sign_changes (map peval_ninf ps) - 
  count_sign_changes (map peval_inf ps);

fun sturm_count_between ps (a,b) =
  if rless a b then 
    count_sign_changes (map (fn p => rsign (peval p a)) ps) - 
    count_sign_changes (map (fn p => rsign (peval p b)) ps)
  else
    0;


(* Isolating roots *)

(* These functions try to divide the real line or parts of it into intervals of the shape
   (a;b] such that each interval contains exactly one root. *)
local
  fun find_bounds [] _ _ = 0
    | find_bounds ([] :: _) _ _ = 0
    | find_bounds sc n_roots b =
        if sturm_count_between sc ((~b,1),(b,1)) <> n_roots then
          find_bounds sc n_roots (2*b)
        else
          b+1;

  fun isolate_roots_between_aux p sc n_roots bounds =
    let fun adjust_interval_left a b =
              if sturm_count_between sc (a, b) = 0 then
                b
              else 
                adjust_interval_left a (rdiv' (radd a b) 2)

         fun adjust_interval_right a b =
              if sturm_count_between sc (a, b) = 1 andalso fst (peval p a) <> 0 then
                a
              else 
                adjust_interval_right (rdiv' (radd a b) 2) b

        fun find_root_splitter 0 _ = error "No roots in interval for root splitting."
          | find_root_splitter n (a,b) =
          let val m = rdiv' (radd a b) 2
              val n' = sturm_count_between sc (a,m)
          in  if n' = 0 then
                find_root_splitter n (m,b)
              else if n' = n then
                find_root_splitter n (a,m)
              else if fst (peval p m) = 0 then
                (adjust_interval_left m b, n')
              else
                (m, n')
          end;
                
        fun isolate_roots_between_aux' 0 _ = []
          | isolate_roots_between_aux' 1 (_,b) = [b]
          | isolate_roots_between_aux' n (a,b) =
             let val (m,n') = find_root_splitter n (a,b)
             in  isolate_roots_between_aux' n' (a,m) @ isolate_roots_between_aux' (n - n') (m,b)
             end;

        val p = pnorm p
    in
      if List.null p then [] else 
        let val (a,b) = bounds
            val a = if fst (peval p a) = 0 then adjust_interval_left a b else a
            val (b, n_roots) = if fst (peval p b) = 0 then 
                                  (adjust_interval_right a b, n_roots - 1)
                                else (b, n_roots)
        in  a :: isolate_roots_between_aux' n_roots (a,b)
        end
    end;

in
  fun isolate_roots_between p bounds = 
    let val sc = sturmd p;
        val n_roots = sturm_count_between sc bounds;
    in  isolate_roots_between_aux p sc n_roots bounds
    end;

  fun isolate_roots_greater p a = 
    let val sc = sturmd p;
        val b = find_bounds sc (sturm_count sc) 2;
        val n_roots = sturm_count_between sc (a, (b,1));
    in  isolate_roots_between_aux p sc n_roots (a, (b,1))
    end;

  fun isolate_roots_leq p a = 
    let val sc = sturmd p;
        val b = find_bounds sc (sturm_count sc) 2;
        val n_roots = sturm_count_between sc ((~b,1), a);
    in  isolate_roots_between_aux p sc n_roots ((~b,1), a)
    end;

  fun isolate_roots p =
    let val sc = sturmd p;
        val n_roots = sturm_count sc;
        val b = find_bounds sc n_roots 2;
    in  isolate_roots_between_aux p sc n_roots ((~b,1),(b,1))
    end; 

end;


(* Creating witness for nonnegativity of a real polynomial *)

fun check_witness w p p' mono strict =
  case filter (fn (_,y) => rsign y < 0) (map (fn x => (x, peval p' x)) w) of
    [] => true
  | (x,y) :: _ => 
      let val p' = "[:" ^ String.concatWith ", " (map rat_to_string p) ^ ":]"
          fun int_to_string a = if a < 0 then "-" ^ Int.toString (~a) else Int.toString a
          fun rat_to_string' a = case ratsimp a of
                                   (a,1) => if a < 0 then "(" ^ int_to_string a ^ ")"
                                              else int_to_string a
                                 | (a,b) => "(" ^ int_to_string a ^ " / " ^ int_to_string b ^ ")"
          val msg = if not mono then
                      "Failed to show nonnegativity of p = " ^ p' ^ 
                         ".\nCounterexample: peval p " ^ 
                         rat_to_string' x ^ " = " ^ rat_to_string y
                    else if strict then
                      "Failed to show strict monotonicity of p = " ^ p' ^ 
                         ".\nCounterexample: peval p' " ^ 
                         rat_to_string' x ^ " = " ^ rat_to_string y
                    else
                      "Failed to show monotonicity of p = " ^ p' ^ 
                         ".\nCounterexample: peval p' " ^ 
                         rat_to_string' x ^ " = " ^ rat_to_string y
          val _ = Output.urgent_message msg
      in
        false
  end;

fun poly_nonneg_witness p = 
  let val p = dest_poly' p
      val w = isolate_roots p
  in  if check_witness w p p false false then
        SOME (HOLogic.mk_list @{typ "real"}  (map mk_rat_number w))
      else
        NONE
  end;

fun poly_nonneg_witness_above p a = 
  let val p = dest_poly' p
      val a = dest_rat_number a
      val w = isolate_roots_greater p a
  in  if check_witness w p p false false then
        SOME (HOLogic.mk_list @{typ "real"}  (map mk_rat_number w))
      else
        NONE
  end;

fun poly_nonneg_witness_below p a = 
  let val p = dest_poly' p
      val a = dest_rat_number a
      val w = isolate_roots_leq p a
  in  if check_witness w p p false false then
        SOME (HOLogic.mk_list @{typ "real"}  (map mk_rat_number w))
      else
        NONE
  end;

fun poly_nonneg_witness_between p (a,b) = 
  let val p = dest_poly' p
      val (a, b) = (dest_rat_number a, dest_rat_number b)
      val w = isolate_roots_between p (a, b)
  in  if check_witness w p p false false then
        SOME (HOLogic.mk_list @{typ "real"}  (map mk_rat_number w))
      else
        NONE
  end;

fun poly_mono_witness p strict = 
  let val p = dest_poly' p
      val p' = pderiv p
      val w = isolate_roots p'
  in  if strict andalso List.null (pnorm p') then
        let val _ = Output.urgent_message ("Failed to show strict monotonicity of p = " ^ 
                                 "[:" ^ String.concatWith ", " (map rat_to_string p) ^ ":]" ^
                                 "; polynomial is constant.")
        in NONE
        end
      else if check_witness w p p' true strict then
        SOME (HOLogic.mk_list @{typ "real"}  (map mk_rat_number w))
      else
        NONE
  end;

end;

