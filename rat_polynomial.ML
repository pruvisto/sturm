
signature RAT_POLYNOMIAL =
sig
  type rat
  type pol
  
  val rat_to_string : rat -> string

  val gcd : int -> int -> int
  val ratsimp : rat -> rat
  val radd : rat -> rat -> rat
  val rmul : rat -> rat -> rat
  val rmul' : rat -> int -> rat
  val rdiv : rat -> rat -> rat
  val rdiv' : rat -> int -> rat
  val rsub : rat -> rat -> rat
  val rsign : rat -> int
  val rless : rat -> rat -> bool
  
  val lc : pol -> rat
  val pnorm : pol -> pol
  val pdegree : pol -> int
  val padd : pol -> pol -> pol
  val psub : pol -> pol -> pol
  val pscale : pol -> rat -> pol
  val pmul : pol -> pol -> pol
  val pdivmod : pol -> pol -> pol * pol
  val pdiv : pol -> pol -> pol
  val pmod : pol -> pol -> pol
  val pgcd : pol -> pol -> pol
  val pderiv : pol -> pol
  val peval : pol -> rat -> rat
  val peval_inf : pol -> int
  val peval_ninf : pol -> int
  
  val mk_rat_number : rat -> term
  
  val dest_rat_number : term -> rat
  val dest_poly : term -> term list
  val dest_poly' : term -> rat list
end;

structure Rat_Polynomial : RAT_POLYNOMIAL = 
struct

type rat = int * int;
type pol = rat list;

(* Rational numbers *)

fun gcd a b = 
  let fun gcd' a 0 = a 
        | gcd' a b = gcd b (a mod b)
  in  gcd' (abs a) (abs b)
  end;

fun ratsimp (a, b) = 
  let val g = gcd a b 
      val (a', b') = if b<0 then (~a,~b) else (a,b)
  in  (a' div g, b' div g)
  end;

fun int_to_string a = if a < 0 then "-" ^ Int.toString (~a) else Int.toString a

fun rat_to_string r =
  case ratsimp r of
    (a, 1) => int_to_string a
  | (a, b) => int_to_string a ^ " / " ^ Int.toString b;
  
fun radd (a1,b1) (a2,b2) = ratsimp (a1*b2+a2*b1,b1*b2);
fun rmul (a1,b1) (a2,b2) = ratsimp (a1*a2,b1*b2);
fun rmul' (a1,b1) c = ratsimp (a1*c,b1);
fun rdiv (a1,b1) (a2,b2) = ratsimp (a1*b2,b1*a2);
fun rdiv' (a1,b1) c = ratsimp (a1,b1*c);
fun rsub (a1,b1) (a2,b2) = ratsimp (a1*b2-a2*b1,b1*b2);
fun rsign ((a,_):rat) = Int.sign(a);
fun rless (a1,b1) (a2,b2) = a1*b2 < a2*b1;


(* Polynomials *)

fun lc [] = (0,1) 
  | lc xs = List.last xs;

fun prest [] = [] 
  | prest (p:pol) = List.take (p, length p - 1);

fun pnorm [] = [] 
  | pnorm p = if lc p = (0, 1) then pnorm (prest p) else p;

fun pdegree [] = ~1
  | pdegree ((n,_)::p) = if n = 0 then pdegree p else length p;


(* Arithmetic operations on polynomials *)

fun padd p1 p2 =
  let fun padd' [] [] r = r 
        | padd' (x::xr) [] r = padd' xr [] (x::r) 
        | padd' [] (y::yr) r = padd' [] yr (y::r) 
        | padd' (x::xr) (y::yr) r = padd' xr yr (radd x y ::r) 
  in  pnorm (rev (padd' p1 p2 [])) 
  end;

fun psub p1 p2 = 
  let fun psub' [] [] r = r 
        | psub' (x::xr) [] r = psub' xr [] (x::r) 
        | psub' [] (y::yr) r = psub' [] yr (y::r) 
        | psub' (x::xr) (y::yr) r = psub' xr yr (rsub x y ::r) 
  in  pnorm (rev (psub' p1 p2 []))
  end;

fun pscale p a = pnorm (map (rmul a) p);

fun pshift p n = List.tabulate (n, fn _ => (0,1)) @ p

fun pmul p1 p2 = 
  let fun pmul' [] _ r = r 
        | pmul' (c::cr) p2 r = pmul' cr ((0,1)::p2) (padd r (pscale p2 c)) 
  in  pnorm (pmul' p1 p2 [])
  end;

fun pdivmod p q = 
  let fun pdivmod' p q r = 
        if length p < length q then 
          (r, p) 
        else 
          let val d = length p - length q 
              val c = rdiv (lc p) (lc q) 
          in  pdivmod' (psub p (pshift (pscale q c) d)) q (padd r (pshift [c] d))
          end
  in  pdivmod' p q []
  end;

fun pdiv p q = fst (pdivmod p q);

fun pmod p q = snd (pdivmod p q);

fun pgcd p q = if pnorm q = [] then p else pgcd q (pmod p q);



(* Derivative *)

fun pderiv [] = []
  | pderiv p = 
  let fun pderiv' [] _ r = r 
        | pderiv' (c::p) i r = pderiv' p (i+1) (rmul c (i,1)::r) 
  in  rev (pderiv' (tl p) 1 [])
  end;


(* Evaluation *)

fun peval p x = 
  let fun peval' [] _ _ r = r 
        | peval' (c::cr) x xn r = peval' cr x (rmul xn x) (radd r (rmul xn c)) 
        
  in  peval' p x (1,1) (0,1) 
  end;

fun peval_inf p = rsign (lc p);

fun peval_ninf p = let val s = rsign (lc p) in if length p mod 2 = 0 then ~s else s end;



(* Constructors for rational numbers *)

fun mk_rat_number (a,1) = HOLogic.mk_number @{typ "real"} a
  | mk_rat_number (a,b) = 
    @{term "op/ :: real \<Rightarrow> real \<Rightarrow> real"} $ 
        HOLogic.mk_number @{typ "real"} a $ HOLogic.mk_number @{typ "real"} b;

(* Destructors for rational numbers / polynomials *)

fun dest_rat_number t =
  case t of 
    (Const ("Fields.inverse_class.divide",_)) $ a $ b
      => ratsimp (snd (HOLogic.dest_number a), snd (HOLogic.dest_number b))
  | (Const ("Rat.field_char_0_class.of_rat",_)) $ (Const ("Rat.Frct", _) $ 
        (Const ("Product_Type.Pair", _) $ a $ b))
      => ratsimp (snd (HOLogic.dest_number a), snd (HOLogic.dest_number b))
  | _ => (snd (HOLogic.dest_number t), 1);

fun dest_poly p =
  let fun dest_poly' p acc =
        case p of
          Const ("Polynomial.pCons", _) $ c $ p' =>
              dest_poly' p' (c :: acc)
        | Const ("Groups.zero_class.zero",_) =>
              rev acc
        | _ => raise TERM ("dest_poly", [p]);
  in
    dest_poly' p []
  end;

fun dest_poly' p = pnorm (map dest_rat_number (dest_poly p));

end;
