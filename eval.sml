
load "Int";
load "Bool";
load "Random";

(* Stringa rappresentante una locazione in memoria *)
type sloc = string

(* Memoria per variabili intere *)
type store = sloc * int list

(* Tutti i tipi supportati dal linguaggio *)
datatype Texp = Tref of Texp (* Solo le intref solo implementate *)
              | Tunit 
              | Tproc
              | Tbool 
              | Tint

(* Tutte le operazioni supportate *)
datatype oper = Add | Ge

(* Tutti i possibili costrutti del linguaggio *)
datatype expr = Boolean of bool
              | Integer of int
              | Op      of expr * oper * expr
              | If      of expr * expr * expr
              | Assign  of sloc * expr
              | While   of expr * expr
              | Seq     of expr * expr
              | Deref   of sloc
              | Await   of expr * expr
              | Par     of expr * expr
              | Choice  of expr * expr
              | Skip

(* Semplice interprete per il linguaggio *)
structure ExprInt = struct

    (* Indica che l'expressione è un valore *)
    fun value (Boolean b)     = true
      | value (Integer x)     = true
      | value (Skip)          = true
      | value _               = false

    (* Valuta un'espressione con uno store fino a raggiungere un valore o non poter più applicare regole di riduzione *)
    fun reduce (exp, store) = (

          (* Esegue una regola di riduzione sull'espressione se possibile *)
      let fun step (Boolean b, store) = NONE
            | step (Integer n, store) = NONE
            | step (Skip,      store) = NONE

            (* Regole: Operazioni aritmetiche e booleane *)
            | step (Op (a, oper, b), store) = (
                case (a, oper, b)
                  of (Integer a, Add, Integer b) => SOME (Integer (a +  b), store)
                   | (Integer a,  Ge, Integer b) => SOME (Boolean (a >= b), store)
                   | (a, oper, b) => (* Left to Right *)
                        if value a then
                          case step (b, store)
                            of SOME (b', store') => SOME (Op (a, oper, b'), store')
                             | NONE => NONE
                        else
                          case step (a, store)
                            of SOME (a', store') => SOME (Op (a', oper, b), store')
                             | NONE => NONE
            )

            (* Regole: If *)
            | step (If (guard, te, fe), store) = (
                case guard
                  of (Boolean true)  => SOME (te, store)
                   | (Boolean false) => SOME (fe, store)
                   | guard => (* Avanza la guardia *)
                    case step (guard, store)
                      of SOME (guard', store') => SOME (If (guard', te, fe), store)
                       | NONE => NONE
            )
          
            (* Assegnamento *)  
            | step (Assign (loc, e), store) = (
                if value e then
                  case e
                    of (Integer n) => (* Accettiamo solo interi per ora *)
                      case Store.update store (loc, n)
                          of SOME (store') => SOME (Skip, store')
                           | NONE => NONE (* TODO: Crea nuova locazione *)
                     | _ => NONE
                else
                  case step (e, store)
                      of SOME (e', store') => SOME (Assign (loc, e'), store')
                       | NONE => NONE
                (*
                case e
                  of (Integer n) => (* Accettiamo solo interi nelle locazioni *)
                    case Store.update store (loc, n)
                      of SOME (store') => SOME (Skip, store')
                       | NONE => NONE
                   | _ =>
                    case step (e, store)
                      of SOME (e', store') => SOME (Assign (loc, e'), store')
                       | NONE => NONE *)
            )

            (* Dereferenziazione *)
            | step (Deref loc, store) = (
                case Store.read store loc 
                  of SOME value => SOME (Integer value, store)
                   | NONE => NONE
            )

            (* Composizione sequenziale *)
            | step (Seq (a, b), store) = (
                case a
                  of Skip => SOME (b, store)
                   | _ => 
                    case step (a, store)
                      of SOME (a', store') => SOME (Seq (a', b), store')
                       | NONE => NONE
            )

            (* Ciclo while: riscrittura come IF sequenziale *)
            | step (While (g, e), store) = 
                SOME (If (g, Seq (e, While (g, e)), Skip), store) 
          

            (* Composizione Parallela: ParL - ParR - endL - endR *)
            | step (Par (l, r), store) = (
                case (l, r)
                  of (Skip, r) => SOME (r, store) (* End Left  *)
                   | (l, Skip) => SOME (l, store) (* End Right *)
                   | _ => 
                    case (step (l, store), step (r, store))
                      of (SOME (l', lstore), NONE) => SOME (Par (l', r), lstore) (* Par Left  OBBLIGATA *)
                       | (NONE, SOME (r', rstore)) => SOME (Par (l, r'), rstore) (* Par Right OBBLIGATA *)
                       | (SOME (l', lstore), SOME (r', rstore)) => (
                        case Random.range (0, 2) (Random.newgen ())
                          of 0 => SOME (Par (l', r), lstore)  (* Par Left  CASUALE *)
                           | _ => SOME (Par (l, r'), rstore)) (* Par Right CASUALE *)
                       | _ => NONE
            )

            (* Scelta Non Deterministica: ChoiceL - ChoiceR *)
            | step (Choice (l, r), store) = (
                case (step (l, store), step (r, store))
                  of (SOME (l', lstore), NONE) => SOME (l', lstore) (* Choice Left  OBBLIGATA *)
                   | (NONE, SOME (r', rstore)) => SOME (r', rstore) (* Choice Right OBBLIGATA *)
                   | (SOME (l', lstore), SOME (r', rstore)) => (
                    case Random.range (0, 2) (Random.newgen ())
                      of 0 => SOME (l', lstore)  (* Choice Left  CASUALE *)
                       | _ => SOME (r', rstore)) (* Choice Right CASUALE *)
                   | _ => NONE
            )

            (* Await *)
            | step (Await (g, e), store) = (
                case g 
                  of (Boolean false) => NONE
                   | (Boolean true)  => (
                    case eval (e, store) (* Esegue tutto il corpo in un colpo solo *) 
                      of (Skip, store') => SOME (Skip, store')
                       | _ => NONE)
                   | g => (
                    case step (g, store) (* Esegue la guardia *)
                      of SOME (g', store') => SOME (Await (g', e), store')
                       | NONE => NONE)
            )

            (* Impossibile *)
            | step (expr, store) = NONE

          (* Continua ad applicare le regole di riduzione *)
          and eval (expr, store) = case step (expr, store) 
                                     of SOME (expr', store') => eval (expr', store')
                                      | NONE => (expr, store)
      in
        eval (exp, store)
      end
    )

end

(* Deduce il tipo di un'espressione nel linguaggio *)
structure TypeChecker = struct

    (* (string * Texp) list * expr -> Texp option *)
    fun inferType gamma (Integer n) = SOME Tint
      | inferType gamma (Boolean b) = SOME Tbool
      | inferType gamma (Skip)      = SOME Tunit

      (* Tipo dipende dall'operazione *)
      | inferType gamma (Op (a, oper, b)) = (
          case (inferType gamma a, oper, inferType gamma b)
            of (SOME Tint, Add, SOME Tint) => SOME Tint
             | (SOME Tint,  Ge, SOME Tint) => SOME Tbool
             | _ => NONE
      )

      (* I tipi dei rami vero e falso devono essere uguali *)
      | inferType gamma (If (g, t, f)) = (
          case (inferType gamma g, inferType gamma t, inferType gamma f) 
            of (SOME Tbool, SOME t1, SOME t2) => if t1 = t2 then SOME t1 else NONE
             | _ => NONE
      )

      (* Accettiamo solo locazioni di interi *)
      | inferType gamma (Deref x) = (
          case Store.read gamma x
            of SOME (Tref Tint) => SOME Tint
             | _ => NONE
      )

      (* Accettiamo solo locazioni di interi *)
      | inferType gamma (Assign (loc, e)) = (
          case (Store.read gamma loc, inferType gamma e)
            of (SOME (Tref Tint), SOME Tint) => SOME Tunit
             | _ => NONE
      )

      (* Composizione sequenziale *)
      | inferType gamma (Seq (a, b)) = (
          case (inferType gamma a, inferType gamma b)
            of (SOME Tunit, SOME t) => SOME t
             | _ => NONE
      )

      | inferType gamma (While (g, e)) = (
          case (inferType gamma g, inferType gamma e)
            of (SOME Tbool, SOME Tunit) => SOME Tunit
             | _ => NONE
      )

      (* Composizione parallela, varie combinazioni di tipi sono ammesse *)
      | inferType gamma (Par (l, r)) = (
          case (inferType gamma l, inferType gamma r)
            of (SOME Tunit, SOME Tunit) => SOME Tproc
             | (SOME Tunit, SOME Tproc) => SOME Tproc
             | (SOME Tproc, SOME Tunit) => SOME Tproc
             | (SOME Tproc, SOME Tproc) => SOME Tproc
             | _ => NONE   
      )

      | inferType gamma (Await (g, e)) = (
          case (inferType gamma g, inferType gamma e)
            of (SOME Tbool, SOME Tunit) => SOME Tunit
             | _ => NONE
      )

      (* Scelta Non Deterministica *)
      | inferType gamma (Choice (l, r)) = (
          case (inferType gamma l, inferType gamma r)
            of (SOME Tunit, SOME Tunit) => SOME Tunit
             | _ => NONE
      )

      (* Impossibile *)
      | inferType gamma expr = NONE

end

(* Int.evalExpr (Seq(Assign("x", Integer 4), Op(Integer 1, Add, Deref "x")), [("x", 1)]); *)
(* Int.evalExpr (App(Fn("x", Op(Sym "x", Add, Sym "x")), Integer 2), []); *)

structure PrettyPrinter = struct

  (* fn: op -> string *)
  fun printOper Add   = "+"
    | printOper Ge    = ">="

  (* fn: Texp -> string *)
  fun printType (Tref t) = "ref " ^ (printType t)
    | printType (Tunit)  = "unit"
    | printType (Tbool)  = "bool"
    | printType (Tint)   = "int"
    | printType (Tproc)  = "proc"

  (* fn: expr -> string *)
  fun printExpr (Skip)            = "skip"
    | printExpr (Integer n)       = (Int.toString n)
    | printExpr (Boolean b)       = (Bool.toString b)
    | printExpr (Op (a, oper, b)) = "(" ^ (printExpr a) ^ " " ^ (printOper oper) ^ " " ^ (printExpr b) ^ ")"
    | printExpr (If (g, t, f))    = "if " ^  (printExpr g) ^ " then {" ^ (printExpr t) ^ "} else {" ^ (printExpr f) ^ "}"
    | printExpr (Deref x)         = "!" ^ x
    | printExpr (Assign (loc, n)) = loc ^ " := " ^ (printExpr n)
    | printExpr (Seq (a, b))      = (printExpr a) ^ "; " ^ (printExpr b)
    | printExpr (While (g, e))    = "while " ^ (printExpr g) ^ " do {" ^ (printExpr e) ^ "}"
    | printExpr (Par (l, r))      = (printExpr l) ^ " || " ^ (printExpr r)
    | printExpr (Choice (l, r))   = "{" ^ (printExpr l) ^ "} Y {" ^ (printExpr r) ^ "}"
    | printExpr (Await (g, e))    = "await " ^ (printExpr g) ^ " protect {" ^ (printExpr e) ^ "} end"

end

(* Dato uno store di semplici interi ritorna una gamma adatta *)
fun generate_gamma [] result = result
  | generate_gamma ((loc, _)::tail) result =
      generate_gamma tail ((loc, Tref Tint)::result)

(* Printa il contenuto dello store *)
fun print_store [] = ()
  | print_store [(loc, value)] = print ("(" ^ loc ^ ", " ^ (Int.toString value) ^ ")")
  | print_store ((loc, value)::tail) = (
      print ("(" ^ loc ^ ", " ^ (Int.toString value) ^ "), ");
      print_store tail)

(* Printa il contenuto di gamma *)
fun print_gamma [] = ()
  | print_gamma [(loc, ty)] = print ("(" ^ loc ^ ", " ^ (PrettyPrinter.printType ty) ^ ")")
  | print_gamma ((loc, ty)::tail) = (
      print ("(" ^ loc ^ ", " ^ (PrettyPrinter.printType ty) ^ "), ");
      print_gamma tail)

(* Funzione che accetta un'espressione, controlla se è tipabile, printa il suo tipo
 * ed in fine la visualizza in un formato comprensibile *)
fun digest expr NONE = (digest expr (SOME []))
  | digest expr (SOME store) = (
      print ("Espressione: " ^ (PrettyPrinter.printExpr expr));
      let val gamma = generate_gamma store [] 
      in
        case TypeChecker.inferType gamma expr
          of NONE    => print "\nEspressione non e' tipabile!\n"
           | SOME t  => (
              print "\nGamma: ["; print_gamma gamma; print "]";
              print "\nStore iniziale: ["; print_store store; print "]";
              print ("\nTipo dell'espressione: " ^ (PrettyPrinter.printType t));
              let val (res, store) = ExprInt.reduce (expr, store) 
              in
                print "\nStore finale: ["; print_store store; print "]";
                print ("\nRiduzione: " ^ (PrettyPrinter.printExpr res) ^ "\n")
              end)
      end)


(* PARALLELO *)

(* digest (Par (Op (Integer 1, Add, Integer 1), Op (Integer 2, Add, Integer 2))) NONE; *)
(* digest (Par (Assign ("x", Integer 0), Op (Integer 2, Add, Integer 2))) (SOME [("x", 10)]); *)
(* digest (Par (Assign ("x", Integer 0), Assign("x", Integer 5))) (SOME [("x", 10)]); *)

(* NON-DET *)

(* (x := 1 + 1; y := 1) Y (y := 2; x := 2 + 2)*)
(* digest (Choice (Seq (Assign ("x", Op (Integer 1, Add, Integer 1)), Assign ("y", Integer 1)), Seq (Assign("y", Integer 2), Assign ("x", Op (Integer 2, Add, Integer 2))))) (SOME [("x", 0), ("y", 0)]); *)

(* AWAIT *)

(* digest (Assign ("x", Integer 10)) (SOME [("x", 0)]); *)
(* digest (Await (Boolean true, Assign ("x", Integer 0))) (SOME [("x", 10)]); *)
(* digest (Await (Boolean false, Assign ("x", Integer 0))) (SOME [("x", 10)]); *)

(* Esegue solo uno dei due await *)
(* digest (Par (Await (Op (Deref "g", Ge, Integer 1), Seq (Assign ("r", Integer 1), Assign ("g", Integer 0))), Await (Op (Deref "g", Ge, Integer 1), Seq (Assign ("r", Integer 2), Assign ("g", Integer 0))))) (SOME [("g", 1), ("r", 0)]); *)