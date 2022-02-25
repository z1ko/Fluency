
load "Int";
load "Bool";
load "Random";

type sloc = string
type svar = string

(* Tutte le locazioni di memoria definite *)
type store = sloc * int list

datatype Texp = Tref  of Texp
              | Tunit 
              | Tproc
              | Tbool 
              | Tint

(* Tutte le operazioni conosciute *)
datatype oper = Add | Eq

(* Tutti i possibili costrutti del nostro linguaggio *)
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

    (* Valuta un'espressione con uno store fino a raggiungere un valore costante *)
    fun reduce (exp, store) = (

          (* Esegue una regola di riduzione *)
      let fun step (Boolean b,      store) = NONE
            | step (Integer n,      store) = NONE
            | step (Skip,           store) = NONE

            (* Regole: Operazioni aritmeniche e booleane *)
            | step (Op (a, oper, b), store) = (
                case (a, oper, b)
                  of (Integer a, Add, Integer b) => SOME (Integer (a + b), store)
                   | (Integer a,  Eq, Integer b) => SOME (Boolean (a = b), store)
                   | (a, oper, b) =>
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
            | step (If (g, t, f), store) = (
                case g
                  of (Boolean true)  => SOME (t, store)
                   | (Boolean false) => SOME (f, store)
                   | g => 
                    case step (g, store)
                      of SOME (g', store') => SOME (If (g', t, f), store)
                       | NONE => NONE
            )
          
            (* Accettiamo solo interi nelle locazioni *)
            | step (Assign (loc, e), store) = (
                case e
                  of (Integer n) => 
                    case Store.update store (loc, n)
                      of SOME (store') => SOME (Skip, store')
                       | NONE => NONE
                   | _ => 
                    case step (e, store)
                      of SOME (e', store') => SOME (Assign (loc, e'), store')
                       | NONE => NONE
            )

            | step (Deref loc, store) = (
                case Store.read store loc 
                  of SOME value => SOME (Integer value, store)
                   | NONE => NONE
            )

            | step (Seq (a, b), store) = (
                case a
                  of Skip => SOME (b, store)
                   | _ => 
                    case step (a, store)
                      of SOME (a', store') => SOME (Seq (a', b), store')
                       | NONE => NONE
            )

            | step (While (g, e), store) = 
                SOME (If (g, Seq (e, While (g, e)), Skip), store) 
          
            (* Regole: ParL - ParR - endL - endR *)
            | step (Par (l, r), store) = (
                case (l, r)
                  of (Skip, r) => SOME (r, store)
                   | (l, Skip) => SOME (l, store)
                   | _ => 
                    case (step (l, store), step (r, store))
                      of (SOME (l', lstore), NONE) => SOME (Par (l', r), lstore)
                       | (NONE, SOME (r', rstore)) => SOME (Par (l, r'), rstore) 
                       | (SOME (l', lstore), SOME (r', rstore)) => (
                        case Random.range (0, 2) (Random.newgen ()) (* Sceglie a caso *)
                          of 0 => SOME (Par (l', r), lstore)
                           | _ => SOME (Par (l, r'), rstore)
                        )
                       | _ => NONE
            )

            (* Regole: ChoiceL - ChoiceR *)
            | step (Choice (l, r), store) = (
                case (step (l, store), step (r, store))
                  of (SOME (l', lstore), NONE) => SOME (l', lstore)
                   | (NONE, SOME (r', rstore)) => SOME (r', rstore) 
                   | (SOME (l', lstore), SOME (r', rstore)) => (
                    case Random.range (0, 2) (Random.newgen ()) (* Sceglie a caso una delle due strade *)
                      of 0 => SOME (l', lstore)
                       | _ => SOME (r', rstore)
                    )
                   | _ => NONE
            )

            (* Regole: Await *)
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

            (* Irriducibile *)
            | step (expr, store) = NONE

          (* Continua a ridurre ad applicare le regole di riduzione *)
          and eval (expr, store) = case step (expr, store) 
                                     of SOME (expr', store') => eval (expr', store')
                                      | NONE => (expr, store)
      in
        eval (exp, store)
      end
    )

end

(* Controlla se l'espressione è ben tipata *)
structure TypeChecker = struct

    (* (string * Texp) list * expr -> Texp option *)
    fun inferType gamma (Integer n) = SOME Tint
      | inferType gamma (Boolean b) = SOME Tbool
      | inferType gamma (Skip)      = SOME Tunit

      | inferType gamma (Op (a, oper, b)) = (
          case (inferType gamma a, oper, inferType gamma b)
            of (SOME Tint, Add, SOME Tint) => SOME Tint
             | (SOME Tint,  Eq, SOME Tint) => SOME Tbool
             | _ => NONE
      )

      | inferType gamma (If (g, t, f)) = (
          case (inferType gamma g, inferType gamma t, inferType gamma f) 
            of (SOME Tbool, SOME t1, SOME t2) => if t1 = t2 then SOME t1 else NONE
             | _ => NONE
      )

      | inferType gamma (Deref x) = (
          case Store.read gamma x
            of SOME (Tref t) => SOME t
             | _ => NONE
      )

      | inferType gamma (Assign (loc, e)) = (
          case (Store.read gamma loc, inferType gamma e)
            of (SOME (Tref t), SOME t') => if t = t' then SOME Tunit else NONE
             | _ => NONE
      )

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

      | inferType gamma (Choice (l, r)) = (
          case (inferType gamma l, inferType gamma r)
            of (SOME Tunit, SOME Tunit) => SOME Tunit
             | _ => NONE
      )

      | inferType gamma expr = NONE

end

(* Int.evalExpr (Seq(Assign("x", Integer 4), Op(Integer 1, Add, Deref "x")), [("x", 1)]); *)
(* Int.evalExpr (App(Fn("x", Op(Sym "x", Add, Sym "x")), Integer 2), []); *)

structure PrettyPrinter = struct

  (* fn: op -> string *)
  fun printOper Add   = "+"
    | printOper Eq    = "="

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
    | printExpr (If (g, t, f))    = "if " ^  (printExpr g) ^ " then " ^ (printExpr t) ^ " else " ^ (printExpr f)
    | printExpr (Deref x)         = "!" ^ x
    | printExpr (Assign (loc, n)) = loc ^ " := " ^ (printExpr n)
    | printExpr (Seq (a, b))      = (printExpr a) ^ "; " ^ (printExpr b)
    | printExpr (While (g, e))    = "while " ^ (printExpr g) ^ " do " ^ (printExpr e)
    | printExpr (Par (l, r))      = (printExpr l) ^ " || " ^ (printExpr r)
    | printExpr (Choice (l, r))   = (printExpr l) ^ " Y " ^ (printExpr r)
    | printExpr (Await (g, e))    = "await " ^ (printExpr g) ^ " protect " ^ (printExpr e) ^ " end"

end

(* Dato uno store di semplici interi ritorna una gamma adatta *)
fun generate_gamma [] result = result
  | generate_gamma ((loc, _)::tail) result =
      generate_gamma tail ((loc, Tref Tint)::result)

(* Printa il contenuto dello store *)
fun print_store [] = ()
  | print_store ((loc, value)::tail) = (
      print ("\t(" ^ loc ^ ", " ^ (Int.toString value) ^ ")\n");
      print_store tail)

(* Printa il contenuto di gamma *)
fun print_gamma [] = ()
  | print_gamma ((loc, ty)::tail) = (
      print ("\t(" ^ loc ^ ", " ^ (PrettyPrinter.printType ty) ^ ")\n");
      print_gamma tail)

(* Funzione che accetta un'espressione, controlla se è tipabile, printa il suo tipo
 * ed in fine la visualizza in un formato comprensibile *)

fun digest expr NONE = (digest expr (SOME []))
  | digest expr (SOME store) = (
      print ("Espressione: " ^ PrettyPrinter.printExpr expr ^ "\n");
      let val gamma = generate_gamma store [] 
      in
        case TypeChecker.inferType gamma expr
          of NONE    => print "ERRORE: non è tipabile!\n"
           | SOME t  => (
              print "Gamma:\n"; print_gamma gamma;
              print "Store iniziale:\n"; print_store store;
              print ("Tipo dell'espressione: " ^ (PrettyPrinter.printType t) ^ "\n");
              let val (res, store) = ExprInt.reduce (expr, store) 
              in
                print "Store finale:\n"; print_store store;
                print ("Riduzione: " ^ (PrettyPrinter.printExpr res) ^ "\n")
              end)
      end)


(* PARALLELO *)
(* ExprInt.reduce (Par (Op (Integer 1, Add, Integer 1), Op (Integer 2, Add, Integer 2)), []); *)
(* ExprInt.reduce (Par (Assign ("x", Integer 0), Op (Integer 2, Add, Integer 2)), [("x", 10)]); *)
(* ExprInt.reduce (Par (Assign ("x", Integer 0), Assign("x", Integer 5)), [("x", 10)]); *)

(* NON-DET *)
(* ExprInt.reduce (Choice (Op (Integer 1, Add, Integer 1), Op (Integer 2, Add, Integer 2)), []); *)

(* AWAIT *)
(* ExprInt.reduce (Assign ("x", Integer 10), [("x", 0)]); *)
(* ExprInt.reduce (Await (Boolean true, Assign ("x", Integer 0)), [("x", 10)]); *)
(* ExprInt.reduce (Await (Boolean false, Assign ("x", Integer 0)), [("x", 10)]); *)
