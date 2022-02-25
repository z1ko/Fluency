
load "Int";
load "Bool";

type sloc = string
type svar = string

(* Tutte le locazioni di memoria definite *)
type store = sloc * int list

datatype Texp = Tfunc of Texp * Texp  
              | Tref  of Texp
              | Tunit 
              | Tbool 
              | Tint

(* Tutte le operazioni conosciute *)
datatype oper = Add | Eq

(* Tutti i possibili costrutti del nostro linguaggio *)
datatype expr = Boolean of bool
              | Integer of int
              | Fn      of Texp * svar * expr
              | Sym     of svar
              | Op      of expr * oper * expr
              | If      of expr * expr * expr
              | Assign  of sloc * expr
              | While   of expr * expr
              | Seq     of expr * expr
              | App     of expr * expr
              | Deref   of sloc
              | Skip

(* Semplice interprete per il linguaggio *)
structure ExprInt = struct

    (* Indica che l'expressione è un valore *)
    fun value (Boolean b)     = true
      | value (Integer x)     = true
      | value (Fn (t, v, f))  = true
      | value (Sym x)         = true
      | value (Skip)          = true
      | value _               = false


    (* Sostituisce l'espressione 'repl' con tutte le istanze di variabile 'var' in 'exp' *)
    fun substitute var repl (Boolean b)         = Boolean b
      | substitute var repl (Integer n)         = Integer n
      | substitute var repl (Fn (t, x, e))      = Fn (t, x, substitute var repl e)
      | substitute var repl (If (g, t, f))      = If (substitute var repl g, substitute var repl t, substitute var repl f)
      | substitute var repl (Assign (loc, e))   = Assign (loc, substitute var repl e)
      | substitute var repl (While (g, e))      = While (substitute var repl g, substitute var repl e)
      | substitute var repl (Seq (a,b))         = Seq (substitute var repl a, substitute var repl b)
      | substitute var repl (App (f, e))        = App (substitute var repl f, substitute var repl e)
      | substitute var repl (Deref loc)         = Deref loc
      | substitute var repl (Op (a, oper, b))   = Op (substitute var repl a, oper, substitute var repl b)
      | substitute var repl (Sym x)             = if x = var then repl else (Sym x)
      | substitute var repl Skip                = Skip

    (* Esegue un singolo step di computazione *)
    (* fn: expr * ((string * int) list) -> (expr * (string * int) list) option) *)
    fun step (Boolean b,      store) = NONE
      | step (Integer n,      store) = NONE
      | step (Fn (t, x, e),   store) = NONE
      | step (Sym x,          store) = NONE (* Se arriviamo a questo punto vuol dire che x è unbound! *)
      | step (Skip,           store) = NONE

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
                       | NONE => NONE)

      | step (If (g, t, f), store) = (
          case g
            of (Boolean True)  => SOME (t, store)
             | (Boolean False) => SOME (f, store)
             | g => case step (g, store)
                      of SOME (g', store') => SOME (If (g', t, f), store)
                       | NONE => NONE)

      (* Accettiamo solo interi nelle locazioni *)
      | step (Assign (loc, e), store) = (
          case e
            of (Integer n) => case Store.update store (loc, n)
                                of SOME (store') => SOME (Skip, store')
                                 | NONE => NONE
             | _ => case step (e, store)
                      of SOME (e', store') => SOME (Assign (loc, e'), store')
                       | NONE => NONE)

      | step (Deref loc, store) = (
          case Store.read store loc 
            of SOME value => SOME (Integer value, store)
             | NONE => NONE)

      | step (Seq (a, b), store) = (
          case a
            of Skip => SOME (b, store)
             | _ => case step (a, store)
                      of SOME (a', store') => SOME (Seq (a', b), store')
                       | NONE => NONE)

      | step (While (g, e), store) = 
          SOME (If (g, Seq (e, While (g, e)), Skip), store) 
    
      (* Call By Value *)
      | step (App (a, b), store) = (
          case (a, b)
            of (Fn (t, x, e), Integer n) => SOME (substitute x (Integer n) e, store)
             | (a, b) => 
                  if value a then
                    case step (b, store) 
                      of SOME (b', store') => SOME (App (a, b'), store)
                       | NONE => NONE
                  else
                    case step (a, store)
                      of SOME (a', store') => SOME (App (a', b), store)
                       | NONE => NONE)

      | step (expr, store) = NONE


    (* Valuta un'espressione con uno store fino a raggiungere un valore costante *)
    fun evalExpr (exp, store) =
        case step (exp, store) of SOME((exp', store')) => evalExpr (exp', store')
            | NONE => (exp, store)

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
             | _ => NONE)

      | inferType gamma (If (g, t, f)) = (
          case (inferType gamma g, inferType gamma t, inferType gamma f) 
            of (SOME Tbool, SOME t1, SOME t2) => if t1 = t2 then SOME t1 else NONE
             | _ => NONE)

      | inferType gamma (Deref x) = (
          case Store.read gamma x
            of SOME (Tref t) => SOME t
             | _ => NONE)

      | inferType gamma (Assign (loc, e)) = (
          case (Store.read gamma loc, inferType gamma e)
            of (SOME (Tref t), SOME t') => if t = t' then SOME Tunit else NONE
             | _ => NONE)

      | inferType gamma (Seq (a, b)) = (
          case (inferType gamma a, inferType gamma b)
            of (SOME Tunit, SOME t) => SOME t
             | _ => NONE)

      | inferType gamma (While (g, e)) = (
          case (inferType gamma g, inferType gamma e)
            of (SOME Tbool, SOME Tunit) => SOME Tunit
             | _ => NONE)

      | inferType gamma (Fn (t, x, e)) = (
          let val gamma' = Store.insert gamma (x, t) in
            case inferType gamma' e
              of SOME t1 => SOME (Tfunc (t, t1))
               | NONE => NONE
          end)

      | inferType gamma (Sym x) = (
          case Store.read gamma x
            of SOME t => SOME t
             | NONE => NONE)
      
      | inferType gamma (App (f, b)) = (
          case (inferType gamma f, inferType gamma b)
            of (SOME (Tfunc (t1, t2)), SOME t3) => if t1 = t3 then SOME t2 else NONE
             | _ => NONE)

      | inferType gamma expr = NONE

end

(* Int.evalExpr (Seq(Assign("x", Integer 4), Op(Integer 1, Add, Deref "x")), [("x", 1)]); *)
(* Int.evalExpr (App(Fn("x", Op(Sym "x", Add, Sym "x")), Integer 2), []); *)

structure PrettyPrinter = struct

  (* fn: op -> string *)
  fun printOper Add   = "+"
    | printOper Eq    = "="

  (* fn: Texp -> string *)
  fun printType (Tfunc (t1, t2))  = (printType t1) ^ " -> " ^ (printType t2)
    | printType (Tref t)          = "ref " ^ (printType t)
    | printType (Tunit)           = "unit"
    | printType (Tbool)           = "bool"
    | printType (Tint)            = "int"

  (* fn: expr -> string *)
  fun printExpr (Skip)            = "skip"
    | printExpr (Integer n)       = (Int.toString n)
    | printExpr (Boolean b)       = (Bool.toString b)
    | printExpr (Sym x)           = x
    | printExpr (Op (a, oper, b)) = "(" ^ (printExpr a) ^ " " ^ (printOper oper) ^ " " ^ (printExpr b) ^ ")"
    | printExpr (If (g, t, f))    = "if " ^  (printExpr g) ^ " then " ^ (printExpr t) ^ " else " ^ (printExpr f)
    | printExpr (Deref x)         = "!" ^ x
    | printExpr (Assign (loc, n)) = loc ^ " := " ^ (printExpr n)
    | printExpr (Seq (a, b))      = (printExpr a) ^ "; " ^ (printExpr b)
    | printExpr (While (g, e))    = "while " ^ (printExpr g) ^ " do " ^ (printExpr e)
    | printExpr (Fn (t, x, e))    = "fn " ^ x ^ ": " ^ (printType t) ^ " => " ^ (printExpr e)
    | printExpr (App (a, b))      = "(" ^ (printExpr a) ^ ") " ^ (printExpr b)

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
              let val (res, store) = ExprInt.evalExpr (expr, store) 
              in
                print "Store finale:\n"; print_store store;
                print ("Riduzione: " ^ (PrettyPrinter.printExpr res) ^ "\n")
              end)
      end)


(* digest (Op(Integer 5, Add, Boolean false)); *)
