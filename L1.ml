open Printf
(*++++++++++++++++++++++++++++++++++++++*)
(*  Interpretador para L1               *)
(*   - inferência de tipos              *)
(*   - avaliador big step com ambiente  *)
(*++++++++++++++++++++++++++++++++++++++*)

(**+++++++++++++++++++++++++++++++++++++++++*)
(*  SINTAXE, AMBIENTE de TIPOS e de VALORES *)
(*++++++++++++++++++++++++++++++++++++++++++*) 
type tipo =
  | TyInt
  | TyBool
  | TyFn of tipo * tipo
  | TyRef of tipo
  | TyUnit

type ident = string

type op = Sum | Sub | Mult | Eq | Gt | Lt | Geq | Leq

type expr =
  | Num of int
  | Var of ident
  | True
  | False
  | Binop of op * expr * expr
  | If of expr * expr * expr
  | Fn of ident * tipo * expr
  | App of expr * expr
  | Let of ident * tipo * expr * expr
  | LetRec of ident * tipo * expr  * expr
  | Asg of expr * expr
  | Dref of expr
  | New of expr
  | Seq of expr * expr
  | Whl of expr * expr
  | Skip
              
type tenv = (ident * tipo) list

type valor =
  | VNum of int
  | VTrue
  | VFalse
  | VClos  of ident * expr * renv
  | VRclos of ident * ident * expr * renv
  | VSkip
  | VIdent of ident
and
  renv = (ident * valor) list 
  
type mem = (ident * valor) list
    
(* funções polimórficas para ambientes *)
let rec lookup a k =
  match a with
  | [] -> None
  | (y,i) :: tl -> if (y=k) then Some i else lookup tl k
       
let rec update a k i = 
  (match a with
   | [] -> 
       (k,i) :: a
   | (y,a) :: tl -> 
       if (y=k) then (k,i) :: tl
       else (y,a) :: (update tl k i)) 
  
let rec max_address a m =
  (match a with
   | [] -> m 
   | (y,a) :: tl -> 
       let v = int_of_string y in 
       max_address tl (max v m))
  
(* exceções que não devem ocorrer  *) 
exception BugParser 
exception BugTypeInfer
                       
(**+++++++++++++++++++++++++++++++++++++++++*)
(*         INFERÊNCIA DE TIPOS              *)
(*++++++++++++++++++++++++++++++++++++++++++*)
exception TypeError of string

let rec typeinfer (tenv:tenv) (e:expr) : tipo =
  match e with
  | Num _ -> TyInt
    
  | Var x ->
      (match lookup tenv x with
         Some t -> t
       | None -> raise (TypeError ("variavel nao declarada:" ^ x)))

  | True  -> TyBool
    
  | False -> TyBool
    
  | Binop(oper,e1,e2) ->
      let t1 = typeinfer tenv e1 in
      let t2 = typeinfer tenv e2 in
      if t1 = TyInt && t2 = TyInt then
        (match oper with
           Sum | Sub | Mult -> TyInt
         | Eq | Lt | Gt | Geq | Leq -> TyBool)
      else raise (TypeError "operando nao é do tipo int")

  | If(e1,e2,e3) ->
      (match typeinfer tenv e1 with
         TyBool ->
           let t2 = typeinfer tenv e2 in
           let t3 = typeinfer tenv e3
           in if t2 = t3 then t2
           else raise (TypeError "then/else com tipos diferentes")
       | _ -> raise (TypeError "condição de IF não é do tipo bool"))

  | Fn(x,t,e1) ->
      let t1 = typeinfer (update tenv x t) e1
      in TyFn(t,t1)

  | App(e1,e2) ->
      (match typeinfer tenv e1 with
         TyFn(t, t') ->  if (typeinfer tenv e2) = t then t'
           else raise (TypeError "tipo argumento errado" )
       | _ -> raise (TypeError "tipo função era esperado"))

  | Let(x,t,e1,e2) ->
      if (typeinfer tenv e1) = t then typeinfer (update tenv x t) e2
      else raise (TypeError "expr nao é do tipo declarado em Let" )

  | LetRec(f,(TyFn(t1,t2) as tf), Fn(x,tx,e1), e2) ->
      let tenv_com_tf = update tenv f tf in
      let tenv_com_tf_tx = update tenv_com_tf x tx in
      if (typeinfer tenv_com_tf_tx e1) = t2
      then typeinfer tenv_com_tf e2
      else raise (TypeError "tipo da funcao diferente do declarado")

  | LetRec _ -> raise BugParser

  | Skip -> TyUnit

  | Asg(e1,e2) ->
      let t1 = typeinfer tenv e1 in
      let t2 = typeinfer tenv e2 in
      (match t1 with
         TyRef(t) ->
           if t2 = t then TyUnit
           else raise (TypeError "ref e atribuicao de tipos diferentes")
       | _ -> raise (TypeError "era esperado um tipo ref"))

  | Dref(e1) ->
      let t1 = typeinfer tenv e1 in
      (match t1 with
         TyRef(t) -> t
       | _ -> raise (TypeError "era esperado um tipo ref"))

  | Whl(e1, e2) ->
      let t1 = typeinfer tenv e1 in
      let t2 = typeinfer tenv e2 in
      (match (t1,t2) with
         (TyBool, TyUnit) -> TyUnit
       | _ -> raise (TypeError "era esperado um tipo bool e um tipo unit"))

  | New(e1) -> TyRef(typeinfer tenv e1)

  | Seq(e1,e2) ->
      let t1 = typeinfer tenv e1 in
      let t2 = typeinfer tenv e2 in
      (match t1 with
         TyUnit -> t2
       | _     -> raise (TypeError "era esperado um tipo unit"))

(**+++++++++++++++++++++++++++++++++++++++++*)
(*                 AVALIADOR                *)
(*++++++++++++++++++++++++++++++++++++++++++*) 
let compute (oper: op) (v1: valor) (v2: valor) : valor =
  match (oper, v1, v2) with
  | (Sum, VNum(n1), VNum(n2)) -> VNum (n1 + n2)
  | (Sub, VNum(n1), VNum(n2)) -> VNum (n1 - n2)
  | (Mult, VNum(n1),VNum(n2)) -> VNum (n1 * n2)
  | (Eq, VNum(n1), VNum(n2))  -> if (n1 = n2)  then VTrue else VFalse
  | (Gt, VNum(n1), VNum(n2))  -> if (n1 > n2)  then VTrue else VFalse
  | (Lt, VNum(n1), VNum(n2))  -> if (n1 < n2)  then VTrue else VFalse
  | (Geq, VNum(n1), VNum(n2)) -> if (n1 >= n2) then VTrue else VFalse
  | (Leq, VNum(n1), VNum(n2)) -> if (n1 <= n2) then VTrue else VFalse
  | _ -> raise BugTypeInfer


let rec eval (renv:renv) (mem:mem) (e:expr) : (valor * mem) =
  match e with
  | Num n -> (VNum n, mem)

  | True -> (VTrue, mem)

  | False -> (VFalse, mem)

  | Var x ->
      (match lookup renv x with
         Some v -> (v, mem)
       | None -> raise BugTypeInfer)

  | Binop(oper,e1,e2) ->
      let (v1, mem) = eval renv mem e1 in
      let (v2, mem) = eval renv mem e2 in
      (compute oper v1 v2, mem)

  | If(e1,e2,e3) ->
      let (v1, mem) = eval renv mem e1 in
      (match v1 with
         VTrue  -> eval renv mem e2
       | VFalse -> eval renv mem e3
       | _ -> raise BugTypeInfer)

  | Fn (x,_,e1) ->  (VClos(x,e1,renv), mem)

  | App(e1,e2) ->
      let (v1, mem) = eval renv mem e1 in
      let (v2, mem) = eval renv mem e2 in
      (match v1 with
         VClos(x,ebdy,renv') ->
           let renv'' = update renv' x v2
           in eval renv'' mem ebdy

       | VRclos(f,x,ebdy,renv') ->
           let renv''  = update renv' x v2 in
           let renv''' = update renv'' f v1
           in eval renv''' mem ebdy
       | _ -> raise BugTypeInfer)

  | Let(x,_,e1,e2) ->
      let (v1, mem) = eval renv mem e1
      in eval (update renv x v1) mem e2

  | LetRec(f,TyFn(t1,t2),Fn(x,tx,e1), e2) when t1 = tx ->
      let renv'= update renv f (VRclos(f,x,e1,renv))
      in eval renv' mem e2

  | LetRec _ -> raise BugParser
                  
  | Skip -> (VSkip, mem)
                  
  | Asg(e1,e2) ->
      let (v1, mem) = eval renv mem e1 in 
      let (v2, mem) = eval renv mem e2 in
      (match v1 with 
         VIdent(t) -> 
           (match lookup mem t with
              Some a -> (VSkip, update mem t v2) 
            | None -> raise BugTypeInfer) 
       | _ -> raise BugTypeInfer)
      
  | Dref(e) -> 
      let (v, mem) = eval renv mem e in
      (match v with 
         VIdent(t) ->
           (match lookup mem t with
              Some a -> (a, mem)
            | None -> raise BugTypeInfer) 
       | _ -> raise BugTypeInfer) 
      
  | New(e) ->
      let (v, mem) = eval renv mem e in
      let i = sprintf "%d" ((max_address mem 0) + 1) in
      (VIdent(i), update mem i v)
      
  | Whl(e1, e2) ->  eval renv mem (If (e1, Seq(e2, Whl(e1, e2)), Skip)) 
                      
  | Seq(e1,e2) ->
      let (v1, mem) = eval renv mem e1 in
      (match v1 with
         VSkip -> eval renv mem e2
       | _ -> raise BugTypeInfer)
          
(* função auxiliar que converte tipo para string *)
let rec ttos (t:tipo) : string =
  match t with
  | TyInt  -> "int"
  | TyBool -> "bool"
  | TyFn(t1,t2)   ->  "("  ^ (ttos t1) ^ " --> " ^ (ttos t2) ^ ")"
  | TyRef(t) ->  "Ref("  ^ (ttos t) ^ ")"
  | TyUnit -> "unit"

(* função auxiliar que converte valor para string *)
let rec vtos (v: valor) : string =
  match v with
  | VNum n -> string_of_int n
  | VTrue -> "true"
  | VFalse -> "false"
  | VClos _ ->  "fn"
  | VRclos _ -> "fn"
  | VSkip -> "skip"
  | VIdent _ -> "ident"

(* principal do interpretador *)
let int_bse (e:expr) : unit =
  try
    let t = typeinfer [] e in
    let (v, mem) = eval [] [] e
    in  print_string ((vtos v) ^ " : " ^ (ttos t))
  with 
    TypeError msg ->  print_string ("erro de tipo - " ^ msg)
  (* as exceções abaixo nao podem ocorrer   *) 
  | BugTypeInfer  ->  print_string "corrigir bug em typeinfer"
  | BugParser     ->  print_string "corrigir bug no parser para let rec"

(* +++++++++++++++++++++++++++++++++++++++*)
(*                TESTES                  *)
(*++++++++++++++++++++++++++++++++++++++++*) 
(*  
    o programa abaixo retorna
        valor   = 7 
        memória = [(l1, 4)] 
    
    let x : int ref = new 3 in  -- x = end 1; 
    let y : int = !x in  --  y = 3
        (x := !x + 1);   -- 
        y + !x
*) 
let teste1 = Let("x", TyRef TyInt, New (Num 3),
                 Let("y", TyInt, Dref (Var "x"),
                     Seq(Asg(Var "x", Binop(Sum, Dref(Var "x"), Num 1)),
                         Binop(Sum, Var "y",  Dref (Var "x")))))
                                                                 
(*
        o programa abaixo retorna
        valor   = 1 
        memória = [(l1, 1)] 

     let x: int ref  = new 0 in
     let y: int ref  = x in
        x := 1;
        !y
*) 
let teste2 = Let("x", TyRef TyInt, New (Num 0),
                 Let("y", TyRef TyInt, Var "x",
                     Seq(Asg(Var "x", Num 1),
                         Dref (Var "y"))))
                                           
(*  
    o programa abaixo retorna
    valor   = 3
    memória = [(l1, 2)]
    

      let counter : int ref = new 0  in 
      let next_val : unit -> int =
         fn ():unit  =>
            counter := (!counter) + 1;
           !counter
      in  (next_val()  + next_val())  
*) 
let counter1 = Let("counter", TyRef TyInt, New (Num 0),
                   Let("next_val", TyFn(TyUnit, TyInt),
                       Fn("w", TyUnit,
                          Seq(Asg(Var "counter",Binop(Sum, Dref(Var "counter"), Num 1)),
                              Dref (Var "counter"))),
                       Binop(Sum, App (Var "next_val", Skip),
                             App (Var "next_val", Skip))))
  
(*   
     o programa abaixo retorna
     valor = 120
     memória = [(l2, 120), (l1,0) ]
     
let fat (x:int) : int = 

  let z : int ref = new x in
  let y : int ref = new 1 in 
  while (!z > 0) (
      y :=  !y * !z;
      z :=  !z - 1;
    );
    ! y
in
fat 5
       
       
       
  SEM açucar sintático
    
let fat : int-->int = fn x:int => 

                           let z : int ref = new x in
                           let y : int ref = new 1 in 
        
                           while (!z > 0) (
                               y :=  !y * !z;
                               z :=  !z - 1;
                             );
                             ! y
in
fat 5
*)
let whilefat = Whl(Binop(Gt, Dref (Var "z"), Num 0),
                   Seq( Asg(Var "y", Binop(Mult, Dref (Var "y"), Dref (Var "z"))),
                        Asg(Var "z", Binop(Sub, Dref (Var "z"), Num 1)))
                  )
                             
let bodyfat = Let("z", TyRef TyInt, New (Var "x"),
                  Let("y", TyRef TyInt, New (Num 1), Seq (whilefat, Dref (Var "y"))))
    
let impfat = Let("fat", TyFn(TyInt,TyInt), Fn("x", TyInt, bodyfat), App(Var "fat", Num 5))