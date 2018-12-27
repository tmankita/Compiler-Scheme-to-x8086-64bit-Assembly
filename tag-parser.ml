
(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "reader.ml";;


type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;



module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct


(* work on the tag parser starts here *)


let disj_expr nt1 nt2 =
  fun s ->
  try (nt1 s)
  with X_syntax_error -> (nt2 s);;

let nt_none _ = raise X_syntax_error;;
  
let disj_list_expr nts = List.fold_right disj_expr nts nt_none;;


  
let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

  

 let rec make_expr () =
   disj_list_expr [make_Const ; make_Variable; make_if; make_LambdaSimple; make_LambdaOpt; make_Or; make_Define ; make_Set; make_Seq;make_Applic ]
   
  and make_Const = 
    fun  sexpr->
    match sexpr with
    |Bool(c)-> Const(Sexpr(Bool(c)))
    |Char(c)-> Const(Sexpr(Char(c)))
    |Number(c)->Const(Sexpr(Number(c)))
    |String(c)->Const(Sexpr(String(c)))
    |Pair(Symbol("quote"),Pair(sexpr,Nil))->Const(Sexpr(sexpr))
    |Pair(Symbol("unquote"),Pair(sexpr,Nil))->Const(Sexpr(sexpr))
    |_->raise X_syntax_error


   and make_Variable = 
    fun sexpr->
    match sexpr with
    |Symbol(c)->if (ormap (fun s-> (compare s c)= 0) reserved_word_list) = false then Var(c) 
                  else raise X_syntax_error
    |_-> raise X_syntax_error
  
  and make_test = 
    fun sexpr->
    match sexpr with
    |Pair (test_,rest)-> (make_expr () test_),rest
    |_-> raise X_syntax_error

    and make_then = 
    fun sexpr->
    match sexpr with
    |Pair (then_,rest)-> (make_expr () then_),rest
    |_-> raise X_syntax_error


    and make_else = 
    fun sexpr->
    
    match sexpr with
    |Nil -> Const(Void),Nil
    |Pair (else_,Nil)-> (make_expr () else_),Nil
    |_-> raise X_syntax_error
     
  and  make_if =
    fun sexpr ->
    match sexpr with 
    | Pair(Symbol("if"),rest)->  let (test_,rest1) = make_test rest in 
                                let (then_,rest2)= make_then rest1  in
                                let (else_,rest3)= make_else rest2 in
                                If(test_,then_,else_)
    |_-> raise X_syntax_error

    and build_seq_list= 
    fun sexpr ->
    match sexpr with
    |Pair(sexpr,Nil)->[make_expr () sexpr]
    |Pair( a, b ) -> List.concat [[make_expr () a] ; build_seq_list b ] 
    |_-> raise X_syntax_error


    and make_Seq = 
    fun sexpr->
    match sexpr with
    |Pair(Symbol("begin"),Nil)-> Const(Void)
    |Pair(Symbol("begin"),Pair(sexpr,Nil))->make_expr () sexpr
    |Pair(Symbol("begin"),c) -> Seq(build_seq_list c)
    |_->raise X_syntax_error
  
   and make_params = 
   fun sexpr->
   match sexpr with
   |Nil->[]
   |Pair (Symbol(c),rest)-> (List.concat [[c];(make_params rest )]) 
   |_-> raise X_syntax_error

   and checkParamsSyntaxSimple=
   fun params->
   match params with
    | [] -> true
    | _ -> (not (List.exists (fun a-> String.equal a (List.nth params 0)) (List.tl params))) && (checkParamsSyntaxSimple (List.tl params))

    and buildLambdaSimple=
    fun (params,body)->
      let syntax= (checkParamsSyntaxSimple params) in
     match syntax with
     |true-> LambdaSimple(params,  body)
     |false-> raise X_syntax_error


    and make_LambdaSimple = 
    fun sexpr->
    match sexpr with 
    | Pair(Symbol("lambda"),Pair(params,Nil))-> raise X_syntax_error
    | Pair(Symbol("lambda"),Pair(params,Pair(body,Nil)))->  buildLambdaSimple (make_params params, make_expr () body)                                                                                                    
    | Pair(Symbol("lambda"),Pair(params,body))->  buildLambdaSimple( (make_params params),make_Seq (Pair(Symbol("begin"),body)))                                 
    |_-> raise X_syntax_error

  and make_params_opt=
  fun sexpr->
  match sexpr with
   |Pair(Symbol(c),Nil)-> [c],""
   |Pair (Symbol(c),Symbol(s))-> [c],s
   |Pair (Symbol(c),rest)-> let (params_list,opt)= make_params_opt rest in
                                (List.concat [[c]; params_list]) ,opt
   |_-> raise X_syntax_error

   and checkMixedParamsSyntax =
   fun (params, opt)->
      
     match params with
     |[]->true
     |_ -> let checkCorrect=  (andmap (fun s-> not((compare s opt)= 0)) params) in
             if checkCorrect then true else false
      

  

   and checkParamsSyntaxOpt=
   fun (params, opt)->
   let simple= (checkParamsSyntaxSimple params) in
   let mixed= (checkMixedParamsSyntax (params,opt)) in
   simple && mixed 

   and buildLambdaOpt=
   fun (params,opt,body)->
     let syntax= (checkParamsSyntaxOpt (params,opt)) in
     
    match syntax with
    |true-> LambdaOpt(params,opt,body)
    |false->raise X_syntax_error

    and make_LambdaOpt = 
    fun sexpr ->
    match sexpr with 
    | Pair(Symbol("lambda"),Pair(params,Nil))-> raise X_syntax_error
    | Pair(Symbol("lambda"),Pair (Symbol(param),Pair(Pair(body,Nil),Nil)))->  buildLambdaOpt ([],param,(make_expr () (Pair(body,Nil)))) 
    
    | Pair(Symbol("lambda"),Pair (Symbol(param),body))->  buildLambdaOpt ([],param,(make_Seq (Pair(Symbol("begin"),body)))) 
    | Pair(Symbol("lambda"),Pair (params,Pair(body,Nil)))-> let (params_,opt_params)= make_params_opt params in
                                                              buildLambdaOpt (params_,opt_params,(make_expr () body)) 
    | Pair(Symbol("lambda"),Pair (params,body))-> let (params_,opt_params)= make_params_opt params in
                                                    buildLambdaOpt(params_,opt_params, (make_Seq (Pair(Symbol("begin"),body))))
                                                      
    |_->raise X_syntax_error


  

    and make_list_sexprs_for_app = 
    fun sexpr_list ->
    match sexpr_list with
    |Nil->[]
    |Pair(sexpr,Nil) -> [make_expr () sexpr]
    |Pair(sexpr1,sexpr2)-> List.concat [[(make_expr () sexpr1)] ; (make_list_sexprs_for_app sexpr2)]
    |_-> raise X_syntax_error


    and make_Applic = 
    fun sexpr->
    match sexpr with
    |Pair(sexpr1,list_sexpr) ->let list_sexpr_ = make_list_sexprs_for_app list_sexpr in 
                                Applic(make_expr () sexpr1 ,list_sexpr_ )
    |_->raise X_syntax_error

    and make_Or = 
    fun sexpr->
    match sexpr with
    |Pair(Symbol("or"),Nil) -> Const (Sexpr (Bool false))
    |Pair(Symbol("or"),Pair(sexpr,Nil)) ->(make_expr () sexpr)
    |Pair(Symbol("or"),list_sexpr) ->let list_sexpr_ = make_list_sexprs_for_app list_sexpr in 
                                Or(list_sexpr_ )
    |_->raise X_syntax_error

    and make_Define = 
    fun sexpr->
    match sexpr with
    |Pair(Symbol("define"),Pair(var,Pair(sexp,Nil))) -> Def ((make_Variable var), make_expr () sexp)
    |_->raise X_syntax_error
    
    and make_Set = 
    fun sexpr->
    match sexpr with
    |Pair(Symbol("set!"),Pair(var,Pair(sexp,Nil))) -> Set ((make_Variable var), make_expr () sexp)
    |_->raise X_syntax_error;;
    


    let car_cond = 
      fun pair->
      match pair with
      |Pair(car,rest)-> car
      |_->  raise PC.X_no_match;;
  
      let cdr_cond = 
        fun pair->
        match pair with
        |Pair(_,cdr)-> cdr
        |_->raise PC.X_no_match;;



        let rec expand_cond_disj () =
            PC.disj_list [expand_Cond3 ;expand_Cond2; expand_Cond1]  
          
          
          and expand_Cond1 = 
          fun (car_sexpr, cdr_sexpr)->
          match car_sexpr,cdr_sexpr with 
          | Pair (_test, _seq), Nil -> Pair(Symbol("if"),Pair(_test,Pair(Pair(Symbol("begin"),_seq),Nil)))
          | Pair (_test, _seq), rest -> Pair(Symbol("if"),Pair(_test,Pair(Pair(Symbol("begin"),_seq),   Pair((expand_cond_disj () ((car_cond rest), (cdr_cond rest)) ),Nil)      )))
          | _,_->  raise PC.X_no_match
  
        and expand_Cond2 = 
          fun (car_sexpr ,cdr_sexpr)->
        match car_sexpr, cdr_sexpr with
        | Pair (_test, Pair (Symbol "=>",Pair (_sexprf, Nil))), Nil ->Pair (Symbol "let", Pair (Pair (Pair (Symbol "value", Pair (_test, Nil)), Pair (Pair (Symbol "f", Pair (Pair (Symbol "lambda", Pair (Nil, Pair (_sexprf, Nil))), Nil)), Nil)), Pair (Pair (Symbol "if", Pair (Symbol "value", Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)),Nil))), Nil)))
        | Pair (_test, Pair (Symbol "=>",Pair (_sexprf, Nil))), rest->
         Pair (Symbol "let", 
         Pair 
         (Pair  (Pair (Symbol "value", Pair (_test, Nil)),
          Pair (Pair (Symbol "f", Pair (Pair (Symbol "lambda", Pair (Nil, Pair (_sexprf, Nil))), Nil)),  Pair (Pair (Symbol "rest", Pair (Pair (Symbol "lambda", Pair (Nil, Pair ((expand_cond_disj () ((car_cond rest), (cdr_cond rest))  ), Nil))), Nil)), Nil))
          ),
           Pair (Pair (Symbol "if", Pair (Symbol "value", Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)), 
             Pair(Pair(Symbol "rest",Nil),Nil)    ))), Nil)))
        | _,_-> raise PC.X_no_match

        and expand_Cond3 = 
        fun (car_sexpr, cdr) ->
        match car_sexpr,cdr with
        |Pair(Symbol "else", _seq),Nil-> Pair(Symbol("begin"),_seq)
        |_,_->raise PC.X_no_match;;

   
  



    let rec macro_Expender () = 
      PC.disj_list [ expand_Quasiquoted; expand_mitDefine;expand_and ; make_let_rec ; expand_let_klini; expand_Cond ;expand_Let ;make_empty_case ] 

      and make_empty_case=
      fun sexpr->
      sexpr

      and expand_Quasiquoted = 
      fun sexpr->
      match sexpr with
      | Pair(Symbol("quasiquote"),Pair (Pair(Symbol("unquote"),Pair(sexpr,Nil)),Nil))-> sexpr
      | Pair(Symbol("quasiquote"), Pair (Pair (Symbol("unquote-splicing"),Pair(sexpr,Nil)),Nil))-> raise PC.X_no_match
      | Pair(Symbol("quasiquote"),Pair(Nil,Nil))-> Pair (Symbol("quote"),Pair(Nil,Nil))
      | Pair(Symbol("quasiquote"),Pair(Vector(sexpr_list),Nil))-> Pair(Symbol("vector"),(List.fold_right (fun sexpr1 sexpr2-> Pair(expand_Quasiquoted  (Pair(Symbol("quasiquote"),Pair(sexpr1,Nil))),sexpr2 )) sexpr_list Nil) )
      | Pair(Symbol("quasiquote"),Pair(Pair(Pair(Symbol("unquote-splicing"),sexprA),sexprB),Nil))->  Pair(Symbol("append"),Pair( expand_Quasiquoted (Pair(Symbol("quasiquote"),Pair (Pair(Symbol("unquote"),sexprA),Nil))) , Pair (expand_Quasiquoted (Pair(Symbol("quasiquote"),Pair(sexprB,Nil))),Nil) ))
      | Pair(Symbol("quasiquote"), Pair(Pair(sexprA,Pair(Symbol("unquote-splicing"),sexprB)),Nil)) -> Pair(Symbol("cons"),Pair (expand_Quasiquoted (Pair(Symbol("quasiquote"),Pair(sexprA,Nil))),sexprB))
      | Pair(Symbol("quasiquote"),Pair(Pair(sexprA,sexprB),Nil)) ->Pair(Symbol "cons",Pair(expand_Quasiquoted (Pair(Symbol("quasiquote"),Pair(sexprA,Nil))) ,  Pair(expand_Quasiquoted  (Pair(Symbol("quasiquote"),Pair(sexprB,Nil)))  ,Nil)))
      | Pair(Symbol("quasiquote"),Pair(sexpr,Nil))->Pair (Symbol("quote"),Pair(sexpr,Nil))
      | _-> raise PC.X_no_match  
  
      and expand_Cond = 
      fun sexpr->
      match sexpr with
      |Pair (Symbol "cond", Pair(Pair(Symbol "else",list_of_conds),Nil))-> (expand_cond_disj () ((car_cond (Pair(Pair(Symbol "else",list_of_conds),Nil))), (cdr_cond (Pair(Pair(Symbol "else",list_of_conds),Nil)))))
      |Pair (Symbol "cond", Pair(Pair(Symbol "else",list_of_conds),_))-> raise PC.X_no_match

      |Pair (Symbol "cond", list_of_conds)-> (expand_cond_disj () ((car_cond list_of_conds), (cdr_cond list_of_conds)))
      |_-> raise PC.X_no_match

      and build_list_vars =
      fun sexpr->
      match sexpr with 
      |Pair(Pair(Symbol(c),_ ) ,Nil) -> Pair(Symbol(c),Nil)
      | Pair(Pair(Symbol(c),_ ) ,rest) -> Pair(Symbol(c),build_list_vars rest)
      |_->raise PC.X_no_match

      and build_list_values =
      fun sexpr->
      match sexpr with 
      | Pair(Pair( _ ,Pair(v,Nil) ) ,Nil) ->  Pair(v,Nil)
      | Pair(Pair(_,Pair(v,Nil) ) ,rest) -> Pair(v,build_list_values rest)
      |_->  raise PC.X_no_match
 
      and expand_Let = 
      fun sexpr->
      match sexpr with

      |Pair (Symbol "let", Pair (Nil,Pair(_body,Nil)))-> Pair (Pair(Symbol "lambda", Pair(Nil,Pair(_body,Nil))),Nil)
      |Pair (Symbol "let", Pair (Pair (_arg, _args),Pair(_body,Nil))) -> let vars = build_list_vars (Pair(_arg,_args)) in
                                                                let values= build_list_values (Pair(_arg,_args)) in
                                                              Pair (Pair(Symbol "lambda", Pair(vars,Pair(_body,Nil))),values) 
      |Pair (Symbol "let", Pair (Nil,_body))->Pair (Pair(Symbol "lambda", Pair(Nil,_body)),Nil)
      |Pair (Symbol "let", Pair (Pair (_arg, _args),_body))-> let vars = build_list_vars (Pair(_arg,_args)) in
                                                              let values= build_list_values (Pair(_arg,_args)) in
                                                               Pair (Pair(Symbol "lambda", Pair(vars,_body)),values)
      |Pair (Symbol "let", Pair (Symbol(var),Pair(val1,_body)))-> Pair (Pair(Symbol "lambda", Pair(Symbol(var),_body)),val1)
      |_-> raise PC.X_no_match

      and make_let =
       fun (args,body)->
       match args with
      | Nil -> body
      | Pair(car,cdr) -> Pair(Pair (Symbol "let", Pair (Pair (car, Nil),make_let (cdr,body))),Nil)
      | _ ->raise PC.X_no_match





        and generate_Emptylet =
      fun body->
      Pair (Symbol "let", Pair (Nil, Pair (body, Nil)))

      and generate_whatever =
      fun sexpr ->
      match sexpr with
      |Pair(Symbol(c) ,Nil) ->Pair(Pair(Symbol(c),Pair( Pair (Symbol("quote"),Pair(Symbol("whatever"),Nil)),Nil )),Nil)
      | Pair(Symbol(c),rest) -> Pair(Pair(Symbol(c),Pair( Pair (Symbol("quote"),Pair(Symbol("whatever"),Nil)),Nil)),generate_whatever rest)
      |_->raise PC.X_no_match

      and generate_setBang=
      fun (var,values,body) ->
      match var, values with 
      |Pair(Symbol(c),Nil), Pair(_sexpr,Nil) -> Pair(Pair (Symbol "set!", Pair (Symbol c, Pair (_sexpr, Nil))),(body))
      |Pair(Symbol(c),restVars), Pair(_sexpr,restValues) ->Pair(Pair (Symbol "set!", Pair (Symbol c, Pair (_sexpr, Nil))) , (generate_setBang(restVars,restValues,body)) )
      |_->raise PC.X_no_match


      and get1_pair=
      fun pair->
      match pair with
      |Pair(a,b)-> a
      |_-> raise PC.X_no_match
      and get2_pair=
      fun pair->
      match pair with
      |Pair(a,b)-> b
      |_-> raise PC.X_no_match

      and build_setList=
      fun setSexpr->
      match setSexpr with
      |Nil->Nil
      |Pair(s,Pair(e1,rest))->Pair(get1_pair s,build_setList rest )
      |_->raise PC.X_no_match

      and make_let_rec= 
      fun sexpr->
      match sexpr with
      | Pair (Symbol "letrec", Pair (Nil,_body))-> Pair (Pair(Symbol "lambda", Pair(Nil,_body)),Nil)
      | Pair (Symbol "letrec", Pair (Pair (_arg, _args),_body)) ->let vars = build_list_vars (Pair(_arg,_args)) in
                                                                                let values= build_list_values (Pair(_arg,_args)) in
                                                                                Pair(Symbol "let", Pair((generate_whatever vars),(generate_setBang (vars, values,_body))))
      |_-> raise PC.X_no_match
      
      and expand_let_klini = 
      fun sexpr->
      match sexpr with
      |Pair (Symbol "let*", Pair (Pair (_arg, Nil),_body)) -> Pair (Symbol "let", Pair (Pair (_arg, Nil),make_let (Nil,_body)))
      |Pair (Symbol "let*", Pair (Pair (_arg, _args),_body)) -> Pair (Symbol "let", Pair (Pair (_arg, Nil),make_let (_args,_body)))
      
      |Pair (Symbol "let*", Pair (Nil,Nil)) -> raise PC.X_no_match
      |Pair (Symbol "let*", Pair (Nil,_body)) -> Pair (Symbol "let", Pair (Nil,_body))
     
                                        
      |_-> raise PC.X_no_match



      and expand_and=
      fun sexpr->
      match sexpr with
      |Pair(Symbol "and",Nil)->Bool(true)
      |Pair(Symbol "and",Pair(s1,Nil))->s1
      |Pair (Symbol "and", Pair (_x1, _rest))->Pair (Symbol "if", Pair (_x1, Pair (expand_and (Pair(Symbol("and"),_rest)), Pair (Bool(false), Nil))))
      |_-> raise PC.X_no_match

      and expand_mitDefine= 
      fun sexpr->
      match sexpr with 
      |Pair (Symbol "define", Pair (Pair (_var, _argList), _sexprPlus))->Pair (Symbol "define", Pair (_var, Pair (Pair (Symbol "lambda", Pair (_argList, _sexprPlus)), Nil)))
      |_->raise PC.X_no_match;;
 

        
        let rec nt_expand = 
          fun sexpr->
        match sexpr with
        |Nil->Nil
        |Pair(Symbol("quote"),_)->sexpr
        |Pair(car,Nil)-> macro_Expender ()(Pair((macro_Expender () (nt_expand car)),Nil))
        |Pair(car,cdr)-> macro_Expender ()(Pair((macro_Expender () (nt_expand car)) , (macro_Expender () (nt_expand cdr))))
        |c -> c;;
        
        let final_expander  =
          fun sexpr->
          (nt_expand (macro_Expender () sexpr));;

    

let tag_parse_expression sexpr =
  let expand_sexpr= (final_expander sexpr) in
  make_expr () expand_sexpr;;



let tag_parse_expressions sexpr = List.map (tag_parse_expression) sexpr;;

  
end;; (* struct Tag_Parser *)
