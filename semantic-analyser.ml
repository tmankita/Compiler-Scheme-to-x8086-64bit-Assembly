


(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

  let rec expr'_eq e1 e2 =
    match e1, e2 with
    | Const' Void, Const' Void -> true
    | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
    | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
    | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
    | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
    | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                              (expr'_eq th1 th2) &&
                                                (expr'_eq el1 el2)
    | (Seq'(l1), Seq'(l2)
    | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
    | (Set'(var1, val1), Set'(var2, val2)
    | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                               (expr'_eq val1 val2)
    | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
    | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
       (String.equal var1 var2) &&
         (List.for_all2 String.equal vars1 vars2) &&
           (expr'_eq body1 body2)
    | Applic'(e1, args1), Applic'(e2, args2)
    | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
     (expr'_eq e1 e2) &&
       (List.for_all2 expr'_eq args1 args2)
    | Box'(_), Box'(_) -> true
    | BoxGet'(_), BoxGet'(_) -> true
    | BoxSet'(_, v1), BoxSet'(_, v2) -> expr'_eq v1 v2 
    | _ -> false;;
   
 

 (* struct Semantics *)



 exception Semantic_Error ;;
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct
 
    
 
  let rec existP=
    fun (params,c,index)->
     if((List.length params) = 0)
      then (-1) 
        else(if ((List.length params) = index) 
              then (-1)
                else(if (String.equal (List.nth params index) c ) 
                  then (index) 
                    else (existP ( params,c,(index+1) ) ) ));;
  let rec existB=
    fun (params,c,(major,minor))->
    if((List.length params) = 0)
    then (-1,-1) 
    else  (let i = existP ((List.nth params 0), c,0) in 
            if ( i!= (-1) ) 
              then (major,i) 
                else (existB ((List.tl params),c,(major+1,0)) )  )
                  
                  
  
  let make_pvar_bvar_fvar =
    fun (params,rest)->
    match rest with
    |Var(c)-> let i = existP((List.hd params),c,0) in
                        if (i!=(-1)) 
                          then (Var'(VarParam(c,i))) 
                            else (let (major,minor)= (existB ((List.tl params),c,(0,0))) in
                                  if (major!= (-1)) 
                                    then (Var'(VarBound(c,major,minor))) 
                                      else (Var'(VarFree(c))))
   |_-> raise Semantic_Error;;

let rec make_lamda_body = 
  fun (params,body)->
  match body with 
  |Const(c)->Const'(c)
  |Var(c)->  (make_pvar_bvar_fvar (params,body))
  |If(test_,then_,else_)-> If'((make_lamda_body (params,test_)),(make_lamda_body (params,then_)),(make_lamda_body (params,else_)))
  |Seq(exprList) -> Seq'(List.map make_lamda_body (List.map (fun s->(params,s)) exprList))
  |Set(a,b)-> Set'((make_lamda_body (params,a)),(make_lamda_body (params,b)))
  |Def(a,b) ->Def'(( make_lamda_body(params,a)),(make_lamda_body (params,b)))
  |Or(exprList) ->Or'(List.map make_lamda_body (List.map (fun s->(params,s)) exprList))
  |Applic(exp,exprList) -> Applic' ((make_lamda_body (params,exp)),(List.map make_lamda_body (List.map (fun s->(params,s)) exprList)))
  |LambdaSimple (params1,body)-> LambdaSimple'(params1,make_lamda_body((List.append [params1] params),body))
  |LambdaOpt(params1,opt,body)->LambdaOpt'(params1,opt,make_lamda_body((List.append [(List.append params1 [opt])] params),body));;
  

  let rec make_expr'  =
    fun expr->
    match expr with 
    |Const(c)->Const'(c)
    |Var(c)->Var'(VarFree(c))
    |If(test_,then_,else_)-> If'((make_expr' test_),(make_expr' then_),(make_expr' else_))
    |Seq(exprList) -> Seq'(List.map make_expr' exprList)
    |Set(a,b)-> Set'((make_expr' a),(make_expr' b))
    |Def(a,b) ->Def'((make_expr' a),(make_expr' b))
    |Or(exprList) ->Or'(List.map make_expr' exprList)
    |Applic(exp,exprList) -> Applic' ((make_expr' exp),(List.map make_expr' exprList))
    |LambdaSimple (params,body)->LambdaSimple'(params,make_lamda_body([params],body))
    |LambdaOpt(params,opt,body)->LambdaOpt'(params,opt,make_lamda_body([(List.append params [opt])],body));;





    let rec make_tail_call= 
      fun exprTag->
       match exprTag with
       |LambdaSimple'(params,body)-> make_tail exprTag
       |LambdaOpt'(params,opt,body)-> make_tail exprTag
       |If'(test_,_then,_else)->If'(make_tail_call test_, make_tail_call _then, make_tail_call _else)
       |Seq'(exprList)-> Seq'(List.map (fun e-> make_tail_call e) exprList )
       |Or'(exprList)-> Or'(List.map (fun e-> make_tail_call e) exprList) 
       |Set'(a,b)-> Set'(a , make_tail_call b) 
       |Applic'(a,listb)-> Applic'(make_tail_call a,(List.map (fun s->make_tail_call s ) listb)) 
       |Def'(a,b)->Def'(a,make_tail_call b)         
       |_-> exprTag


      and make_tail =
      fun expr'->
      match expr' with
      |LambdaSimple'(params,Applic'(e,eList))-> LambdaSimple'(params,ApplicTP'((make_tail_call_inside_applicTP e),(List.map make_tail_call_inside_applicTP eList)))
      |LambdaOpt'(params,opt,Applic'(e,eList))-> LambdaOpt'(params,opt,ApplicTP'((make_tail_call_inside_applicTP e),(List.map make_tail_call_inside_applicTP eList)))
      |LambdaSimple'(params,body)-> LambdaSimple'(params,make_tail body)
      |LambdaOpt'(params,opt,body)-> LambdaOpt'(params,opt,make_tail body)
      |If'(test_,Applic'(e1,eList1),Applic'(e2,eList2))->If'(test_,ApplicTP'((make_tail_call_inside_applicTP e1),(List.map make_tail_call_inside_applicTP eList1)),ApplicTP'((make_tail_call_inside_applicTP e2),(List.map make_tail_call_inside_applicTP eList2)))
      |If'(test_,_then,Applic'(e2,eList2))->If'(test_,(make_tail _then),ApplicTP'((make_tail_call_inside_applicTP e2),(List.map make_tail_call_inside_applicTP eList2)))
      |If'(test_,Applic'(e1,eList1),_else)->If'(test_,ApplicTP'((make_tail_call_inside_applicTP e1),(List.map make_tail_call_inside_applicTP eList1)),make_tail _else)
      |If'(test_,_then,_else)->If'(test_, (make_tail _then),(make_tail _else))
      |Seq'(exprList)-> let last= (List.nth exprList ((List.length exprList)-1)) in( make_tail_seq (last, exprList))
      |Or'(exprList)-> let last= (List.nth exprList ((List.length exprList)-1)) in (make_tail_or (last,(exprList))) 
      |Set'(a,b)-> Set'(a , make_tail b) 
      |Applic'(a,listb)-> Applic'(make_tail a,(List.map (fun s->make_tail s ) listb)) 
      |Def'(a,b)->Def'(a,make_tail b)         
      |_-> expr'
      and make_tail_seq =
        fun (last,exprList)->
        match last with
        |Applic'(e,el)->Seq'((List.append (List.map ((fun c-> make_tail c)) (List.rev (List.tl (List.rev (exprList) )))) ([ApplicTP'((make_tail_call_inside_applicTP e),(List.map make_tail_call_inside_applicTP el))]) ))
        |_->Seq'(List.map make_tail exprList)
  
      and make_tail_or =
        fun (last,exprList)->
        match last with
        |Applic'(e,el)->Or'((List.append (List.map ((fun c-> make_tail c)) (List.rev (List.tl (List.rev (exprList) )))) ([ApplicTP'((make_tail_call_inside_applicTP e),(List.map make_tail_call_inside_applicTP el))]) ))
        |_->Or'(List.map make_tail exprList)

     and  make_tail_call_inside_applicTP =
      fun exprTag->
      match exprTag with
        |LambdaSimple'(params,bo)->make_tail exprTag
        |LambdaOpt'(params,opt,bo)->make_tail exprTag
        |_->exprTag;;
     


 let rec make_list_of_lambdas = 
  fun (expr',paramName)->
  match expr' with
  |LambdaSimple'(params,body)-> if((List.length (List.filter (fun p-> String.equal p paramName) params) != 0 )) then ([]) else  ( [expr']) (*(List.concat [[expr']; (make_list_of_lambdas (body,paramName)) ])*)
  |LambdaOpt' (params,opt,body)-> if((List.length (List.filter (fun p-> String.equal p paramName) params) != 0 )) then ([]) else  ( [expr']) (*(List.concat [[expr']; (make_list_of_lambdas (body,paramName)) ])*)
  |Seq'(exprList)-> (List.flatten (List.map  make_list_of_lambdas (List.map (fun expr->(expr,paramName)) exprList) ))
  |If'(_test,_then,_else)-> (List.flatten (List.map  make_list_of_lambdas (List.map (fun expr->(expr,paramName)) [_test;_then;_else]) ))
  | Set'(_,b)-> make_list_of_lambdas (b,paramName)
  | Def'(_,b)-> make_list_of_lambdas (b,paramName)
  | Or' (exprList)-> (List.flatten (List.map  make_list_of_lambdas (List.map (fun expr->(expr,paramName)) exprList) ))
  | Applic'(expr,exprList)-> (List.flatten (List.map  make_list_of_lambdas (List.map (fun expr->(expr,paramName)) (List.concat [[expr];exprList]) )))
  | ApplicTP' (expr,exprList)-> (List.flatten (List.map  make_list_of_lambdas (List.map (fun expr->(expr,paramName)) (List.concat [[expr];exprList]) )))
  |_->[];;

  let rec hasGetter = 
  fun (expr',paramName)->
  match expr' with 
  |Var'(VarBound(c,_,_))->  String.equal paramName c 
  |LambdaSimple'(params,body)-> if((List.length (List.filter (fun p-> String.equal p paramName) params) != 0 )) then false else (hasGetter (body,paramName))
  |LambdaOpt'(params,opt,body)->if((List.length (List.filter (fun p-> String.equal p paramName) params) != 0 )) then false else (hasGetter (body,paramName))
  |Seq'(exprList)->(ormap (fun expr-> hasGetter (expr,paramName)) exprList)
  |If'(_test,_then,_else)-> (ormap (fun expr-> hasGetter (expr,paramName)) [_test;_then;_else])
  |Set'(_,b)-> (hasGetter (b,paramName))
  |Def'(_,b)-> (hasGetter (b,paramName))
  |Or' (exprList)-> (ormap (fun expr-> hasGetter (expr,paramName)) exprList)
  |Applic'(expr,exprList)-> (ormap (fun expr-> hasGetter (expr,paramName)) (List.concat [[expr];exprList]))
  |ApplicTP' (expr,exprList)-> (ormap (fun expr-> hasGetter (expr,paramName)) (List.concat [[expr];exprList]))
  |_->false;;


  let print_toupleBol =
    fun (p,b)->
    print_string(" (");print_string(p);print_string(") ");
    match b with 
    | true ->print_string("t, ")
    | false-> print_string("f, ");;


  let rec make_lambdas_list_of_getters =
    fun (lambdasList , paramName) ->
    match lambdasList with
    |[]->[]
    |car::cdr-> if (hasGetter (car,paramName)) then (List.concat [[car]; make_lambdas_list_of_getters (cdr,paramName)]) else  (make_lambdas_list_of_getters (cdr,paramName));;



    let rec hasSetter = 
    fun (expr',paramName)->
    match expr' with 
    |Set'(Var'(VarBound(c,_,_)),b)-> if (String.equal paramName c) then true else (hasSetter (b,paramName))
    |LambdaSimple'(params,body)->if((List.length (List.filter (fun p-> String.equal p paramName) params) != 0 )) then false else (hasSetter (body,paramName))
    |LambdaOpt'(params,opt,body)->if((List.length (List.filter (fun p-> String.equal p paramName) (List.concat [[opt];params])) != 0 )) then false else (hasSetter (body,paramName))
    |Seq'(exprList)->(ormap (fun expr-> hasSetter (expr,paramName)) exprList)
    |If'(_test,_then,_else)-> (ormap (fun expr-> hasSetter (expr,paramName)) [_test;_then;_else])
    |Def'(_,b)-> (hasSetter (b,paramName))
    |Or' (exprList)-> (ormap (fun expr-> hasSetter (expr,paramName)) exprList)
    |Applic'(expr,exprList)-> (ormap (fun expr-> hasSetter (expr,paramName)) (List.concat [[expr];exprList])) 
    |ApplicTP' (expr,exprList)-> (ormap (fun expr-> hasSetter (expr,paramName)) (List.concat [[expr];exprList]))
    |_->false;;

    let rec make_lambdas_list_of_setters =
      fun (lambdasList , paramName) ->
      match lambdasList with
      |[]->[]
      |car::cdr-> if (hasSetter (car,paramName)) then (List.concat [[car]; make_lambdas_list_of_setters (cdr,paramName)]) else  (make_lambdas_list_of_setters (cdr,paramName));;
  
      

      let rec atLeastOneDiffrentInList =
        fun (list1,var)->
        match list1 with
        |[]-> false
        |car::cdr-> if (try (expr'_eq car var) with Invalid_argument _ ->false) then (atLeastOneDiffrentInList (cdr,var) )  else true;;

      let exsitDiffrent =
        fun (list1,list2)->
        (List.length (List.filter (fun a-> (atLeastOneDiffrentInList(list2,a))) list1)) != 0;;

        let rec makeListBoundByParam=
          fun (expr',p)->
          match expr' with
          |Var'(VarBound(c,mj,_))-> if(String.equal p c) then [mj] else []
          |Set'(a,b)-> (List.concat [(makeListBoundByParam(a,p));(makeListBoundByParam(b,p))])
          |Seq'(exprList)->(List.flatten (List.map (fun e->( makeListBoundByParam(e,p))) exprList))
          |If'(_test,_then,_else)-> (List.flatten (List.map (fun e->( makeListBoundByParam(e,p))) [_test;_then;_else]))
          |Def'(_,b)-> makeListBoundByParam (b,p)
          |Or' (exprList)-> (List.flatten (List.map (fun e->( makeListBoundByParam(e,p))) exprList))
          |Applic'(expr,exprList)->  (List.flatten (List.map (fun e->( makeListBoundByParam(e,p))) (List.concat [[expr];exprList])))
          |ApplicTP' (expr,exprList)-> (List.flatten (List.map (fun e->( makeListBoundByParam(e,p))) (List.concat [[expr];exprList])))
          |_->[];;

          let rec makeListVarParam_GetByParam=
            fun (expr',p)->
            match expr' with
            |Var'(VarParam(c,index))->  if(String.equal p c) then [c] else []
            |Set'(_,b)-> (makeListVarParam_GetByParam(b,p))
            |Seq'(exprList)-> (List.flatten (List.map (fun e->( makeListVarParam_GetByParam(e,p))) exprList))
            |If'(_test,_then,_else)-> (List.flatten (List.map (fun e->( makeListVarParam_GetByParam(e,p))) [_test;_then;_else]))
            |Def'(_,b)-> makeListVarParam_GetByParam (b,p)
            |Or' (exprList)-> (List.flatten (List.map (fun e->( makeListVarParam_GetByParam(e,p))) exprList))
            |Applic'(expr,exprList)->  (List.flatten (List.map (fun e->( makeListVarParam_GetByParam(e,p))) (List.concat [[expr];exprList])))
            |ApplicTP' (expr,exprList)-> (List.flatten (List.map (fun e->( makeListVarParam_GetByParam(e,p))) (List.concat [[expr];exprList])))
            |_->[];;

            let rec makeListVarParam_SetByParam=
              fun (expr',p)->
              match expr' with
              |Set'(Var'(VarParam(c,index)),b)-> if (String.equal p c) then [c] else (makeListVarParam_SetByParam(b,p))
              |Seq'(exprList)-> (List.flatten (List.map (fun e->( makeListVarParam_SetByParam(e,p))) exprList))
              |If'(_test,_then,_else)-> (List.flatten (List.map (fun e->( makeListVarParam_SetByParam(e,p))) [_test;_then;_else]))
              |Def'(_,b)-> makeListVarParam_SetByParam (b,p)
              |Or' (exprList)-> (List.flatten (List.map (fun e->( makeListVarParam_SetByParam(e,p))) exprList))
              |Applic'(expr,exprList)->  (List.flatten (List.map (fun e->( makeListVarParam_SetByParam(e,p))) (List.concat [[expr];exprList])))
              |ApplicTP' (expr,exprList)-> (List.flatten (List.map (fun e->( makeListVarParam_SetByParam(e,p))) (List.concat [[expr];exprList])))
              |_->[];;
  

  let rec make_intersection= 
    fun (list1,list2)->
    match list1,list2 with
    |[],[]-> []
    |_,[] -> raise X_this_should_not_happen
    |[],_ -> raise X_this_should_not_happen
    |car1::cdr1, car2::cdr2 -> if(String.equal car1 car2) 
                                then (List.concat [[car1]; (make_intersection (cdr1,cdr2))]) 
                                  else (List.concat [[""]; (make_intersection (cdr1,cdr2))]);;

  let rec make_union= 
    fun (list1,list2)->
    match list1,list2 with
    |[],[]-> []
    |_,[] -> raise X_this_should_not_happen
    |[],_ -> raise X_this_should_not_happen
    |car1::cdr1, car2::cdr2 -> if(String.equal car1 car2) 
                                then (List.concat [[car1]; (make_union (cdr1,cdr2))]) 
                                  else (if (String.equal car1 "") 
                                         then  List.concat [[car2]; (make_union (cdr1,cdr2))] 
                                          else List.concat [[car1]; (make_union (cdr1,cdr2))]);;

  let rec make_list_of_sets = 
    fun (needToBox,index)->
      match needToBox with
      |[]-> []
      |car::cdr-> if(not(String.equal car "")) then  ((List.concat [[ Set'(Var'(VarParam(car,index)),Box'(VarParam(car,index))) ]; make_list_of_sets (cdr,index+1)]))  else  make_list_of_sets(cdr,index+1) ;;

  let rec update_getter_and_setters =
    fun (expr',paramName)->
    match expr' with
    |Var'(VarBound(c,mj,mi))-> if(String.equal c paramName) then (BoxGet'(VarBound(c,mj,mi))) else expr'
    |Var'(VarParam(c,index))-> if(String.equal c paramName) then (BoxGet'(VarParam(c,index))) else expr'
    |Set'(Var'(VarBound(c,mj,mi)),expr)->  if(String.equal c paramName) then (BoxSet'(VarBound(c,mj,mi), update_getter_and_setters(expr,paramName))) else Set'(Var'(VarBound(c,mj,mi)),update_getter_and_setters(expr,paramName))
    |Set'(Var'(VarParam(c,index)) ,expr)->   if(String.equal c paramName) then (BoxSet'((VarParam(c,index)),update_getter_and_setters(expr,paramName))) else Set'(Var'(VarParam(c,index)) ,update_getter_and_setters(expr,paramName))
    |Set'(Var'(VarFree(c)) ,expr)-> Set'(Var'(VarFree(c)) ,update_getter_and_setters(expr,paramName))
    |LambdaSimple'(params,body)->if((List.length (List.filter (fun p-> String.equal p paramName) params) != 0 )) then expr' else LambdaSimple'(params,update_getter_and_setters(body,paramName))  
    |LambdaOpt'(params,opt,body)->if((List.length (List.filter (fun p-> String.equal p paramName) (List.concat [[opt];params])) != 0 )) then expr' else LambdaOpt'(params,opt,update_getter_and_setters(body,paramName))
    |Seq'(exprList)-> Seq'(List.map (fun expr->update_getter_and_setters(expr,paramName)) exprList)
    |If'(_test,_then,_else)-> If'(update_getter_and_setters(_test,paramName),update_getter_and_setters(_then,paramName),update_getter_and_setters(_else,paramName))
    |Def'(a,b)-> Def'(update_getter_and_setters(a,paramName),update_getter_and_setters(a,paramName))
    |Or' (exprList)->  Or'(List.map (fun expr->update_getter_and_setters(expr,paramName)) exprList)
    |Applic'(expr,exprList)->  Applic'(update_getter_and_setters(expr,paramName),(List.map (fun expr->update_getter_and_setters(expr,paramName)) exprList))
    |ApplicTP' (expr,exprList)-> ApplicTP'(update_getter_and_setters(expr,paramName),(List.map (fun expr->update_getter_and_setters(expr,paramName)) exprList))
    |BoxSet'(a,b)-> BoxSet'(a,update_getter_and_setters (b,paramName))
    |_->expr';;
(*G for getter and S for setter*)
    let rec update_GAS_list_of_param =
      fun (expr',paramList)->
      match paramList with
      |[]->expr'
      |car::cdr-> update_GAS_list_of_param( update_getter_and_setters(expr',car),cdr );;
(*P for param and B for bound*)
      let rec make_list_PAB_need_to_box=
        fun (varParamList,varBoundList)->
        match varParamList,varBoundList with
        |[],[]->[]
        |[],_->[]
        |_,[]->[]
        |car1::cdr1,car2::cdr2-> match car1,car2 with |(p,listP),(_,listB)-> if((List.length listP)>0 && (List.length listB)>0) then (List.concat [[p]; make_list_PAB_need_to_box(cdr1,cdr2)]) else [""];;
    
        let rec print_stringList =
      fun l->
      match l with 
      | [] ->print_string("]")
      | car::cdr->print_string(car);print_string(", "); print_stringList cdr;;
      let rec print_intList =
        fun l->
        match l with 
        | [] ->print_string("]\n")
        | car::cdr->print_int(car);print_string(", "); print_intList cdr;;

      let rec print_toupleintList =
        fun (p,l)->
        print_string(" (");print_string(p);print_string(") ");
        match l with 
        | [] ->print_string("]\n")
        | car::cdr->print_int car; print_toupleintList (p,cdr);;

       

          let rec print_ListToupleBolList = 
            fun listT->
            print_string(" [");
            match listT with
            |[]->print_string("]\n")
            |car::cdr-> print_toupleBol car; print_ListToupleBolList cdr;;

      let rec make_list_of_params = 
        fun (list1,list2)->
        match list1,list2 with
        |[],[]->[]
        |[],l2->l2
        |l1,[]->l1
        |car1::cdr1,car2::cdr2-> if(String.equal car1 "") then (List.concat [[car2];(make_list_of_params(cdr1,cdr2))]) else (List.concat [[car1];(make_list_of_params(cdr1,cdr2))]);;



let check_if_equal =
  fun (l1,l2)->
  if(try ((expr'_eq l1 l2)) with Invalid_argument _ -> false) then true else false;;

let rec make_list_of_the_same_lambdas=
  fun (lambda_list) ->
  match lambda_list with
  |[]->[]
  |car::cdr-> (List.flatten(List.map (fun l-> if (check_if_equal (l,car))  then (List.concat [[car];(make_list_of_the_same_lambdas cdr)])  else (make_list_of_the_same_lambdas cdr) ) cdr));;
  
  let print_ListTouplesStringAndStringlList = 
    fun (s,sL)->
    print_string("(");print_string s;print_string("[");print_stringList sL;print_string(")");;
    

  let rec print_toupleListOfStringAndStringList =
    fun toupleList->
    match toupleList with
    |[]->print_string "]\n"
    |car::cdr-> print_ListTouplesStringAndStringlList car; print_toupleListOfStringAndStringList cdr ;;

  let rec make_box=
    fun expr'->
    match expr' with
    |LambdaSimple'(params,body)-> let listOfLambdaListByParam = (List.map (fun p-> (p,make_list_of_lambdas (body,p)) ) params ) in
                                  let list_Of_paris_Of_Getters_And_Setters_By_Param = (List.map   (fun (p,listByParam)-> (p,make_lambdas_list_of_getters (listByParam,p),(make_lambdas_list_of_setters(listByParam,p))))   listOfLambdaListByParam) in
                                  let list_Of_paris_Of_Setters_By_Param = (List.map   (fun (p,listByParam)-> (p,(make_lambdas_list_of_setters(listByParam,p))))   listOfLambdaListByParam) in
                                  let list_of_params_that_have_setters = (List.map (fun (p,setList)->if((List.length setList)!=0)then p else "") list_Of_paris_Of_Setters_By_Param) in
                                  let list_Of_paris_Of_Getters_By_Param=(List.map   (fun (p,listByParam)-> (p,(make_lambdas_list_of_getters(listByParam,p))))   listOfLambdaListByParam) in
                                  let list_of_params_that_have_getter = (List.map (fun (p,getList)->if((List.length getList)!=0)then p else "") list_Of_paris_Of_Getters_By_Param) in
                                  let list_of_same_lambdas_by_param=(List.map (fun (p,listLambdas)->(p,make_list_of_the_same_lambdas listLambdas)) listOfLambdaListByParam) in
                                  let raise_suspicious_by_same_lambda=(List.map   (fun (p,listByParam)-> (p,(List.filter (fun l-> (hasGetter (l,p))&&(hasSetter (l,p))) listByParam)))   list_of_same_lambdas_by_param) in
                                  let need_to_box_by_same_lambda=(List.map (fun (p,listExpr)-> if((List.length listExpr) > 0) then p else "" ) raise_suspicious_by_same_lambda) in
                                  let exist_setter_and_getter_Each_from_another_clousere_by_param = (List.map (fun (p,getters,setters)-> (p,exsitDiffrent(getters,setters))) list_Of_paris_Of_Getters_And_Setters_By_Param) in
                                  let need_to_box_by_getters_and_setters=  (List.map  (fun (p,answer)->if(answer=true) then p else "")   exist_setter_and_getter_Each_from_another_clousere_by_param) in
                                  let union_need_to_box_index_save = (make_union (need_to_box_by_same_lambda,need_to_box_by_getters_and_setters)) in
                                  let union_need_to_box_unIndex=(List.filter (fun s-> not(String.equal "" s)) union_need_to_box_index_save) in
                                  let list_of_varParam_get_by_param=(List.map (fun p-> (p,makeListVarParam_GetByParam(body,p)) ) params) in
                                  let list_of_varParam_set_by_param=(List.map (fun p-> (p,makeListVarParam_SetByParam(body,p)) ) params) in
                                  let list_of_params_that_have_VarParam_get = (List.map (fun (p,pList)->if((List.length pList)!=0)then p else "") list_of_varParam_get_by_param) in
                                  let list_of_params_that_have_VarParam_set = (List.map (fun (p,pList)->if((List.length pList)!=0)then p else "") list_of_varParam_set_by_param) in
                                  let need_to_box_param_get_and_set_index_save= make_intersection(list_of_params_that_have_VarParam_get,list_of_params_that_have_setters) in
                                  let need_to_box_param_set_and_get_index_save= make_intersection(list_of_params_that_have_VarParam_set,list_of_params_that_have_getter) in
                                  let need_to_box_union_param_set_get= make_union (need_to_box_param_get_and_set_index_save,need_to_box_param_set_and_get_index_save) in
                                  let need_to_box_param_and_bound_unIndex=(List.filter (fun s-> not(String.equal "" s)) need_to_box_union_param_set_get) in
                                  let new_body_case_1=(update_GAS_list_of_param (body,need_to_box_param_and_bound_unIndex)) in
                                  let new_body_case_2=(update_GAS_list_of_param (new_body_case_1,union_need_to_box_unIndex)) in
                                  let list_of_params_need_sets=make_list_of_params(union_need_to_box_index_save,need_to_box_union_param_set_get) in
                                  let list_set_box= (make_list_of_sets(list_of_params_need_sets,0)) in 
                                  if(((List.length need_to_box_param_and_bound_unIndex)!=0) || ((List.length union_need_to_box_unIndex)!=0)) then make_return_value(expr',new_body_case_2,list_set_box) else LambdaSimple'(params,make_box body)

    |LambdaOpt'(params1,opt,body)->let params=(List.concat [params1;[opt]]) in
                                    let listOfLambdaListByParam = (List.map (fun p-> (p,make_list_of_lambdas (body,p)) ) params ) in
                                    let list_Of_paris_Of_Getters_And_Setters_By_Param = (List.map   (fun (p,listByParam)-> (p,make_lambdas_list_of_getters (listByParam,p),(make_lambdas_list_of_setters(listByParam,p))))   listOfLambdaListByParam) in
                                    let list_Of_paris_Of_Setters_By_Param = (List.map   (fun (p,listByParam)-> (p,(make_lambdas_list_of_setters(listByParam,p))))   listOfLambdaListByParam) in
                                    let list_of_params_that_have_setters = (List.map (fun (p,setList)->if((List.length setList)!=0)then p else "") list_Of_paris_Of_Setters_By_Param) in
                                    let list_Of_paris_Of_Getters_By_Param=(List.map   (fun (p,listByParam)-> (p,(make_lambdas_list_of_getters(listByParam,p))))   listOfLambdaListByParam) in
                                    let list_of_params_that_have_getter = (List.map (fun (p,getList)->if((List.length getList)!=0)then p else "") list_Of_paris_Of_Getters_By_Param) in
                                    let list_of_same_lambdas_by_param=(List.map (fun (p,listLambdas)->(p,make_list_of_the_same_lambdas listLambdas)) listOfLambdaListByParam) in
                                    let raise_suspicious_by_same_lambda=(List.map   (fun (p,listByParam)-> (p,(List.filter (fun l-> (hasGetter (l,p))&&(hasSetter (l,p))) listByParam)))   list_of_same_lambdas_by_param) in
                                    let need_to_box_by_same_lambda=(List.map (fun (p,listExpr)-> if((List.length listExpr) > 0) then p else "" ) raise_suspicious_by_same_lambda) in
                                    let exist_setter_and_getter_Each_from_another_clousere_by_param = (List.map (fun (p,getters,setters)-> (p,exsitDiffrent(getters,setters))) list_Of_paris_Of_Getters_And_Setters_By_Param) in
                                    let need_to_box_by_getters_and_setters=  (List.map  (fun (p,answer)->if(answer=true) then p else "")   exist_setter_and_getter_Each_from_another_clousere_by_param) in
                                    let union_need_to_box_index_save = (make_union (need_to_box_by_same_lambda,need_to_box_by_getters_and_setters)) in
                                    let union_need_to_box_unIndex=(List.filter (fun s-> not(String.equal "" s)) union_need_to_box_index_save) in
                                    let list_of_varParam_get_by_param=(List.map (fun p-> (p,makeListVarParam_GetByParam(body,p)) ) params) in
                                    let list_of_varParam_set_by_param=(List.map (fun p-> (p,makeListVarParam_SetByParam(body,p)) ) params) in
                                    let list_of_params_that_have_VarParam_get = (List.map (fun (p,pList)->if((List.length pList)!=0)then p else "") list_of_varParam_get_by_param) in
                                    let list_of_params_that_have_VarParam_set = (List.map (fun (p,pList)->if((List.length pList)!=0)then p else "") list_of_varParam_set_by_param) in
                                    let need_to_box_param_get_and_set_index_save= make_intersection(list_of_params_that_have_VarParam_get,list_of_params_that_have_setters) in
                                    let need_to_box_param_set_and_get_index_save= make_intersection(list_of_params_that_have_VarParam_set,list_of_params_that_have_getter) in
                                    let need_to_box_union_param_set_get= make_union (need_to_box_param_get_and_set_index_save,need_to_box_param_set_and_get_index_save) in
                                    let need_to_box_param_and_bound_unIndex=(List.filter (fun s-> not(String.equal "" s)) need_to_box_union_param_set_get) in
                                    let new_body_case_1=(update_GAS_list_of_param (body,need_to_box_param_and_bound_unIndex)) in
                                    let new_body_case_2=(update_GAS_list_of_param (new_body_case_1,union_need_to_box_unIndex)) in
                                    let list_of_params_need_sets=make_list_of_params(union_need_to_box_index_save,need_to_box_union_param_set_get) in
                                    let list_set_box= (make_list_of_sets(list_of_params_need_sets,0)) in 
                                    if(((List.length need_to_box_param_and_bound_unIndex)!=0) || ((List.length union_need_to_box_unIndex)!=0)) then make_return_value(expr',new_body_case_2,list_set_box) else LambdaOpt'(params1,opt,make_box body)

                                  
    |Seq'(exprList)-> Seq'(List.map (fun expr->make_box(expr)) exprList)
    |If'(_test,_then,_else)-> If'(make_box(_test),make_box(_then),make_box(_else))
    |Set'(a,b)->Set'(make_box(a),make_box(b))
    |Def'(a,b)-> Def'(make_box(a),make_box(b))   
    |BoxSet'(a,b)-> BoxSet'(a,make_box(b))
    |Or' (exprList)->  Or'(List.map (fun expr->make_box(expr)) exprList)
    |Applic'(expr,exprList)->  Applic'(make_box(expr),(List.map (fun expr->make_box(expr)) exprList))
    |ApplicTP' (expr,exprList)-> ApplicTP'(make_box(expr),(List.map (fun expr->make_box(expr)) exprList))
    |_->expr'

    and  make_return_value =
    fun (expr',new_body,list_set_box) ->
match expr',new_body with
|LambdaSimple'(params,_),body-> LambdaSimple'(params,Seq'(List.concat [list_set_box; [make_box body]]))
|LambdaOpt'(params,opt,_),body->LambdaOpt'(params,opt,Seq'(List.concat [list_set_box; [make_box body]]))
|_->raise X_this_should_not_happen;;
  

let annotate_lexical_addresses e = make_expr' e;;

let annotate_tail_calls e = make_tail_call e;;

let box_set e = make_box e;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)

