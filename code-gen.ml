
#use "semantic-analyser.ml";;




let rec make_const_list =
  fun expr'->
  match expr' with
  | Const'(c)->[c]
  | BoxSet'(_,expr)-> make_const_list expr
  | If'(_test,_then,_else)->(List.concat [(make_const_list _test);(make_const_list _then);(make_const_list _else)])
  | Seq'(exprList)->(List.flatten (List.map make_const_list exprList))
  | Set' (expr1,expr2)->(List.concat [(make_const_list expr1);(make_const_list expr2)])
  | Def' (expr1,expr2)->(List.concat [(make_const_list expr1);(make_const_list expr2)])
  | Or' (exprList)-> (List.flatten (List.map make_const_list exprList))
  | LambdaSimple'(_,body)->make_const_list body
  | LambdaOpt' (_,_,body)->make_const_list body
  | Applic' (expr,exprList)->(List.concat [(make_const_list expr);((List.flatten (List.map make_const_list exprList)))])
  | ApplicTP'(expr,exprList)->(List.concat [(make_const_list expr);((List.flatten (List.map make_const_list exprList)))])
  |_->[];;

 let const_eq =
  fun (c1,c2)->
  match c1, c2 with
  | Void, Void -> true
  | Sexpr s1,Sexpr s2 -> sexpr_eq s1 s2
  |_->false;;

  let rec remove_duplicates =
    fun constList->
  match constList with
  |[]->[]
  |car::cdr-> (List.concat [[car];(remove_duplicates (List.filter (fun const-> not(try(const_eq (car,const)) with Invalid_argument _->false)) cdr))]);;

let rec make_topologic =
  fun const->
  match const with
  | Void->[Void]
  | Sexpr(Nil)->[Sexpr(Nil)]
  | Sexpr(Bool(c))->[Sexpr(Bool(c))]
  | Sexpr(Number(c))->[Sexpr(Number(c))]
  | Sexpr(Char(c))->[Sexpr(Char(c))]
  | Sexpr(String(c))->[Sexpr(String(c))]
  | Sexpr(Symbol(c))-> [Sexpr(Symbol(c))]
  | Sexpr(Pair(car,cdr))->  (List.concat [make_topologic (Sexpr(car)); make_topologic (Sexpr(cdr)); [Sexpr(Pair(car,cdr))]])
  | Sexpr(Vector(sexprList))->(List.concat [(List.flatten (List.map (fun sexpr-> (make_topologic (Sexpr(sexpr))) ) sexprList));[Sexpr(Vector(sexprList))]]);;
 


  let sort_topologic =
    fun constList->
    let const_tbl= [Void;Sexpr(Nil);Sexpr(Bool(false));Sexpr(Bool(true))] in
    remove_duplicates(List.flatten (List.map make_topologic (List.concat [const_tbl;constList])));;


sort_topologic ([Void;Sexpr(Bool(true));Sexpr(Pair(Number(Int(1)),Nil));Void;Sexpr(Pair(Number(Int(2)),Nil));Sexpr(Pair(Number(Int(1)),Nil))]);;

let rec concate_string_list =
  fun (stringList, curr)->
  match stringList with
   |[]-> curr
   |car::cdr-> concate_string_list (cdr,(String.concat car [curr; ""]));;

let check_if_equal =
  fun ((sexpr,size,ass),c)->
if (try(const_eq (sexpr, c)) with Invalid_argument _ ->false) then size else -1;; 

let rec find_in_const_table=
  fun (table,c)->
  match table with
  |[]-> -1
  |car::cdr-> let index= (check_if_equal (car,c)) in if (index = -1) then find_in_const_table (cdr,c) else index;;

let make_string_for_vector =
  fun (sexprList,table)->
  let middle_string_list = (List.map (fun sexpr-> (concate_string_list (["consts+"; (string_of_int (find_in_const_table (table,Sexpr(sexpr)))) ; "," ],"") )) sexprList) in
  let concate_string_list_1= (concate_string_list (middle_string_list, "")) in
   let fixed_string =(String.sub concate_string_list_1 (0) (String.length concate_string_list_1 -1)) in
    concate_string_list (["MAKE_LITERAL_VECTOR(";  fixed_string; ")"],"")


let make_tuple_for_const =
  fun (const,table,size)->
  match const with
  | Void -> [(Void ,0 ,"MAKE_VOID" )] , 1
  | Sexpr(Nil)->[(Sexpr(Nil) ,1 ,"MAKE_NIL" )] , 2 
  | Sexpr(Bool(c))->if (c) then [(Sexpr(Bool(true)) ,4 ,"MAKE_BOOL(1)" )], 6 else [(Sexpr(Bool(false)) ,2 ,"MAKE_BOOL(0)" )], 4
  | Sexpr(Number(Int(c)))-> [(Sexpr(Number(Int(c))) ,size , concate_string_list (["MAKE_LITERAL_INT(";string_of_int c ;")"],"") )] ,size+8+1
  | Sexpr(Number(Float(c)))->[(Sexpr(Number(Float(c))) ,size , concate_string_list (["MAKE_LITERAL_FLOAT(";string_of_float c ;")"],"") )] ,size+8+1
  | Sexpr(Char(c))-> [(Sexpr(Char(c)) ,size ,concate_string_list (["MAKE_LITERAL_CHAR('";Char.escaped c ;"')"],"") ) ],size+2
  | Sexpr(String(c))-> [(Sexpr(String(c)) ,size ,concate_string_list (["MAKE_LITERAL_STRING \"";c ;"\""],"") )], size+8+1+(String.length c)
  | Sexpr(Symbol(c))-> let index =(find_in_const_table (table,Sexpr(String(c)))) in if (index=(-1)) then  ([(Sexpr(String(c)),size,concate_string_list (["MAKE_LITERAL_STRING \"";c ;"\" "],""));
                                                                                                            (Sexpr(Symbol(c)), size+(String.length c)+8+1,concate_string_list (["MAKE_LITERAL_SYMBOL(consts+";string_of_int size ;")"],""))]
                                                                                                          ,size+(String.length c) +1+8+1+8) 
                                                                                                        else [(Sexpr(Symbol(c)),size,concate_string_list (["MAKE_LITERAL_SYMBOL(consts+";string_of_int index ;")"],""))],size+8+1
  | Sexpr(Pair(car,cdr))->  [(Sexpr(Pair(car,cdr)),size ,concate_string_list (["MAKE_LITERAL_PAIR(consts+";string_of_int (find_in_const_table (table,Sexpr(car))) ;" ,consts+";string_of_int (find_in_const_table (table,Sexpr(cdr)));")"],"") )], size+1+8+8
  | Sexpr(Vector(sexprList))->let string_for_vector= (make_string_for_vector (sexprList,table)) in
                                              ([(Sexpr(Vector(sexprList)),size,   string_for_vector )],(List.length sexprList)*8+8+1);;


let rec make_const_tbl=
  fun (constList, curr ,size_in_byte)->
  match constList with
  |[]->curr
  |car::cdr -> let (listT,s)=make_tuple_for_const (car,curr,size_in_byte) in  make_const_tbl (cdr,List.concat [curr;listT ] ,s);;

 

    

let rec make_fvar_table =
  fun (expr',currTable)->
match expr' with
| Var'(VarFree(c))->List.concat [currTable;[(c, 0)]]
| Box' (VarFree(c))->List.concat [currTable;[(c, 0)]]
| BoxGet'(VarFree(c))-> List.concat [currTable;[(c, 0)]]
| BoxSet' (VarFree(c),expr) -> make_fvar_table( expr, (List.concat [currTable;[(c, 0)]]))
| BoxSet' (_,expr)-> make_fvar_table(expr,currTable)
| If' (_test,_then,_else)-> let testTable=make_fvar_table(_test,currTable) in
                              let thenTable= make_fvar_table(_then,testTable) in
                                make_fvar_table(_else,thenTable) 
| Seq'(exprList)-> make_fvar_table_for_expr_list (exprList,currTable)
| Set' (expr1,expr2)-> let expr1Table = make_fvar_table(expr1,currTable) in
                          make_fvar_table(expr2,expr1Table)
| Def'(expr1,expr2)->let expr1Table=make_fvar_table(expr1,currTable) in
                      make_fvar_table(expr2,expr1Table)
| Or'(exprList)-> make_fvar_table_for_expr_list (exprList,currTable)
| LambdaSimple'(_,body)->make_fvar_table (body,currTable)
| LambdaOpt'(_,_,body)->make_fvar_table (body,currTable)
| Applic'(expr,exprList)-> let exprTable= make_fvar_table(expr,currTable) in
                              make_fvar_table_for_expr_list(exprList,exprTable)
| ApplicTP'(expr,exprList)->let exprTable= make_fvar_table(expr,currTable) in
                              make_fvar_table_for_expr_list(exprList,exprTable)
|_->currTable

and make_fvar_table_for_expr_list = 
fun (exprList,currTable)->
match exprList with
|[]-> currTable
|car::cdr->let carTable= make_fvar_table (car,currTable) in make_fvar_table_for_expr_list(cdr,carTable);;


let rec remove_duplicates_fvars=
  fun table->
  match table with
  |[]->[]
  |car::cdr-> (List.concat [[car];(remove_duplicates_fvars (List.filter (fun (name,index)-> let (nameCar,indexCar)=car in (not(String.equal name nameCar))) cdr))]);;


let rec fill_index=
  fun (table,newTable,index)->
  match table with
  |[]->newTable
  |(nameCar,_)::cdr-> fill_index(cdr,(List.concat [newTable;[(nameCar,index)]]),index+1);;


  let rec build_fvars_table=
    fun (exprList,currTable)->
    match exprList with
    |[]-> currTable
    |car::cdr->let carTable= make_fvar_table (car,currTable) in make_fvar_table_for_expr_list(cdr,carTable);;

    let rec addressInConstTable =
      fun (constTable,const)->
      match constTable with
      | []->""
      | (carConst,(offset,_))::cdr-> if (const_eq (carConst,const)) then (concate_string_list (["consts+";string_of_int offset;],"")) else  addressInConstTable(cdr,const);;

    let rec labelInFVarTable =
      fun (fvarTable,fvar)->
      match fvarTable with
      | []->""
      | (carName,index)::cdr-> if (String.equal carName fvar) then (concate_string_list (["fvar_tbl+";string_of_int index;"*WORD_SIZE"],"")) else  labelInFVarTable(cdr,fvar);;
      (*let stringGenlist= (List.map (fun expr-> make_generate(expr,"",constTable,fvarTable,envSize,labelIndex+1)) exprList) in
                          concate_string_list ((List.concat [[currGen];stringGenlist]),"")*)


    let rec make_generate=
      fun (expr',currGen,constTable,fvarTable,envSize)-> 
      match expr' with
      | Const'(c)-> concate_string_list ([currGen; "mov rax, ";addressInConstTable(constTable,c);"\n"],"")
      | Var'(VarFree(c))->concate_string_list ([currGen; "mov rax, qword [";labelInFVarTable(fvarTable,c);"]\n"],"")
      | Var'(VarBound(c,mjr,mnr))->concate_string_list ([currGen; 
                                                        "mov rax, qword [rbp+8*2]\n";
                                                        "mov rax, qword [rax+8*";string_of_int mjr ;"]\n";
                                                        "mov rax, qword [rax+8*";string_of_int mnr ;"]\n"],"")
      | Var'(VarParam(c,mnr))-> concate_string_list ([currGen; "mov rax, qword [rbp+8*(4+";string_of_int mnr ;")]\n"],"")


      | Box' (VarFree(c))-> concate_string_list ([currGen;
                                                 "lea rax, [";labelInFVarTable(fvarTable,c);"]\n";
                                                 "push rax\n";
                                                 "MALLOC rax, WORD_SIZE\n";
                                                 "pop qword [rax]\n"],"") 
      | Box' (VarParam(c,mnr))->   concate_string_list ([currGen;
                                                        "lea rax, [rbp+8*(4+";string_of_int mnr ;")]\n";
                                                        "push rax\n";
                                                        "MALLOC rax, WORD_SIZE\n";
                                                        "pop qword [rax]\n"],"")                   

      | BoxGet'(v)->let varGetGenCodeExpand= make_generate(Var'(v),"",constTable,fvarTable,envSize) in
                      concate_string_list ([currGen;varGetGenCodeExpand;
                                            "mov rax, qword [rax]\n"],"")
 
      | BoxSet' (v,expr) -> let genCodeExpr_expandCurrGen= make_generate (expr,"",constTable,fvarTable,envSize) in
                            concate_string_list ([currGen;genCodeExpr_expandCurrGen;
                                                  "push rax\n";
                                                  make_generate(Var'(v),"",constTable,fvarTable,envSize);
                                                  "pop qword [rax]\n";
                                                  "mov rax, consts+0\n"],"")
      | Def'(Var'(VarFree(c)),expr2)-> let genCodeExpr2_expandCurrGen= make_generate (expr2,"",constTable,fvarTable,envSize) in
                                          concate_string_list ([currGen;genCodeExpr2_expandCurrGen; 
                                          "mov qword [";labelInFVarTable(fvarTable,c);"], rax\n";
                                          "mov rax, consts+0\n"],"")
      | If' (_test,_then,_else)-> let _=next_val() in let index1=(!counter) in
                                    let testGenCode_expand= concate_string_list([make_generate(_test,"",constTable,fvarTable,envSize);
                                                                              "cmp rax, consts+4\n";
                                                                              "je Lelse";string_of_int index1 ;"\n"],"") in  let _=next_val() in 
                                    let thenGenCode_expand= concate_string_list([make_generate(_then,"",constTable,fvarTable,envSize);
                                                                              "jmp Lexit";string_of_int index1 ;"\n";
                                                                              "Lelse";string_of_int index1 ;":\n"],"") in let _=next_val() in
                                    let elseGenCode_expand= concate_string_list([make_generate(_else,"",constTable,fvarTable,envSize);
                                                                              "Lexit";string_of_int index1 ;":\n"],"") in let _=next_val() in
                              concate_string_list ([currGen;testGenCode_expand;thenGenCode_expand;elseGenCode_expand],"")
      | Seq'(exprList)-> let stringGenlist= (List.map (fun expr-> make_generate(expr,"",constTable,fvarTable,envSize)) exprList) in
                          concate_string_list ((List.concat [[currGen];stringGenlist]),"")
      | Set' (Var'(VarParam(_,mnr)),expr2)-> let genCodeExpr2_expandCurrGen= make_generate (expr2,"",constTable,fvarTable,envSize) in
                                               concate_string_list ([currGen;genCodeExpr2_expandCurrGen; 
                                                                    "mov qword [rbp+8*(4+";string_of_int mnr ;")], rax\n";
                                                                    "mov rax, consts+0\n"],"")
      | Set' (Var'(VarBound(_,mjr,mnr)),expr2)->let genCodeExpr2_expandCurrGen= make_generate (expr2,"",constTable,fvarTable,envSize) in 
                                                    concate_string_list ([currGen;genCodeExpr2_expandCurrGen; 
                                                                          "mov rbx, qword [rbp+8*2]]\n";
                                                                          "mov rbx, qword [rbx+8*";string_of_int mjr ;"]\n";
                                                                          "mov qword [rbx+8*";string_of_int mnr ;"], rax\n";
                                                                          "mov rax, consts+0\n"],"")
      | Set' (Var'(VarFree(c)),expr2)-> let genCodeExpr2_expandCurrGen= make_generate (expr2,"",constTable,fvarTable,envSize) in
                                    concate_string_list ([currGen;genCodeExpr2_expandCurrGen; 
                                    "mov qword [";labelInFVarTable(fvarTable,c);"], rax\n";
                                    "mov rax, consts+0\n"],"")


      | Or'(exprList)-> let subListWithoutLast=(List.rev (List.tl (List.rev (exprList) ))) in
                        let lastExpr=(List.nth exprList ((List.length exprList)-1)) in
                        next_val();let index=counter.contents in
                        let stringGenlist= (List.map (fun expr-> concate_string_list ([make_generate(expr,"",constTable,fvarTable,envSize);
                                                                                      "cmp rax, qword consts+2\n";
                                                                                      "jne Lexit";string_of_int index;"\n"],"")) subListWithoutLast) in
                        let final_string_gen_list=(List.concat [stringGenlist; [(concate_string_list ( [make_generate(lastExpr,"",constTable,fvarTable,envSize);
                                                                                                      "Lexit";string_of_int index;":\n"],""))]]) in
                        concate_string_list ((List.concat [[currGen];final_string_gen_list]),"")
      | Applic'(proc,exprList)->let pushMagic=concate_string_list(["push SOB_NIL_ADDRESS\n"],"")in 
                                let argCode= List.fold_right (fun  expr' acc-> concate_string_list([acc; make_generate (expr',"",constTable,fvarTable,envSize);"push rax\n"],"")) exprList "" in
                                  let argNumber=concate_string_list (["push ";(string_of_int (List.length exprList));"\n" ],"") in
                                   let procCode= make_generate (proc,"",constTable,fvarTable,envSize) in
                                    (*need to add verify clouser maybe in assembly or maybe in ocaml*)
                                    let pushEnv=concate_string_list (["CLOSURE_ENV r9, rax\n";
                                                                      "push r9\n";
                                                                      "CLOSURE_CODE r9, rax\n";
                                                                      "call r9\n"],"") in
                                    let applicCode=concate_string_list([currGen;
                                                                        pushMagic;
                                                                        argCode;
                                                                        argNumber;
                                                                        procCode;
                                                                        pushEnv;
                                                                        "add rsp, 8*1   ;pop env\n";
                                                                        "pop rbx        ;pop arg count\n";
                                                                        "shl rbx, 3     ;rbx = rbx*8\n";
                                                                        "add rsp, rbx   ;pop args\n";
                                                                        "add rsp, 8*1   ;pop magic\n"],"") in
                                      applicCode
      | ApplicTP'(proc,exprList)-> let pushMagic=concate_string_list(["push SOB_NIL_ADDRESS\n"],"")in 
                                    let argCode= List.fold_right (fun  expr' acc-> concate_string_list([acc; make_generate (expr',"",constTable,fvarTable,envSize);"push rax\n"],"")) exprList "" in
                                      let argNumber=concate_string_list (["push ";(string_of_int (List.length exprList));"\n" ],"") in
                                      let procCode= make_generate (proc,"",constTable,fvarTable,envSize) in
                                        (*need to add verify clouser maybe in assembly or maybe in ocaml*)
                                        let pushEnv=concate_string_list (["CLOSURE_ENV r9, rax\n";
                                                                          "push r9\n";
                                                                          "CLOSURE_CODE r9, rax\n";
                                                                          "mov rax, r9\n"
                                                                          ],"") in
                                        let applicCode=concate_string_list([currGen;
                                                                            pushMagic;
                                                                            argCode;
                                                                            argNumber;
                                                                            procCode;
                                                                            pushEnv;
                                                                            "lea r9, [";string_of_int (List.length exprList);"+4]\n";
                                                                            "lea r10,[rbp+3*8]\n";
                                                                            "mov r8, [r10]    ;n of the prev frame\n";    
                                                                            "push qword [rbp + 8*1]   ;old ret addres\n";
                                                                            "mov r14, qword [rbp]\n";
                                                                            "SHIFT_FRAME r9, r8\n";
                                                                            "push r14\n";
                                                                            "add rax, 0x1\n";
                                                                            "jmp rax    ;jump to code\n"],"") in
                                          applicCode
      | LambdaSimple'(params,body)->let extEnvSize=envSize+1 in
                                        let bodyGenCode= make_generate(body,"",constTable,fvarTable,extEnvSize) in
                                         let _= next_val() in let index=counter.contents in
                                          let checkDummyFrame= concate_string_list ([currGen;
                                                                                      "mov rdi, qword [rsp+1*8]\n";
                                                                                      "mov rsi, qword T_UNDEFINED\n";
                                                                                      "cmp rdi, rsi\n";
                                                                                      "jne Lambda";string_of_int index;"\n";
                                                                                      "mov rdi, qword [rsp+2*8]\n";
                                                                                      "lea rsi, [consts+1]\n";
                                                                                      "cmp rdi, rsi\n";
                                                                                      "mov rax,rdi\n";
                                                                                      "jne Lcont";string_of_int index;"\n";
                                                                                      "MALLOC rax, 1*WORD_SIZE\n";
                                                                                      "push rsi\n";
                                                                                      "pop qword [rax]\n";
                                                                                      "mov qword [rsp+2*8], rax\n";
                                                                                      "jmp Lcont";string_of_int index;"\n";
                                                                                      "Lambda";string_of_int index;":\n";
                                                                                      "lea r10, [rbp+2*8]\n";
                                                                                      "mov rdi, qword [r10]\n ";
                                                                                      "mov rsi, qword T_UNDEFINED\n";
                                                                                      "cmp rdi, rsi\n";
                                                                                      "je Lcont";string_of_int index;"\n";
                                                                                      ],"") in 
                                          let extEnvInitial= concate_string_list([checkDummyFrame;
                                                                                  "mov rdi,qword [rbp+8*3]\n";
                                                                                  "mov rcx, rdi\n";
                                                                                  "cmp rdi, 0x0\n";
                                                                                  "je NoNeedCopy";string_of_int index;"\n";
                                                                                  "lea rdi, [rdi*WORD_SIZE]\n";
                                                                                  "MALLOC rax, rdi\n";
                                                                                  "sub rdi, WORD_SIZE\n";
                                                                                  "lea rax, [rax+rdi]\n";
                                                                                  "lea r10, [rbp + 3*8 + rcx*WORD_SIZE]\n";
                                                                                  "mov r9, qword [r10]\n";
                                                                                  "mov qword [rax],r9\n";
                                                                                  "lea rax, [rax-WORD_SIZE]\n";
                                                                                  "dec rcx\n";
                                                                                  "cmp rcx, 0x0\n";
                                                                                  "je endInsert";string_of_int index;"\n";
                                                                                  "InsertParam";string_of_int index;":\n";
                                                                                  "dec rcx\n";
                                                                                  "lea r10, [rbp + 4*8 + rcx*WORD_SIZE]\n";
                                                                                  "mov r9, qword [r10]\n";
                                                                                  "mov qword [rax],r9\n";
                                                                                  "lea rax, [rax-WORD_SIZE]\n";
                                                                                  "cmp rcx, 0x0\n";
                                                                                  "jne InsertParam";string_of_int index;"\n";
                                                                                  "endInsert";string_of_int index;":\n";
                                                                                  "lea rax, [rax+WORD_SIZE]\n";
                                                                                  "push rax\n";
                                                                                  "MALLOC rax, ";string_of_int extEnvSize;"*WORD_SIZE\n";
                                                                                  "pop qword [rax]\n";
                                                                                  "jmp NoMaloc";string_of_int index;"\n";
                                                                                  "NoNeedCopy";string_of_int index;":\n"
                                                                                  ],"") in
                                            let extEnv= if (envSize!=0) then concate_string_list ([extEnvInitial;
                                                                            
                                                                            ";r8 going to be new addres for start of extEnv\n"; 
                                                                            ";rsi going to be old envSize\n";
                                                                            ";rdi going to be addres of env[i]\n";
                                                                            ";rcx going to be counter fo loop\n";
                                                                            ";r9 temp register\n";
                                                                            "MALLOC rax, ";string_of_int extEnvSize;"*WORD_SIZE\n";
                                                                            "lea r10, [consts+1]\n";
                                                                            "push r10\n";
                                                                            "pop qword [rax]\n";
                                                                            "NoMaloc";string_of_int index;":\n";
                                                                            "mov r8, rax\n";
                                                                            "mov qword rsi, ";string_of_int envSize;"\n";
                                                                            "mov rax, qword [rbp+8*2]     ;rax is start of current lexEnv\n";
                                                                            "mov qword rcx, 1\n";
                                                                            "LoopEnv";string_of_int index;":\n";
                                                                            "lea rdi, [rax+8*rcx -8]\n";
                                                                            "mov r15, qword [rdi]\n";
                                                                            "mov rdi, r15\n";
                                                                            "lea r9, [r8+rcx*8]\n";
                                                                            "mov qword [r9], rdi\n";
                                                                            "inc rcx\n";
                                                                            "cmp rcx, rsi\n";
                                                                            "jle LoopEnv";string_of_int index;"\n";
                                                                            "End_loop";string_of_int index;":\n";
                                                                            "mov qword rax, r8\n";
                                                                            ],"") else concate_string_list([extEnvInitial;
                                                                                                            "NoMaloc";string_of_int index;":\n";
                                                                                                            ],"") in
                                                let codeClosure= concate_string_list([extEnv;
                                                                                      "jmp Lcont";string_of_int index;"\n";
                                                                                      "Lcode";string_of_int index;":\n";
                                                                                      "push rbp\n";
                                                                                      "mov rbp, rsp\n";
                                                                                      bodyGenCode;
                                                                                      "leave\n";
                                                                                      "ret\n";
                                                                                      "Lcont";string_of_int index;":\n";
                                                                                      "mov rdi,rax\n";
                                                                                      "MAKE_CLOSURE(rax,rdi,Lcode";string_of_int index;")\n";],"") in
                                                  codeClosure
      | LambdaOpt'(params,opt,body)-> let extEnvSize=envSize+1 in
                                        let bodyGenCode= make_generate(body,"",constTable,fvarTable,extEnvSize) in
                                        let paramSize=(List.length params) in
                                        let _= next_val() in let index=counter.contents in
                                        let optAvailable= not (String.equal opt "") in
                                          let checkDummyFrame= concate_string_list ([currGen;
                                                                                      "mov rdi, qword [rsp+1*8]\n";
                                                                                      "mov rsi, qword T_UNDEFINED\n";
                                                                                      "cmp rdi, rsi\n";
                                                                                      "jne Lambda";string_of_int index;"\n";
                                                                                      "mov rdi, qword [rsp+2*8]\n";
                                                                                      "lea rsi, [consts+1]\n";
                                                                                      "cmp rdi, rsi\n";
                                                                                      "mov rax,rdi\n";
                                                                                      "jne Lcont";string_of_int index;"\n";
                                                                                      "MALLOC rax, 1*WORD_SIZE\n";
                                                                                      "push rsi\n";
                                                                                      "pop qword [rax]\n";
                                                                                      "mov qword [rsp+2*8], rax\n";
                                                                                      "jmp Lcont";string_of_int index;"\n";
                                                                                      "Lambda";string_of_int index;":\n";
                                                                                      "lea r10, [rbp+2*8]\n";
                                                                                      "mov rdi, qword [r10]\n ";
                                                                                      "mov rsi, qword T_UNDEFINED\n";
                                                                                      "cmp rdi, rsi\n";
                                                                                      "je Lcont";string_of_int index;"\n";],"") in 
                                          let extEnvInitial= concate_string_list([checkDummyFrame;
                                                                                  "mov rdi,qword [rbp+8*3]\n";
                                                                                  "mov rcx, rdi\n";
                                                                                  "cmp rdi, 0x0\n";
                                                                                  "je NoNeedCopy";string_of_int index;"\n";
                                                                                  "lea rdi, [rdi*WORD_SIZE]\n";
                                                                                  "MALLOC rax, rdi\n";
                                                                                  "sub rdi, WORD_SIZE\n";
                                                                                  "lea rax, [rax+rdi]\n";
                                                                                  "lea r10, [rbp + 3*8 + rcx*WORD_SIZE]\n";
                                                                                  "mov r9, qword [r10]\n";
                                                                                  "mov qword [rax],r9\n";
                                                                                  "lea rax, [rax-WORD_SIZE]\n";
                                                                                  "dec rcx\n";
                                                                                  "cmp rcx, 0x0\n";
                                                                                  "je endInsert";string_of_int index;"\n";
                                                                                  "InsertParam";string_of_int index;":\n";
                                                                                  "dec rcx\n";
                                                                                  "lea r10, [rbp + 4*8 + rcx*WORD_SIZE]\n";
                                                                                  "mov r9, qword [r10]\n";
                                                                                  "mov qword [rax],r9\n";
                                                                                  "lea rax, [rax-WORD_SIZE]\n";
                                                                                  "cmp rcx, 0x0\n";
                                                                                  "jne InsertParam";string_of_int index;"\n";
                                                                                  "endInsert";string_of_int index;":\n";
                                                                                  "lea rax, [rax+WORD_SIZE]\n";
                                                                                  "push rax\n";
                                                                                  "MALLOC rax, ";string_of_int extEnvSize;"*WORD_SIZE\n";
                                                                                  "pop qword [rax]\n";
                                                                                  "jmp NoMaloc";string_of_int index;"\n";
                                                                                  "NoNeedCopy";string_of_int index;":\n"
                                                                                  ],"") in
                                            let extEnv= if (envSize!=0) then concate_string_list ([extEnvInitial;
                                                                            
                                                                            ";r8 going to be new addres for start of extEnv\n"; 
                                                                            ";rsi going to be old envSize\n";
                                                                            ";rdi going to be addres of env[i]\n";
                                                                            ";rcx going to be counter fo loop\n";
                                                                            ";r9 temp register\n";
                                                                            "MALLOC rax, ";string_of_int extEnvSize;"*WORD_SIZE\n";
                                                                            "lea r10, [consts+1]\n";
                                                                            "push r10\n";
                                                                            "pop qword [rax]\n";
                                                                            "NoMaloc";string_of_int index;":\n";
                                                                            "mov r8, rax\n";
                                                                            "mov qword rsi, ";string_of_int envSize;"\n";
                                                                            "mov rax, qword [rbp+8*2]     ;rax is start of current lexEnv\n";
                                                                            "mov qword rcx, 1\n";
                                                                            "LoopEnv";string_of_int index;":\n";
                                                                            "lea rdi, [rax+8*rcx -8]\n";
                                                                            "mov r15, qword [rdi]\n";
                                                                            "mov rdi, r15\n";
                                                                            "lea r9, [r8+rcx*8]\n";
                                                                            "mov qword [r9], rdi\n";
                                                                            "inc rcx\n";
                                                                            "cmp rcx, rsi\n";
                                                                            "jle LoopEnv";string_of_int index;"\n";
                                                                            "End_loop";string_of_int index;":\n";
                                                                            "mov qword rax, r8\n";
                                                                            ],"") else concate_string_list([extEnvInitial;
                                                                                                            "NoMaloc";string_of_int index;":\n";
                                                                                                            ],"") in
                                                let codeClosure=  if optAvailable 
                                                                  then concate_string_list([extEnv;
                                                                                      "jmp Lcont";string_of_int index;"\n";
                                                                                      "Lcode";string_of_int index;":\n";
                                                                                      "mov qword rdi,";string_of_int paramSize;"  ;rdi hold paramSize\n";
                                                                                      "mov rsi,qword [rsp+8*2]    ;rsi hold n\n";
                                                                                      "sub rsi, rdi\n";
                                                                                      "mov rcx, rsi               ;rcx hold the counterLoop= n - paramSize\n";
                                                                                      "lea r10, [rsp+3*8+rdi*8]\n" ;  
                                                                                      "mov r9, r10                ;r9 hold the address of the first element that need to copy \n";
                                                                                      "lea r11, [rcx*8 -8]\n";
                                                                                      "add r10, r11             ;r10 hold the address of the element that need to copy in the loop \n";
                                                                                      "mov rsi, qword [r10]       ;rsi hold the first element that need to copy \n";
                                                                                      "mov rax, rsi\n";
                                                                                      "cmp rcx, 0x0\n";
                                                                                      "je EndOpt";string_of_int index;"\n";
                                                                                      "MAKE_PAIR (rax, rsi, SOB_NIL_ADDRESS) \n";
                                                                                      "dec rcx\n";
                                                                                      "cmp rcx, 0x0\n";
                                                                                      "je EndOpt";string_of_int index;"\n";
                                                                                      "CopyOptParams";string_of_int index;":\n";
                                                                                      "sub r10, WORD_SIZE \n";
                                                                                      "push qword [r10]\n";
                                                                                      "pop qword r8\n";
                                                                                      "mov r11, rax\n";
                                                                                      "MAKE_PAIR (rax, r8, r11) \n";
                                                                                      "dec rcx\n";
                                                                                      "cmp rcx, 0x0\n";
                                                                                      "jg CopyOptParams";string_of_int index;"\n";
                                                                                      "EndOpt";string_of_int index;":\n";
                                                                                      "push rax             ;rax hold the pointer to optParamList\n";
                                                                                      "pop qword [r9]      ;override first opt params with optParamVector\n";
                                                                                      "push rbp\n";
                                                                                      "mov rbp, rsp\n";
                                                                                      bodyGenCode;
                                                                                      "leave\n";
                                                                                      "ret\n";
                                                                                      "Lcont";string_of_int index;":\n";
                                                                                      "mov rdi,rax\n";
                                                                                      "MAKE_CLOSURE(rax,rdi,Lcode";string_of_int index;")\n";],"")
                                                                  else concate_string_list([extEnv;
                                                                                      "jmp Lcont";string_of_int index;"\n";
                                                                                      "Lcode";string_of_int index;":\n";
                                                                                      "push rbp\n";
                                                                                      "mov rbp, rsp\n";
                                                                                      bodyGenCode;
                                                                                      "leave\n";
                                                                                      "ret\n";
                                                                                      "Lcont";string_of_int index;":\n";
                                                                                      "mov rdi,rax\n";
                                                                                      "MAKE_CLOSURE(rax,rdi,Lcode";string_of_int index;")\n";],"") in
                                                  codeClosure
      |_->currGen
      ;;
      
      
(*let rec print_listOfPr =
  fun listP->
  match listP with 
  |[]->print_string "]"
  |(pName,_)::cdr->print_string "(\"";print_string pName; print_string "\",0)";print_string ";";print_listOfPr cdr;;

  print_string "\n[";print_listOfPr["boolean?", "is_boolean"; "float?", "is_float"; "integer?", "is_integer"; "pair?", "is_pair";
  "null?", "is_null"; "char?", "is_char"; "vector?", "is_vector"; "string?", "is_string";
  "procedure?", "is_procedure"; "symbol?", "is_symbol"; "string-length", "string_length";
  "string-ref", "string_ref"; "string-set!", "string_set"; "make-string", "make_string";
  "vector-length", "vector_length"; "vector-ref", "vector_ref"; "vector-set!", "vector_set";
  "make-vector", "make_vector"; "symbol->string", "symbol_to_string"; 
  "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "eq?", "is_eq";
  "+", "bin_add"; "*", "bin_mul"; "-", "bin_sub"; "/", "bin_div"; "<", "bin_lt"; "=", "bin_equ"];;*)
      

module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> (constant * ( int * string)) list
  val make_fvars_tbl : expr' list -> (string * int) list
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct
let primitive_fvar_table=[("boolean?",0);("float?",0);("integer?",0);("pair?",0);("null?",0);("char?",0);("vector?",0);("string?",0);
                          ("procedure?",0);("symbol?",0);("string-length",0);("string-ref",0);("string-set!",0);("make-string",0);
                          ("vector-length",0);("vector-ref",0);("vector-set!",0);("make-vector",0);("symbol->string",0);
                          ("char->integer",0);("integer->char",0);("eq?",0);("+",0);("*",0);("-",0);("/",0);("<",0);("=",0);
                          ("cons",0);("car",0);("cdr",0);("set-car!",0);("set-cdr!",0)]

  let make_consts_tbl asts =  let tables= (List.flatten(List.map make_const_list asts)) in 
                                let final_table= make_const_tbl( (sort_topologic(remove_duplicates (tables))) ,[] , 0 ) in
                            (List.map (fun (a,b,c)->(a,(b,c))) final_table) ;;
  let make_fvars_tbl asts = fill_index((remove_duplicates_fvars(build_fvars_table (asts,primitive_fvar_table))),[],0);;

  let generate consts fvars e = next_val(); make_generate (e,"",consts,fvars,0);;
end;;





