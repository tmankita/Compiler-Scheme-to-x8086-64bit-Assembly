

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~PC.ml~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* pc.ml
 * A parsing-combinators package for ocaml
 *
 * Prorammer: Mayer Goldberg, 2018
 *)

(* general list-processing procedures *)

let rec ormap f s =
  match s with
  | [] -> false
  | car :: cdr -> (f car) || (ormap f cdr);;

let rec andmap f s =
  match s with
  | [] -> true
  | car :: cdr -> (f car) && (andmap f cdr);;	  

let lowercase_ascii  =
  let delta = int_of_char 'A' - int_of_char 'a' in
  fun ch ->
  if ('A' <= ch && ch <= 'Z')
  then char_of_int ((int_of_char ch) - delta)
  else ch;;

let string_to_list str =
  let rec loop i limit =
    if i = limit then []
    else (String.get str i) :: (loop (i + 1) limit)
  in
  loop 0 (String.length str);;

let list_to_string s =
  String.concat "" (List.map (fun ch -> String.make 1 ch) s);;

module PC = struct

(* the parsing combinators defined here *)
  
exception X_not_yet_implemented;;

exception X_no_match;;

let const pred =
  function 
  | [] -> raise X_no_match
  | e :: s ->
     if (pred e) then (e, s)
     else raise X_no_match;;

let caten nt1 nt2 s =
  let (e1, s) = (nt1 s) in
  let (e2, s) = (nt2 s) in
  ((e1, e2), s);;

let pack nt f s =
  let (e, s) = (nt s) in
  ((f e), s);;

let nt_epsilon s = ([], s);;

let caten_list nts =
  List.fold_right
    (fun nt1 nt2 ->
     pack (caten nt1 nt2)
	  (fun (e, es) -> (e :: es)))
    nts
    nt_epsilon;;

let disj nt1 nt2 =
  fun s ->
  try (nt1 s)
  with X_no_match -> (nt2 s);;

let nt_none _ = raise X_no_match;;
  
let disj_list nts = List.fold_right disj nts nt_none;;

let delayed thunk s =
  thunk() s;;

let nt_end_of_input = function
  | []  -> ([], [])
  | _ -> raise X_no_match;;

let rec star nt s =
  try let (e, s) = (nt s) in
      let (es, s) = (star nt s) in
      (e :: es, s)
  with X_no_match -> ([], s);;

let plus nt =
  pack (caten nt (star nt))
       (fun (e, es) -> (e :: es));;

let guard nt pred s =
  let ((e, _) as result) = (nt s) in
  if (pred e) then result
  else raise X_no_match;;
  
let diff nt1 nt2 s =
  match (let result = nt1 s in
	 try let _ = nt2 s in
	     None
	 with X_no_match -> Some(result)) with
  | None -> raise X_no_match
  | Some(result) -> result;;

let not_followed_by nt1 nt2 s =
  match (let ((_, s) as result) = (nt1 s) in
	 try let _ = (nt2 s) in
	     None
	 with X_no_match -> (Some(result))) with
  | None -> raise X_no_match
  | Some(result) -> result;;
	  
let maybe nt s =
  try let (e, s) = (nt s) in
      (Some(e), s)
  with X_no_match -> (None, s);;

(* useful general parsers for working with text *)

let make_char equal ch1 = const (fun ch2 -> equal ch1 ch2);;

let char = make_char (fun ch1 ch2 -> ch1 = ch2);;

let char_ci =
  make_char (fun ch1 ch2 ->
	     (lowercase_ascii ch1) =
	       (lowercase_ascii ch2));;

let make_word char str = 
  List.fold_right
    (fun nt1 nt2 -> pack (caten nt1 nt2) (fun (a, b) -> a :: b))
    (List.map char (string_to_list str))
    nt_epsilon;;

let word = make_word char;;

let word_ci = make_word char_ci;;

let make_one_of char str =
  List.fold_right
    disj
    (List.map char (string_to_list str))
    nt_none;;

let one_of = make_one_of char;;

let one_of_ci = make_one_of char_ci;;

let nt_whitespace = const (fun ch -> ch <= ' ');;

let make_range leq ch1 ch2 (s : char list) =
  const (fun ch -> (leq ch1 ch) && (leq ch ch2)) s;;

let range = make_range (fun ch1 ch2 -> ch1 <= ch2);;

let range_ci =
  make_range (fun ch1 ch2 ->
	      (lowercase_ascii ch1) <=
		(lowercase_ascii ch2));;

let nt_any (s : char list) = const (fun ch -> true) s;;

let trace_pc desc nt s =
  try let ((e, s') as args) = (nt s)
      in
      (Printf.printf ";;; %s matched the head of \"%s\", and the remaining string is \"%s\"\n"
		     desc
		     (list_to_string s)
		     (list_to_string s') ;
       args)
  with X_no_match ->
    (Printf.printf ";;; %s failed on \"%s\"\n"
		   desc
		   (list_to_string s) ;
     raise X_no_match);;

(* testing the parsers *)

let test_string nt str =
  let (e, s) = (nt (string_to_list str)) in
  (e, (Printf.sprintf "->[%s]" (list_to_string s)));;

end;; (* end of struct PC *)

(* end-of-input *)

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~END PC.ml~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

 #use "pc.ml";;

 exception X_not_yet_implemented;;
 exception X_this_should_not_happen;;
   
 type number =
   | Int of int
   | Float of float;;
   
 type sexpr =
   | Bool of bool
   | Nil
   | Number of number
   | Char of char
   | String of string
   | Symbol of string
   | Pair of sexpr * sexpr
   | Vector of sexpr list;;
 


 let rec sexpr_eq s1 s2 =
   match s1, s2 with
   | Bool(b1), Bool(b2) -> b1 = b2
   | Nil, Nil -> true
   | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
   | Number(Int n1), Number(Int n2) -> n1 = n2
   | Char(c1), Char(c2) -> c1 = c2
   | String(s1), String(s2) -> s1 = s2
   | Symbol(s1), Symbol(s2) -> s1 = s2
   | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
   | Vector(l1), Vector(l2) -> List.for_all2 sexpr_eq l1 l2
   | _ -> false;;

  

module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end

= struct

  let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;
  

     
  let lowercase_ascii_help  =
    let delta = int_of_char 'A' - int_of_char 'a' in
    fun ch ->
    if ('A' <= ch && ch <= 'Z')
    then char_of_int ((int_of_char ch) - delta)
    else ch;;

   let _space_ =    
    PC.const (fun ch -> ch <= ' ');;
  
  let make_enclosed _l_ _p_ _r_ =
    let _enclosed_ = PC.caten (PC.caten _l_ _p_) _r_ in
    PC.pack _enclosed_ (fun ((l, p), r) -> p);;
    
  let make_spaced _p_ = 
    let _st_space_ = PC.star _space_ in
    make_enclosed _st_space_ _p_ _st_space_;;

    let make_enclosed_left _l_ _p_  =
      let _enclosed_ =  (PC.caten _l_ _p_)  in
      PC.pack _enclosed_ (fun ((l, p)) -> p);;

    let make_spaced_from_left _p_ = 
      let _st_space_ = PC.star _space_ in
      make_enclosed_left _st_space_ _p_ ;;
  
  let _hashSymbol_ =
    PC.char '#';;

  let _boolean_ = make_spaced (PC.caten _hashSymbol_ (PC.one_of_ci "tf"));;

  let correct_boolean e = 
    let ( symbol , be) = e in         
    if (be = 't' || be ='T') then Bool(true)
    else if (be = 'f' || be ='F') then Bool(false)
    else raise PC.X_no_match;;  

  

    let make_sign =PC.maybe (PC.one_of "+-");;
   
  
    let nt_e = PC.caten (PC.one_of_ci "e") ( PC.caten make_sign (PC.plus (PC.one_of "0123456789")));;
    
      let nt_HexInteger = PC.caten (_hashSymbol_) ((PC.caten (PC.caten (PC.char_ci 'x')
                                                              (make_sign))
                                                    (PC.plus (PC.one_of_ci "0123456789abcdef"))));;
    
      let nt_decimal = PC.caten make_sign (PC.plus (PC.one_of "0123456789"));;
    
      let nt_integer= make_spaced (PC.caten (PC.disj (nt_HexInteger) (PC.pack nt_decimal (fun ((a,b)) -> '#' ,(('d',a), b)  ))) (PC.maybe nt_e));;
    
    let build_integer opt numberList = int_of_string (String.concat  "" [opt ; list_to_string numberList]) ;;
    
  
    
    let make_hex_number sign num = 
      match sign with
      | Some c -> if c = '-' then -1 * build_integer "0x" num
                  else build_integer "0x" num
      |None -> build_integer "0x" num;;
    
    let make_decimal_number sign num =
      match sign with
      | Some c -> if c = '-' then  (-1 * build_integer "" num)
                  else build_integer "" num
      |None -> build_integer "" num ;;
    
    (*this is a help function for make integer*)
let helpNumber (opt, sign) num = if opt = 'x' || opt = 'X' then make_hex_number sign num
                                  else make_decimal_number sign num ;;
let correct_integer sign num rest = 
      (Number(Int(helpNumber sign num)),rest);;


let correct_e sign num = 
  let n = make_decimal_number sign num in
  Number(Float(10. ** float_of_int n)) ;;

let mul_number num1  num2 = 
  match num1, num2 with
  |Number(Int(n1)), Number(Float(n2))-> Number(Float((float_of_int n1)*.n2))
  |Number(Float(n1)),Number(Float(n2))-> Number(Float(n1*.n2))
  |_->raise X_this_should_not_happen;;

  let make_integer = 
    fun s ->
    let (((_, (e, num)), some_e), rest) = (nt_integer s) in
    match some_e with 
    |Some (_,(sign,e_num))-> let (num3,_)= correct_integer e num rest in
                                
                                  ((mul_number (num3) (correct_e sign e_num)),rest)

    |None->   correct_integer e num rest;;

    
let disj_sexpr p1 p2 = 
  fun s ->
  try p1  s
  with PC.X_no_match -> p2  s;;

(*let nt_none _ = raise X_no_match;;*)
  
let disj_sexpr_list ps = List.fold_right disj_sexpr ps PC.nt_none;;

let decimal_point = 
  PC.char '.';;

let nt_right_side_floating_point = PC.caten decimal_point (PC.plus (PC.one_of "0123456789"));;

let nt_floating_point= make_spaced (PC.caten (PC.caten nt_decimal nt_right_side_floating_point) (PC.maybe nt_e));;

let charList_to_left_number b charList minus = List.fold_left (fun num acc -> b *. num +. acc ) 0.0 (List.map (fun x->  float_of_int((int_of_char x)-(int_of_char minus)) ) charList) ;;
let charList_to_right_number b charList minus = (List.fold_right (fun num acc ->   num  +. acc/.b )  (List.map (fun x-> float_of_int((int_of_char x)-(int_of_char minus)) ) charList) 0.0)/. b;;

let makeLeftSide left =  charList_to_left_number left;;
let makeRightSide right= charList_to_right_number right;; 
let catenFloat left right = (makeLeftSide 10.0 left '0') +. (makeRightSide  10.0 right '0');;

let build_float sign left right= 
  match sign with
  | None -> catenFloat left right
  | Some nOp -> if nOp = '+' then catenFloat left right
                else if nOp = '-' then (-1.0 *. (catenFloat left right))
                else raise PC.X_no_match;;

(*need to check about zeros after decimal point like -102.000000000000001*)
let correct_floating_point sign left_num right_num s = 
     (Number(Float(build_float sign (List.map lowercase_ascii left_num) (List.map lowercase_ascii right_num))),s);;
    

let make_floating_point = 
  fun s->
  let ( (((sign, left_num), (dot,right_num)), some_e) , rest ) = (nt_floating_point s) in
  match some_e with 
  |Some (_,(sign_e,e_num))-> let (num3,_)= correct_floating_point sign left_num right_num rest in
                              
                                ((mul_number (num3) (correct_e sign_e e_num)),rest)

  |None->    correct_floating_point sign left_num right_num rest;;
  
  

 let nt_right_side_hex_floating_point = PC.caten decimal_point (PC.plus (PC.one_of_ci "0123456789abcdef"));;

 let nt_HexFloat= make_spaced (PC.caten nt_HexInteger nt_right_side_hex_floating_point);;

 
 let concat_hex left right= String.concat "" ["0x" ; (list_to_string left) ; "." ; (list_to_string right)];; 
 let catenFloat_hex left right = float_of_string (concat_hex left right) ;;
 
 let build_float_hex sign left right= 
   match sign with
   | None -> catenFloat_hex left right
   | Some nOp -> if nOp = '+' then catenFloat_hex left right
                 else if nOp = '-' then (-1.0 *. (catenFloat_hex left right))
                 else raise PC.X_no_match;;
 
               
 let make_HexFloat= 
  fun s->
  let (((hash, ((x, sign), left_Hexnumber)), (dot, right_Hexnumber)), s) = (nt_HexFloat s) in
  ((Number(Float(build_float_hex  sign left_Hexnumber right_Hexnumber))),s);;




let nt_symbol =  make_spaced (PC.plus (PC.one_of_ci "abcdefghijklmnopqrstuvwxyz0123456789!?$+*/-=^<>_:"));;

 let correct_symbol symbol s = 
  (Symbol(list_to_string (List.map lowercase_ascii symbol )),s);;

 


  let nt_slash = PC.char '\\';;
  let nt_x = PC.char_ci 'x';;

  let nt_CharPrefix = PC.caten _hashSymbol_ nt_slash;;
  let nt_VisibleSimpleChar =make_spaced (PC.caten nt_CharPrefix (PC.diff PC.nt_any PC.nt_whitespace));;
  let nt_NamedChar = make_spaced (PC.caten nt_CharPrefix (PC.disj_list [(PC.word_ci "newline"); (PC.word_ci "nul"); (PC.word_ci "page"); (PC.word "return"); (PC.word_ci "space"); (PC.word "tab");(PC.word "double quote");(PC.word_ci "\\\\");(PC.word "\"");(PC.word_ci "f"); (PC.word "t"); (PC.word_ci "r"); (PC.word_ci "n")] ));;
  let nt_HexChar= make_spaced (PC.caten nt_CharPrefix (PC.caten nt_x (PC.plus (PC.one_of_ci "0123456789abcdef")))) ;;
  


  let make_VisibleSimpleChar = 
    fun s->
    let (e,s) = (nt_VisibleSimpleChar s) in
      let(prefix,c) = e in
      (Char(c),s);;
      

let correct_char ascii = Char(Char.chr ascii);; 


let build_NamedChar e s =
  let (prefix,namedChar) = e in
  match  list_to_string (List.map (fun x -> (lowercase_ascii_help x)) namedChar) with
  |"newline"  -> (correct_char 010 ,s)
  |"n" ->   (correct_char 010 ,s)
  |"page" -> (correct_char 012 ,s)
  |"f" -> (correct_char 012 ,s)
  |"return" -> (correct_char 013 ,s)
  |"r"-> (correct_char 013 ,s)
  |"tab" ->(correct_char 009 ,s)
  |"t"->(correct_char 009 ,s)
  |"backslash" ->(correct_char 092 ,s)
  |"\\"->(correct_char 092 ,s)
  |"double qoute" ->(correct_char 034 ,s)
  |"\"" ->(correct_char 034 ,s)
  |"nul" ->(correct_char 000 ,s)
  |"space" ->(correct_char 032 ,s)
  | _-> raise PC.X_no_match;;

let make_NamedChar =
  fun s ->
  let (e,s)= (nt_NamedChar s) in 
  build_NamedChar e s;;


  let make_HexChar = 
    fun s->
    let ((_, (x, hex_num)), rest)= (nt_HexChar s) in
    let char_val=   Char.chr ((int_of_string (String.concat  "" ["0x" ; list_to_string hex_num])))in
      (Char(char_val),rest);;

    




let nt_semicolon= PC.char ';';; 
  
  let nt_slash_x =  PC.caten nt_slash (nt_x);;
  
  let nt_StringHexChar = ( PC.caten (PC.caten nt_slash_x (PC.plus (PC.one_of_ci "0123456789abcdef"))) nt_semicolon);;
  
  let nt_StringMetaChar =  (PC.disj_list [(PC.word "\\\"");(PC.word "\\\\"); (PC.word_ci "\\t");(PC.word_ci "\\f");(PC.word_ci "\\n");(PC.word_ci "\\r")] );;  
  let nt_StringLiteralChar = (PC.diff PC.nt_any (PC.one_of "\\\""));;

nt_StringMetaChar (string_to_list "\\\"");;
  let make_StringHexChar=
    fun s->
    let (e,s)= (nt_StringHexChar s) in
    let ((prefix, hexNumber), semicolon) = e in
    let string_val= Char.chr ((int_of_string (String.concat  "" ["0x" ; list_to_string hexNumber])))in   
    ([string_val],s);;

  let make_StringLiteralChar= 
    fun s->
   
    let (e,s)= (nt_StringLiteralChar s) in
     ([e],s);;

     

     let build_StringMetaChar e s =
      match list_to_string (List.map (fun x -> (lowercase_ascii_help x)) e) with 
      |"\\n" -> (['\n'],s)
      |"\\f" -> ([Char.chr 012],s)
      |"\\r"-> (['\r'],s)
      |"\\t"->(['\t'],s)
      |"\\\"" ->(['\"'],s)
      |"\\\\" -> (['\\'],s) 
      |_-> ([],s);;

  let make_StringMetaChar = 
    fun s->
    let (e,s)= (nt_StringMetaChar s) in
    build_StringMetaChar e s;;

   


  let nt_StringChar= PC.disj_list [make_StringHexChar; make_StringMetaChar ; make_StringLiteralChar];;

  let nt_doubleQuote= PC.char '"';;

  let nt_String=  make_spaced (PC.caten nt_doubleQuote  (PC.caten ((PC.star nt_StringChar)) nt_doubleQuote)) ;;
  
let build_string e = 
  let (q_1, (sen, q_2)) = e in
  String (String.concat "" [list_to_string (List.map (fun l -> (List.nth l 0)) sen)]);;




  let nt_endOfLine = 
     PC.char '\n' ;;
     

  let nt_commentLine = make_spaced( PC.caten nt_semicolon 
                      (PC.star (PC.diff PC.nt_any (PC.disj PC.nt_end_of_input (PC.pack nt_endOfLine (fun s->[]))))));;


  
  let nt_Nil= make_spaced (PC.caten_list [PC.char '('; (PC.pack (PC.star (PC.disj_list [_space_ ; (PC.pack nt_commentLine (fun s-> 's'))])) (fun s-> 'e' )); PC.char ')']);;

  let rec nt_sexpr_three_dotted = 
    function 
     |_->PC.pack (PC.caten (PC.star (PC.disj make_commentLineD make_SexprComemntD)) (PC.caten (PC.disj_list [make_emptyD;make_NilD;make_booleanD; make_CharD; make_NumberD; make_StringD ; make_symbolD;  make_DottedlistD;make_listD;  make_vectorD;make_QuotedD;make_QQuotedD;make_UnquotedD;make_UnquotedSplicedD] ) (PC.star (PC.disj make_commentLineD make_SexprComemntD)))) 
     (fun (nil1,(sexpr,nil2)) -> sexpr)
 
     and make_NilD = 
       fun s->
       let (e,s) = (nt_Nil s) in
        (Nil,s)
   
   
   and make_emptyD= 
     fun s-> 
     match s with
     |[]->(Nil,[])
     |_->raise PC.X_no_match


     and make_StringD =
       fun s->
       let (e,s)=  (nt_String s) in
        ((build_string e),s)

   and make_CharD = PC.disj_list [make_NamedChar;  make_HexChar; make_VisibleSimpleChar ]

   and make_symbolD = 
       fun s->
       let ( e , rest ) = (nt_symbol s) in

        correct_symbol e rest

   and make_NumberD= PC.disj_list [make_floating_point; make_HexFloat;make_integer]

   and make_booleanD = 
       fun s->
       let (e , s) = (_boolean_ s) in 
       (correct_boolean e,s)

       and make_SexprComemntD = 
       fun s->
       let nt_se=make_spaced (PC.word "#;") in
       let (e,s) = nt_se s in
       let (void,rest) = nt_sexpr_three_dotted 's' s in 
       Nil,rest
       (*match void,rest with
       |_, ')'::e -> Nil,rest
       |_, ']'::e -> Nil,rest
       |_, '.'::e -> Nil,rest
       |_,[]-> Nil,[]
       |Nil, s -> (nt_sexpr 's' (List.concat [['#';';'];s]))
       |_,t-> (nt_sexpr 's' t)*)
       
       and make_commentLineD = 
       fun s ->
         let (_,s1) = (nt_commentLine s) in
         Nil,s1
   
       (*  match s1 with
         |[]->Nil,[]
         |')'::e -> Nil,s1
         |']'::e -> Nil,s1
         |'.'::e -> Nil,s1
         |_-> nt_sexpr 's' s1*)
    and make_listD =
     fun s->
     let nt_list= make_spaced (PC.caten (PC.char '(') (PC.caten (PC.star (nt_sexpr_three_dotted 's')) (PC.maybe(PC.char ')')))) in
     let nt_square_list=make_spaced (PC.caten (PC.char '[') (PC.caten (PC.star (nt_sexpr_three_dotted 's')) (PC.maybe(PC.char ']')))) in
     let nt_sqOrCy= PC.disj_list [nt_list; nt_square_list] in
     let ((left, (list_s, right)),s)= (nt_sqOrCy s) in
     ((List.fold_right  (fun sexp1 sexp2 ->  Pair(sexp1,sexp2))  ( list_s)  Nil)  ,s) ;
     
     and make_DottedlistD =
     fun s->
     let nt_DottedList= make_spaced (PC.caten (PC.char '(') (PC.caten (PC.plus (nt_sexpr_three_dotted 's')) (PC.caten (PC.char '.') (PC.caten (nt_sexpr_three_dotted 's') (PC.maybe(PC.char ')')))))) in
     let nt_square_DottedList= make_spaced (PC.caten (PC.char '[') (PC.caten (PC.plus (nt_sexpr_three_dotted 's')) (PC.caten (PC.not_followed_by (PC.char '.') (PC.char '.')) (PC.caten (nt_sexpr_three_dotted 's') (PC.maybe(PC.char ']')))))) in
     let nt_DottedSqOrCy= PC.disj_list [nt_DottedList; nt_square_DottedList] in
     let ((left, (list_s,( dot, (sexpr,right)))),s)= (nt_DottedSqOrCy s) in
     ((List.fold_right  (fun sexp1 sexp2 -> Pair(sexp1,sexp2))  ( list_s)  (sexpr))  ,s) ;
     
     and make_vectorD = 
     fun s->
     let nt_vector= make_spaced (PC.caten _hashSymbol_ (PC.caten (PC.char '(') (PC.caten (PC.star (nt_sexpr_three_dotted 's')) (PC.maybe(PC.char ')'))))) in
     let ((hash,(left, (list_s, right))),s1) = (nt_vector s) in
       (Vector(list_s),s1) ;
     
      and make_QuotedD = 
     fun s -> 
     let nt_q1 = PC.word  "'" in
     let nt_Quoted = PC.caten nt_q1 (nt_sexpr_three_dotted 'w')  in
     let (sym_sexp,rest ) = (nt_Quoted s) in
       let (name,sexpr)= sym_sexp in
         (Pair(Symbol("quote"), Pair(sexpr, Nil)),rest) ;
     
         and make_QQuotedD = 
     fun s -> 
     let nt_q2= PC.word "`" in
     let nt_QQuoted = PC.caten nt_q2 (nt_sexpr_three_dotted 'w')  in
     let (sym_sexp,rest ) = (nt_QQuoted s) in
       let (name,sexpr)= sym_sexp in
         (Pair(Symbol("quasiquote"), Pair(sexpr, Nil)),rest) ;
     and make_UnquotedSplicedD = 
     fun s -> 
     let nt_q3= PC.word  ",@" in
     let nt_UnquotedSpliced = PC.caten nt_q3 (nt_sexpr_three_dotted 'w') in
     let (sym_sexp,rest ) = (nt_UnquotedSpliced s) in
       let (name,sexpr)= sym_sexp in
         (Pair(Symbol("unquote-splicing"), Pair(sexpr, Nil)),rest) ;
     and make_UnquotedD = 
     fun s -> 
     let nt_q4= PC.word  "," in
     let nt_Unquoted = PC.caten nt_q4 (nt_sexpr_three_dotted 'w' ) in
     let (sym_sexp,rest ) = (nt_Unquoted s) in
       let (name,sexpr)= sym_sexp in
         (Pair(Symbol("unquote"), Pair(sexpr, Nil)),rest);;


         let three_dots= make_spaced (PC.word "...");;
     
     let rec nt_sexpr = 
     function
      |_->PC.pack (PC.caten (PC.star (PC.disj make_commentLine make_SexprComemnt)) (PC.caten (PC.disj_list [make_empty;make_Nil;make_boolean; make_Char; make_Number; make_String ; make_symbol;  make_list; make_Dottedlist; make_vector;make_Quoted;make_QQuoted;make_Unquoted;make_UnquotedSpliced] ) (PC.star (PC.disj make_commentLine make_SexprComemnt)))) 
                        (fun (  (nil1 , ( sexpr , nil2 ) )) ->  sexpr)
  
      and make_Nil = 
        fun s->
        let (e,s) = (nt_Nil s) in
         (Nil,s)
    
    
    and make_empty= 
      fun s-> 
      match s with
      |[]->(Nil,[])
      |_->raise PC.X_no_match


      and make_String =
        fun s->
        let (e,s)=  (nt_String s) in
         ((build_string e),s)

    and make_Char = PC.disj_list [make_NamedChar;  make_HexChar; make_VisibleSimpleChar ]

    and make_symbol = 
        fun s->
        let ( e , rest ) = (nt_symbol s) in

         correct_symbol e rest

    and make_Number= PC.disj_list [make_floating_point; make_HexFloat;make_integer]

    and make_boolean = 
        fun s->
        let (e , s) = (_boolean_ s) in 
        (correct_boolean e,s)

    and make_SexprComemnt = 
    fun s->
    let nt_se=make_spaced (PC.word "#;") in
    let (e,s) = nt_se s in
    let (void,rest) = nt_sexpr 's' s in 
    Nil,rest
    (*match void,rest with
    |_, ')'::e -> Nil,rest
    |_, ']'::e -> Nil,rest
    |_, '.'::e -> Nil,rest
    |_,[]-> Nil,[]
    |Nil, s -> (nt_sexpr 's' (List.concat [['#';';'];s]))
    |_,t-> (nt_sexpr 's' t)*)
    
    and make_commentLine = 
    fun s ->
      let (_,s1) = (nt_commentLine s) in
      Nil,s1

    (*  match s1 with
      |[]->Nil,[]
      |')'::e -> Nil,s1
      |']'::e -> Nil,s1
      |'.'::e -> Nil,s1
      |_-> nt_sexpr 's' s1*)

     and make_list =
      fun s->

      let nt_list= make_spaced((PC.disj  (PC.caten (PC.char '(') (PC.caten (PC.star (nt_sexpr_three_dotted 's')) (three_dots)))) (PC.caten (PC.char '(') (PC.caten (PC.star (nt_sexpr 's')) (PC.word ")"))) ) in
      let nt_square_list=make_spaced (PC.disj (PC.caten (PC.char '[') (PC.caten (PC.star (nt_sexpr_three_dotted 's')) (three_dots))) (PC.caten (PC.char '[') (PC.caten (PC.star (nt_sexpr 's')) (PC.word "]"))) ) in
      let nt_sqOrCy= PC.disj_list [nt_list; nt_square_list] in
      let ((left, (list_s, right)),s)= (nt_sqOrCy s) in
      ((List.fold_right  (fun sexp1 sexp2 ->  Pair(sexp1,sexp2))  ( list_s)  Nil)  ,s) ;
      and make_Dottedlist =
      fun s->
      let nt_DottedList= make_spaced (PC.disj(PC.caten (PC.char '(') (PC.caten (PC.plus (nt_sexpr_three_dotted 's')) (PC.caten (PC.char '.') (PC.caten (nt_sexpr_three_dotted 's') (three_dots)))))  (PC.caten (PC.char '(') (PC.caten (PC.plus (nt_sexpr 's')) (PC.caten ( (PC.char '.')) (PC.caten (nt_sexpr 's') (PC.word ")")))))  ) in
      let nt_square_DottedList= make_spaced (PC.disj (PC.caten (PC.char '[') (PC.caten (PC.plus (nt_sexpr_three_dotted 's')) (PC.caten (PC.char '.') (PC.caten (nt_sexpr_three_dotted 's') (three_dots))))) (PC.caten (PC.char '[') (PC.caten (PC.plus (nt_sexpr 's')) (PC.caten (PC.not_followed_by (PC.char '.') (PC.char '.')) (PC.caten (nt_sexpr 's') (PC.word "]"))))) ) in
      let nt_DottedSqOrCy= PC.disj_list [nt_DottedList; nt_square_DottedList] in
      let ((left, (list_s,( dot, (sexpr,right)))),s)= (nt_DottedSqOrCy s) in
      
      ((List.fold_right  (fun sexp1 sexp2 -> Pair(sexp1,sexp2))  ( list_s)  (sexpr))  ,s) ;
      and make_vector = 
      fun s->
      let nt_vector= make_spaced (PC.disj (PC.caten _hashSymbol_ (PC.caten (PC.char '(') (PC.caten (PC.star (nt_sexpr_three_dotted 's')) (three_dots)))) (PC.caten _hashSymbol_ (PC.caten (PC.char '(') (PC.caten (PC.star (nt_sexpr 's')) (PC.word ")")))) ) in
      let ((hash,(left, (list_s, right))),s1) = (nt_vector s) in
        (Vector(list_s),s1) ;
      and make_Quoted = 
      fun s -> 
      let nt_q1 = PC.word  "'" in
      let nt_Quoted = PC.caten nt_q1 (nt_sexpr 'w')  in
      let (sym_sexp,rest ) = (nt_Quoted s) in
        let (name,sexpr)= sym_sexp in
          (Pair(Symbol("quote"), Pair(sexpr, Nil)),rest) ;
      and make_QQuoted = 
      fun s -> 
      let nt_q2= PC.word "`" in
      let nt_QQuoted = PC.caten nt_q2 (nt_sexpr 'w')  in
      let (sym_sexp,rest ) = (nt_QQuoted s) in
        let (name,sexpr)= sym_sexp in
          (Pair(Symbol("quasiquote"), Pair(sexpr, Nil)),rest) ;
      and make_UnquotedSpliced = 
      fun s -> 
      let nt_q3= PC.word  ",@" in
      let nt_UnquotedSpliced = PC.caten nt_q3 (nt_sexpr 'w') in
      let (sym_sexp,rest ) = (nt_UnquotedSpliced s) in
        let (name,sexpr)= sym_sexp in
          (Pair(Symbol("unquote-splicing"), Pair(sexpr, Nil)),rest) ;
      and make_Unquoted = 
      fun s -> 
      let nt_q4= PC.word  "," in
      let nt_Unquoted = PC.caten nt_q4 (nt_sexpr 'w' ) in
      let (sym_sexp,rest ) = (nt_Unquoted s) in
        let (name,sexpr)= sym_sexp in
          (Pair(Symbol("unquote"), Pair(sexpr, Nil)),rest);;


let build_list listOflist  = List.filter (fun list-> (List.length list != 1) || ( List.hd list != '(' && List.hd list != ')' && List.hd list != '.')) listOflist;;


  
 
let read_sexprs string = 
  let charList = (string_to_list string) in

  let rec sexpr_rec charlist sexprList =  
    match charlist with
  |[]-> [Nil]
  |s-> (make_sexpr_rec s sexprList) 
  

  and make_sexpr_rec rest sexprList =
  
  let (e,s) = (nt_sexpr 's' rest) in 
  match s with 
  |[] -> List.concat [sexprList;[e]]
  |t -> (sexpr_rec t (List.concat [sexprList;[e]])) in match string with | ""-> []
                                                                         |_->(sexpr_rec charList []);;

let read_sexpr string = 
  try let list1 = read_sexprs string
  in
  if (List.length list1 = 1) then (List.hd list1)
  else if (List.length list1 = 0) then Nil
  else raise X_this_should_not_happen  
  with PC.X_no_match -> raise PC.X_no_match ;;



 
end;; (* struct Reader *)



