(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~else~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
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


  let nt_symbol =  make_spaced ((PC.plus (PC.one_of_ci "abcdefghijklmnopqrstuvwxyz0123456789!?$+*/-=^<>_:")) );;

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
    
      let nt_integer= PC.not_followed_by (make_spaced (PC.caten (PC.disj (nt_HexInteger) (PC.pack nt_decimal (fun ((a,b)) -> '#' ,(('d',a), b)  ))) (PC.maybe nt_e))) (nt_symbol);;
    
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

 let nt_HexFloat= PC.not_followed_by (make_spaced (PC.caten nt_HexInteger nt_right_side_hex_floating_point)) (nt_symbol);;

 
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



 let correct_symbol symbol s = 
  (Symbol(list_to_string (List.map lowercase_ascii symbol )),s);;

 


  let nt_slash = PC.char '\\';;
  let nt_x = PC.char_ci 'x';;

  let nt_CharPrefix = PC.caten _hashSymbol_ nt_slash;;
  let nt_VisibleSimpleChar =make_spaced (PC.caten nt_CharPrefix (PC.diff PC.nt_any PC.nt_whitespace));;
  let nt_NamedChar = make_spaced (PC.caten nt_CharPrefix (PC.disj_list [(PC.word_ci "newline"); (PC.word_ci "nul"); (PC.word_ci "page"); (PC.word_ci "return"); (PC.word_ci "space"); (PC.word_ci "tab");(PC.word_ci "double quote")] ));;
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

  let make_Number= make_spaced( (PC.disj_list [make_floating_point; make_HexFloat;make_integer]) ) ;;



  let nt_endOfLine = 
     PC.char '\n' ;;
     

  let nt_commentLine = make_spaced( PC.caten nt_semicolon 
                      (PC.star (PC.diff PC.nt_any (PC.disj PC.nt_end_of_input (PC.pack nt_endOfLine (fun s->[]))))));;


  
  let nt_Nil= make_spaced (PC.caten_list [PC.char '('; (PC.pack (PC.star (PC.disj_list [_space_ ; (PC.pack nt_commentLine (fun s-> 's'))])) (fun s-> 'e' )); PC.char ')']);;

  let rec nt_sexpr_three_dotted = 
    function 
     |_->PC.pack (PC.caten (PC.star (PC.disj make_commentLineD make_SexprComemntD)) (PC.caten (PC.disj_list [make_emptyD;make_NilD;make_booleanD; make_CharD;  make_Number;  make_symbolD;  make_StringD ;   make_DottedlistD;make_listD;  make_vectorD;make_QuotedD;make_QQuotedD;make_UnquotedD;make_UnquotedSplicedD] ) (PC.star (PC.disj make_commentLineD make_SexprComemntD)))) 
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

   and make_CharD = PC.disj_list [make_NamedChar;  make_HexChar ; make_VisibleSimpleChar ]

   and make_symbolD = 
       fun s->
       let ( e , rest ) = (nt_symbol s) in

        correct_symbol e rest



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
      |_->PC.pack (PC.caten (PC.caten (PC.star (PC.disj make_commentLine make_SexprComemnt)) (PC.caten (PC.disj_list [make_empty;make_Nil;make_boolean; make_Char;make_Number; make_symbol;  make_String ;   make_list; make_Dottedlist; make_vector;make_Quoted;make_QQuoted;make_Unquoted;make_UnquotedSpliced] ) (PC.star (PC.disj make_commentLine make_SexprComemnt)))) (PC.maybe three_dots)) 
                        (fun (  (nil1 , ( sexpr , nil2 ) ), opt ) ->  sexpr)
  


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
      let nt_Quoted = make_spaced((PC.caten nt_q1 (nt_sexpr 'w')))  in
      let (sym_sexp,rest ) = (nt_Quoted s) in
        let (name,sexpr)= sym_sexp in
          (Pair(Symbol("quote"), Pair(sexpr, Nil)),rest) ;
      and make_QQuoted = 
      fun s -> 
      let nt_q2= PC.word "`" in
      let nt_QQuoted = make_spaced(PC.caten nt_q2 (nt_sexpr 'w'))  in
      let (sym_sexp,rest ) = (nt_QQuoted s) in
        let (name,sexpr)= sym_sexp in
          (Pair(Symbol("quasiquote"), Pair(sexpr, Nil)),rest) ;
      and make_UnquotedSpliced = 
      fun s -> 
      let nt_q3= PC.word  ",@" in
      let nt_UnquotedSpliced =make_spaced( PC.caten nt_q3 (nt_sexpr 'w')) in
      let (sym_sexp,rest ) = (nt_UnquotedSpliced s) in
        let (name,sexpr)= sym_sexp in
          (Pair(Symbol("unquote-splicing"), Pair(sexpr, Nil)),rest) ;
      and make_Unquoted = 
      fun s -> 
      let nt_q4= PC.word  "," in
      let nt_Unquoted = make_spaced( PC.caten nt_q4 (nt_sexpr 'w' )) in
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
 
  

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~end-else~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)


#use "semantic-analyser.ml";;
 


let rec make_const_list =
  fun expr'->
  match expr' with
  | Const'(Sexpr(c))->  [c]
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


  let rec remove_duplicates =
    fun sexprList->
  match sexprList with
  |[]->[]
  |car::cdr-> (List.concat [[car];(remove_duplicates (List.filter (fun sexpr-> not(try(sexpr_eq car sexpr) with Invalid_argument _->false)) cdr))]);;

let rec make_topologic =
  fun sexpr->
  match sexpr with
  | Bool(_)->[sexpr]
  | Nil->[sexpr]
  | Number(_)->[sexpr]
  | Char(_)->[sexpr]
  | String(_)->[sexpr]
  | Symbol(_)-> [sexpr]
  | Pair(car,cdr)->  (List.concat [make_topologic car;make_topologic cdr; [sexpr]])
  | Vector(sexprList)->List.flatten (List.map make_topologic sexprList);;
 


  let sort_topologic =
    fun sexprList->
    remove_duplicates(List.flatten (List.map make_topologic sexprList));;

sort_topologic ([Bool(true);Pair(Number(Int(1)),Pair(Number(Int(2)),Nil))]);;

module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> (constant * ('a * string)) list
  val make_fvars_tbl : expr' list -> (string * 'a) list
  val generate : (constant * ('a * string)) list -> (string * 'a) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct
  let make_consts_tbl asts = raise X_not_yet_implemented;;
  let make_fvars_tbl asts = raise X_not_yet_implemented;;
  let generate consts fvars e = raise X_not_yet_implemented;;
end;;

