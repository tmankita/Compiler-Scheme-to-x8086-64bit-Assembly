
(*--------------------------pc.ml--------------------------------------------------------*)
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



(*--------------------------end pc.ml-----------------------------------------------------*)


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
   | Number(n1), Number(n2) -> n1 = n2
   | Char(c1), Char(c2) -> c1 = c2
   | String(s1), String(s2) -> s1 = s2
   | Symbol(s1), Symbol(s2) -> s1 = s2
   | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
   | Vector(l1), Vector(l2) -> List.for_all2 sexpr_eq l1 l2
   | _ -> false;;
   
   int_of_char 'c' - int_of_char 'W';; 
 let charList_to_left_number b charList minus = List.fold_left (fun num acc -> b *. num +. acc ) 0.0 (List.map (fun x->  float_of_int((int_of_char x)-(int_of_char minus)) ) charList) ;;
 let charList_to_right_number b charList minus = (List.fold_right (fun num acc ->   num  +. acc/.b )  (List.map (fun x-> float_of_int((int_of_char x)-(int_of_char minus)) ) charList) 0.0)/. b;;
 
  let _space_ =       (*add more kind of spaces*)
    PC.const (fun ch -> ch <= ' ');;
  
  let make_enclosed _l_ _p_ _r_ =
    let _enclosed_ = PC.caten (PC.caten _l_ _p_) _r_ in
    PC.pack _enclosed_ (fun ((l, p), r) -> p);;
    
  let make_spaced _p_ = 
    let _st_space_ = PC.star _space_ in
    make_enclosed _st_space_ _p_ _st_space_;;
  
  let _hashSymbol_ =
    PC.char '#';;

  let _boolean_ = (make_spaced (PC.caten _hashSymbol_ (PC.one_of_ci "tf")));;

  let correct_boolean e = 
    let ( symbol , be) = e in         
    if (be = 't' || be ='T') then Bool(true)
    else if (be = 'f' || be ='F') then Bool(false)
    else raise PC.X_no_match;;  

  let make_boolean = 
    fun s->
    let (e , s) = (_boolean_ s) in
    match s with 
    | [] -> correct_boolean e
    | head:: tail -> 
        if head <= ' ' then correct_boolean e
        else raise PC.X_no_match ;;
      

  let make_sign =PC.maybe (PC.one_of "+-");;
     
  let nt_HexInteger = PC.caten (_hashSymbol_) ((PC.caten (PC.caten (PC.char_ci 'x')
                                                          (make_sign))
                                                (PC.plus (PC.one_of_ci "0123456789abcdef"))));;

  let nt_decimal = PC.caten make_sign (PC.plus (PC.one_of "0123456789"));;

  let nt_integer= make_spaced (PC.disj (nt_HexInteger) (PC.pack nt_decimal (fun ((a,b)) -> '#' ,(('d',a), b)  )));;

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
  let correct_integer e = 
    let (symbol , rest) = e in
    let (e , num ) = rest in
        Number(Int(helpNumber e num));;
    
  let make_integer = 
    fun s ->
    let (e, rest) = (nt_integer s) in
    match rest with 
    | [] -> correct_integer e
    | head:: tail -> 
    if head <= ' ' then correct_integer e
    else raise PC.X_no_match ;;

    make_integer (string_to_list "0000000003");;
    
let disj_sexpr p1 p2 =
  fun s ->
  try p1  s
  with PC.X_no_match -> p2  s;;

(*let nt_none _ = raise X_no_match;;*)
  
let disj_sexpr_list ps = List.fold_right disj_sexpr ps PC.nt_none;;

let decimal_point = 
  PC.char '.';;

let nt_right_side_floating_point = PC.caten decimal_point (PC.plus (PC.one_of "0123456789"));;

let nt_floating_point= make_spaced PC.(PC.caten nt_decimal nt_right_side_floating_point);;

nt_floating_point (string_to_list "5a.34");;

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
let correct_floating_point e = 
  let (left_side, right_side) = e in
   let (sign, left_num) = left_side in
    let (point, right_num) = right_side in
     Number(Float(build_float sign (List.map lowercase_ascii left_num) (List.map lowercase_ascii right_num)));;
    

let make_floating_point = 
  fun s->
  let ( e , rest ) = (nt_floating_point s) in
  match rest with 
  | [] -> correct_floating_point e
  | head:: tail -> if head <= ' ' then correct_floating_point e
                    else raise PC.X_no_match ;;
  

 let nt_right_side_hex_floating_point = PC.caten decimal_point (PC.plus (PC.one_of_ci "0123456789abcdef"));;

 let nt_HexFloat=  make_spaced( PC.caten (PC.caten nt_HexInteger nt_right_side_hex_floating_point) PC.nt_end_of_input);;

 
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
  let ((((hash, ((x, sign), left_Hexnumber)), (dot, right_Hexnumber)), nil2), nil1) = (nt_HexFloat s) in
  Number(Float(build_float_hex  sign left_Hexnumber right_Hexnumber));;


let make_Number= PC.disj_list [make_integer ; make_floating_point ; make_HexFloat];;

let nt_symbol = make_spaced  (PC.plus (PC.one_of_ci "abcdefghijklmnopqrstuvwxyz0123456789!?$+*/-=^<>_"));;

 let correct_symbol symbol = 
  Symbol(list_to_string (List.map lowercase_ascii symbol ));;

 let make_symbol = 
  fun s->
  let ( e , rest ) = (nt_symbol s) in
  match rest with 
  | [] -> correct_symbol e
  | head:: tail -> if head <= ' ' then correct_symbol e
                    else raise PC.X_no_match ;;


  let nt_slash = PC.char '\\';;
  let nt_x = PC.char 'x';;

  let nt_CharPrefix = PC.caten _hashSymbol_ nt_slash;;
  let nt_VisibleSimpleChar = PC.caten (PC.caten nt_CharPrefix (PC.diff PC.nt_any PC.nt_whitespace)) PC.nt_end_of_input;;
  let nt_NamedChar =PC.caten (PC.caten nt_CharPrefix (PC.disj_list [(PC.word "newline"); (PC.word "nul"); (PC.word "page"); (PC.word "return"); (PC.word "space"); (PC.word "tab");(PC.word "double quote");(PC.word "\\");(PC.word "\"");(PC.word "f"); (PC.word "t"); (PC.word "r"); (PC.word "n")] )) PC.nt_end_of_input;;
  let nt_HexChar= PC.caten (PC.caten nt_CharPrefix (PC.caten nt_x  (PC.one_of_ci "0123456789abcdef"))) PC.nt_end_of_input;;
  


  let make_VisibleSimpleChar = 
    fun s->
    let (e,s) = (nt_VisibleSimpleChar s) in
    let (e,s) = e in
      let(prefix,c) = e in
        Char(c);;
let correct_char ascii = Char(Char.chr ascii);; 

let make_NamedChar =
  fun s ->
  let (e,s)= (nt_NamedChar s) in
  let (e,s)= e in
  let (prefix,namedChar) = e in
  match  list_to_string namedChar with
  | "newline"  -> correct_char 010
  |"n" -> correct_char 010
  |"page" -> correct_char 012
  | "f" -> correct_char 012
  |"return" -> correct_char 013
  |"r"-> correct_char 013
  |"tab" ->correct_char 009
  |"t"->correct_char 009
  |"backslash" ->correct_char 092
  |"\\"->correct_char 092
  |"double qoute" ->correct_char 034
  |"\"" ->correct_char 034
  |"nul" ->correct_char 000
  | _-> Nil;;

 let make_HexChar = 
  fun s->
  let ((e,es),s)= (nt_HexChar s) in
  let (prefix, (x,hexChar))= e in
    Char(hexChar);;


let make_Char = PC.disj_list [make_VisibleSimpleChar; make_HexChar; make_NamedChar];;

let nt_semicolon= PC.char ';';; 
  
  let nt_slash_x =  PC.caten nt_slash (nt_x);;
  
  let nt_StringHexChar =PC.caten (PC.caten nt_slash_x (PC.plus (PC.one_of_ci "0123456789abcdef"))) nt_semicolon;;
  
  let nt_StringMetaChar = PC.disj_list [(PC.word "\\\""); (PC.word "\\\\"); (PC.word "\\\\t");(PC.word "\\\\f");(PC.word "\\\\n");(PC.word "\\\\r")] ;;
  
  let nt_StringLiteralChar = PC.diff PC.nt_any (PC.one_of "\\\"");;

 

   let make_StringHexChar= 
    fun s->
    let (e,s)= (nt_StringHexChar s) in
    let ((prefix, hexNumber), semicolon) = e in
    (hexNumber,s);;

  let make_StringLiteralChar= 
    fun s->
    let (e,s)= (nt_StringLiteralChar s) in
     ([e],s);;
     string_to_list "\"\"\"\"\"";;


  let make_StringMetaChar = 
    fun s->
    let (e,s)= (nt_StringMetaChar s) in
   
    match list_to_string e with
    |"n" -> (['\n'],s)
    |"f" -> ( ['\\';'f'],s)
    |"r"-> (['\r'],s)
    |"t"->(['\t'],s)
    |"\\"->(['\\'],s)
    |"\\\"" ->(['\"'],s)
    |_-> ([],s);;

  let nt_StringChar= PC.disj_list [make_StringHexChar; make_StringMetaChar ; make_StringLiteralChar];;

  let nt_doubleQuote= PC.char '"';;

  let nt_String=PC.caten(PC.caten nt_doubleQuote  (PC.caten (PC.star nt_StringChar) nt_doubleQuote)) PC.nt_end_of_input  ;;

let build_string e = 
  let (q_1, (sen, q_2)) = e in
  String (String.concat "" ["\"";list_to_string (List.map (fun l -> (List.nth l 0)) sen);"\""]);;

  let make_String =
    fun s->
    let (e,s)=  (nt_String s) in
    let (e,s)= e in
     (build_string e);;


  nt_StringChar (string_to_list "a");;
  nt_StringLiteralChar (string_to_list "aba");;
  nt_String (string_to_list "\"a ba\"");;
  make_String (string_to_list "\\\"\\\"\\\"\\\"\\\"");;
     
                 
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

let read_sexpr string = raise X_not_yet_implemented ;;

let read_sexprs string = raise X_not_yet_implemented;;
  
end;; (* struct Reader *)
