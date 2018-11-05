
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
   

 let charList_to_number base charList = List.fold_left (fun num acc -> base*num +acc ) 0 (List.map (fun x-> (int_of_char x)-(int_of_char '0') ) charList);;
  
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


  let get1_1 (e1, e2)= e1;;
  let get1_2 (e1, e2)= e2;;

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
      
  make_boolean ['#';'t';' '];;
                              


  let make_sign =PC.maybe (PC.one_of "+-");;
     
  
  let nt_hex = PC.caten (_hashSymbol_) ((PC.caten (PC.caten (PC.char_ci 'x')
                                                          (make_sign))
                                                (PC.plus (PC.one_of_ci "0123456789abcdef"))));;

  let nt_decimal = PC.caten make_sign (PC.plus (PC.one_of "0123456789"));;

   

  let nt_integer= make_spaced (PC.disj (nt_hex) (PC.pack nt_decimal (fun ((a,b)) -> '#' ,(('d',a), b)  )));;

  nt_integer ['-';'1';'a'];;

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
  let make_number (opt, sign) num = if opt = 'x' || opt = 'X' then make_hex_number sign num
                                    else make_decimal_number sign num ;;
  let correct_integer e = 
    let (symbol , rest) = e in
    let (e , num ) = rest in
        Number(Int(make_number e num));;
    
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

let nt_floating_point= make_spaced (PC.caten nt_decimal nt_right_side_floating_point);;

nt_floating_point (string_to_list "5a.34");;

let build_float sign number= 
  match sign with
  | None -> number
  | Some nOp -> if nOp = '+' then number
                else if nOp = '-' then (-1.0 *. number)
                else raise PC.X_no_match;;

(*need to check about zeros after decimal point like -102.000000000000001*)
let correct_floating_point e = 
  let (right_side, left_side) = e in
   let (sign, right_num) = right_side in
    let (point, left_num) = left_side in
     Number(Float(build_float sign (float_of_string (list_to_string (right_num @ point :: left_num)))));;
    

let make_floating_point = 
  fun s->
  let ( e , rest ) = (nt_floating_point s) in
  match rest with 
  | [] -> correct_floating_point e
  | head:: tail -> if head <= ' ' then correct_floating_point e
                    else raise PC.X_no_match ;;
  

 make_floating_point (string_to_list "-102.00000001");;

 let nt_symbol = make_spaced  (PC.plus (PC.one_of_ci "abcdefghijklmnopqrstuvwxyz0123456789!?$+*/-=^<>_"));;

nt_symbol (string_to_list "acl");;

 let correct_symbol symbol = 
  Symbol(list_to_string (List.map lowercase_ascii symbol ));;

 let make_symbol = 
  fun s->
  let ( e , rest ) = (nt_symbol s) in
  match rest with 
  | [] -> correct_symbol e
  | head:: tail -> if head <= ' ' then correct_symbol e
                    else raise PC.X_no_match ;;
  
make_integer (string_to_list "20000000000000000000000000000000");;
  
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

  
