let string_to_list str =
  let rec loop i limit =
    if i=limit then []
    else (String.get str i) :: (loop (i + 1) limit)
  in
  loop 0 (String.length str);;

  let list_to_string s=
    let rec loop s n =
      match s with
      | [] -> String.make n '?'
      | car :: cdr ->
          let result = loop cdr (n+1) in
          Bytes.set result n car;
          result
      in
      loop s 0 ;;
