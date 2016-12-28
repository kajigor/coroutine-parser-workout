open GT

@type tree = S of char | Seq of tree * tree | E | EOF with show

type stream = char list

let of_string s =
  let n = String.length s in
  let rec loop i = 
    if i = n then [] else s.[i] :: loop (i+1)
  in
  loop 0

module Direct =
  struct

    type 'a p = stream -> ('a * stream) list

    let eof = function [] -> [EOF, []] | _ -> []

    let empty s = [E, s]

    let sym x = function
    | y::tl when y = x -> [S x, tl]
    | _ -> []

    let seq a b s =
      let a' = a s in
      List.flatten (
        List.map 
            (fun (at, s) -> 
            let b' = b s in
            List.map (fun (bt, s) -> Seq (at, bt), s) b'
          ) 
          a'
     )

    let alt a b s = (a s) @ (b s)

    let refine s = 
      try List.find (function (_, []) -> true | _ -> false) s |> fun x -> Some (fst x)
      with Not_found -> None

    let (|>) = seq
    let (<>) = alt

    let a = sym 'a'
    let b = sym 'b'
    let c = sym 'c'
        
    let test01 = a |> b |> c |> eof
    let test02 = (a <> b <> c) |> eof
      
    let test03 = 
      let rec pali s = (
        (a |> pali |> a) <>
        (b |> pali |> b) <>
        (c |> pali |> c) <>
        empty    
       ) s
      in
      pali |> eof

    let test04 =
      let rec expr s = (
        (expr |> sym '+' |> expr) <>
        a
       ) s
      in
      expr |> eof

    let run test input =
      Printf.printf "%s\n" @@
      show(option) (show(tree)) @@ refine (test @@ of_string input)

    let _ = 
      Printf.printf "Running direct style:\n";
(*       run test01 "abc";
      run test01 "abcd";
      run test02 "a";
      run test02 "b";
      run test02 "c";
      run test03 "abcccabaabaaabbbcccaaabbccccccbbaaacccbbbaaabaabacccba";
      (* loops: run test04 "a";  *)
      (* loops: run test04 "a+a" *)
*)
  end

module CPS =
  struct

    (* Result of "one-step" parsing *)
    type 'a result = 
    (*          parsed residual    residual parsing
                value   stream        steps
                   |      |             |
                   v      v             v
    *)
    | Ok       of 'a * stream * (unit -> 'a result) 
    (*             residual parsing
                        steps
                          |
                          v
    *)
    | Continue of (unit -> 'a result)   
    | End 

    let rec maps f k () = 
      match k () with
      | Ok (t, s, k) -> Ok (f t, s, maps f k)
      | Continue k   -> Continue (maps f k)
      | End          -> End

    (* One-step parser *)
    type 'a p = stream -> 'a result

    (* Some tracing noodles *)
    let log = ref false
    let log_on  () = log := true
    let log_off () = log := false

    let ticker () =
      let i = ref 0 in
      (fun s -> 
         if !log then (
            Printf.printf "%s %d\n%!" s !i;
           incr i;
           ignore (read_line ())
        )
      )

    (* Empty residual parsing steps *)
    let stop () = End

    (* Some primitive parsers *)
    let eof = function [] -> Ok (EOF, [], stop) | _ -> End

    let empty s = Ok (E, s, stop)

    let sym x = function
    | y::tl when y = x -> Ok (S x, tl, stop)
    | _ -> End

    let seq a b s =
      let rec inner ka kb () =
        match kb () with
        | Ok (tb, sb, kb) -> Ok (tb, sb, inner kb ka)
        | Continue kb     -> Continue (inner kb ka)
        | End             -> Continue ka
      in
      Continue (
        let rec outer ka kb () =
           match ka () with
           | Ok (ta, sa, ka) -> Continue (outer ka (inner kb (maps (fun tb -> Seq (ta, tb)) (fun () -> b sa))))
           | Continue ka     -> Continue (inner (outer ka stop) kb)
           | End             -> Continue kb
        in
        outer (fun () -> a s) stop
      )
(*
    (* Sequential combinator seq : tree p -> tree p -> tree p *)
    let rec seq a b s = 
      let t = ticker () in
      let rec outer a kb () =
        match a () with
        | Ok (ta, sa, ka) -> 
            t ("seq: a=" ^ show(tree) ta);
            Continue (
              let rec inner b () =
                match b () with
                | Ok (tb, sb, kb) -> 
                    t ("seq: b=" ^ show(tree) tb);  (* <- tracing *)
                    Ok (Seq (ta, tb), sb, inner kb) (* essential part *)
                | Continue kb -> 
                    t "seq: b=continue"; (* <- tracing *)
                    Continue (outer ka (inner kb)) (* (inner kb) essential part  (* <- problem *)*)
                | End -> 
                    t "seq: b=end";     (* tracing *)
                    Continue (outer ka stop) (* essential part *)
              in
              inner (fun () -> b sa)
            )
        | Continue ka -> 
            t "seq: a=continue"; 
            Continue (
              let rec inner ka kb () =
                match kb () with
                | Ok (tb, sb, kb) -> Ok (tb, sb, outer ka stop)
                | Continue kb     -> Continue (outer ka kb)
                | End             -> Continue ka
              in 
              inner ka kb 
            )
        | End -> 
            Continue kb
(*
            t "seq: a=end"; 
            End
*)
      in
      Continue (outer (fun () -> a s) stop)
*)
    (* Parallel combinator alt : tree p -> tree p -> tree p *)
    let alt a b s = 
      let t = ticker () in
      let rec inner a b () =
        match a () with
        | Ok (ta, sa, ka) -> 
            t ("alt:" ^ show(tree) ta); 
            Ok (ta, sa, inner b ka)
        | Continue ka -> 
            t "alt:continue"; 
            Continue (inner b ka)
        | End -> 
            t "alt:end"; 
            b ()
      in
      Continue (inner (fun () -> a s) (fun () -> b s))

    (* Apply gets the first result *)
    let apply p s =
      (* let t = ticker () in *)
      let rec inner p =
        match p () with
        | Ok (tp, sp, kp) -> Some tp
        | Continue kp     -> inner kp
        | End             -> None
      in
      inner (fun () -> p s)

    let (|>) = seq
    let (<>) = alt

    let a = sym 'a'
    let b = sym 'b'
    let c = sym 'c'
        
    let test01 = a |> b |> c |> eof

    let test02 = (a <> b <> c) |> eof
      
    let test03 = 
      let rec pali s = (
        (a |> pali |> a) <>
        (b |> pali |> b) <>
        (c |> pali |> c) <>
        empty    
       ) s
      in
      pali |> eof

    let test04 =
      let rec expr s = (
        (expr |> sym '+' |> expr) <>
        a
       ) s
      in
      expr |> eof

    let test05 =
      let rec inner s = (
        (inner |> a) <> empty
      ) s
      in
      inner |> eof

    let test06 =
      let rec addi  s = (mulli   <> (addi  |> sym '+' |> mulli  )) s
      and     mulli s = (primary <> (mulli |> sym '*' |> primary)) s
      and     primary = a <> b <> c in
      addi |> eof

    let expr n = 
      let rec e s = (m <> (e |> (sym '+' <> sym '-') |> m )) s
      and     m s = (p <> (m |> (sym '*' <> sym '/') |> p)) s
      and     p s = (n <> (sym '(' |> e |> sym ')')) s in
      e |> eof

    let test07 = expr (a <> b <> c)
    
    let test08 = expr (sym 'n')

    let integer = 
      let nzdigit   = List.fold_left (fun acc x -> acc <> sym x) (sym '1') (of_string "23456789") in
      let digit     = sym '0' <> nzdigit in 
      let rec num s = ((digit |> num) <> empty) s in
      (nzdigit |> num) <> (sym '0')
    
    let test09 = expr integer

    let run test input =
      Printf.printf "%s\n%!" @@
      show(option) (show(tree)) (apply test @@ of_string input)

    let _ = 
      Printf.printf "Running CPS-style:\n%!";
(*
      run test01 "abc";
      run test01 "abcd";
      run test02 "a";
      run test02 "b";
      run test02 "c";

(*
      run test03 "abcccabaabaaabbbccccccbbbaaabaabacccba";       
      run test03 "abccbbaccbacaabbbbaabbbbaacabccabbccba";
      run test03 "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
*)
      run test04 "a";
      run test04 "a+a";
      run test05 "aaaaa";
      run test06 "a";
      run test06 "b";

      run test06 "c";
      run test06 "a+a+a";        
      run test06 "a*b+c";
      
      run test07 "a*(b+c)";
      
      run test08 "n*(n+n)";
      run test08 "n/(n*(n+n)-n+n*n/(n-n*n+n))";

      (* run test08 "(n+(n+(n+(n+(n+(n+n))))))"; *)
      
      run test09 "1-2+0"; *)
  end

module MonadicCPS =
  struct

    (* Result of "one-step" parsing *)
    type 'a result = 
    (*          parsed residual    residual parsing
                value   stream        steps
                   |      |             |
                   v      v             v
    *)
    | Ok       of 'a * stream * (unit -> 'a result) 
    (*             residual parsing
                        steps
                          |
                          v
    *)
    | Continue of (unit -> 'a result)   
    | End 

    let rec maps f k () = 
      match k () with
      | Ok (t, s, k) -> Ok (f t, s, maps f k)
      | Continue k   -> Continue (maps f k)
      | End          -> End

    (* One-step parser *)
    type 'a p = stream -> 'a result

    (* Some tracing noodles *)
    let log = ref false
    let log_on  () = log := true
    let log_off () = log := false

    let ticker () =
      let i = ref 0 in
      (fun s -> 
         if !log then (
           Printf.printf "%s %d\n%!" s !i;
           incr i;
           ignore (read_line ())
        )
      )

    (* Empty residual parsing steps *)
    let stop () = End

    (* Some primitive parsers *)
    let eof = function [] -> Ok ((), [], stop) | _ -> End

    let get_eof = (fun x s -> maps (fun _ -> x) (fun () -> eof s) ())

    let empty s = Ok ((), s, stop)

    let sym x = function
    | y::tl when y = x -> Ok (x, tl, stop)
    | _ -> End

    let seq a b s =
      let rec inner ka kb () =
        match kb () with
        | Ok (tb, sb, kb) -> Ok (tb, sb, inner kb ka)
        | Continue kb     -> Continue (inner kb ka)
        | End             -> Continue ka
      in
      Continue (
        let rec outer ka kb () =
           match ka () with
           | Ok (ta, sa, ka) -> Continue (outer ka (inner kb (fun () -> b ta sa)))
           | Continue ka     -> Continue (inner (outer ka stop) kb)
           | End             -> Continue kb
        in
        outer (fun () -> a s) stop
      )

    let alt a b s = 
      let rec inner a b () =
        match a () with
        | Ok (ta, sa, ka) -> Ok (ta, sa, inner b ka)
        | Continue ka     -> Continue (inner b ka)
        | End             -> b ()
      in
      Continue (inner (fun () -> a s) (fun () -> b s))

    (* Apply gets the first result *)
    let apply p s =
      (* let t = ticker () in *)
      let rec inner p =
        match p () with
        | Ok (tp, sp, kp) -> Some tp
        | Continue kp     -> inner kp
        | End             -> None
      in
      inner (fun () -> p s)


    let (|>) = seq
    let (<>) = alt

    let a = sym 'a'
    let b = sym 'b'
    let c = sym 'c'

    let test00 =
         a |> (fun x s -> maps (fun y -> `Pair (x, y)) (fun () -> b s) ()) 
      <> (fun s -> maps (fun c -> `Single c) (fun () -> c s) ())

    let test01 = 
         a 
      |> (fun x     s -> maps (fun y -> x,y  ) (fun () -> b s) ())
      |> (fun (x,y) s -> maps (fun z -> x,y,z) (fun () -> c s) ())
      |> get_eof

    let test02 = 
         (a <> b <> c) |> get_eof

    let test03 = 
      let rec pali s =
       (
          (a 
          |> (fun x s -> maps (fun y -> x,y) (fun () -> pali s) ()) 
          |> (fun (l,p) s -> maps (fun r -> `T (l,p,r)) (fun () -> a s) ())
          )
       <> (b 
          |> (fun x s -> maps (fun y -> x,y) (fun () -> pali s) ()) 
          |> (fun (l,p) s -> maps (fun r -> `T (l,p,r)) (fun () -> b s) ()) 
          )
       <> (c
          |> (fun x s -> maps (fun y -> x,y) (fun () -> pali s) ()) 
          |> (fun (l,p) s -> maps (fun r -> `T (l,p,r)) (fun () -> c s) ()) 
          )
       <> (fun s -> maps (fun _ -> `E) (fun () -> empty s) ())
       ) s
      in pali |> get_eof

     let test04 = 
       let rec expr s = 
        ( 
           (expr 
           |> (fun x s -> maps (fun _ -> x) (fun () -> sym '+' s) ())
           |> (fun x s -> maps (fun y -> `Sum (x,y)) (fun () -> expr s) ())
           )
        <> (fun s -> maps (fun x -> `Primary x) (fun () -> a s) ())
        ) s
       in expr |> get_eof
    
    let test05 = 
      let rec inner s = 
        (
           inner |> (fun x s -> maps (fun y -> y::x) (fun () -> a s) ())
        <> (fun s -> maps (fun _ -> []) (fun () -> empty s) ())
        ) s
      in inner |> get_eof 

    let test06 = 
      let rec addi s = 
        (
           mulli
        <> (addi 
           |> (fun x s -> maps (fun _ -> x) (fun () -> sym '+' s) ()) 
           |> (fun x s -> maps (fun y -> `Sum (x, y)) (fun () -> mulli s) ()) 
           )
        ) s
      and mulli s = 
        (
           primary
        <> (mulli 
           |> (fun x s -> maps (fun _ -> x) (fun () -> sym '*' s) ()) 
           |> (fun x s -> maps (fun y -> `Mul (x, y)) (fun () -> primary s) ()) 
           )
        ) s
      and primary = 
        fun s -> maps (fun x -> `Primary x) (fun () -> (a <> b <> c) s) () 
      in addi |> get_eof

    let expr n = 
      let rec e s = 
        (
           m 
        <> (e 
           |> (fun x s -> maps (fun op -> x,op) (fun () -> (sym '+' <> sym '-') s) ()) 
           |> (fun (x,op) s -> maps (fun y -> `BinOp (op, x, y)) (fun () -> m s) ())
           )
        ) s
      and m s = 
        (
           p 
        <> (m 
           |> (fun x s -> maps (fun op -> x,op) (fun () -> (sym '*' <> sym '/') s) ()) 
           |> (fun (x,op) s -> maps (fun y -> `BinOp (op, x, y)) (fun () -> p s) ())
           )
        ) s
      and p s = 
        (
           n
        <> (sym '(' 
           |> (fun _ s -> maps (fun e -> `Bracket e) (fun () -> e s) ()) 
           |> (fun x s -> maps (fun _ -> x) (fun () -> sym ')' s) ())
           )
        ) s 
      in e |> get_eof

    let test07 = expr (fun s -> maps (fun x -> `Primary x) (fun () -> (a <> b <> c) s) ())
    
    let test08 = expr (fun s -> maps (fun x -> `Primary x) (fun () -> sym 'n' s) ())

    let integer = 
      let to_int c = int_of_char c - int_of_char '0' in
      let nzdigit s = maps (fun x -> to_int x)
                           (fun () -> (List.fold_left 
                                        (fun acc x -> acc <> sym x)
                                        (sym '1') 
                                        (of_string "23456789")) s) 
                           () 
      in
      let digit s   = 
        (
           (fun s -> maps (fun x -> to_int x) (fun () -> sym '0' s) ()) 
        <> (fun s -> maps (fun x -> x) (fun () -> nzdigit s) ())
        ) s
      in 
      let rec num s = 
        (  
           (digit 
           |> (fun x s -> maps (fun n -> x :: n) (fun () -> num s) ())
           )
        <> (fun s -> maps (fun _ -> []) (fun () -> empty s) ())
        ) s 
      in
      fun s -> 
        maps 
          (fun l -> List.fold_left (fun acc x -> acc * 10 + x) 0 l)
          (fun () -> (
                        (nzdigit 
                        |> (fun x s -> maps (fun y -> x :: y) (fun () -> num s) ())
                        ) 
                     <> (fun s -> maps (fun x -> [to_int x]) (fun () -> sym '0' s) ())
                     ) s)
          ()

    let test09 = expr (fun s -> maps (fun x -> `Primary x) (fun () -> integer s) ())

    let test10 = 
      let rec w s = 
        (
           (w
           |> (fun x     s -> maps (fun y -> x,y           ) (fun () -> w s) ())
           |> (fun (x,y) s -> maps (fun z -> `Three (x,y,z)) (fun () -> w s) ())
           )
        <> (w
           |> (fun x     s -> maps (fun y -> `Two (x,y)    ) (fun () -> w s) ())
           )
        <> (fun s -> maps (fun _ -> `One) (fun () -> a s) ())
        ) s 
      in w |> get_eof

    let test11 = 
      let rec w s = 
        (
           (fun s -> maps (fun _ -> `One) (fun () -> a s) ())
        <> (w
           |> (fun x     s -> maps (fun y -> `Two (x,y)    ) (fun () -> w s) ())
           )
        <>
           (w
           |> (fun x     s -> maps (fun y -> x,y           ) (fun () -> w s) ())
           |> (fun (x,y) s -> maps (fun z -> `Three (x,y,z)) (fun () -> w s) ())
           )
        ) s 
      in w |> get_eof

    let run printer test input =
      Printf.printf "%s\n%!" @@
      show(option) printer (apply test @@ of_string input)

    let runtest00 =
      let print = function
      | `Pair (x, y) -> Printf.sprintf "%c %c" x y
      | `Single x    -> Printf.sprintf "%c" x
      in run print test00

    let runtest01 = 
      let print (a,b,c) = Printf.sprintf "%c %c %c" a b c
      in run print test01
      
    let runtest02 = 
      let print = Printf.sprintf "%c"
      in run print test02
    
    let runtest03 = 
      let rec print = function 
      | `E -> ""
      | `T (l, p, r) -> Printf.sprintf "%c [%s] %c" l (print p) r
      in run print test03

    let print_expr print_primary = 
      let rec print = function
      | `Primary x -> print_primary x
      | `Sum (x,y) -> Printf.sprintf "%s + %s" (print x) (print y)
      | `Mul (x,y) -> Printf.sprintf "%s * %s" (print x) (print y)
      in print 

    let print_expr' print_primary = 
      let rec print = function
      | `Primary x -> print_primary x
      | `BinOp (op,x,y) -> Printf.sprintf "%s %c %s" (print x) op (print y)
      | `Bracket e -> Printf.sprintf "(%s)" (print e)
      in print 

    let runtest04 = run (print_expr (Printf.sprintf "%c")) test04

    let runtest05 = 
      let print x = List.fold_left (fun acc _ -> "a" ^ acc) "" x
      in run print test05

    let runtest06 = run (print_expr (Printf.sprintf "%c")) test06

    let runtest07 = run (print_expr' (Printf.sprintf "%c")) test07
    
    let runtest08 = run (print_expr' (fun _ -> "n")) test08

    let runtest1_ = 
      let rec print = function 
      | `One           -> "a"
      | `Two (x,y)     -> Printf.sprintf "[%s %s]" (print x) (print y)
      | `Three (x,y,z) -> Printf.sprintf "[%s %s %s]" (print x) (print y) (print z)
      in run print

    let runtest10 = runtest1_ test10

    let runtest11 = runtest1_ test11

    let runinteger = 
      let rec print = Printf.sprintf "%i"
      in run print (integer |> get_eof)

    let runtest09 = run (print_expr' (Printf.sprintf "%i")) test09

    let runtest09' = 
      let rec eval_expr = function 
      | `Primary x -> x
      | `BinOp (op,x,y) -> 
        let f = function 
        | '+' -> fun x y -> x + y
        | '*' -> fun x y -> x * y
        | '-' -> fun x y -> x - y
        | '/' -> fun x y -> x / y
        in (f op) (eval_expr x) (eval_expr y)
      | `Bracket x -> eval_expr x
      in run (fun x -> Printf.sprintf "%i" (eval_expr x)) test09

    let _ = 
      Printf.printf "Running monadic CPS-style:\n%!";
(*
      runtest00 "ab";
      runtest00 "c";
      runtest00 "d";

      runtest01 "abc";
      runtest01 "abcd";
      runtest02 "a";
      runtest02 "b";
      runtest02 "c";

      runtest03 "";
      runtest03 "abcccabaabaaabbbccccccbbbaaabaabacccba";
      runtest03 "abccbbaccbacaabbbbaabbbbaacabccabbccba";
      runtest03 "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";


      runtest04 "a";
      runtest04 "a+a";

      runtest05 "aaaaa";

      runtest06 "a";
      runtest06 "b";
      runtest06 "c";
      runtest06 "a+a+a";        
      runtest06 "a*b+c";
      
      runtest07 "a*(b+c)";
      
      runtest08 "n*(n+n)";
      runtest08 "n/(n*(n+n)-n+n*n/(n-n*n+n))";

      (* runtest08 "(n+(n+(n+(n+(n+(n+n))))))"; *)
(*      
      runtest09 "1-2+0";
*)

      runtest10 "a";
      runtest10 "aa";
      runtest10 "aaa";
      runtest10 "aaaaa";
      runtest10 "aaaaaaaaaa";
      (* runtest10 "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" *)
*)
(*
      runtest11 "a";
      runtest11 "aa";
      runtest11 "aaa";
      runtest11 "aaaaa";
      runtest11 "aaaaaaaaaa";
      runtest11 "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
*)
      runinteger "123";

      runtest09 "1+23*9";

      runtest09' "1-2-3";
      runtest09' "1+2-3";
      runtest09' "1-(2-3)";
      runtest09' "1-2*3";
      runtest09' "1/2+3";
      runtest09' "1*2/3";
      
  end

