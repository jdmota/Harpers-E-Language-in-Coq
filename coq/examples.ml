open Printf
open Eval

(* Based on https://stackoverflow.com/a/29957505 *)
let to_str l = String.concat "" (List.map (String.make 1) l)

(* Based on https://stackoverflow.com/a/24174540 *)
let rec from_str s = match s with
  | "" -> []
  | s -> (String.get s 0)::(from_str (String.sub s 1 ((String.length s) - 1)))

let exec e =
  match eval_big e with
  | Some (ENum n) -> Printf.printf "Result: %d\n" n
  | Some (EStr s) -> Printf.printf "Result: %s\n" (to_str s)
  | Some _ -> Printf.printf "Impossible\n"
  | None -> Printf.printf "Failure\n"

let str s = EStr (from_str s)

let () = exec (EPlus (ENum 0, ENum 3))
let () = exec (ELet (ENum 2, 0, (EPlus (EId 0, ENum 3))))

let () = exec (ECat (str "a", str "b"))
let () = exec (ELet (str "a", 0, (ECat (EId 0, str "b"))))

let () = exec (ELet (ENum 2, 0, (EPlus (EId 1, ENum 3))))
let () = exec (ELet (str "a", 0, (EPlus (EId 1, str "b"))))
