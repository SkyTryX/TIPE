type formula = (* Definition d'un type simple de formule logique *)
  | Atom of (string* bool)
  | And of (string*bool) * formula
  | Or of (string*bool) * formula

type branch = (* Definition de notre stockage des branches*)
  | Empty
  | Node of (formula option * formula * branch);;

let extract (f:formula option) = match f with
  | None ->  Atom("none", false)
  | Some t -> t

let rec print_formula (f:formula) = match f with
  | Atom(s, b) -> if b then print_string s else print_string "Not ";print_string s;
  | And ((f, b),g) -> if b then print_string f else print_string "Not ";print_string f;print_string " And ";print_formula g
  | Or ((f,b),g) -> if b then print_string f else print_string "Not ";print_string f;print_string " Or ";print_formula g;;

let rec print_branches (b:branch) =
  print_string " [";
  match b with
    | Empty -> ()
    | Node(a1, a2, b) -> print_formula@@extract a1;print_string ", ";print_formula a2;print_branches b;
  print_string "]";;

(* Construction du tableau en O(nb_connecteur ET) *)
let rec formula2branch (f:formula) : branch = match f with
  | And(a, Or(b, Atom(c))) -> Node(Some(Atom b), Atom a, Node(None, Atom(c), Empty))
  | And(a, Or(b, c)) ->  Node(Some(Atom b), Atom a, formula2branch c)
  | And(a, Atom(b)) -> Node(Some (Atom b), Atom a, Empty)
  | _ -> failwith "Pas alternée"

let has_cycle (br:branch) : bool = 
  let rec aux (br:branch) (d:(string,bool) Hashtbl.t) : bool = match br with
  | Node(None, Atom (f, b), Empty) -> 
    if Hashtbl.mem d f then 
      Hashtbl.find d f = b
    else
      true
  | Node(Some(Atom(fg, bg)), Atom (fd, bd), Empty) -> 
        if Hashtbl.mem d fd then
          if Hashtbl.find d fd = bd then
            not @@ (Hashtbl.mem d fg && Hashtbl.find d fg <> bg)
          else 
            false
        else(
          Hashtbl.add d fd bd;
          not @@ (Hashtbl.mem d fg && Hashtbl.find d fg <> bg)
        )
  | Node(Some (Atom (fg, bg)), Atom (fd, bd), nb) ->
    if Hashtbl.mem d fd then
      if Hashtbl.find d fd <> bd then
        false
      else
        if Hashtbl.mem d fg then
          if Hashtbl.find d fg = bg then
            true
          else
            aux nb d
        else
          true
    else
      (Hashtbl.add d fd bd;
      if Hashtbl.mem d fg then
        if Hashtbl.find d fg = bg then
          true
        else
          aux nb d
      else
        true)
  | _ -> failwith "Pas alternée"
  in aux br (Hashtbl.create 100);;

let is_satisfiable (f:formula) : bool = let b = formula2branch f in has_cycle b;;

