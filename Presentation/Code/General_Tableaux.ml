type prop =
  | Var of string
  | Not of prop
  | And of prop * prop
  | Or  of prop * prop

(* Une branche c'est une liste de formule avec un signe *)
type branch =  (bool * prop) list

let is_literal = function
  | (true, Var _) -> true
  | (false, Var _) -> true
  | (true, Not (Var _)) -> true
  | (false, Not (Var _)) -> true
  | _ -> false

(* Check les contradictions *)
let branch_closed (br : branch) : bool =
  let pos = Hashtbl.create 16 in
  let neg = Hashtbl.create 16 in
  let record = function
    | (true, Var v) -> Hashtbl.replace pos v true
    | (false, Var v) -> Hashtbl.replace neg v true
    | (true, Not (Var v)) -> Hashtbl.replace neg v true
    | (false, Not (Var v)) -> Hashtbl.replace pos v true
    | _ -> ()
  in
  List.iter record br;
  let closed = ref false in
  Hashtbl.iter (fun v _ ->
    if (Hashtbl.mem pos v) && (Hashtbl.mem neg v) then closed := true
  ) pos;
  !closed

(* La decomposition usuelle faites durant la méthode des tableaux *)
let decompose_once (br : branch) : branch list option =
  let rec find_nonlit acc = function
    | [] -> None
    | x :: xs ->
      if is_literal x then find_nonlit (x::acc) xs
      else Some (List.rev acc, x, xs)
  in
  match find_nonlit [] br with
  | None -> None
  | Some (left, (sign, form), right) ->
    let rest = left @ right in
    let mk b p = (b, p) in
    (match sign, form with
     | true, And (a,b) ->
       Some [ (mk true a) :: (mk true b) :: rest ]
     | false, Or (a,b) ->
       Some [ (mk false a) :: (mk false b) :: rest ]
     | true, Or (a,b) ->
       Some [ (mk true a)::rest; (mk true b)::rest ]
     | false, And (a,b) ->
       Some [ (mk false a)::rest; (mk false b)::rest ]
     | true, Not a ->
       Some [ (mk false a) :: rest ]
     | false, Not a ->
       Some [ (mk true a) :: rest ]
     | _, _ -> None)

(* La Methode des Tableaux en soit *)
let satisfiable (phi : prop) : bool =
  let initial_branch = [ (true, phi) ] in
  let rec explore_stack stack =
    match stack with
    | [] -> false
    | br :: rest ->
      if branch_closed br then explore_stack rest else
      match decompose_once br with
      | None -> true
      | Some new_branches -> explore_stack (new_branches @ rest)
    in explore_stack [ initial_branch ]


(* Debug, pour faire des beaux print *)
let rec string_of_prop = function
  | Var v -> v
  | Not p -> "¬(" ^ string_of_prop p ^ ")"
  | And (a,b) -> "(" ^ string_of_prop a ^ " ∧ " ^ string_of_prop b ^ ")"
  | Or (a,b) -> "(" ^ string_of_prop a ^ " v " ^ string_of_prop b ^ ")"
let string_of_signed (b, p) = (if b then "T " else "F ") ^ string_of_prop p
let string_of_branch br = String.concat ", " (List.map string_of_signed br);;