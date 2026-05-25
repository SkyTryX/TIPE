type literal = V of int | NV of int;;
type clause = literal list;;
type cnf = clause list;;

type proposition =
  | Var of int
  | Not of proposition
  | And of proposition * proposition
  | Or of proposition * proposition

let rec nnf prop =
  match prop with
  | Var _ -> prop
  | Not (Var _ as v) -> Not v
  | Not (Not p) -> nnf p
  | Not (And (p, q)) -> Or (nnf (Not p), nnf (Not q))
  | Not (Or (p, q)) -> And (nnf (Not p), nnf (Not q))
  | And (p, q) -> And (nnf p, nnf q)
  | Or (p, q) -> Or (nnf p, nnf q)

let rec distribute_or p1 p2 =
  match (p1, p2) with
  | (And (a, b), x) ->
      And (distribute_or a x, distribute_or b x)
  | (x, And (a, b)) ->
      And (distribute_or x a, distribute_or x b)
  | _ -> Or (p1, p2)

let rec to_cnf prop =
  match prop with
  | And (p, q) -> And (to_cnf p, to_cnf q)
  | Or (p, q) ->
      let cp = to_cnf p in
      let cq = to_cnf q in
      distribute_or cp cq
  | _ -> prop

let rec prop_to_cnf prop =
  prop
  |> nnf
  |> to_cnf

  let rec literal_of_prop p =
  match p with
  | Var n -> V n
  | Not (Var n) -> NV n
  | _ -> failwith "Invalid literal in clause"

let rec prop_to_cnf_data prop =
  match prop with
  | And (p, q) ->
      (prop_to_cnf_data p) @ (prop_to_cnf_data q)
  | _ ->
      (* a clause is a disjunction of literals *)
      let rec gather_literals p lits =
        match p with
        | Or (p1, p2) -> gather_literals p1 (gather_literals p2 lits)
        | _ ->
            let lit = literal_of_prop p in
            lit :: lits
      in
      [gather_literals prop []]

let proposition_to_cnf p =
  p |> prop_to_cnf |> prop_to_cnf_data

let litt_of_name_and_bool x b =
  if b then V x else NV x;;

let printclause c=
  Printf.printf "[";
  let rec aux = function
      [] ->  Printf.printf "]";
    | l::q -> match l with
      | NV x ->  Printf.printf "NV %d; " x; aux q;
      | V x -> Printf.printf "V %d; " x; aux q;
  in aux c
;;

let printprop p =  Printf.printf "prop = [";
  let rec aux = function
      [] ->  Printf.printf "]\n";
    | c::q -> printclause c; aux q;
  in aux p;;

let delete_lit (c:clause) (x:int) (b:bool) =
  List.filter
    ((<>) @@ litt_of_name_and_bool x (not b))
    c;;

let rec subst (f:cnf) (x:int) (b:bool) : cnf option  =
  match f with
    [] -> Some []
  | c::q -> let q' =  subst q x b in
            match q' with
            | None -> None
            | Some q2 -> let c = delete_lit c x b in
                         if c = [] then None else
                           if List.mem (litt_of_name_and_bool x b) c
                           then Some q2
                           else Some (c::q2);;

let get_var (f:cnf) : int = match f with 
  | (V x::_)::_ | (NV x::_)::_ -> x
  | _ -> failwith "pas de variable";;

let rec quine f = match f with
  | [] -> true
  | _ -> let x = get_var f in
    (*totest : substitution partielle*)
    let rec aux f totest =   match totest with
      | [] -> false (*on a testé x<-T et x<-F sans succès*)
      | b::q -> let sf = subst f x b (*x<-b*)
        in match sf with
        | Some f2 ->
           if quine f2
           then true (*un choix de substitution donne true*)
           else aux f q (*x<-b marche pas,on essaye le suivant*)
        | None -> aux f q
    in aux f [true;false];;

let sat (f:proposition) : bool = quine @@ proposition_to_cnf f;;

let tests (fa: proposition array): unit =
  let t = Sys.time() in
  let remove_t = ref 0. in
  for i = 0 to Array.length fa -1 do
    let t1 = Sys.time() in
    let form = proposition_to_cnf fa.(i) in
    remove_t := !remove_t +. (Sys.time() -. t1);
    let _ = quine form in ()
  done;Printf.printf "Execution time (QUINE): %fs\n" (Sys.time() -. t -. !remove_t);;