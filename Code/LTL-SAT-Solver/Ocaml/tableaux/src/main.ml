(* Type corresponding to LTL formulas (the restricted fragment)  *)
type ltl =
| Prop of char
| Top
| Bot
| Neg of ltl
| And of ltl * ltl
| Or of ltl * ltl
| F of ltl
| G of ltl
| X of ltl

(**Type characterizing LTL formulas by their main operator, following structure of static rules*)
type ltl_op =
| Prop_op
| Top_op
| NTop_op
| Bot_op
| NBot_op
| Neg_op
| NNeg_op
| And_op
| NAnd_op
| Or_op
| NOr_op
| F_op
| NF_op
| G_op
| NG_op
| X_op
| NX_op


(**Computes main operator of any ltl formula, following structure of static rules*)
let main_op :ltl->ltl_op=function
|Prop _|Neg (Prop _)->Prop_op
|Top->Top_op
|Neg(Top)->NTop_op
|Bot->Bot_op
|Neg(Bot)->NBot_op
|F _->F_op
|Neg(F _)->NF_op
|G _->G_op
|Neg(G _)->NG_op
|And(_,_)->And_op
|Neg(And(_,_))->NAnd_op
|Or(_,_)->Or_op
|Neg(Or(_,_))->NOr_op
|Neg(Neg _ )-> NNeg_op
|X _->X_op
|Neg(X _)->NX_op

(**Turns phi into a printable string*)
let rec string_ltl (phi:ltl) =
match phi with
|Prop c ->String.make 1 c
|Top->"T"
|Bot ->"B"
|Neg psi -> (match main_op psi with 
  |And_op|Or_op->"Neg("^(string_ltl psi)^")"
  |_->"Neg "^(string_ltl psi))
|And (psi1,psi2)-> (match main_op psi1 with
  |Or_op->(match main_op psi2 with
    |Or_op->("("^((string_ltl psi1) ^ ")&(")) ^(string_ltl psi2^")")
    |_->("("^((string_ltl psi1) ^ ")& ")) ^(string_ltl psi2))
  |_->(match main_op psi2 with
    |Or_op->((string_ltl psi1) ^ " &(") ^(string_ltl psi2^")")
    |_->((string_ltl psi1) ^ " & ") ^(string_ltl psi2)))
|Or (psi1,psi2)->(match main_op psi1 with
  |And_op->(match main_op psi2 with
    |And_op->("("^((string_ltl psi1) ^ ")|(")) ^(string_ltl psi2^")")
    |_->("("^((string_ltl psi1) ^ ")| ")) ^(string_ltl psi2))
  |_->(match main_op psi2 with
    |And_op->((string_ltl psi1) ^ " |(") ^(string_ltl psi2^")")
    |_->((string_ltl psi1) ^ " | ") ^(string_ltl psi2)))
|F psi ->(match main_op psi with 
  |And_op|Or_op->"F("^(string_ltl psi)^")"
  |_->"F "^(string_ltl psi))
|G psi ->(match main_op psi with
  |And_op|Or_op->"G("^(string_ltl psi)^")"
  |_->"G "^(string_ltl psi))
|X psi ->(match main_op psi with
  |And_op|Or_op->"X("^(string_ltl psi)^")"
  |_->"X "^(string_ltl psi))

(**Makes a 'a list printer out of a 'a printer*)
let printer_to_list (printer:'a->string)=
  let rec list_string = function
  |[]->""
  |x::[]->(printer x)
  |x::l'->(printer x)^" ; "^(list_string l')^"\n" in 
  list_string

(**Printer for ltl lists*)
let string_ltl_list = printer_to_list string_ltl


(**Turns a ltl_op into a printable string*)
let string_ltl_op : ltl_op->string = function
| Prop_op -> "Prop_op"
| Top_op -> "Top_op"
| NTop_op ->"NTop_op"
| Bot_op -> "Bot_op"
| NBot_op -> "NBot_op"
| Neg_op -> "Neg_op"
| NNeg_op -> "NNeg_op"
| And_op -> "And_op"
| NAnd_op -> "NAnd_op"
| Or_op -> "Or_op"
| NOr_op -> "NOr_op"
| F_op -> "F_op"
| NF_op -> "NF_op"
| G_op -> "G_op"
| NG_op -> "NG_op"
| X_op -> "X_op"
| NX_op -> "NX_op"

(**Printer for 'a option out of printer for 'a*)
let string_option (printer:'a->string):('a option ->string)=function
  |None->"None"
  |Some x ->"Some"^(printer x)


(*let rec ltl_of_string (string_fml:string):ltl=
  if string_fml="" then failwith "empty formula" else match string_fml.[0] with
  |' '|'('|')'->ltl_of_string (String.sub string_fml 1 (String.length string_fml -1 ))
  |'P'->Prop(string_fml.[6])
  |'T'->Top
  |'B'->Bot
  |'A'->let sep= String.split_on_char ',' (String.sub string_fml 4 (String.length string_fml -4 )) in
    And(ltl_of_string sep[0],ltl_of_string sep[1])
  |'O'->
  |'N'->
  |'X'->
  |'F'->
  |'G'->
  |_->*)




(**NOT USED Computes negative normal form of phi *)
let rec nnf (phi:ltl)=
  match phi with
    |Prop _|Neg (Prop _)|Top|Neg Top|Bot|Neg Bot -> phi
    |And (psi1, psi2) -> And ((nnf psi1), (nnf psi2)) 
    |Neg (And (psi1, psi2)) -> Or ((nnf (Neg psi1)), nnf(Neg psi2))
    |Or (psi1, psi2) -> Or ((nnf psi1), (nnf psi2)) 
    |Neg (Or(psi1, psi2)) -> And ((nnf (Neg psi1)), nnf(Neg psi2))
    |F psi -> F(nnf psi)
    |Neg(F psi) -> G(nnf (Neg psi))
    |G psi -> G(nnf psi)
    |Neg(G psi) -> F(nnf (Neg psi))
    |X psi -> X(nnf psi)
    |Neg(X psi) -> X(nnf(Neg psi))
    |Neg(Neg psi)-> nnf psi


(**NOT USED Computes the list of subformulas of phi, along with successors of F and G subformulas*)
let rec s_plus (phi:ltl)=
match phi with
|Prop _->[phi]
|Top->[Top]
|Bot->[Bot]
|And(psi1,psi2)|Or(psi1,psi2)->phi::((s_plus psi1) @ (s_plus psi2))
|Neg psi|X psi -> phi :: (s_plus psi)
|F psi|G psi-> phi :: ((X phi) ::(s_plus psi))


(**Returns true iff the list contains contradictory formulas*)
let contains_contra (l:ltl list) : bool =
  let contains_neg (l:ltl list)(phi:ltl):bool=
    List.exists(fun psi -> (psi = Neg phi)) l
  in
  List.exists(fun phi->contains_neg l phi) l


(**Applies transition rule to a list of ltl*)
let apply_trans (l:ltl list) =
  let next_fml = List.filter(fun phi -> let op = main_op phi in op= X_op || main_op phi = NX_op) l in 
    List.map(function 
    |X psi ->psi
    |Neg(X(psi))->Neg(psi)
    |_->failwith "not a X formula" )next_fml



(**Returns Some op if some formula with main operator op can still be unraveled, None if not*)
let rec static_rule :ltl list->ltl_op option=function
  |[]->None
  |phi::l'->let op = main_op phi in 
    if op = X_op || op = NX_op || op = Prop_op  then static_rule l' else Some op

(**Returns true iff rule associated with operator is binary*)
let is_binary_op = function
| NAnd_op|Or_op| F_op| NG_op->true
|_->false

(**Returns Some k if the list contains a formula with main operator op at index k; None if it does nowhere *)
let contains_op = 
  let rec contains_op_0 (k:int)(op:ltl_op)(l:ltl list):int option=
  match l with
  |[]->None
  |phi::l0->if main_op phi=op then Some k else contains_op_0 (k+1) op l0 in
contains_op_0 0 


(**Takes list where the (0 or 1)-ary rule related to op can be applied, and does so.*)
let get_rid_Unary (op:ltl_op)(l:ltl list):ltl list=
  let rec get_rid_Unary_0 (k:int)(l:ltl list)(m:ltl list):ltl list = 
    match l with
    |[]->failwith "operator not found after exploring all the list"
    |phi::l'->if k=0 then 
      match phi with
      |Top|Neg Bot->m@l'
      |And(psi1,psi2)->m@(psi1::psi2::l')
      |Neg(Or(psi1,psi2))->m@((Neg psi1)::(Neg psi2) :: l')
      |Neg (Neg psi)->m@(psi::l')
      |G psi ->m@(psi :: X (G psi):: l')
      |Neg (F psi)-> m@(Neg psi :: (X (Neg (F psi))) :: l')
      |_->failwith "no 0-ary or unary rule applies"
    else get_rid_Unary_0 (k-1) l' (m@[phi]) in
  match contains_op op l with
      |None -> failwith "list does not contain operator"
      |Some k -> get_rid_Unary_0 k l []


(**Takes list where the (0 or 1)-ary rule related to op can be applied, and does so.*)
let get_rid_Binary (op:ltl_op)(l:ltl list):bool->ltl list=
  let rec get_rid_Binary_0 (k:int)(l:ltl list)(m:ltl list):bool->ltl list = match l with
    |[]->failwith "operator not found after exploring all the list"
    |phi::l'->if k=0 then match phi with
      |Or(psi1,psi2)->(function |false->m@(psi1::l')|true->m@(psi2::l'))
      |Neg(And(psi1,psi2))->(function |false->m@((Neg psi1)::l')|true->m@((Neg psi2)::l'))
      |F psi->(function |false->m@(psi::l') |true->m@((X(F psi))::l'))
      |Neg(G psi)->(function |false->m@((Neg psi)::l') |true->m@(X(Neg(G psi)))::l') 
      |_->failwith "no binary rule applies"
    else get_rid_Binary_0 (k-1) l' (m@[phi]) in
  match contains_op op l with
      |None -> failwith "list does not contain operator"
      |Some k -> get_rid_Binary_0 k l []
  

(**Syntactical shortcut to test whether some element is included in a list*)
let belongs_list (x:'a):'a list->bool=
  List.exists (fun y->y=x)

(**Returns true iff list l is included in list m sets-wise*)
let rec is_included (l:'a list) (m:'a list):bool=
    match l with
    |[]->true
    |phi::l'->belongs_list phi m && is_included l' m

(**Returns true iff both lists are equal sets-wise*)    
let are_equal (l:'a list)(m:'a list):bool = 
  is_included l m && is_included m l


(**  Returns the list of indexes of the proper ancestors of t containing its list sets wise*)
let poised_ancestors_contain :ltl list list->int list = 
  let rec poised_ancestors_contain_0 (ll:ltl list list)(l:ltl list)(k:int):int list=
    match ll with
    |[]->[]
    |m::ll'->(if static_rule m = None && is_included l m then [k] else [])@(poised_ancestors_contain_0 ll' l (k+1)) in 
  function
  |[]->failwith "empty list of ancestors"
  |l::ll-> poised_ancestors_contain_0 ll l 1


(**Returns true iff there is an X-eventuality in the list*)
let contains_X_ev :ltl list->bool=
  List.exists(fun phi -> match phi with 
  |X(F _)|X (G _)|Neg(X (F _))|Neg(X (G _))->true
  |_->false)

(**Returns the list of phi for all X F phi in the list*)
let f_X_ev (l:ltl list):ltl list=
  let xf_ev = List.filter(fun phi -> match phi with 
  |X(F _)->true
  |_->false) l in 
  List.map(function 
    |X(F psi) ->psi
    |_->failwith "not a XF formula" )xf_ev
    

(**Returns the list of ints between j and k-1*)
let rec range (j:int)(k:int) : int list =
  if j>=k then [] else
    (range j(k-1))@[k-1]

(**Returns true iff the loop rule applies to the tableau*)
let loop_applies (ll:ltl list list):bool=
let i = poised_ancestors_contain ll in
    let current_list = List.hd ll in
      List.exists(fun k_v -> is_included (List.nth ll k_v)(current_list)&&
      (*there is a proper poised ancestor v contained in current poised label and*)
      List.for_all(fun phi->List.exists (fun j->belongs_list phi (List.nth ll j)) (range 1 (k_v+1) ))(f_X_ev (current_list)))i
      (*every XF-ev in current label was satisfied after v*)

(**Returns true iff the prune rule applies to the tableau*)
let prune_applies (ll:ltl list list):bool = 
  let i = poised_ancestors_contain ll in 
  let current_list = List.hd ll in
    List.exists(fun k_v -> are_equal(List.nth ll k_v)(current_list)&&
    List.exists(fun k_w->k_w>k_v&&are_equal(List.nth ll k_w)(current_list)&& 
(* there are proper poised ancestors v and w, both their labels are equal to current poised label sets-wise and*)
    List.for_all (fun phi->List.exists (fun k_y->belongs_list phi (List.nth ll k_y))(range 1 (k_v+1))
      ||not(List.exists (fun k_x->belongs_list phi (List.nth ll k_x))(range (k_v+1) (k_w+1))))
(*every XF-ev that had to be satisfied between v and w still has to be satisfied after v*)
    (f_X_ev current_list))i )i

(**Returns true iff the prune_0 applies to the tableau*)
let prune_0_applies (ll:ltl list list):bool = 
  let i = poised_ancestors_contain ll in 
  let current_list = List.hd ll in
  contains_X_ev current_list =false &&
  (*there is at least one X-ev and*)
    List.exists(fun k_v -> are_equal(List.nth ll k_v)(current_list)&& 
(* there is a proper poised ancestor v whose label is equal to the current label sets-wise and*)
    List.for_all (fun phi->not(List.exists (fun k_x->belongs_list phi (List.nth ll k_x))(range 1 (k_v+1))))
(*no XF-ev in v is satisfied between the two nodes*)
    (f_X_ev current_list))i

(**Gets fitting valuation for a list where transition applies*)
let required_val (l:ltl list):ltl list=
  List.filter(fun x -> main_op x = Prop_op)l


(**Returns true iff phi is satisfyable in the fragment of ltl logic without until*)
let sat (phi:ltl):bool =
  (*Also prints the unraveling of the tableau*)
  let _ = print_string("Testing satisfyability of "^(string_ltl phi)^"\n\n") in

  (*body of the function*)
  let rec sat_0 (ll:ltl list list)(model:ltl list list):bool=

    (*current node in the tableau*)  
    let current_list = List.hd ll in 
    let _ = print_string ("Node: "^ string_ltl_list current_list ^"\n") in

      (*testing empty rule, contradiction rule and bottom rule*)
      if current_list = [] then 
        let () = print_string("Empty rule has validated this branch\n\nA model is:\n") in 
        let () = print_string((printer_to_list string_ltl_list)model^"\n")in true else
      if contains_contra current_list then let () = print_string("Contradiction rule has discarded this branch\n\n") in false else
      if contains_op Bot_op current_list <>None then  let () = print_string("Bottom rule has discarded this branch\n\n") in false else

      (*testing other static rules and applying them if possible*)
      match static_rule current_list with
      |Some op-> if is_binary_op op then let _ = print_string("Branching\n\n") in 
      let two_sons = get_rid_Binary op current_list in
        (let _ = print_string("Branch 1\n") in sat_0 (two_sons false::ll) model)||(let _ = print_string("Branch 2\n") in sat_0 (two_sons true::ll) model) else 
        sat_0 (get_rid_Unary op current_list :: ll) model

      (*testing dynamic rules*)  
      |None->if loop_applies ll then  
        let () = print_string("Loop rule has validated this branch\n\nA model is:\n\n") in
        let () = print_string((printer_to_list string_ltl_list)model^"Loop from now on\n\n")in true else
        if prune_applies ll then  let () = print_string("Prune rule has discarded this branch\n\n") in false else
        if prune_0_applies ll then  let () = print_string("Prune_0 rule has discarded this branch\n\n") in false else 
        

      (*if none applies, save the valuation and make transition*)
        let () = print_string ("Transition\n\n") in
        let valuation = required_val current_list in
        sat_0 (apply_trans current_list :: ll) (model@[valuation]) in

  let satis = sat_0[[phi]][] in 
    if satis then let () = print_string(string_ltl phi ^" is satisfyable\n\n\n") in true else
      let () = print_string(string_ltl phi ^" is not satisfyable\n\n\n") in false
    



(**Returns true iff phi is valid in the fragment of ltl logic without until*)
let valid phi = not(sat(Neg(phi)));;





(And(Or(Neg(Prop('a')), Or(Neg(And(Prop('b'), Neg(X(Prop('b'))))), And(Prop('b'), Neg(X(Prop('b')))))), Prop('a')))


