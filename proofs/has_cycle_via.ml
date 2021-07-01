(*@ open Set *)
(*@ open Seq *)
(*@ open SeqOfList *)

module type COMPARABLE = sig
  type t
  val [@logic] compare : t -> t -> int
  (*@ axiom pre_order_compare: is_pre_order compare*)

  val [@logic] hash : t -> int

  val equal : t -> t -> bool
  (*@ b = equal t1 t2 
        ensures b <-> t1 = t2*)
end

(*@ lemma seq_cons: forall s1 s2: 'a seq, x: 'a.
      s1 = cons x s2 -> forall i. 0 <= i < Seq.length s2 -> s1[i+1] = s2[i] *)


(* ORIGINAL CODE ALTERED, NOW RETURNS THE CYCLE INSTEAD OF JUST TRUE/FALSE *)

module type T = sig
  val is_directed : bool
  module V : COMPARABLE

  type gt
  (*@ model dom: V.t fset 
      model suc: V.t -> V.t fset
      invariant forall v1, v2. Set.mem v1 dom /\ Set.mem v2 (suc v1) -> Set.mem v2 dom*)

   val [@logic] succ : gt -> V.t -> V.t list
   (*@ l = succ g v
        requires Set.mem v g.dom
        ensures forall v'. List.mem v' l -> Set.mem v' g.dom
        ensures forall v'. List.mem v' l <-> Set.mem v' (g.suc v) *)

  val all : gt -> V.t list
  (*@ l = all g 
        ensures forall v. List.mem v l <-> Set.mem v g.dom *)
end


module Cycle( G : T ) = struct

module H = Hashtbl.Make(G.V)

(*@ predicate edge (v1 : G.V.t) (v2 : G.V.t) (g : G.gt) = Set.mem v2 (g.G.suc v1) *)

(*@ predicate is_path (v1 : G.V.t) (l : G.V.t seq) (v2 : G.V.t) (g : G.gt) =
            let len = Seq.length l in
            if len = 0 then v1 = v2 else
              edge v1 l[0] g && l[len - 1] = v2 && Set.mem v1 g.G.dom &&
            forall i : int. 0 <= i < len - 1 -> edge l[i] l[i+1] g *)
        
(*@ predicate has_path (v1 : G.V.t) (v2 : G.V.t) (g : G.gt) = 
      exists p : G.V.t seq. is_path v1 p v2 g *)

(*@ predicate is_cycle (l : G.V.t seq) (g : G.gt) = 
      let len = Seq.length l in 
      len <> 0 /\ is_path l[len - 1] l l[len - 1] g*)

exception Exit of (G.V.t*G.V.t) 

let build_path v1 v2 via = 
  let l = ref [v2] in 
  let curr = ref v1 in 
  while not ( G.V.equal !curr v2) do 
     l := !curr::!l  ; curr := H.find via !curr ; 
  done ; !l 
(*@ l = build_path v1 v2 via 
      raises Not_found *)

(**Result == Exists at least one path from A to A*)
let has_cycle_directed g =
  let via = H.create 97 in
  let h = H.create 97 in
  let stack = Stack.create () in
  let loop () =
    while not (Stack.is_empty stack) do
      (*@ variant Set.cardinal g.G.dom - Set.cardinal h.H.dom, Seq.length stack.Stack.view 
          invariant forall v. Seq.mem v stack.Stack.view -> Set.mem v g.G.dom
          invariant Set.subset h.H.dom g.G.dom *)
      let v = Stack.top stack in
      if H.mem h v then begin
        H.replace h v false;
        H.clear via ;
        ignore (Stack.pop stack)
      end else begin
        H.add h v true;
        let scs = G.succ g v in 
        let rec iter_succ = function 
        | [] -> () 
        | w :: l -> try if H.find h w then raise (Exit (w, v))
             with Not_found -> Stack.push w stack ; H.add via w v ; iter_succ l  
        (*@ iter_succ l 
              requires forall v'. Seq.mem v' stack.Stack.view -> Set.mem v' g.G.dom 
              requires forall v'. List.mem v' l -> Set.mem v' g.G.dom 
              variant l
              ensures forall v'. Seq.mem v' stack.Stack.view -> Set.mem v' g.G.dom 
              raises Exit *)
        in iter_succ scs 
      end
    done
  (*@ loop ()
        requires forall v. Seq.mem v stack.Stack.view -> Set.mem v g.G.dom
        requires Set.subset h.H.dom g.G.dom 
        raises Exit
        raises Stack.Empty -> false
        ensures Set.subset h.H.dom g.G.dom 
        ensures forall v. Seq.mem v stack.Stack.view -> Set.mem v g.G.dom
        *)
  in
  try
    let rec iter_vertex = function
    | [] -> ()
    | v :: l -> if not (H.mem h v) then begin Stack.push v stack; loop () ; iter_vertex l end 
    (*@ iter_vertex l
          requires Set.subset h.H.dom g.G.dom 
          requires forall v. List.mem v l -> Set.mem v g.G.dom
          requires forall v. Seq.mem v stack.Stack.view -> Set.mem v g.G.dom
          variant l
          raises Exit *)
    in 
    iter_vertex (G.all g) ;
    []
  with Exit (w, v)  ->
    build_path v w via
    (*@ l = has_cycle_directed g
          raises Not_found *)

  let has_cycle_undirected g =
    let h = H.create 97 in
    let via = H.create 97 in
    let father = H.create 97 in
    let is_father u v = (* u is the father of v in the DFS descent *)
      try G.V.equal (H.find father v) u with Not_found -> false
    in
    let stack = Stack.create () in
    let loop () =
      while not (Stack.is_empty stack) do
      (*@ variant Set.cardinal g.G.dom - Set.cardinal h.H.dom, Seq.length stack.Stack.view 
          invariant forall v. Seq.mem v stack.Stack.view -> Set.mem v g.G.dom
          invariant Set.subset h.H.dom g.G.dom *)
        let v = Stack.top stack in
        if H.mem h v then begin
          H.remove father v;
          H.clear via ;
          H.replace h v false;
          ignore (Stack.pop stack)
        end else begin
          H.add h v true;
          let sucs = G.succ g v in 
          let rec iter_succ = function
          | [] -> () 
          | w :: l -> try if H.find h w && not (is_father w v) then raise (Exit (w, v))
               with Not_found -> H.add father w v; Stack.push w stack ; H.add via w v ; iter_succ l
          (*@ iter_succ l 
              requires forall v'. Seq.mem v' stack.Stack.view -> Set.mem v' g.G.dom 
              requires forall v'. List.mem v' l -> Set.mem v' g.G.dom 
              variant l
              ensures forall v'. Seq.mem v' stack.Stack.view -> Set.mem v' g.G.dom 
              raises Exit *)
          in 
          iter_succ sucs
        end
      done
    (*@ loop ()
        requires forall v. Seq.mem v stack.Stack.view -> Set.mem v g.G.dom
        requires Set.subset h.H.dom g.G.dom 
        raises Exit
        raises Stack.Empty -> false
        ensures Set.subset h.H.dom g.G.dom 
        ensures forall v. Seq.mem v stack.Stack.view -> Set.mem v g.G.dom
        *)
    in
    try
      let rec iter_vertex = function 
      | [] -> () 
      | v :: l -> if not (H.mem h v) then begin Stack.push v stack; loop () ; iter_vertex l end
      (*@ iter_vertex l 
            requires forall v'. List.mem v' l -> Set.mem v' g.G.dom 
            requires forall v. Seq.mem v stack.Stack.view -> Set.mem v g.G.dom
            requires Set.subset h.H.dom g.G.dom 
            variant l 
            raises Exit *)
      in 
      iter_vertex (G.all g) ;
      []
    with Exit (w, v) ->
      build_path v w via
    (*@ l = has_cycle_undirected g
          raises Not_found *)

      
     let has_cycle g =
        if G.is_directed then has_cycle_directed g else has_cycle_undirected g
    (*@ l = has_cycle g 
          raises Not_found *)


    let is_empty = function | [] -> true | _ -> false
    (*@ b = is_empty l 
          ensures b <-> l = [] *)

    let hd = function | [] -> raise Not_found | x :: _ -> x 
    (*@ x = hd l 
        raises Not_found -> l = [] 
        ensures x = (of_list l)[0]
        ensures match l with | [] -> false | v::_-> v = x *)

    (*Paths have the form: v1 [vx, ...., v2] where vx is a successor of v1 *)    
    let is_path_func v1 l v2 g = 
      let rec is_succ v = function 
      | [] -> false 
      | v' :: vs -> G.V.equal v' v || is_succ v vs
      (*@ b = is_succ v l 
            variant l
            ensures b <-> List.mem v l *)
      in 
      let rec iter_path = function 
      | [] -> true
      | v' :: v'' :: vs -> is_succ (v'') (G.succ g v') && iter_path (v'' :: vs)
      | v' :: [] -> G.V.equal v' v2
      (*@ b = iter_path l 
            requires l <> []
            requires forall v. List.mem v l -> Set.mem v g.G.dom
            variant l 
            ensures let s = of_list l in 
              b <-> (forall i. 0 <= i < List.length l - 1 -> edge s[i] s[i+1] g) /\ s[List.length l - 1] = v2 *)
      in
      if is_empty l then G.V.equal v1 v2 else 
        is_succ (hd l) (G.succ g v1) && iter_path l
      (*@ b = is_path_func v1 l v2 g
            requires Set.mem v1 g.G.dom 
            requires Set.mem v2 g.G.dom 
            requires forall v. List.mem v l -> Set.mem v g.G.dom
            raises Not_found -> false
            ensures b <-> is_path v1 (of_list l) v2 g *)



      (*Cycles have the form: [vx, ..., v] where vx is a successor of v. 
      So, single vertex loops take the shape of [v] and empty lists aren't loops *)      
      let is_cycle_func l g =
        let rec get_last = function 
        | x :: [] -> x 
        | x :: xs -> get_last xs 
        | [] -> raise Not_found 
        (*@ x = get_last l
              variant l 
              raises Not_found -> l = []
              ensures List.mem x l
              ensures x = (of_list l)[List.length l - 1] *) 
        in
        not (is_empty l) &&
        let v = get_last l in is_path_func v l v g 
        (*@ b = is_cycle_func l g 
              requires forall v. List.mem v l -> Set.mem v g.G.dom
              raises Not_found -> false
              ensures b <-> is_cycle (of_list l) g *)

end

