(*@ open Set *)
(*@ open FsetSum*)
(*@ open Seq*)
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

module type ORDERED_TYPE_DFT = sig 
    type t 
    val [@logic] compare : t -> t -> int 
    (*@ axiom pre_order_compare: is_pre_order compare*)
    val [@logic] default : t
end



module PersistentLabeledGraph(Vertex: COMPARABLE)(Edge: ORDERED_TYPE_DFT) = struct

  module HM = Map.Make(Vertex)

    module V = struct
      type t = Vertex.t
      type label = t
      let [@logic] compare v1 v2 = Vertex.compare v1 v2
      (*@ axiom pre_order_compare: is_pre_order compare*)
      let [@logic] hash v = Vertex.hash v    
      let equal v1 v2 = Vertex.equal v1 v2
      let label v = v
      let create v = v
    end
    
    (* Vertex * Edge pair hashing*)
    module VE = struct
      type t = V.t * Edge.t
      let [@logic] compare (x1, y1) (x2, y2) =
        let cv = V.compare x1 x2 in
        if cv != 0 then cv else Edge.compare y1 y2
      (*@ axiom pre_order_compare: is_pre_order compare*)
    end
  
    module E = struct

      (* Vertex * (Vertex * Edge) pair hashing*)
      module C = struct
        type t = V.t * VE.t
        let [@logic] compare (x1, y1) (x2, y2) =
          let cv = V.compare x1 x2 in
          if cv != 0 then cv else VE.compare y1 y2
        (*@ axiom pre_order_compare: is_pre_order compare*)
      end

      type vertex = V.t
      type label = Edge.t
      type t = vertex * label * vertex
      let [@logic] src (v, _, _) = v
      let [@logic] dst (_, _, v) = v
      let [@logic] label (_, l, _) = l
      let create v1 l v2 = v1, l, v2
      let compare (x1, x2, x3) (y1, y2, y3) =
        C.compare (x1, (x3, x2)) (y1, (y3, y2))
      (*@ axiom pre_order_compare: is_pre_order compare*)
    end
    
    module S = Set.Make(VE)

    type edge = E.t
    
    type vertex = HM.key

    type t = { self : S.t HM.t }
    (*@ invariant forall v1. Set.mem v1 self.HM.dom -> forall e. Set.mem e (self.HM.view v1).S.dom -> 
            let (v2, l) = e in 
              Set.mem v2 self.HM.dom /\ Set.mem (v1, l) (self.HM.view v2).S.dom  *)

    (*@ predicate vertex_belongs ( g : t ) ( v1 : Vertex.t ) = Set.mem v1 g.self.HM.dom *)

    (*@ predicate vertex_belongs_HM ( g : S.t HM.t ) ( v1 : Vertex.t ) = Set.mem v1 g.HM.dom *)

    (*@ predicate edge_belongs_label ( g : t ) ( v1 : V.t ) ( v2 : V.t ) ( l : E.label ) = 
          let s = g.self.HM.view v1 in 
            vertex_belongs g v1 /\ vertex_belongs g v2 /\ Set.mem (v2, l) s.S.dom *)

    (*@ predicate edge_belongs_label_HM ( g : S.t HM.t ) ( v1 : V.t ) ( v2 : V.t ) ( l : E.label ) = 
          let s = g.HM.view v1 in 
            vertex_belongs_HM g v1 /\ vertex_belongs_HM g v2 /\ Set.mem (v2, l) s.S.dom *)
   
    (*@ predicate edge_belongs ( g : t ) ( v1 : V.t ) ( v2 : V.t ) = 
          exists l. edge_belongs_label g v1 v2 l *)

    (*@ predicate edge_belongs_e ( g : t ) (e : E.t ) = 
          let s1 = g.self.HM.view (E.src e) in 
          let s2 = g.self.HM.view (E.dst e) in
          Set.mem (E.dst e, E.label e) s1.S.dom /\ Set.mem (E.src e, E.label e) s2.S.dom*)

    (*@ predicate consistent ( o : t ) ( n : t) = 
              (forall v. vertex_belongs o v -> vertex_belongs n v) /\
              (forall e. edge_belongs_label o (E.src e) (E.dst e) (E.label e) -> edge_belongs_label n (E.src e) (E.dst e) (E.label e)) *)

    (*@ predicate distinct (s : (Vertex.t * S.t) seq) =
      forall i j. 0 <= i < length s -> 0 <= j < length s ->
            i <> j -> s[i] <> s[j] *)

    (*@ lemma first_mem :  forall l. distinct (of_list l) -> forall i. 1 <= i < Seq.length (of_list l) -> (of_list l)[0] <> (of_list l)[i]  *)

    (*@ lemma sub_list : forall l. distinct (of_list l) -> 
          match l with 
          | [] -> true
          | x :: xs -> distinct xs /\ forall e. List.mem e xs -> e <> x*)


  let mem_edge g v1 v2 =
    try S.existe (fun (v2', _) -> V.equal v2 v2') (HM.find v1 g.self)
    with Not_found -> false
  (*@ b = mem_edge g v1 v2 
        ensures b <-> vertex_belongs g v1 /\ edge_belongs g v1 v2 *)

  let mem_edge_e g (v1, l, v2) =
    try
      let ve = v2, l in
      S.existe (fun ve' -> VE.compare ve ve' = 0) (HM.find v1 g.self)
    with Not_found ->
      false
  (*@ b = mem_edge_e g e 
        ensures b <-> vertex_belongs g (E.src e) /\ edge_belongs_label g (E.src e) (E.dst e) (E.label e)*)

  exception Found of edge

  let find_edge g v1 v2 =
    try
      let es = S.elements (HM.find v1 g.self) in 
      let rec iter_es = function 
      | [] -> ()
      | (v2', l) :: r -> if V.equal v2 v2' then raise (Found (v1, l, v2')) else iter_es r
      (*@ iter_es es 
            variant es 
            raises Found e -> List.mem ((E.dst e), (E.label e)) es  /\ (E.dst e) = v2 /\ (E.src e) = v1
            ensures forall p. List.mem p es -> fst p <> v2
            *)
      in
      iter_es es ; raise Not_found
    with Found e ->
      e
  (*@ e = find_edge g v1 v2 
        raises Not_found -> not (vertex_belongs g v1 ) \/ not (edge_belongs g v1 v2)
        ensures (E.src e) = v1 /\ (E.dst e) = v2 /\ edge_belongs_label g (E.src e) (E.dst e) (E.label e) *)

  let find_all_edges g v1 v2 =
    try
      let es = S.elements (HM.find v1 g.self) in 
      let rec iter_es l (succL : (Vertex.t * Edge.t) list) =
        match succL with 
      | [] -> l 
      | (v2', lab) :: r ->  iter_es (if V.equal v2 v2' then (v1, lab, v2) ::l else l) r
      (*@ edge_l = iter_es acc esL 
            requires forall e. List.mem e es -> vertex_belongs g (fst e)
            requires forall e. List.mem e es -> edge_belongs_label g v1 (fst e) (snd e)
            requires forall e. List.mem e esL -> List.mem e es
            requires forall e. List.mem e acc -> List.mem (E.dst e, E.label e) es /\ E.src e = v1 /\ E.dst e = v2 
            variant esL
            ensures forall e. List.mem e es -> vertex_belongs g (fst e)
            ensures forall e. List.mem e es -> edge_belongs_label g v1 (fst e) (snd e)
            ensures forall e. List.mem e edge_l -> List.mem (E.dst e, E.label e) es /\ E.src e = v1 /\ E.dst e = v2
            ensures forall p. List.mem p acc -> List.mem p edge_l 
            ensures forall p. fst p = v2 /\ List.mem p esL -> List.mem (v1, snd p, v2) edge_l  *)
    in 
    iter_es [] es 
    with Not_found ->
      []
    (*@ l = find_all_edges g v1 v2 
          ensures forall la. List.mem (v1, la, v2) l <-> edge_belongs_label g v1 v2 la   *)


  let succ gr v = 
    let g = gr.self in 
    let sucs_e_set = S.elements (HM.find v g) in 
    let rec convert (acc) ( l : (vertex*Edge.t) list) = 
      match l with
      | [] -> acc 
      | (v, _ ):: xs -> convert ( v::acc) xs  
    (*@ l_p = convert acc l 
          requires forall e. List.mem e l -> List.mem e sucs_e_set
          requires forall e. List.mem e acc -> exists la. List.mem (e, la) sucs_e_set
          variant l
          ensures forall e. List.mem e acc -> List.mem e l_p
          ensures forall e. List.mem e l_p -> exists la. List.mem (e, la) sucs_e_set
          ensures forall e. List.mem e l -> List.mem (fst e) l_p *)
    in convert [] sucs_e_set
  (*@  l = succ g v 
        raises Not_found -> not ( vertex_belongs g v ) 
        ensures forall v'. edge_belongs g v v' <-> List.mem v' l  *)

  let succ_e gr v =     
    let g = gr.self in 
    let sucs_e_set = S.elements (HM.find v g) in 
    let rec convert (acc) ( l : (vertex*Edge.t) list) = 
      match l with
      | [] -> acc 
      | (v', c ):: xs -> convert ( (v, c, v' )::acc) xs  
    (*@ l_p = convert acc l 
          requires forall e. List.mem e l -> List.mem e sucs_e_set
          requires forall e. List.mem e acc -> List.mem (E.dst e, E.label e) sucs_e_set /\ E.src e = v
          variant l
          ensures forall e. List.mem e acc -> List.mem e l_p
          ensures forall e. List.mem e l_p -> List.mem (E.dst e, E.label e) sucs_e_set /\ E.src e = v
          ensures forall e. List.mem e l -> List.mem (v, snd e, fst e) l_p  *) 

    in convert [] sucs_e_set 
    (*@  l = succ_e g v 
        raises Not_found -> not ( vertex_belongs g v )
        ensures forall e. List.mem e l <-> edge_belongs_label g (E.src e) (E.dst e) (E.label e) /\ E.src e = v *)
    
  let empty = { self = HM.empty }
  (*@ g = empty 
        ensures g.self.HM.dom = Set.empty *)

  let is_empty g = HM.is_empty g.self
  (*@ b = is_empty g
        ensures b <-> g.self.HM.dom = Set.empty *)

  let copy g = g
  (*@ g2 = copy g1
        ensures g1 = g2 *)

  let nb_vertex g = HM.cardinal g.self
  (*@ n_v = nb_vertex g 
        ensures n_v = Set.cardinal g.self.HM.dom *)
  
  (* let nb_edges g = 
    let rec iter_succs su (l : (Vertex.t * S.t) list ) =
    match l with  
    | [] -> su
    | (v, sucs):: xs -> iter_succs (su + S.cardinal sucs) xs 
    (* s = iter_succs sum l 
        variant l
        ensures s = sum_list l sum *)
    in  
    iter_succs 0 (HM.bindings g.self) / 2
  n_e = nb_edges g
       ensures n_e = div (n_edges g) 2*)
  
  let out_degree g v =
    S.cardinal
      (try HM.find v g.self with Not_found -> invalid_arg "[ocamlgraph] out_degree")
  (*@ d = out_degree g v 
        raises Invalid_argument _ -> not (vertex_belongs g v)
        ensures d = Set.cardinal (g.self.HM.view v).S.dom *)

  let mem_vertex g v = HM.mem v g.self
  (*@ b = mem_vertex g v 
        ensures b <-> vertex_belongs g v *)

  let unsafe_add_vertex g v = { self = HM.add v S.empty g.self }
  (*@ g2 = mem_vertex g1 v 
      requires not (vertex_belongs g1 v)
      ensures vertex_belongs g2 v 
      ensures forall v. vertex_belongs g1 v -> vertex_belongs g2 v
      ensures forall vx, vy, l. vertex_belongs g1 vx /\ vertex_belongs g1 vy /\  edge_belongs_label g1 vx vy l -> edge_belongs_label g2 vx vy l 
      ensures (g2.self.HM.view v).S.dom = Set.empty *)

  let add_vertex g v = if HM.mem v g.self then g else unsafe_add_vertex g v
  (*@ g2 = add_vertex g1 v 
      ensures vertex_belongs g2 v 
      ensures consistent g1 g2
      ensures if not (vertex_belongs g1 v) then
         (g2.self.HM.view v).S.dom = Set.empty else (g2.self.HM.view v).S.dom = (g1.self.HM.view v).S.dom*)
  
  let is_directed = false

  let pred g v = succ g v
  (*@ l = pred g v 
        raises Not_found
        ensures forall e. List.mem e l <-> edge_belongs g e v *)


  let in_degree g v = out_degree g v 
  (*@ d = in_degree g v 
        raises Invalid_argument _ -> not (vertex_belongs g v)
        ensures d = Set.cardinal (g.self.HM.view v).S.dom  *)
  
  let pred_e gr v = 
    let g = gr.self in 
    let sucs_e_set = S.elements (HM.find v g) in 
    let rec convert (acc) ( l : (vertex*Edge.t) list) = 
      match l with
      | [] -> acc 
      | (v', c ):: xs -> convert ( (v', c, v )::acc) xs  
    (*@ l_p = convert acc l 
          requires forall e. List.mem e l -> List.mem e sucs_e_set
          requires forall e. List.mem e acc -> List.mem (E.src e, E.label e) sucs_e_set /\ E.dst e = v
          variant l
          ensures forall e. List.mem e acc -> List.mem e l_p
          ensures forall e. List.mem e l_p -> List.mem (E.src e, E.label e) sucs_e_set /\ E.dst e = v
          ensures forall e. List.mem e l -> List.mem (fst e, snd e, v) l_p  *) 

    in convert [] sucs_e_set 
    (*@  l = pred_e g v 
        raises Not_found -> not ( vertex_belongs g v )
        ensures forall e. List.mem e l <-> edge_belongs_label g (E.src e) (E.dst e) (E.label e) /\ E.dst e = v *)

  let add_edge_e g e =
    let (v1, l, v2) = e in 
    if mem_edge_e g e then g
    else
      let g = add_vertex g v1 in
      let g = add_vertex g v2 in
      let gr =  HM.add v1 (S.add (v2, l) (HM.find v1 g.self)) g.self in
      { self = HM.add v2 (S.add (v1, l) (HM.find v2 gr)) gr }
  (*@ g2 = add_edge_e g1 e 
        raises Not_found -> false
        ensures vertex_belongs g2 (E.src e) 
        ensures vertex_belongs g2 (E.dst e)
        ensures edge_belongs_label g2 (E.src e) (E.dst e) (E.label e)
        ensures edge_belongs_label g2 (E.dst e) (E.src e) (E.label e)  *)
        

  let add_edge g v1 v2 = add_edge_e g (v1, Edge.default, v2)
  (*@ g2 = add_edge g1 v1 v2 
        ensures vertex_belongs g2 v1
        ensures vertex_belongs g2 v2
        ensures edge_belongs_label g2 v1 v2 Edge.default
        ensures edge_belongs_label g2 v2 v1 Edge.default *)

  let remove_edge g v1 v2 =
    let not_equal v (v', _) = not (V.equal v v') 
    (*@ b = not_equal v p 
          ensures b <-> v <> fst p *)
    in
    if not (HM.mem v2 g.self) then invalid_arg "[ocamlgraph] remove_edge" else begin
    let gr = HM.add v1 (S.filter (not_equal v2) (HM.find v1 g.self)) g.self in
    let gr = HM.add v2 (S.filter (not_equal v1) (HM.find v2 gr)) gr in { self = gr } end
  (*@ g2 = remove_edge g1 v1 v2 
        raises Not_found -> not (vertex_belongs g1 v1) 
        raises Invalid_argument _ -> not (vertex_belongs g1 v2) 
        ensures not (edge_belongs g2 v1 v2)
        ensures not (edge_belongs g2 v2 v1)
        ensures vertex_belongs g2 v1
        ensures vertex_belongs g2 v2
        ensures forall v. vertex_belongs g1 v -> vertex_belongs g2 v
        ensures forall vy, vx, l. vx <> v1 /\ vx <> v2 /\ edge_belongs_label g1 vx vy l -> edge_belongs_label g2 vx vy l
        ensures forall vy, l. edge_belongs_label g1 v1 vy l /\ vy <> v2 -> edge_belongs_label g2 v1 vy l
        ensures forall vx, l. edge_belongs_label g1 vx v2 l /\ vx <> v1 -> edge_belongs_label g2 vx v2 l *)  

  let remove_edge_e g e =
    let (v1, l, v2) = e in 
    if not (HM.mem v2 g.self) then invalid_arg "[ocamlgraph] remove_edge_e" else begin
    let gr = 
      HM.add v2 (S.remove (v1, l) (HM.find v2 g.self)) g.self in 
    { self = HM.add v1 (S.remove (v2, l) (HM.find v1 gr)) gr } end
  (*@ g2 = remove_edge_e g1 e
        raises Not_found -> not (vertex_belongs g1 (E.src e))
        raises Invalid_argument _ -> not (vertex_belongs g1 (E.dst e))   
        ensures not (edge_belongs_label g2 (E.src e) (E.dst e) (E.label e))
        ensures not (edge_belongs_label g2 (E.dst e) (E.src e) (E.label e))
        ensures forall v. vertex_belongs g1 v -> vertex_belongs g2 v
        ensures forall vy, l. edge_belongs_label g1 (E.src e) vy l /\ vy <> (E.dst e) -> edge_belongs_label g2 (E.src e) vy l
        ensures forall vx, l. edge_belongs_label g1 vx (E.dst e) l /\ vx <> (E.src e) -> edge_belongs_label g2 vx (E.dst e) l
        ensures forall l.  edge_belongs_label g1 (E.src e) (E.dst e) l /\ l <> (E.label e) -> edge_belongs_label g2 (E.src e) (E.dst e) l 
        ensures forall vx, vy, l. edge_belongs_label g1 vx vy l /\ vx <> (E.src e) /\ vx <> (E.dst e) -> edge_belongs_label g2 vx vy l  *)

    let remove_vertex g v = 
      let gr = HM.remove v g.self in 
      let binds = HM.bindings gr in
      let rec iter_keys g (prefix [@ghost] )= function 
      | [] -> g
      | (x, st) :: r -> let st' = S.filter (fun (v',_) -> not (Vertex.equal v v') ) st in 
              iter_keys (HM.add x st' g) (prefix @ [x]) r 
      (*@ g2 = iter_keys g1 pre l 
          requires forall v1. Set.mem v1 g1.HM.dom -> forall e. Set.mem e (g1.HM.view v1).S.dom /\ fst e <> v -> 
            let (v2, l) = e in 
              Set.mem v2 g1.HM.dom /\ Set.mem (v1, l) (g1.HM.view v2).S.dom
          requires not (Set.mem v g1.HM.dom)
          requires distinct l
          requires forall e. List.mem e pre -> forall p. List.mem p l -> fst p <> e
          requires forall v'. Set.mem v' g1.HM.dom -> List.mem v' pre \/ exists s. List.mem (v', s) l
          requires forall e. List.mem e pre -> Set.mem e g1.HM.dom /\ forall p. Set.mem p (g1.HM.view e).S.dom -> fst p <> v
          requires forall p1, p2. List.mem p1 l /\ List.mem p2 l /\ p1 <> p2 -> fst p1 <> fst p2 
          requires forall p. List.mem p l -> Set.mem (fst p) g1.HM.dom /\ snd p = g1.HM.view (fst p)
          variant l 
          ensures not (Set.mem v g1.HM.dom)
          ensures forall v1, v2, l. edge_belongs_label_HM g2 v1 v2 l ->  edge_belongs_label_HM g1 v1 v2 l
          ensures forall v1, v2, l. edge_belongs_label_HM g1 v1 v2 l /\ v1 <> v /\ v2 <> v -> edge_belongs_label_HM g2 v1 v2 l
          ensures forall v'. Set.mem v' g1.HM.dom <-> Set.mem v' g2.HM.dom
          ensures forall v'. Set.mem v' g2.HM.dom -> forall p. Set.mem p (g2.HM.view v').S.dom -> fst p <> v 
          ensures forall v1. Set.mem v1 g2.HM.dom -> forall e. Set.mem e (g2.HM.view v1).S.dom -> 
            let (v2, l) = e in 
              Set.mem v2 g2.HM.dom /\ Set.mem (v1, l) (g2.HM.view v2).S.dom
          *)
      in
      let gr2 = iter_keys gr [] binds in 
      {self = gr2 }
    (*@ g2 = remove_vertex g1 v 
        ensures not (vertex_belongs g2 v)
        ensures forall v'. vertex_belongs g2 v' -> not (edge_belongs g2 v' v)
        ensures forall v'. vertex_belongs g1 v' /\ v' <> v -> vertex_belongs g2 v'
        ensures forall v1, v2, l. edge_belongs_label g1 v1 v2 l /\ v1 <> v /\ v2 <> v -> edge_belongs_label g2 v1 v2 l
        ensures forall v1, v2, l. edge_belongs_label g2 v1 v2 l -> edge_belongs_label g1 v1 v2 l
        *)

end

