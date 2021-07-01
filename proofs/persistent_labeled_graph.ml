(*@ open Set *)

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

    type t = { self : S.t HM.t }
    (*@ invariant forall v1. Set.mem v1 self.HM.dom -> forall e. Set.mem e (self.HM.view v1).S.dom -> 
            Set.mem (fst e) self.HM.dom /\ Set.mem (v1, (snd e)) (self.HM.view (fst e)).S.dom *)

    (*@ predicate edge_belongs ( g : t ) ( v1 : V.t ) ( v2 : V.t ) = 
        let s = g.self.HM.view v1 in 
          exists l. Set.mem (v2, l) s.S.dom *)

    (*@ predicate edge_belongs_label ( g : t ) ( v1 : V.t ) ( v2 : V.t ) ( l : E.label ) = 
        let s = g.self.HM.view v1 in 
          Set.mem (v2, l) s.S.dom *)
    
    (*@ predicate vertex_belongs ( g : t ) ( v1 : Vertex.t ) = Set.mem v1 g.self.HM.dom *)

    (*@ predicate edge_belongs_e ( g : t ) (e : E.t ) = 
          let s1 = g.self.HM.view (E.src e) in 
          let s2 = g.self.HM.view (E.dst e) in
          Set.mem (E.dst e, E.label e) s1.S.dom /\ Set.mem (E.src e, E.label e) s2.S.dom*)

    (*@ predicate consistent ( o : t ) ( n : t) = 
              (forall v. vertex_belongs o v -> vertex_belongs n v) /\
              (forall e. edge_belongs_e o e -> edge_belongs_e n e) *)


  

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
  (*let find_edge g v1 v2 =
    try
      S.iter
        (fun (v2', l) -> if V.equal v2 v2' then raise (Found (v1, l, v2')))
        (HM.find v1 g);
      raise Not_found
    with Found e ->
      e

  let find_all_edges g v1 v2 =
    try
      S.fold
        (fun (v2', l) acc ->
           if V.equal v2 v2' then (v1, l, v2') :: acc else acc)
        (HM.find v1 g)
        []
    with Not_found ->
      []*)

  (*let unsafe_remove_edge g v1 v2 =
    let noEq  (v2', _) = not (V.equal v2 v2')
    (*@ b = noEq p
          ensures b <-> v2 <> fst p *)
    in 
    { self = HM.add
      v1
      (S.filter noEq (HM.find v1 g.self))
      g.self }
  @ g2 = unsafe_remove_edge g1 v1 v2
        requires vertex_belongs g1 v2  
        requires edge_belongs g1 v1 v2 
        raises Not_found -> not (vertex_belongs g1 v1)
        ensures not(edge_belongs g2 v1 v2) 
        ensures forall v. vertex_belongs g1 v -> vertex_belongs g2 v 
        ensures forall vy, vx. vx <> v1 /\ vy <> v2 /\ edge_belongs g1 vx vy -> edge_belongs g2 vx vy
        ensures forall vy. edge_belongs g1 v1 vy /\ vy <> v2 -> edge_belongs g2 v1 vy
        ensures forall vx. edge_belongs g1 vx v2 /\ vx <> v1 -> edge_belongs g2 vx v2 *)

  (*let unsafe_remove_edge_e gr (v1, l, v2) =
    let g = gr.self in 
    { self = HM.add v1 (S.remove (v2, l) (HM.find v1 g)) g }
  @  g2 = unsafe_remove_edge_e g1 e 
        raises Not_found -> not (vertex_belongs g1 (E.src e)) 
        ensures not(edge_belongs_label g2 (E.src e) (E.dst e) (E.label e))
        ensures forall v. vertex_belongs g1 v -> vertex_belongs g2 v 
        ensures forall vy, vx. vx <> E.src e /\ vy <> E.dst e /\ edge_belongs g1 vx vy -> edge_belongs g2 vx vy
        ensures forall vy. edge_belongs g1 (E.src e) vy /\ vy <> (E.dst e) -> edge_belongs g2 (E.src e) vy
        ensures forall vx. edge_belongs g1 vx (E.dst e) /\ vx <> (E.src e) -> edge_belongs g2 vx (E.dst e) *)

  (*let remove_edge_support gr v1 v2 =
    let g = gr.self in 
    if not (HM.mem v2 g) then invalid_arg "[ocamlgraph] remove_edge";
    { self = HM.add
      v1
      (S.filter
         (fun (v2', _) -> not (V.equal v2 v2'))
         (HM.find v1 g))
      g }
  @ g2 = remove_edge_support g1 v1 v2
        requires edge_belongs g1 v1 v2
        raises Not_found -> not (vertex_belongs g1 v1) 
        raises Invalid_argument _  -> not ( vertex_belongs g1 v2 )
        ensures not(edge_belongs g2 v1 v2)        
        ensures forall v. vertex_belongs g1 v -> vertex_belongs g2 v 
        ensures forall vy, vx. vx <> v1 /\ vy <> v2 /\ edge_belongs g1 vx vy -> edge_belongs g2 vx vy
        ensures forall vy. edge_belongs g1 v1 vy /\ vy <> v2 -> edge_belongs g2 v1 vy
        ensures forall vx. edge_belongs g1 vx v2 /\ vx <> v1 -> edge_belongs g2 vx v2  *)

    (*{ self = HM.add
      v1
      (S.filter
         (fun (v2', _) -> not (V.equal v2 v2'))
         (HM.find v1 g))
      g } original, refactoring *)  


  (*let remove_edge_e_support gr (v1, l, v2) =
    let g = gr.self in 
    if not (HM.mem v2 g) then invalid_arg "[ocamlgraph] remove_edge_e";
    { self = HM.add
      v1
      (S.remove (v2, l) (HM.find v1 g))
      g }
    g2 = remove_edge_e_support g1 e 
        raises Not_found -> not ( vertex_belongs g1 (E.src e) )
        raises Invalid_argument _ -> not ( vertex_belongs g1 (E.dst e) )  
        ensures not(edge_belongs_label g2 (E.src e) (E.dst e) (E.label e))        
        ensures forall v. vertex_belongs g1 v -> vertex_belongs g2 v 
        ensures forall vy, vx. vx <> (E.src e) /\ vy <> (E.dst e) /\ edge_belongs g1 vx vy -> edge_belongs g2 vx vy
        ensures forall vy. edge_belongs g1 (E.src e) vy /\ vy <> (E.dst e) -> edge_belongs g2 (E.src e) vy
        ensures forall vx. edge_belongs g1 vx (E.dst e) /\ vx <> (E.src e) -> edge_belongs g2 vx (E.dst e)  *)

  (*let iter_succ f g v =
    S.iter (fun (w, _) -> f w) (HM.find v g)
  let fold_succ f g v =
    S.fold (fun (w, _) -> f w) (HM.find v g)

  let iter_succ_e f g v =
    S.iter
      (fun (w, l) -> f (v, l, w))
      (HM.find v g)

  let fold_succ_e f g v =
    S.fold
      (fun (w, l) -> f (v, l, w))
      (HM.find v g)*)

  let succ gr v = 
    let g = gr.self in 
    let sucs_e_set = S.elements (HM.find v g) in 
    let ss = ref [] in
    let rec iter_s = function 
    | [] -> ()  
    | (v', c):: l -> ss := v'::!ss ; iter_s l 
    (*@ iter_s l1 
        requires forall v'. List.mem v' !ss -> exists la. List.mem (v', la) l1
        variant l1
        ensures forall p. List.mem p l1 <-> List.mem (fst p) !ss *)
    in  
    iter_s sucs_e_set ; !ss
  (*@  l = succ g v 
        raises Not_found -> not ( vertex_belongs g v )
        ensures forall p. Set.mem p (g.self.HM.view v).S.dom -> List.mem (fst p) l
        ensures forall v'. List.mem v' l <-> edge_belongs g v v' *)

  let succ_e gr v =     
    let g = gr.self in 
    let sucs_e_set = S.elements (HM.find v g) in 
    let ss = ref [] in
    let rec iter_s = function 
    | [] -> ()  
    | (v', c):: l -> ss := (v, c, v')::!ss ; iter_s l
    (*@ iter_s l1 
          variant l1 
          requires forall e. List.mem e !ss -> List.mem ((E.dst e), (E.label e)) l1 
          ensures forall e. List.mem e !ss <-> List.mem ((E.dst e), (E.label e)) l1 *)
    in  
    iter_s sucs_e_set ; !ss
  (*@  l = succ_e g v 
       raises Not_found 
       ensures forall e. List.mem e l <-> edge_belongs_label g (E.src e) (E.dst e) (E.label e)*)

  (*let map_vertex f g =
    let module MV = Util.Memo(V) in
    let f = MV.memo f in
    HM.map
      (fun v s -> f v, S.fold (fun (v, l) s -> S.add (f v, l) s) s S.empty) g*)

  
    (*let iter_succ f g v =
      S.iter (fun (w, _) -> f w) (HM.find v g)
    let fold_succ f g v =
      S.fold (fun (w, _) -> f w) (HM.find v g )
  
    let iter_succ_e f g v =
      S.iter
        (fun (w, l) -> f (v, l, w))
        (HM.find v g)
  
    let fold_succ_e f g v =
      S.fold
        (fun (w, l) -> f (v, l, w))
        (HM.find v g)

    let map_vertex f g =
      let module MV = Util.Memo(V) in
      let f = MV.memo f in
      HM.map
        (fun v s -> f v, S.fold (fun (v, l) s -> S.add (f v, l) s) s S.empty) g
  

      let iter_edges f = HM.iter (fun v -> S.iter (fun (w, _) -> f v w))
      let fold_edges f = HM.fold (fun v -> S.fold (fun (w, _) -> f v w))
      let iter_edges_e f =
        HM.iter (fun v -> S.iter (fun (w, l) -> f (v, l, w)))
      let fold_edges_e f =
        HM.fold (fun v -> S.fold (fun (w, l) -> f (v, l, w)))

  
    let iter_pred f g v =
      if not (mem_vertex v g) then invalid_arg "[ocamlgraph] iter_pred";
      iter_edges (fun v1 v2 -> if V.equal v v2 then f v1) g
  
    let fold_pred f g v =
      if not (mem_vertex v g) then invalid_arg "[ocamlgraph] fold_pred";
      fold_edges (fun v1 v2 a -> if V.equal v v2 then f v1 a else a) g*)
  
    (*let iter_pred_e f g v =
      if not (mem_vertex v g) then invalid_arg "[ocamlgraph] iter_pred_e";
      iter_edges_e (fun e -> if V.equal v (E.dst e) then f e) g
  
    let fold_pred_e f g v =
      if not (mem_vertex v g) then invalid_arg "[ocamlgraph] fold_pred_e";
      fold_edges_e (fun e a -> if V.equal v (E.dst e) then f e a else a) g*)


    
  type vertex = HM.key

  let empty = { self = HM.empty }
  (*@ g = empty 
        ensures g.self.HM.dom = Set.empty *)
  let is_empty g = HM.is_empty g.self
  let copy g = g

  (*let nb_vertex g = HM.fold (fun _ _ -> succ) g 0*)
  (*let nb_edges g = HM.fold (fun _ s n -> n + S.cardinal s) g 0*)
  
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
      ensures consistent g1 g2 
      ensures (g2.self.HM.view v).S.dom = Set.empty *)

  (*let unsafe_add_edge gr v1 v2 = let g = gr.self in { self = HM.add v1 (S.add v2 (HM.find v1 g)) g }
  @ g2 = unsafe_add_edge g1 v1 v2 
        raises Not_found *)

  let add_vertex g v = if HM.mem v g.self then g else unsafe_add_vertex g v
  (*@ g2 = add_vertex g1 v 
      ensures vertex_belongs g2 v 
      ensures consistent g1 g2 
      ensures if not (vertex_belongs g1 v) then
         (g2.self.HM.view v).S.dom = Set.empty else (g2.self.HM.view v).S.dom = (g1.self.HM.view v).S.dom*)

    (*let add_edge_e_support g e =
      let (v1, l, v2) = e in
      if mem_edge_e g e then g
      else
        let g = add_vertex g v1 in
        let g = add_vertex g v2 in
        unsafe_add_edge g v1 (v2, l)
    @ g2 = add_edge_e_support g1 e 
          raises Not_found -> false *)

    (*let add_edge_support g v1 v2 = add_edge_e_support g (v1, Edge.default, v2)
    @ g2 = add_edge_support g1 v1 v2 
        raises Not_found -> false *)

    (*let remove_vertex g v =
      if HM.mem v g then
        let g = HM.remove v g in
        let remove v = S.filter (fun (v2, _) -> not (V.equal v v2)) in
        HM.fold (fun k s -> HM.add k (remove v s)) g empty
      else
        g*)
  
  
  let is_directed = false

  (* Redefine iterators and [nb_edges]. *)

  (*let nb_edges g = fold_edges_e (fun _ -> (+) 1) g 0*)

  (* Redefine operations on predecessors:
     predecessors are successors in an undirected graph. *)

  let pred g v = succ g v
  (*@ l = pred g v 
        raises Not_found *)
  let in_degree g v = out_degree g v 
  (*@ d = in_degree g v 
        raises Invalid_argument _ -> not (vertex_belongs g v)
        ensures d = Set.cardinal (g.self.HM.view v).S.dom  *)
  
  let pred_e g v = succ_e g v
  (*@ l = pred_e g v 
        raises Not_found *)  

  (* Redefine the [add_edge] and [remove_edge] operations *)

  (*  let add_edge_e g e =
    let (v1, l, v2) = e in 
    let g = add_edge_e_support g e in
    assert (HM.mem v1 g.self );
    unsafe_add_edge g v2 (v1, l)*)


  let add_edge_e g e =
    let (v1, l, v2) = e in 
    if mem_edge_e g e then g
    else
      let g = add_vertex g v1 in
      let g = add_vertex g v2 in
      let g =  { self = HM.add v1 (S.add (v2, l) (HM.find v1 g.self)) g.self } in
      { self = HM.add v2 (S.add (v1, l) (HM.find v2 g.self)) g.self }
  (*@ g2 = add_edge_e g1 e 
        raises Not_found -> false
        ensures vertex_belongs g2 (E.src e) 
        ensures vertex_belongs g2 (E.dst e)
        ensures edge_belongs_label g2 (E.src e) (E.dst e) (E.label e)
        ensures edge_belongs_label g2 (E.dst e) (E.src e) (E.label e)
        *)
        

  let add_edge g v1 v2 = add_edge_e g (v1, Edge.default, v2)
  (*@ g2 = add_edge g1 v1 v2 
        ensures vertex_belongs g2 v1
        ensures vertex_belongs g2 v2
        ensures edge_belongs_label g2 v1 v2 Edge.default
        ensures edge_belongs_label g2 v2 v1 Edge.default *)

(*  let remove_edge g v1 v2 =
    let g = remove_edge_support g v1 v2 in
    unsafe_remove_edge g v2 v1*)

  let remove_edge g v1 v2 =
    if not (HM.mem v2 g.self) then invalid_arg "[ocamlgraph] remove_edge" else 
    let g = 
    { self = HM.add v1 (S.filter (fun (v2', _) -> not (V.equal v2 v2')) 
                (HM.find v1 g.self)) g.self } in
    { self = HM.add v2 (S.filter (fun (v1', _) -> not (V.equal v1 v1')) 
                (HM.find v2 g.self)) g.self } 
  (*@ g2 = remove_edge g1 v1 v2 
        raises Not_found -> not (vertex_belongs g1 v1) 
        raises Invalid_argument _ -> not (vertex_belongs g1 v2) 
        ensures not (edge_belongs g2 v1 v2)
        ensures not (edge_belongs g2 v2 v1)
        ensures forall v. vertex_belongs g1 v -> vertex_belongs g2 v
        ensures forall vy, vx. vx <> v1 /\ vy <> v2 /\ edge_belongs g1 vx vy -> edge_belongs g2 vx vy
        ensures forall vy. edge_belongs g1 v1 vy /\ vy <> v2 -> edge_belongs g2 v1 vy
        ensures forall vx. edge_belongs g1 vx v2 /\ vx <> v1 -> edge_belongs g2 vx v2
        *)
  
(*  let remove_edge_e g e =
    let (v1, l, v2) = e in 
    let g = remove_edge_e_support g e in
    unsafe_remove_edge_e g (v2, l, v1)*)
  

  let remove_edge_e g e =
    let (v1, l, v2) = e in 
    if not (HM.mem v2 g.self) then invalid_arg "[ocamlgraph] remove_edge_e" else 
    let g = 
      { self = HM.add v2 (S.remove (v1, l) (HM.find v2 g.self)) g.self } in 
    { self = HM.add v1 (S.remove (v2, l) (HM.find v1 g.self)) g.self }
  (*@ g2 = remove_edge_e g1 e
        raises Not_found -> not (vertex_belongs g1 (E.src e))
        raises Invalid_argument _ -> not (vertex_belongs g1 (E.dst e))   
        ensures not (edge_belongs_label g2 (E.src e) (E.dst e) (E.label e))
        ensures not (edge_belongs_label g2 (E.dst e) (E.src e) (E.label e))
        ensures forall v. vertex_belongs g1 v -> vertex_belongs g2 v
        ensures forall e'. e <> e' /\ edge_belongs_label g1 (E.src e') (E.dst e') (E.label e') 
              -> edge_belongs_label g2 (E.src e') (E.dst e') (E.label e') *)

end

