(*@ open Set *)

module type COMPARABLE = sig
  type t
  val[@logic] compare : t -> t -> int

  (*@ axiom pre_order : is_pre_order compare *)

  val hash : t -> int
  val equal : t -> t -> bool
end


module ImperativeUnlabeledDigraph(Vertex: COMPARABLE) = struct

  module HM = Hashtbl.Make(Vertex)

  module S = Set.Make(Vertex)

  module V = struct
    type t = Vertex.t
    type label = t
    let compare = Vertex.compare
    let hash = Vertex.hash
    let equal = Vertex.equal
    let label v = v
    let create v = v
  end

  module E = struct
    type vertex = V.t
    type t = V.t * V.t
    let compare (x1, y1) (x2, y2) =
      let cv = V.compare x1 x2 in
      if cv != 0 then cv else V.compare y1 y2
    let src = fst
    let dst = snd
    type label = unit
    let label _ = ()
    let create v1 () v2 = v1, v2
  end

  type edge = E.t

  type vertex = HM.key

  (*@ function succ_hm ( g : S.t HM.t ) ( v1 : Vertex.t ) : Vertex.t fset = 
        match g.HM.view v1 with    
        | [] -> Set.empty          
        | x :: _ -> x.S.dom *)     

   type t = { mutable self: S.t HM.t }
   (*@ invariant forall v1. Set.mem v1 self.HM.dom -> forall v2. Set.mem v2 (succ_hm self v1) -> Set.mem v2 self.HM.dom *)

  (*@ function succ ( g : t ) ( v1 : Vertex.t ) : Vertex.t fset = 
        match g.self.HM.view v1 with    
        | [] -> Set.empty          
        | x :: _ -> x.S.dom *)     


  (*@ predicate edge_belongs ( g : t ) ( v1 : Vertex.t ) ( v2 : Vertex.t ) = 
      match g.self.HM.view v1 with 
      | [] -> false
      | x :: _ ->  Set.mem v2 x.S.dom *)

  (*@ predicate vertex_belongs ( g : t ) ( v1 : Vertex.t ) = Set.mem v1 g.self.HM.dom *)

  (*@ predicate consistent ( o : t ) ( n : t) = 
            (forall v. vertex_belongs o v -> vertex_belongs n v) /\ (forall v1, v2. edge_belongs o v1 v2 -> edge_belongs n v1 v2 ) *)

  let mem_edge gr v1 v2 =
    let g = gr.self in
    try S.mem v2 (HM.find g v1 )
    with Not_found -> false
  (*@ b = mem_edge g v1 v2
        ensures b <-> edge_belongs g v1 v2 
        ensures consistent (old g) g 
        ensures consistent g (old g) *)

  let mem_edge_e g (v1, v2) = mem_edge g v1 v2
  (*@ b = mem_edge_e g p 
        ensures b <-> edge_belongs g (fst p) (snd p)        
        ensures consistent (old g) g 
        ensures consistent g (old g) *)

  let find_edge g v1 v2 = if mem_edge g v1 v2 then v1, v2 else raise Not_found
  (*@ (vx, vy) = find_edge g v1 v2
        raises Not_found -> not ( edge_belongs g v1 v2 )
        ensures edge_belongs g v1 v2 
        ensures vx = v1 /\ vy = v2 
        ensures consistent (old g) g 
        ensures consistent g (old g) *)

  
  let find_all_edges g v1 v2 = try [ find_edge g v1 v2 ] with Not_found -> []
  (*@ l = find_all_edges g v1 v2
        ensures not ( edge_belongs g v1 v2 ) <-> l = []
        ensures edge_belongs g v1 v2 -> match l with | [] -> false | x :: r -> r = [] /\ fst x = v1 /\ snd x = v2
        ensures consistent (old g) g 
        ensures consistent g (old g)  *)

  (*let unsafe_remove_edge gr v1 v2 = let g = gr.self in HM.add g v1 (S.remove v2 (HM.find g v1))
  @ unsafe_remove_edge g v1 v2
        requires vertex_belongs g v1 -> edge_belongs g v1 v2
        requires vertex_belongs g v1 -> vertex_belongs g v2
        raises Not_found -> not ( vertex_belongs g v1 )
        ensures Set.subset (succ g v1) (succ (old g) v1 )
        ensures forall v. vertex_belongs (old g) v -> vertex_belongs g v
        ensures not ( edge_belongs g v1 v2 )
        ensures forall vy. vy <> v2 /\ edge_belongs (old g) v1 vy -> edge_belongs g v1 vy
        ensures forall vx. vx <> v1 /\ edge_belongs (old g) vx v2 -> edge_belongs g vx v2
        ensures forall vx, vy. vx <> v1 /\ vy <> v2 /\ edge_belongs (old g) vx vy -> edge_belongs g vx vy *)

  (*let unsafe_remove_edge_e g (v1, v2) = unsafe_remove_edge g v1 v2
  @ unsafe_remove_edge_e g p 
        requires edge_belongs g (fst p) (snd p)
        requires vertex_belongs g (snd p)
        requires vertex_belongs g (fst p) 
        raises Not_found -> not ( vertex_belongs g (fst p) )
        ensures Set.subset (succ g (fst p)) (succ (old g) (fst p) )
        ensures not (edge_belongs g (fst p) (snd p))
        ensures forall vy. vy <> (snd p) /\ edge_belongs (old g) (fst p) vy -> edge_belongs g (fst p) vy
        ensures forall vx. vx <> (fst p) /\ edge_belongs (old g) vx (snd p) -> edge_belongs g vx (snd p)
        ensures forall v. vertex_belongs (old g) v -> vertex_belongs g v  
        ensures forall p'. (fst p') <> (fst p) /\ (snd p') <> (snd p) /\ edge_belongs (old g) (fst p') (snd p') -> edge_belongs g (fst p') (snd p')*)
               

  let remove_edge gr v1 v2 =
    let g = gr.self in
    if not (HM.mem g v2 ) then invalid_arg "[ocamlgraph] remove_edge";
    HM.add g v1 (S.remove v2 (HM.find g v1))
  (*@ remove_edge g v1 v2
        raises Not_found -> not vertex_belongs g v1
        raises Invalid_argument _ -> not vertex_belongs g v2 
        ensures not (edge_belongs g v1 v2)
        ensures Set.subset (succ g v1) (succ (old g) v1 )
        ensures forall vx, vy. vx <> v1 /\ vy <> v2 /\ edge_belongs (old g) vx vy -> edge_belongs g vx vy
        ensures edge_belongs g v1 v2 -> let dif = Set.diff (succ (old g) v1 ) (succ g v1) in
               Set.cardinal dif = 1 /\ Set.mem v2 dif *)

  let remove_edge_e g (v1, v2) = remove_edge g v1 v2
  (*@ remove_edge_e g p 
        raises Not_found -> not vertex_belongs g (fst p)
        raises Invalid_argument _ -> not vertex_belongs g (snd p)
        ensures not (edge_belongs g (fst p) (snd p))
        ensures Set.subset (succ g (fst p)) (succ (old g) (fst p) )
        ensures forall p'. (fst p') <> (fst p) /\ (snd p') <> (snd p) /\ edge_belongs (old g) (fst p') (snd p') -> edge_belongs g (fst p') (snd p')
        ensures edge_belongs g (fst p) (snd p) -> let dif = Set.diff (succ (old g) (fst p) ) (succ g (fst p) ) in
               Set.cardinal dif = 1 /\ Set.mem (snd p) dif *) 

  let is_directed = true
  let empty = ()
  let create n = { self = HM.create n } 
  (*@ g = create n 
         ensures g.self.HM.dom = Set.empty *)
  
  let is_empty h = (HM.length h.self = 0)
  (*@ r = is_empty h
        ensures r <-> is_empty h.self.HM.dom *)

  let nb_vertex g = HM.length g.self
  (*@ vs = nb_vertex g 
        ensures vs = Set.cardinal g.self.HM.dom 
        ensures consistent (old g) g 
        ensures consistent g (old g) *)

  (*let copy = HM.copy
  @ g2 = copy g1 
         ensures g2.HM.dom <> g1.HM.dom 
         ensures g2 != g1 *)
         
   let clear g = HM.clear g.self
   (*@ clear g
      ensures g.self.HM.dom = Set.empty *)

  (* let nb_edges g = HM.fold (fun _ s n -> n + S.cardinal s) g 0 *)

  let out_degree g v =
    S.cardinal
      (try HM.find g.self v with Not_found -> invalid_arg "[ocamlgraph] out_degree")
  (*@ d = out_degree g v
        ensures vertex_belongs g v -> d = Set.cardinal (succ g v)
        raises  Invalid_argument _ -> not vertex_belongs g v
        ensures consistent (old g) g 
        ensures consistent g (old g)  *)

  let mem_vertex g v = HM.mem g.self v
  (*@ b = mem_vertex g v 
        ensures b <-> vertex_belongs g v 
        ensures consistent (old g) g 
        ensures consistent g (old g) *)

  let unsafe_add_vertex g v = HM.add g.self v S.empty
  (*@ unsafe_add_vertex g v 
        requires not (vertex_belongs g v)
        ensures vertex_belongs g v
        ensures succ g v = Set.empty
        ensures forall vx, vy. edge_belongs g vx vy -> edge_belongs (old g) vx vy  
        ensures forall v'. v' <> v /\ vertex_belongs g v' -> vertex_belongs (old g) v'
        ensures consistent (old g) g *) 

  let unsafe_add_edge g v1 v2 = HM.add g.self v1 (S.add v2 (HM.find g.self v1))
  (*@ unsafe_add_edge g v1 v2
        requires vertex_belongs g v2
        raises Not_found -> not vertex_belongs g v1 
        ensures edge_belongs g v1 v2
        ensures forall vx, vy. edge_belongs g vx vy /\ vx <> v1 /\ vy <> v2 -> edge_belongs (old g) vx vy  
        ensures forall vx. edge_belongs g vx v2 /\ vx <> v1 -> edge_belongs (old g) vx v2  
        ensures forall vy. edge_belongs g v1 vy /\ vy <> v2 -> edge_belongs (old g) v1 vy  
        ensures vertex_belongs g v1
        ensures consistent (old g) g *)


  let add_vertex g v = if HM.mem g.self v then () else unsafe_add_vertex g v
  (*@ add_vertex g v  
        ensures vertex_belongs g v
        ensures not vertex_belongs g v -> succ g v = Set.empty 
        ensures forall vx, vy. edge_belongs g vx vy -> edge_belongs (old g) vx vy  
        ensures forall v'. v' <> v /\ vertex_belongs g v' -> vertex_belongs (old g) v'
        ensures consistent (old g) g *)

  let add_edge g v1 v2 =
    if mem_edge g v1 v2 then ()
    else
      add_vertex g v1 ; add_vertex g v2 ;
      unsafe_add_edge g v1 v2
  (*@ add_edge g v1 v2 
        ensures forall vx, vy. edge_belongs g vx vy /\ vx <> v1 /\ vy <> v2 -> edge_belongs (old g) vx vy  
        ensures forall vx. edge_belongs g vx v2 /\ vx <> v1 -> edge_belongs (old g) vx v2  
        ensures forall vy. edge_belongs g v1 vy /\ vy <> v2 -> edge_belongs (old g) v1 vy  
        ensures vertex_belongs g v1
        ensures vertex_belongs g v2
        ensures edge_belongs g v1 v2 
        ensures consistent (old g) g 
        raises Not_found -> not ( vertex_belongs g v1 ) 
        *)

   let succ g v = S.elements (HM.find g.self v)
   (*@ l = succ g v 
        raises Not_found -> not ( vertex_belongs g v )
        ensures forall v'. List.mem v' l <-> Set.mem v' (succ g v) 
        ensures consistent (old g) g 
        ensures consistent g (old g) *)

  let add_edge_e g (v1, v2) = add_edge g v1 v2
  (*@ add_edge_e g p 
        ensures vertex_belongs g (fst p)
        ensures vertex_belongs g (snd p)
        ensures edge_belongs g (fst p) (snd p) 
        ensures consistent (old g) g 
        raises Not_found -> not ( vertex_belongs g (fst p) ) *)

   (*let remove_vertex g v =
         if HM.mem g v then begin
           ignore (HM.remove g v);
           let rec remove_all = function 
           | Nil -> () 
           | Cons( x, a) ->  HM.add g x (S.remove v (HM.find g x)) ; remove_all ( a () ) in
           remove_all (HM.to_seq_keys g ())
         end *)

   (*****    HIGHER ORDER FUNCTIONS     *****)

    (* let iter_succ f g v =
   *   S.iter f (HM.find g v)
   *
   * let fold_succ f g v =
   *   S.fold f (HM.find g v)
   *
   * let iter_succ_e f g v = iter_succ (fun v2 -> f (v, v2)) g v
   * let fold_succ_e f g v = fold_succ (fun v2 -> f (v, v2)) g v *)

  (* let succ g v = S.elements (HM.find g v)
   *
   * let succ_e g v = fold_succ_e (fun e l -> e :: l) g v [] *)

  (*let map_vertex f g =
    let module MV = Util.Memo(V) in
    let f = MV.memo f in
    HM.map (fun v s -> f v, S.fold (fun v s -> S.add (f v) s) s S.empty) g*)

  (* let all g= let l = ref [] in HM.iter (fun v k -> l := v::!l) g; !l ;; *)

    (* let iter_edges f = HM.iter (fun v -> S.iter (f v))
     * let fold_edges f = HM.fold (fun v -> S.fold (f v))
     * let iter_edges_e f = iter_edges (fun v1 v2 -> f (v1, v2))
     * let fold_edges_e f = fold_edges (fun v1 v2 a -> f (v1, v2) a) *)

  (* let iter_pred f g v =
   *   if not (mem_vertex g v ) then invalid_arg "[ocamlgraph] iter_pred";
   *   iter_edges (fun v1 v2 -> if  V.equal v v2 then f v1) g
   *
   * let fold_pred f g v =
   *   if not (mem_vertex g v ) then invalid_arg "[ocamlgraph] fold_pred";
   *   fold_edges (fun v1 v2 a -> if  V.equal v v2 then f v1 a else a) g
   *
   * let pred g v = fold_pred (fun v l -> v :: l) g v []
   *
   * let in_degree g v =
   *   if not (mem_vertex g v) then invalid_arg "[ocamlgraph] in_degree";
   *   fold_pred (fun _ n -> n + 1) g v 0
   *
   * let iter_pred_e f g v =
   *   if not (mem_vertex g v) then invalid_arg "[ocamlgraph] iter_pred_e";
   *   iter_edges_e (fun e -> if  V.equal v (E.dst e) then f e) g
   *
   * let fold_pred_e f g v =
   *   if not (mem_vertex g v) then invalid_arg "[ocamlgraph] fold_pred_e";
   *   fold_edges_e (fun e a -> if  V.equal v (E.dst e) then f e a else a) g
   *
   * let pred_e g v = fold_pred_e (fun v l -> v :: l) g v []
   *
   * let iter_vertex f = HM.iter (fun v _ -> f v)
   *
   * let fold_vertex f = HM.fold (fun v _ -> f v)
   *)
end


      (************************************************************************************************************************
      ConcreteDigraph proof notes:

      1. Most functions used to get values are rather straight forward, since we must simply prove that the functions return is
      what we claim it is. Most times, this is a representation of how data ends up being stored. For example, saying an edge 
      exists between v1 and v2 is the same as checking whether v2 is in v1's adjacency list. 

      2. The hardest functions to prove end up being those which alter the structure, logically so. These can be split into two
      general case scenarios, those that *add* information, such as vertices, edges, etc. and those that *remove* information.

            2.1 For those that add information, we must guarantee that all other vertices and edges remain consistent, which is
            why the *consistent* predicate was created. It check whether two graphs, an old and a new, are consistent. This means
            that every vertex and edge that existed in the old graph, but still exist in the new one. All methods which add 
            information must ensure this, as well as make sure what we wanted to add, and *only* what we wanted to add, was added.

            2.2 For those that remove information, we must guarantee that the only information that was removed was the one we
            wanted to in fact remove. As such, we must guarantee that every vertex and edge that existed in the original graph
            except the one we want to remove, still exists in the new graph and that the one we removed does not
      
      3. An interesting thing we need to prove as well is that functions that check for something don't alter the internal state 
      of the graph, such as checking the existence of an edge or vertex.

      4. Some functions were commented out for now, these functions are either higher order functions, or need something that is
      not yet implemented by cameleer. 

      *************************************************************************************************************************)
