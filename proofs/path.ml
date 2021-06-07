(*@ open Set *)
(*@ open Seq *)

(*@ lemma seq_cons: forall s1 s2: 'a seq, x: 'a.
      s1 = cons x s2 -> forall i. 0 <= i < Seq.length s2 -> s1[i+1] = s2[i] *)

module type HASHABLE = sig
  type t
  val [@logic] hash : t -> int

  val equal : t -> t -> bool
  (*@ b = equal t1 t2 
        ensures b <-> t1 = t2*)
end

(** Signature merging {!ORDERED_TYPE} and {!HASHABLE}. *)
module type COMPARABLE = sig
  type t
  val [@logic] compare : t -> t -> int
  (*@ axiom pre_order_compare: is_pre_order compare*)

  val [@logic] hash : t -> int

  val equal : t -> t -> bool
  (*@ b = equal t1 t2 
        ensures b <-> t1 = t2*)
end

(*@ lemma equal_hashes_HASHABLE: forall t1, t2 . t1 = t2 -> HASHABLE.hash t1 = HASHABLE.hash t2 *)
(*@ lemma equal_hashes_COMPARABLE: forall t1, t2 . t1 = t2 -> COMPARABLE.hash t1 = COMPARABLE.hash t2 *)


module Check
    (G :
     sig
       module V : COMPARABLE
      type gt
      (*@ model dom: V.t fset *)

       val succ : gt -> V.t -> V.t list
       (*@ l = succ g v
            requires Set.mem v g.dom
            ensures forall v'. List.mem v' l -> Set.mem v' g.dom *)

     end) =
struct
  module HTProduct = struct
    type t = G.V.t * G.V.t
    let equal (x1, y1) (x2, y2) = G.V.equal x1 x2 && G.V.equal y1 y2
    let hash (x, y) = G.V.hash x + G.V.hash y
  end

  module HV = Hashtbl.Make(G.V)
  module HVV = Hashtbl.Make(HTProduct)

  (* the cache contains the path tests already computed *)
  type path_checker = { cache : bool HVV.t; graph : G.gt }

  let create g = { cache = HVV.create 97; graph = g }

  let check_path pc v1 v2 =
    try
      HVV.find pc.cache (v1, v2)
    with Not_found ->
      (* the path is not in cache; we check it with a BFS *)
      let visited = HV.create 97 in
      let q = Queue.create () in
      let rec loop () =
        if Queue.is_empty q then begin
          HVV.add pc.cache (v1, v2) false;
          false
        end else begin
          let v = Queue.pop q in
          HVV.add pc.cache (v1, v) true;
          if G.V.compare v v2 = 0 then
            true
          else begin
            if not (HV.mem visited v) then begin
              HV.add visited v ();
              let sucs = G.succ pc.graph v in
              let rec iter_succ = function
                | [] -> ()
                | v' :: r -> Queue.add v' q; iter_succ r
              (*@ iter_succ l 
                    requires forall v. List.mem v l -> Set.mem v pc.graph.G.dom
                    requires forall v. Seq.mem v q.Queue.view -> Set.mem v pc.graph.G.dom
                    variant l 
                    ensures forall v. Seq.mem v q.Queue.view -> Set.mem v pc.graph.G.dom *)
              in
              iter_succ sucs
            end;
            loop ()
          end
        end
      (*@ b = loop ()
            requires subset visited.HV.dom pc.graph.G.dom
            requires forall v. Seq.mem v q.Queue.view -> Set.mem v pc.graph.G.dom
            raises  Queue.Empty -> false
            variant Set.cardinal pc.graph.G.dom - Set.cardinal visited.HV.dom, Seq.length q.Queue.view 
            ensures subset visited.HV.dom pc.graph.G.dom
            *)
      in
      Queue.add v1 q;
      loop ()
      (*@ b = check_path pc v1 v2
            requires Set.mem v1 pc.graph.G.dom *)
    end


(*********************************************************************************************************************************
  check_path termination notes:                           
  
  1. It was necessary to specify the iter_succ function, by making it guarantee that all the members it iterates belong to the graph
  and that all the elements it adds to the queue are also part of the graph. 
  
  2. The loop () function must assure that it does not add elements to the queue or to the visited hash table that are not part of 
  the graph, as such as added pre-conditions and postconditions to guarantee this condition - that all elements of the queue belong
  to the graph and that the domain of the visited hash table is a subset of the graphs domain.

  3. The loop () variant is a tricky one - during the execution of this function, there are two main data structures which are 
  altered, the queue and the visited hash table. However, elements aren't added to the hash table every iteration and the number of
  elements on the queue fluctuates. As such, we need a combination of the both to create a variant that decreases every iteration. 
     
      3.1 Most iterations, we'll add an element to the visited table, since the visited table is a subset of the graph's domain,
      this means the amount of valid vertices to be added next iteration decreases - this is represented by subtracting the cardinal
      of the visited table out of the cardinal of the graph's domain. When a vertex is added to this table, the queue can increase
      (as a result of adding the current vertex's successors to it) or decrease by one (due to removing the current vertex, and then
      not adding any - in the situation where a vertex has no successors).

      3.2 On the iterations that we don't add a vertex to the visited table, we don't add any vertices to the queue either. Because
      of this, we know for sure the size of the queue decreases by one, because of the pop we performed to get the current vertex.

  4. We were forced to create the seq_cons lemma because before running the functions loop and iter_succ, we had only removed one
  element of the queue, however the SMT solves weren't being able to prove, that all other vertices still belonged to the graph's domain.
  By creating the lemma, we prove to them, that removing the first element of a sequence, leaves all the other elements untouched. 

******************************************************************************************************************************************)


