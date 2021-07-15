(*@ open Set *)
(*@ open Seq *)
(*@ open SeqOfList *)

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
            (*@ model dom: V.t fset 
                model suc: V.t -> V.t fset
                invariant forall v1, v2. Set.mem v1 dom /\ Set.mem v2 (suc v1) -> Set.mem v2 dom*)
      
             val [@logic] succ : gt -> V.t -> V.t list
             (*@ l = succ g v
                  requires Set.mem v g.dom
                  ensures forall v'. List.mem v' l -> Set.mem v' g.dom
                  ensures forall v'. List.mem v' l <-> Set.mem v' (g.suc v) *)
      


           end) =
      struct
        module HTProduct = struct
          type t = G.V.t * G.V.t
          let equal (x1, y1) (x2, y2) = G.V.equal x1 x2 && G.V.equal y1 y2
          let hash (x, y) = G.V.hash x + G.V.hash y
        end
      
        module HV = Hashtbl.Make(G.V)
        module HVV = Hashtbl.Make(HTProduct)

       (*@ predicate edge (v1 : G.V.t) (v2 : G.V.t) (g : G.gt) = Set.mem v2 (g.G.suc v1)*)

       (*@ predicate distinct (s : G.V.t seq) =
               forall i j. 0 <= i < length s -> 0 <= j < length s ->
                  i <> j -> s[i] <> s[j] *)

       (*@ lemma emp_cons : forall q : 'a seq.
            q == q ++ of_list [] *)
      
      (*@ predicate suffix ( l : G.V.t seq ) ( q : G.V.t seq ) = 
      Seq.length l <= Seq.length q /\
        forall i. 0 <= i < Seq.length l -> l[i] = q[Seq.length q - Seq.length l + i] *)      

      (*@ predicate is_path (v1 : G.V.t) (l : G.V.t seq) (v2 : G.V.t) (g : G.gt) =
            let len = Seq.length l in
            if len = 0 then v1 = v2 else
              edge v1 l[0] g && l[len - 1] = v2 && Set.mem v1 g.G.dom &&
            forall i : int. 0 <= i < len - 1 -> edge l[i] l[i+1] g *)
        
        (*@ predicate has_path (v1 : G.V.t) (v2 : G.V.t) (g : G.gt) = 
              exists p : G.V.t seq. is_path v1 p v2 g *)

        (*@ lemma path_suc : forall v1, v2, v3 : G.V.t, g : G.gt.
              Set.mem v1 g.G.dom -> has_path v1 v2 g -> edge v2 v3 g ->
              has_path v1 v3 g *)

        (* lemma not_empty_succ : forall v1, v2, v3 : G.V.t, g : G.gt. 
              has_path v1 v2 g -> has_path v1 v3 g /\ has_path v3 v2 g -> G.succ g v3 <> [] *)

        (*@ lemma edge_path : forall v1, v2, v3 : G.V.t, g : G.gt. 
              edge v1 v2 g /\ edge v2 v3 g -> is_path v1 (Seq.singleton v2) v3 g -> has_path v1 v3 g*)
        
        (*@ lemma self_path : forall v1 : G.V.t, g: G.gt.
              is_path v1 (Seq.empty) v1 g -> has_path v1 v1 g *)

        let [@ghost] [@logic] cache_empty () = HVV.create 42
        (* c = cache_empty () 
              ensures c.HVV.dom = Set.empty*)

        (* the cache contains the path tests already computed *)
        type path_checker = { cache : bool HVV.t; graph : G.gt }
        (*@ invariant forall p. Set.mem p cache.HVV.dom ->
              match (cache.HVV.view p) with 
              | [] -> false
              | x :: _ -> x <-> has_path (fst p) (snd p) graph *)
              
        let create g = { cache = HVV.create 97; graph = g }

       

        let [@lemma] list_notNil_cons ( l : 'a list ) : unit = 
                match l with 
                | [] -> assert false 
                | x::r -> ()
        (*@ list_notNil_cons l 
              requires l <> []
              ensures exists x, x1. l = x::x1 *)
              
        let check_path pc v1 v2 =
          try
            HVV.find pc.cache (v1, v2)
          with Not_found ->
            (* the path is not in cache; we check it with a BFS *)
            let marked = HV.create 97 in
            let [@ghost] visited = HV.create 97 in
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
                  HV.add visited v () ; 
                  let sucs = G.succ pc.graph v in
                  let rec iter_succ ( prefix [@ghost] ) = function
                    | [] -> ()
                    | v' :: r -> if not (HV.mem marked v' ) then begin HV.add marked v' () ; Queue.add v' q end ; iter_succ (prefix @ [v']) r 
                  (*@ iter_succ p l
                        requires Set.mem v1 marked.HV.dom 
                        requires Seq.mem v1 q.Queue.view -> q.Queue.view == Seq.singleton v1
                        requires Set.mem v1 visited.HV.dom
                        requires not (Set.mem v2 visited.HV.dom)
                        requires forall v'. Set.mem v' visited.HV.dom /\ v' <> v -> forall s. edge v' s pc.graph -> Set.mem s marked.HV.dom 
                        requires forall v'. Seq.mem v' q.Queue.view -> not (Set.mem v' visited.HV.dom)
                        requires distinct q.Queue.view 
                        requires forall v'. Set.mem v' visited.HV.dom -> not (Seq.mem v' q.Queue.view)   
                        requires forall v'. Set.mem v' marked.HV.dom ->  Set.mem v' visited.HV.dom \/ Seq.mem v' q.Queue.view
                        requires forall v'. Set.mem v' visited.HV.dom -> Set.mem v' marked.HV.dom        
                        requires forall v'. Seq.mem v' q.Queue.view -> Set.mem v' marked.HV.dom
                        requires of_list sucs = of_list p ++ of_list l
                        requires forall v'. List.mem v' l -> Set.mem v' pc.graph.G.dom
                        requires forall v'. List.mem v' l -> edge v v' pc.graph
                        requires forall v'. List.mem v' l -> has_path v1 v' pc.graph
                        requires forall v'. Seq.mem v' q.Queue.view -> Set.mem v' pc.graph.G.dom
                        requires forall v'. Set.mem v' visited.HV.dom -> has_path v1 v' pc.graph
                        requires forall v'. Set.mem v' marked.HV.dom -> has_path v1 v' pc.graph
                        requires forall v'. Seq.mem v' q.Queue.view -> has_path v1 v' pc.graph
                        requires subset marked.HV.dom pc.graph.G.dom
                        variant l 
                        ensures Set.mem v1 visited.HV.dom
                        ensures Seq.mem v1 q.Queue.view -> q.Queue.view == Seq.singleton v1
                        ensures not (Set.mem v2 visited.HV.dom)
                        ensures sucs = p @ l
                        ensures distinct q.Queue.view 
                        ensures old pc = pc
                        ensures (old visited) = visited
                        ensures forall v'. Set.mem v' (old marked).HV.dom -> Set.mem v' marked.HV.dom
                        ensures subset marked.HV.dom pc.graph.G.dom
                        ensures forall v'. Set.mem v' marked.HV.dom ->  Set.mem v' visited.HV.dom \/ Seq.mem v' q.Queue.view
                        ensures forall v'. Set.mem v' visited.HV.dom -> has_path v1 v' pc.graph 
                        ensures forall v'. Set.mem v' marked.HV.dom -> has_path v1 v' pc.graph
                        ensures forall v'. Seq.mem v' q.Queue.view -> has_path v1 v' pc.graph
                        ensures forall v'. Seq.mem v' q.Queue.view -> Set.mem v' pc.graph.G.dom  
                        ensures forall v'. List.mem v' l -> Set.mem v' marked.HV.dom
                        ensures has_path v1 v2 pc.graph -> exists w. Seq.mem w q.Queue.view /\ has_path w v2 pc.graph
                        ensures l = sucs -> forall s. edge v s pc.graph -> Set.mem s marked.HV.dom
                        ensures forall v'. Seq.mem v' q.Queue.view -> not (Set.mem v' visited.HV.dom)
                        ensures forall v'. Set.mem v' visited.HV.dom -> not (Seq.mem v' q.Queue.view)
                        ensures forall v'. Set.mem v' visited.HV.dom -> Set.mem v' marked.HV.dom
                        ensures forall v'. Seq.mem v' q.Queue.view -> Set.mem v' marked.HV.dom
                        ensures Set.mem v1 marked.HV.dom 
                        *)
                  in
                  iter_succ [] sucs ;
                  loop ()
                end
              end
            (*@ b = loop () 
                  requires Set.mem v1 marked.HV.dom 
                  requires Seq.mem v1 q.Queue.view -> q.Queue.view == Seq.singleton v1
                  requires not (Set.mem v2 visited.HV.dom)
                  requires forall v'. Set.mem v' marked.HV.dom ->  Set.mem v' visited.HV.dom \/ Seq.mem v' q.Queue.view
                  requires forall v. Set.mem v visited.HV.dom -> forall s. edge v s pc.graph -> Set.mem s marked.HV.dom 
                  requires distinct q.Queue.view 
                  requires forall v. Seq.mem v q.Queue.view -> not (Set.mem v visited.HV.dom)
                  requires forall v. Set.mem v visited.HV.dom -> not (Seq.mem v q.Queue.view)
                  requires forall v. Set.mem v visited.HV.dom -> Set.mem v marked.HV.dom
                  requires forall v. Seq.mem v q.Queue.view -> Set.mem v marked.HV.dom
                  requires has_path v1 v2 pc.graph -> exists w. Seq.mem w q.Queue.view /\ has_path w v2 pc.graph 
                  requires forall v'. Seq.mem v' q.Queue.view -> has_path v1 v' pc.graph           
                  requires forall v. Set.mem v visited.HV.dom -> has_path v1 v pc.graph
                  requires forall v. Set.mem v marked.HV.dom -> has_path v1 v pc.graph
                  requires subset visited.HV.dom pc.graph.G.dom
                  requires subset marked.HV.dom pc.graph.G.dom
                  requires forall v. Seq.mem v q.Queue.view -> Set.mem v pc.graph.G.dom
                  raises  Queue.Empty -> false
                  variant Set.cardinal pc.graph.G.dom - Set.cardinal visited.HV.dom, Seq.length q.Queue.view 
                  ensures distinct q.Queue.view 
                  ensures forall v'. Set.mem v' marked.HV.dom /\ v' <> v2 ->  Set.mem v' visited.HV.dom \/ Seq.mem v' q.Queue.view
                  ensures subset visited.HV.dom pc.graph.G.dom
                  ensures subset marked.HV.dom pc.graph.G.dom
                  ensures forall v. Set.mem v marked.HV.dom -> has_path v1 v pc.graph
                  ensures forall v. Set.mem v visited.HV.dom -> has_path v1 v pc.graph
                  ensures forall v'. Seq.mem v' q.Queue.view -> Set.mem v' pc.graph.G.dom  
                  ensures b <-> has_path v1 v2 pc.graph  
                  ensures not (Set.mem v2 visited.HV.dom)
                  ensures forall v. Seq.mem v q.Queue.view -> not (Set.mem v visited.HV.dom)
                  ensures forall v. Set.mem v visited.HV.dom -> not (Seq.mem v q.Queue.view)
                  ensures forall v. Set.mem v visited.HV.dom -> Set.mem v marked.HV.dom
                  ensures forall v. Set.mem v visited.HV.dom -> forall s. edge v s pc.graph -> Set.mem s marked.HV.dom 
                  ensures forall v. Seq.mem v q.Queue.view -> Set.mem v marked.HV.dom
                  ensures Seq.mem v1 q.Queue.view -> q.Queue.view == Seq.singleton v1
                  ensures Set.mem v1 marked.HV.dom 
                  *)  
            in
            HV.add marked v1 () ;
            Queue.add v1 q;
            loop ()
            (*@ b = check_path pc v1 v2
                  requires Set.mem v1 pc.graph.G.dom
                  ensures b <-> has_path v1 v2 pc.graph *)

          end
          
    (*ensures forall v'. List.mem v' l /\ not (Set.mem v' (old marked).HV.dom) -> Seq.mem v' q.Queue.view /\ Set.mem v' marked.HV.dom*)

    (*************************************************************************************************************************
    
    
    Altered version of the original path.ml. Table *visited* became ghost and a new table was added called *marked*. 
    No repeated vertices are added to the queue now, as they are checked before being added and not on pop. Ghost 
    table *visited* serves to know which vertices are marked, but have already left the queue.
    
    ***************************************************************************************************************************)