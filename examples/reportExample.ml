
module type COMPARABLE = sig
  type t

  val equal : t -> t -> bool
  (*@ b = equal x y
        ensures b <-> x = y *)

end

(* Module Concrete implements:
   - a persistent graph
   - a directed graph (digraph)
   - an unlabeled graph *)
module Concrete (V: COMPARABLE) = struct

  type vertex = V.t

  type t = {
    succ : vertex -> vertex list;
    dom  : vertex list;
  } (*@ invariant forall x. List.mem x dom -> forall y. List.mem y (succ x) ->
          List.mem y dom *)

  let empty =
    { succ = (fun _ -> []); dom = [] }

  let update g x v =
    (fun y -> if V.equal x y then v else g.succ y)


  let rec mem_list v = function
    | [] -> false
    | x :: r -> V.equal v x || mem_list v r
   (*@ b = mem_list v l
         variant l
         ensures b <-> List.mem v l *)

  let[@logic] mem_vertex g v = mem_list v g.dom
  (*@ b = mem_vertex g v
        ensures b <-> List.mem v g.dom *)

  let[@logic] mem_edge g x y =
    mem_vertex g x && mem_list y (g.succ x)
  (*@ b = mem_edge g x y
        ensures b <-> mem_vertex g x && List.mem y (g.succ x) *)

  let add_vertex g v =
    if mem_vertex g v then g
    else { dom = v :: g.dom; succ = update g v [] }
  (*@ r = add_vertex g v
        ensures mem_vertex r v
        ensures forall x. List.mem x g.dom -> List.mem x r.dom *)

  let add_edge g v1 v2 =
    if mem_edge g v1 v2 then g
    else
      let g = add_vertex g v1 in
      let g = add_vertex g v2 in
      { g with succ = update g v1 (v2 :: g.succ v1) }
  (*@ r = add_edge g v1 v2
        ensures  mem_edge r v1 v2
        ensures  mem_vertex r v1 && mem_vertex r v2 *)

end
