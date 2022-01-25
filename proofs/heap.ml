(**************************************************************************)
(*                                                                        *)
(*  Ocamlgraph: a generic graph library for OCaml                         *)
(*  Copyright (C) 2004-2010                                               *)
(*  Sylvain Conchon, Jean-Christophe Filliatre and Julien Signoles        *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(*@ open Numof*)

module type Ordered = sig
  type t
  val [@logic] compare : t -> t -> int
  (*@ axiom pre_order_compare: is_pre_order compare*)

  val [@logic] default : t
end


exception EmptyHeap

exception InvalidArg 

module Imperative(X : Ordered) = struct 
  
  (*@ predicate le ( a1 : X.t ) ( a2 : X.t ) = X.compare a1 a2 >= 0 *)

  (* The heap is encoded in the array [data], where elements are stored
     from [0] to [size - 1]. From an element stored at [i], the left
     (resp. right) subtree, if any, is rooted at [2*i+1] (resp. [2*i+2]). *)

  (* Pedicate to know if a given array, with [size] elements is a heap in  
    an array, as explained above.                                         *)
  (*@ predicate is_heap (data : X.t array) (size : int) =      
        size > 0 -> forall i. 0 <= i < size -> (
          (0 < 2*i + 1 < size -> le data.(i) data.(2*i+1) ) /\
          (0 < 2*i + 2 < size -> le data.(i) data.(2*i+2) ) )
  *)


  (* Predicate to know if an element is the largest in the array. *)
  (* predicate maximum (data : X.t array) (el : X.t ) = 
        Array.mem el data /\ forall i. 0 <= i < Array.length data -> le el data.(i) *)

  type t = { mutable size : int ; data : X.t array }
  (*@ invariant size >= 0 
      invariant size <= Array.length data *)

  (* Given an array, an element and two indices, counts the number of 
  occurences that number has between the two indices                *)
  (*@ function numocc (a: X.t array) (c: X.t) (l u: int) : int =
        numof a c l u   *)

  (* Given an array and an element, counts the number of instances that
  element has in the given array, with a given size                 *)
  (*@ function numocc' (a : X.t array) (c: X.t) (size : int) : int =
        numof a c 0 size  *)

  (*@ function heap_maximum (h: t) : X.t *)

  (*@ predicate is_maximum (x: X.t) (h: t) =
     forall e. Array.mem e h.data -> le x e *)

  (*@ axiom max_def: forall h. h.size <> 0 -> heap_maximum h = h.data.(0)*)

  (*@ lemma num_exist:
        forall h : t, x : X.t. numocc' h.data x h.size > 0 ->
          exists i. 0 <= i < Array.length h.data /\ h.data.(i) = x *)

    let [@ghost] ancestor_f (a : X.t array) (size : int) (i : int) =
    ()
  (*@ requires is_heap a size
        requires 0 <= i < size
        ensures  i > 0 -> le a.(div (i-1) 2) a.(i) *)

  (*@ predicate ancestor (a : X.t array) (size : int) (i : int) =
        is_heap a size ->  0 <= i < size -> i > 0 -> le a.(div (i-1) 2) a.(i) *)
    
  let [@ghost] children_f (a : X.t array) (size : int) (i : int) = ()
  (*@ requires is_heap a size 
    requires 0 <= i < size
    ensures 2*i+1 < size -> le a.(i) a.(2*i+1) 
    ensures 2*i+2 < size -> le a.(i) a.(2*i+2) *)

  (*@ predicate children  (a : X.t array) (size : int) (i : int) =
      is_heap a size -> 0 < i <= size -> (2*i+1 < size -> le a.(i) a.(2*i+1)) -> (2*i+2 < size -> le a.(i) a.(2*i+2))  *)

  (*@ lemma transativity :
        forall h : t, i : int. 
          is_heap h.data h.size -> 0 <= i < h.size -> ancestor h.data h.size i -> children h.data h.size i ->
            i > 0 /\ 2*i+1 < h.size -> le h.data.(div (i-1) 2) h.data.(2*i+1) -> 
            i > 0 /\ 2*i+2 < h.size -> le h.data.(div (i-1) 2) h.data.(2*i+2)  *)
  
  (* lemma grandfather : forall h : t, i : int. 
        is_heap h.data h.size
  *)

  let [@lemma] max_coherent (h: t) =
    let s = h.data in
    let n = h.size in
    let rec ismin (i: int) = 
      if i > 0 then ismin ((i-1) / 2)
    (*@ ismin i
        requires 0 <= i < n
        variant i
        ensures le s.(0) s.(i) *)
    in ()
    (*@ max_coherent h
          requires is_heap h.data h.size
          requires h.size > 0
          ensures is_maximum (heap_maximum h) h *) 

  (*@ predicate pop ( a1 a2: t ) =
      a2.size = a1.size - 1 /\
        forall i. 0 <= i < a2.size -> a1.data.(i) = a2.data.(i) *)

  (*@ lemma pop_occ_1: forall a1 a2 : t, x : X.t.
      pop a1 a2 -> x <> a1.data.(a1.size - 1) ->
        numocc' a1.data x a1.size = numocc' a2.data x a2.size *)

  (*@ lemma pop_occ_2: forall a1 a2 : t.
        pop a1 a2 ->
        numocc' a1.data a1.data.(a1.size - 1) a1.size - 1
      = numocc' a2.data a1.data.(a1.size - 1) a2.size *)

  (*@ lemma pop_order: forall a1 a2. pop a1 a2 -> is_heap a1.data a1.size -> is_heap a2.data a2.size *)

  (* lemma same_occ: forall b: bag X.t, x a : X.t.
        x <> a -> nb_occ x (Bag.diff b (Bag.singleton a)) = nb_occ x b*)

  let create n =
    { size = 0 ; data = Array.make n X.default}
  (*@ h = create n 
      requires n >= 0 *)

  let [@logic] is_empty h = h.size <= 0
  (*@ r = is_empty h
        ensures r <-> (h.size <= 0) *)

  (*@ predicate subst (a1 : X.t array) (a2 : X.t array) (i : int) (size1 size2 : int) =
        size1 = size2 /\ 
          0 <= i < size1 /\  
            (forall k. 0 <= k < size1 -> k <> i -> a1.(k) = a2.(k) )   
  *)

  (*@ lemma bigger_father : 
        forall a, size.       
          is_heap a size -> 
            forall i. 0 < i < size -> 
              le a.(div (i-1) 2) a.(i)  *)

  let [@lemma] [@logic] sub_order (a1 : X.t array) (size1 : int ) (a2 : X.t array) (size2 : int) (i : int) = 
      ()
    (*@ 
          requires subst a1 a2 i size1 size2
          requires is_heap a1 size1 
          requires size2 = size1 
          requires i > 0 -> le a1.(div (i - 1) 2) a2.(i) 
          requires 0 < 2*i + 1 < size1 -> le a2.(i) a1.(2*i + 1)   
          requires 0 < 2*i + 2 < size1 -> le a2.(i) a1.(2*i + 2)       
          ensures is_heap a2 size2
    *)

  (*@ lemma sub_occ_1: forall a1 a2 : X.t array, i : int, x : X.t, size1 size2 : int.
      size1 = size2 -> subst a1 a2 i size1 size2 -> (x <> a1.(i) /\ x <> a2.(i)) -> numocc' a1 x size1 = numocc' a2 x size2*)

  (*@  lemma sub_occ_2: forall a1 a2 : X.t array, i : int, size1 size2 : int.
       size1 > 0 -> size1 = size2 -> subst a1 a2 i size1 size2 -> a1.(i) <> a2.(i) ->
        let e = a1.(i) in 
          numocc' a1 e size1 = (numocc' a2 e size2) + 1 *)
  
  (*@  lemma sub_occ_2_1: forall a1 a2 : X.t array, i : int, size1 size2 : int.
       size1 > 0 -> size1 = size2 -> subst a1 a2 i size1 size2 -> a1.(i) <> a2.(i) ->
        let e = a1.(i) in 
          (numocc' a1 e size1) - 1 = (numocc' a2 e size2) *)

  (*@ lemma sub_occ_3: forall a1 a2 : X.t array, i : int, size1 size2 : int.
      size1 = size2 -> subst a1 a2 i size1 size2 -> a1.(i) = a2.(i) -> numocc' a1 a1.(i) size1 = numocc' a2 a1.(i) size2 *)

  (*@ predicate push (a1 a2 : X.t array ) (size1 size2 : int) =
        size2 = size1 + 1 /\
      forall i. 0 <= i < size1 -> a1.(i) = a2.(i)  *)

  (* lemma last_occ : forall a : X.t array, size : int, i: int. 0 <= i < size -> numocc' a (a.(i)) size >= 1 *)

  (*@ lemma push_occ: forall a1 a2 : X.t array, size1 size2 : int .
        push a1 a2 size1 size2 -> size1 > 0 ->
          (forall x. x <> a2.(size2 - 1) -> numocc' a1 x size1 = numocc' a2 x size2 ) /\
            let e = a2.(size2 - 1) in
              (numocc' a1 e size1) + 1 = numocc' a2 e size2 *)

  (*@ lemma push_order: forall a1 a2 : X.t array, a1size a2size : int .
        Array.length a1 > 0 -> push a1 a2 a1size a2size -> 
            X.compare (a2.(div (a1size - 1) 2)) (a2.(a1size)) >= 0 ->
               is_heap a1 a1size -> is_heap a2 a2size         *)

               (*          ensures let o = (old h.data).(i) in
                 if x = o then
                   numocc' d x (n + 1) = numocc' (old d) x n
                 else 
                   numocc' d x (n + 1) = numocc' (old d) x (n) + 1/\
                   numocc' d o (n + 1) = numocc' (old d) o (n) - 1*)

  let add h x =
    let n = h.size in
    let d = h.data in
    (* moving [x] up in the heap *)
    h.size <- n + 1 ;
    d.(n) <- d.((n - 1) / 2); (* Added, for simplicity sake *)
    let rec moveup i =
      let [@ghost] a = Array.copy d in
      let fi = (i - 1) / 2 in (* father's position *)
      if i > 0 && X.compare d.(fi) x < 0 then begin
        d.(i) <- d.(fi);
        moveup fi
            end else begin 
        d.(i) <- x 
            end
    (*@ moveup i
          requires is_heap h.data h.size
          requires 0 <= i < h.size
          requires Array.length h.data > h.size
          requires 0 < 2*i + 1 < h.size -> le x (h.data.(2*i + 1)) 
          requires 0 < 2*i + 2 < h.size -> le x (h.data.(2*i + 2)) 
          variant i
          ensures Array.mem x h.data
          ensures is_heap h.data (h.size)
          ensures forall e. e <> x -> e <> (old d).(i) -> numocc' (old h).data e (old h).size =  numocc' h.data e h.size
          ensures old h.size = h.size
          ensures let ol = (old h.data).(i) in
                if ol = x then 
                    numocc' (old h).data x (old h).size =  numocc' h.data x h.size  
                else     
                    (numocc' (old h).data x  (old h).size) + 1 =  numocc' h.data x  h.size /\
                    (numocc' (old h).data ol (old h).size) - 1 =  numocc' h.data ol h.size   *)
    in
    moveup n
    (*@ add h x 
          requires is_heap h.data h.size
          requires Array.length h.data > h.size + 1
          ensures Array.mem x (h.data)
          ensures numocc' (old h).data x ((old h).size) + 1 =  numocc' h.data x h.size 
          ensures forall e. e <> x -> numocc' (old h).data e (old h).size =  numocc' h.data e h.size 
          ensures (old h).size + 1 = h.size 
          ensures is_heap h.data h.size *)
  ;;

  let maximum h =
    if h.size = 0 then raise EmptyHeap;
    h.data.(0)
  (*@ m = maximum h
        raises EmptyHeap -> h.size = 0
        requires is_heap h.data h.size 
        ensures is_maximum m h *)
    

  let remove h =
    if h.size <= 0 then raise EmptyHeap;
    let n = h.size - 1 in
    h.size <- n;
    let d = h.data in
    let x = d.(n) in
    (* moving [x] down in the heap *)
    let rec movedown i =
      let j = 2 * i + 1 in
      if j < n then
        let j =
          let j' = j + 1 in
          if j' < n && X.compare d.(j') d.(j) > 0 then j' else j
        in
        if X.compare d.(j) x > 0 then begin
          d.(i) <- d.(j);
          movedown j
        end else
          d.(i) <- x
            else
        d.(i) <- x
      (*@ movedown i
          requires Array.length h.data > h.size
          requires 0 < i < h.size -> le (h.data.(div (i - 1) 2 )) x 
          requires is_heap h.data h.size
          requires n >= i >= 0
          variant n - i 
          ensures is_heap h.data h.size *)
    in
      movedown 0
  (*@ remove h 
      raises EmptyHeap -> is_empty h 
      requires is_heap h.data h.size 
      ensures is_heap h.data h.size
      ensures h.size = (old h).size - 1 *)

  let pop_maximum h = let m = maximum h in remove h; m
  (*@ m = pop_maximum h 
      raises EmptyHeap -> h.size = 0
      requires is_heap h.data h.size 
      ensures is_heap h.data h.size
      ensures is_maximum m (old h) *)

end