(** For the sack of simplicity, sets are modeled as lists without
    repetitions. For a proper sets implementation, one should use the Set
    functor from the OCaml standard library (cf,
    https://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.html). *)

(** {1 A Small Library of Sets} *)

 (*@ function occ (x: 'a) (l: 'a list) : integer = match l with
        | [] -> 0
        | y :: r -> if x = y then 1 + occ x r else occ x r *)

  (*@ lemma occ_nonneg: forall x: 'a, l: 'a list.
        0 <= occ x l *)
  
  (*@ lemma occ_no_belong: forall x: 'a, l: 'a list.
        not List.mem x l -> occ x l = 0 *)

   (*@ lemma occ_sum: forall x: 'a, l1 l2: 'a list.
        occ x (l1 @ l2) = occ x l1 + occ x l2 *)

  (*@ predicate list_set (l: 'a list) =
        forall x. List.mem x l -> occ x l = 1 *)

  (*@ lemma list_set_cons: forall x: 'a, l: 'a list. 
         list_set (x::l) -> list_set l *)
  
  (* lemma list_remove: forall l1, l2: 'a list. 
        ((forall e. List.mem e l1 -> List.mem e l2) /\ list_set l2 ) -> list_set l1 *)

    

type 'a set = 'a list

(** [singleton x] returns a new set containg only [x] *)
let [@logic] singleton x =
  [x]
(*@ s = singleton x 
      ensures list_set s
      ensures List.length s = 1 
      ensures List.mem x s *)

(** [in_set x s] checks if [x] is in set [s] *)
let in_set x s =
  List.mem x s
(*@ b = in_set x s 
      requires list_set s
      ensures b <-> List.mem x s *)

(** [cardinal s] computes the cardinality of a set [s] *)
let card s =
  List.length s
(*@ c = card s 
      requires list_set s
      ensures c = List.length s *)

(** [s1 -- s2] computes the difference between sets [s1] and [s2] *)
let [@logic] dif s1 s2 =
  List.filter (fun y -> not (List.mem y s2)) s1
(*@ s' = dif s1 s2 
    requires list_set s1
    requires list_set s2
    ensures forall e. List.mem e s' <-> List.mem e s1 /\ not List.mem e s2
    ensures forall e. List.mem e s2 ->  not List.mem e s'
    ensures list_set s' *)

(** [union s1 s2] computes the union of sets [s1] and [s2] *)
let [@logic] union s1 s2 =
  (dif s1 s2) @ s2
(*@ s' = dif s1 s2 
    requires list_set s1
    requires list_set s2
    ensures forall e. List.mem e s' -> List.mem e s1 \/ List.mem e s2
    ensures forall e. List.mem e s1 -> List.mem e s'
    ensures forall e. List.mem e s2 -> List.mem e s'
    ensures list_set s' *)

let [@logic] intersection s1 s2 =
    List.filter (fun y -> List.mem y s2) s1
  (*@ s' = dif s1 s2 
      requires list_set s1
      requires list_set s2
      ensures forall e. List.mem e s' <-> List.mem e s1 /\ List.mem e s2
      ensures list_set s' *)

(*let iter_union f s =
  List.fold_left (fun acc x -> union acc (singleton (f x))) [] s*)

(** {1 Exercice 1: System of users' access to printers} *)

(** {2 Paragraph a: model the system's set of states with a set APRINTER} *)

type user    = string
type printer = string

type access   = user * printer set
type aprinter = access set

(** {2 Paragraph b: check if a user has access to a specific printer} *)

(*@ predicate valid_system (ap : ('b * 'a list) list ) = 
        list_set ap /\ forall p. List.mem p ap -> list_set (snd p)  *)

(* check_access : user -> printer -> aprinter -> bool *)
let rec check_access (u: user) (p: printer) (ap: aprinter) =
  (* List.exists (fun (a, pp) -> a = u && in_set p pp) ap List.exists not supported currently due to name clashes with exists*)
  match ap with
  | [] -> false 
  | (a, pp):: xs -> ( String.equal a u && in_set p pp ) || check_access u p xs
(*@ b = check_access u p ap 
    requires valid_system ap
    variant ap
    ensures b <-> exists ps. List.mem (u, ps) ap /\ List.mem p ps *)

(** {2 Paragraph c: give a user access to a printer} *)

(* give_access : user -> printer -> aprinter -> aprinter *)
let give_access (u: user) (p: printer) (ap: aprinter) =
  let user = List.find_all (fun (a, _) -> String.equal a u) ap in
  match user with
  | [] ->
    (*ap*)
    union ap (singleton (u, singleton p))
  | [(x, pp)] ->
    union (dif ap user) (singleton (x, union pp (singleton p)))
  | _ ->
    invalid_arg "give_access: there should be no repeated users in the system" 
(*@ ap' = give_access u p ap 
    requires valid_system ap 
    raises Invalid_argument _ -> exists p1, p2. List.mem p1 ap /\ List.mem p2 ap /\ fst p1 = fst p2 /\ fst p1 = u
    ensures valid_system ap'
    ensures forall p'. List.mem p' ap /\ fst p' <> u -> List.mem p' ap'
    ensures exists p'. List.mem p' ap' /\ fst p' = u /\ List.mem p (snd p')
*)

(** {2 Paragraph d: returns the users that can access more printers} *)

(* Had to resort to auxiliarly functions, instead of List.filter and List.find_all
due to list_set invariant. Could also remove this invariant.*)


(*@ predicate larger (i : int) ( l : ('a * 'b list) list ) =
        forall p. List.mem p l -> i >= List.length (snd p)*)


let rec larger_all i (l : aprinter) =
  match l with 
  | [] -> true
  | (_, pp):: xs -> i >= card pp && larger_all i xs 
(*@ b = larger_all i l 
    requires valid_system l 
    variant l
    ensures b <-> larger i l *)

(* max_access : aprinter -> user set *)
let max_access (ap : aprinter) =
  let rec larger l =  
  match l with 
  | [] -> [] 
  | (u, pp)::xs -> let size = card pp in 
    if larger_all size ap then u :: larger xs else larger xs
  (*@ us = larger l 
      requires valid_system l
      variant l
      ensures forall u. List.mem u us -> 
        exists p. List.mem p l /\ fst p = u /\ larger (List.length (snd p)) ap        
  *)
  in 
  larger ap
  (*@ us = max_access ap 
      requires valid_system ap
      ensures forall u. List.mem u us -> 
        exists p. List.mem p ap /\ fst p = u /\ larger (List.length (snd p)) ap        
  *)


(** {1 Exercice 2: System of playlists} *)

(** {2 Paragraph a: model the system's set of states with a set SPLAYLIST} *)

type title    = string
type artist   = string
type duration = int
type rating   = int
type song     = title * artist * duration * rating

type name     = string
type playlist = name * song set

type splaylist = playlist set

(** {2 Paragraph b: add a song to a playlist} *)

(*@ predicate valid_playlist (pl : 'a * 'b list) = list_set (snd pl)*)

(*@ predicate valid_splay (sp : ('a * 'b list) list ) = list_set sp /\
    forall x. List.mem x sp -> valid_playlist x *)

(* add_song_list : playlist -> song -> playlist *)
let [@logic] add_song_list (p : playlist) s =
  let (name, song_set) = p in
    (name, union song_set (singleton s))
(*@ pl' = add_song_list pl s
      requires valid_playlist pl
      ensures snd pl' = union (snd pl) (singleton s)
      ensures List.mem s (snd pl')
      ensures forall ss. List.mem ss (snd pl) -> List.mem ss (snd pl')
      ensures forall ss. List.mem ss (snd pl') /\ ss <> s -> List.mem ss (snd pl)
      ensures fst pl' = fst pl
      ensures valid_playlist pl'*)

(* add_song : playlist -> song -> splaylist -> splaylist *)
let add_song p s sp =
  union (dif sp (singleton p)) (singleton (add_song_list p s))
(*@ sp' = add_song p s sp
    requires valid_playlist p
    requires valid_splay sp
    ensures sp' = union (dif sp (singleton p)) (singleton (add_song_list p s))
    ensures forall pl. pl <> p /\ List.mem pl sp -> List.mem pl sp'
    ensures exists p'. List.mem p' sp' /\ (forall ss. List.mem ss (snd p) -> List.mem ss (snd p')) /\ fst p = fst p'
            /\ List.mem s (snd p') /\ (forall ss. List.mem ss (snd p') /\ ss <> s -> List.mem ss (snd p))
    ensures valid_splay sp'*)


(** {2 Paragraph c: remove a song from playlist} *)

(* remove_song_list : song -> playlist -> playlist *)
let [@logic] remove_song_list (p : playlist) s  =
  let (name, song_set) = p in
  (name, dif song_set (singleton s))
(*@ pl' = remove_song_list pl s
      requires valid_playlist pl
      ensures snd pl' = dif (snd pl) (singleton s)
      ensures not List.mem s (snd pl')
      ensures forall ss. List.mem ss (snd pl') -> List.mem ss (snd pl)
      ensures forall ss. List.mem ss (snd pl) /\ ss <> s -> List.mem ss (snd pl')
      ensures fst pl' = fst pl
      ensures valid_playlist pl'*)


(* remove_song : playlist -> song -> splaylist -> splaylist *)
let [@logic] remove_song p s sp =
  union (dif sp (singleton p)) (singleton (remove_song_list p s))
(*@ sp' = remove_song p s sp 
    requires valid_playlist p
    requires valid_splay sp
    ensures sp' = union (dif sp (singleton p)) (singleton (remove_song_list p s))
    ensures forall pl. pl <> p /\ List.mem pl sp -> List.mem pl sp'
    ensures exists p'. List.mem p' sp' /\ 
          (forall ss. List.mem ss (snd p') -> List.mem ss (snd p)) /\ fst p = fst p'
          /\ not List.mem s (snd p') /\ (forall ss. List.mem ss (snd p) /\ ss <> s -> List.mem ss (snd p'))
    ensures valid_splay sp'*)


(** {2 Paragraph d: remove a song from all playlists} *)

(* remove_song_all: song -> splaylist -> splaylist *)
let rec remove_song_all s sp =
  match sp with 
  | [] -> [] 
  | p :: pls -> remove_song_list p s:: remove_song_all s pls
(*@ sp' = remove_song_all s sp
    requires valid_splay sp 
    variant sp
    ensures valid_splay sp
    ensures forall p. List.mem p sp' -> exists p'. List.mem p' sp /\ p = remove_song_list p' s
    ensures forall p. List.mem p sp -> exists p'. List.mem p' sp /\ fst p = fst p' /\ 
      forall s'. s <> s' /\ List.mem s' (snd p) -> List.mem s' (snd p')
    ensures forall p.  List.mem p sp' -> not List.mem s (snd p)*)

(** {2 Paragraph e: returns all the playlists containing a given song} *)

let rec title_in_songs (t : title) ( sxs : song set) =
  match sxs with 
  | [] -> false 
  | (t', _, _, _):: ss -> String.equal t' t || title_in_songs t ss
(*@ b = song_in_list t sxs
    variant sxs
    ensures b <-> exists s. List.mem s sxs /\ let (t', _, _, _) = s in t' = t
*)

(* song_in_list : title -> playlist -> bool *)
let song_in_list (t : title) ( p : playlist)=
  let (_, song_set) = p in
  title_in_songs t song_set
(*@ b = song_in_list t p 
    requires valid_playlist p
    ensures b <-> exists s. List.mem s (snd p) /\ let (t', _, _, _) = s in t' = t
*)

let rec all_with_song (t : title) ( sp : splaylist) =
  match sp with 
  | [] -> []
  | p :: ps -> if song_in_list t p then p::all_with_song t ps else all_with_song t ps 
(*@ sp' = all_with_song t sp 
    requires valid_splay sp
    variant sp
    ensures forall p. List.mem p sp' -> List.mem p sp /\ exists s. List.mem s (snd p) /\ let (t', _, _, _) = s in t' = t 
    ensures valid_splay sp*)

(* all_playlists_song : title -> splaylist -> name set*)
let all_playlists_song (t : title) ( sp : splaylist) =
  let rec get_names l = 
  match l with 
  | [] -> []
  | (n, _):: ps -> n::get_names ps 
  (*@ ln = get_names sp 
    variant sp
    ensures forall n. List.mem n ln -> exists p. List.mem p sp /\ fst p = n
    ensures forall p. List.mem p sp -> exists n. List.mem n ln /\ fst p = n
  *) 
  in
  let l = all_with_song t sp in
  get_names l
(*@ ln = all_playlists_song t sp 
    requires valid_splay sp 
    ensures forall n. List.mem n ln ->
      exists p. List.mem p sp /\ fst p = n
    ensures forall n. List.mem n ln ->
       exists p, s. List.mem p sp /\ fst p = n /\ List.mem s (snd p) /\ let (t', _, _, _) = s in t' = t   *)



(** {1 Exercice 3: System of Circles+} *)

(** {2 Paragraph a: model SCIRCLE, the set of states of the system} *)

type cuser     = string
type scuser    = cuser set

type cname    = string
type circle   = cname * scuser

type scircle = circle set

(** {2 Paragraph b: Define (with a function or relation) the operation on SCIRCLE that adds a user to a set of circles.} *)

(*@ predicate valid_circle (c : 'b * 'a list) = list_set (snd c) *)

(*@ predicate valid_scircle (cs : ('b * 'a list) list) = list_set cs /\
      forall c. List.mem c cs -> valid_circle c *)

let [@logic] add_to_circle (c :circle) u = 
  let (name, users) = c in 
    (name, union users (singleton u))
(*@ c' = add_to_circle c u 
    requires valid_circle c
    ensures snd c' = union (snd c) (singleton u)
    ensures fst c' = fst c
    ensures List.mem u (snd c')
    ensures valid_circle c' *)

let [@logic] delete_from_circle (c :circle) u = 
  let (name, users) = c in 
      (name, dif users (singleton u))
  (*@ c' = add_to_circle c u 
      requires valid_circle c
      ensures snd c' = dif (snd c) (singleton u)
      ensures fst c' = fst c
      ensures not List.mem u (snd c')
      ensures valid_circle c' *)

(* scircle -> user -> scircle *)
let [@logic] rec add_to_all_circles sc u =
    match sc with 
    | [] -> []
    | c :: cs -> ( add_to_circle c u )::(add_to_all_circles cs u)
(*@ sc' = add_to_all_circles sc u 
      requires valid_scircle sc
      ensures forall c. List.mem c sc -> List.mem (add_to_circle c u) sc'
      ensures forall c. List.mem c sc' -> List.mem u (snd c)
      ensures valid_scircle sc' *)
      
let add_to_scircle sc1 sc2 u =
  union (dif sc1 sc2) (add_to_all_circles sc2 u)
(*@ sc' = add_to_scircle sc1 sc2 u
      requires valid_scircle sc1
      requires valid_scircle sc2
      ensures valid_scircle sc'
      ensures sc' =  union (dif sc1 sc2) (add_to_all_circles sc2 u)
*)


(** {2 Paragraph c: Define (with a function or relation) the operation on SCIRCLE that retrieves all people in a circle.} *)


let rec circle_with_name (sc:scircle) n = 
  match sc with 
  | [] -> invalid_arg "no circle with that name"
  | c::xs -> let (n', _) = c in 
      if String.equal n' n then c else circle_with_name xs n 
(*@ c = circle_with_name sc n 
      variant sc
      raises Invalid_argument _ -> forall c'. List.mem c' sc -> fst c' <> n
      ensures List.mem c sc
      ensures fst c = n *)

    (*requires valid_scircle sc  
      ensures valid_circle c*)

let users_in_circle sc n =
  let (_, u) = circle_with_name sc n in u 
(*@ us = users_in_circle sc n 
      raises Invalid_argument _ -> forall c'. List.mem c' sc -> fst c' <> n
      ensures exists c. List.mem c sc /\ us = snd c *)

(** {2 Paragraph d: Define (with a function or relation) the operation on SCIRCLE that blocks a user, i.e., deletes a user from all circles.} *)

let [@logic] rec block_user sc u =
    match sc with 
    | [] -> []
    | c :: cs -> ( delete_from_circle c u )::(block_user cs u)
(*@ sc' = add_to_all_circles sc u 
      requires valid_scircle sc
      ensures forall c. List.mem c sc -> List.mem (delete_from_circle c u) sc'
      ensures forall c. List.mem c sc' -> not List.mem u (snd c)
      ensures valid_scircle sc' *)

(** {2 Paragraph e: Define (with a function or relation) the operation on SCIRCLE that retrieves all the circles associated with a given user.} *)

let [@logic] rec all_users_circle (sc:scircle) u = 
  match sc with 
  | [] -> []
  | c::r -> let (_, us) = c in 
      if in_set u us then c::(all_users_circle r u) else all_users_circle r u
(*@ sc' = all_users_circle sc u 
      requires valid_scircle sc
      variant sc
      ensures forall c. List.mem c sc' -> List.mem c sc /\ List.mem u (snd c) 
      ensures forall c. List.mem c sc /\ List.mem u (snd c) -> List.mem c sc'
      ensures valid_scircle sc'*)

(** {2 Paragraph f: Define (with a function or relation) the operation on SCIRCLE that given a user, retrieves its larger circle.} *)

let rec largest l = 
  match l with
  | [] -> invalid_arg "Empty list"
  | [c] -> c
  | c::xs -> 
      let (_, us) = c in        
      let c' = largest xs in 
      let (_, us') = c' in 
      if card us >= card us' then c else c' 
  (*@ c = largest l 
        requires forall e. List.mem e l -> list_set ( snd e )
        raises Invalid_argument _ -> l = []
        variant l
        ensures forall e. List.mem e l -> List.length (snd c) >= List.length (snd e)
        ensures List.mem c l *)

let larger_circle (sc : scircle) u = 
  largest (all_users_circle sc u)
(*@ c = larger_circle sc u 
      requires valid_scircle sc
      raises Invalid_argument _ -> all_users_circle sc u = []
      ensures forall e. List.mem e sc /\ List.mem u (snd e) -> List.length (snd c) >= List.length (snd e)
*)

(** {2 Paragraph g: Define (with a function or relation) the operation on SCIRCLE that given two circles names, retrieves the users that belong to the intersection.} *)

let in_both (sc: scircle) n1 n2 = 
  let (_, c1) = circle_with_name sc n1 in 
  let (_, c2) = circle_with_name sc n2 in 
  intersection c1 c2
(*@ us = both_circles sc n1 n2 
    requires valid_scircle sc
    raises Invalid_argument _ -> forall c'. List.mem c' sc -> fst c' <> n1 \/ fst c' <> n2
    ensures exists c1, c2. fst c1 = n1 /\ fst c2 = n2 /\
      forall u. List.mem u us -> List.mem u (intersection (snd c1) (snd c2)) *)

(** {2 Paragraph g: An extended circle of an user are its circle’s circles, i.e. people who are at one degreeof distance.
Define (with a function or relation) the operation on SCIRCLE that given a user, retrieves its extended circle.} *)

let rec join_all l =
  match l with 
  | [] -> [] 
  | (_, us)::xs -> union us (join_all xs)
(*@ us = join_all l
      requires valid_scircle l
      variant l
      ensures forall u. List.mem u us -> exists c. List.mem c l /\ List.mem u (snd c)
      ensures list_set us *)



let extended_circle (sc: scircle) u =
  let uc = all_users_circle sc u in 
  let rec extended l =
    match l with 
    | [] -> [] 
    | u'::us -> 
        let circles = List.filter (fun (_, users) -> not (in_set u users) ) (all_users_circle sc u') in 
        let no_u = join_all circles in 
        union no_u (extended us)
    (*@ ex = extended l
        requires list_set l 
        variant l
        ensures forall e. List.mem e ex -> exists c. List.mem e (snd c) /\ not (List.mem u (snd c)) /\ List.mem c sc *)
    in
  extended (join_all uc)
  (*@ us = extended_circle sc u
      requires valid_scircle sc 
      ensures forall v. List.mem v us -> exists c1, c2. 
          List.mem c1 sc /\ List.mem c2 sc /\ List.mem u (snd c1) /\ List.mem v (snd c1) /\
          List.mem v (snd c2) /\ not List.mem u (snd c2)  *)
