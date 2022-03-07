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
  
  (*@ lemma list_set_sublist: forall l1, l2: 'a list. 
        ((forall e. List.mem e l1 -> List.mem e l2) /\ list_set l2 ) -> list_set l1 *)

type 'a set = 'a list

(** [singleton x] returns a new set containg only [x] *)
let singleton x =
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
let dif s1 s2 =
  List.filter (fun y -> not (List.mem y s2)) s1
(*@ s' = dif s1 s2 
    requires list_set s1
    requires list_set s2
    ensures forall e. List.mem e s' <-> List.mem e s1 /\ not List.mem e s2
    ensures forall e. List.mem e s2 ->  not List.mem e s'
    ensures list_set s' *)

(** [union s1 s2] computes the union of sets [s1] and [s2] *)
let union s1 s2 =
  (dif s1 s2) @ s2
(*@ s' = dif s1 s2 
    requires list_set s1
    requires list_set s2
    ensures forall e. List.mem e s' -> List.mem e s1 \/ List.mem e s2
    ensures forall e. List.mem e s1 -> List.mem e s'
    ensures forall e. List.mem e s2 -> List.mem e s'
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
let rec check_access u p ap =
  (* List.exists (fun (a, pp) -> a = u && in_set p pp) ap List.exists not supported currently due to name clashes with exists*)
  match ap with
  | [] -> false 
  | (a, pp):: xs -> ( a = u && in_set p pp ) || check_access u p xs
(*@ b = check_access u p ap 
    requires valid_system ap
    variant ap
    ensures b <-> exists ps. List.mem (u, ps) ap /\ List.mem p ps *)


(** {2 Paragraph c: give a user access to a printer} *)

(* give_access : user -> printer -> aprinter -> aprinter *)
let give_access u p ap =
  let user = List.find_all (fun (a, _) -> a = u) ap in
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
    ensures forall p'. List.mem p' ap -> fst p' <> u -> List.mem p' ap'
    ensures exists p'. List.mem p' ap' /\ fst p' = u /\ List.mem p (snd p')
*)

(** {2 Paragraph d: returns the users that can access more printers} *)

(* Had to resort to auxiliarly functions, instead of List.filter and List.find_all
due to list_set invariant. Could also remove this invariant.*)


(*@ predicate larger (i : int) ( l : ('a * 'b list) list ) =
        forall p. List.mem p l -> i >= List.length (snd p)*)


let rec larger_all i l =
  match l with 
  | [] -> true
  | (_, pp):: xs -> i >= card pp && larger_all i xs 
(*@ b = larger_all i l 
    requires valid_system l 
    variant l
    ensures b <-> larger i l *)

(* max_access : aprinter -> user set *)
let max_access ap =
  let rec larger l =  
  match l with 
  | [] -> [] 
  | (u, pp)::xs -> let size = card pp in 
    if larger_all size ap then u :: larger xs else  larger xs
  (*@ us = larger l 
      requires valid_system l
      variant l
      ensures forall u. List.mem u us -> exists p. List.mem p l /\ fst p = u /\ larger (List.length (snd p)) ap        
  *)
  in 
  larger ap
  (*@ us = max_access ap 
      requires valid_system ap
      ensures forall u. List.mem u us -> exists p. List.mem p ap /\ fst p = u /\ larger (List.length (snd p)) ap        
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
let add_song_list p s =
  let (name, song_set) = p in
    (name, union song_set (singleton s))
(*@ pl' = add_song_list pl s
      requires valid_playlist pl
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
    ensures forall pl. pl <> p /\ List.mem pl sp -> List.mem pl sp'
    ensures exists p'. List.mem p' sp' /\ (forall ss. List.mem ss (snd p) -> List.mem ss (snd p')) /\ fst p = fst p'
            /\ List.mem s (snd p') /\ (forall ss. List.mem ss (snd p') /\ ss <> s -> List.mem ss (snd p))
    ensures valid_splay sp'*)


(** {2 Paragraph c: remove a song from playlist} *)

(* remove_song_list : song -> playlist -> playlist *)
let remove_song_list s p =
  let (name, song_set) = p in
  (name, dif song_set (singleton s))
(*@ pl' = remove_song_list s pl
      requires valid_playlist pl
      ensures not List.mem s (snd pl')
      ensures forall ss. List.mem ss (snd pl') -> List.mem ss (snd pl)
      ensures forall ss. List.mem ss (snd pl) /\ ss <> s -> List.mem ss (snd pl')
      ensures fst pl' = fst pl
      ensures valid_playlist pl'*)


(* remove_song : playlist -> song -> splaylist -> splaylist *)
let remove_song p s sp =
  union (dif sp (singleton p)) (singleton (remove_song_list s p))
(*@ sp' = remove_song p s sp 
    requires valid_playlist p
    requires valid_splay sp
    ensures forall pl. pl <> p /\ List.mem pl sp -> List.mem pl sp'
    ensures exists p'. List.mem p' sp' /\ (forall ss. List.mem ss (snd p') -> List.mem ss (snd p)) /\ fst p = fst p'
            /\ not List.mem s (snd p') /\ (forall ss. List.mem ss (snd p) /\ ss <> s -> List.mem ss (snd p'))
    ensures valid_splay sp'*)


(** {2 Paragraph d: remove a song from all playlists} *)

(* remove_song_all: song -> splaylist -> splaylist *)
let rec remove_song_all s sp =
  match sp with 
  | [] -> [] 
  | p :: pls -> remove_song_list s p :: remove_song_all s pls
(*@ sp' = remove_song_all s sp
    requires valid_splay sp 
    variant sp
    ensures valid_splay sp
    ensures forall p. List.mem p sp -> exists p'. List.mem p' sp /\ fst p = fst p' /\ 
      forall s'. s <> s' /\ List.mem s' (snd p) -> List.mem s' (snd p')
    ensures forall p.  List.mem p sp' -> not List.mem s (snd p)*)

(** {2 Paragraph e: returns all the playlists containing a given song} *)

let rec title_in_songs t sxs =
  match sxs with 
  | [] -> false 
  | (t', _, _, _):: ss -> t' = t || title_in_songs t ss
(*@ b = song_in_list t sxs
    variant sxs
    ensures b <-> exists s. List.mem s sxs /\ let (t', _, _, _) = s in t' = t
*)

(* song_in_list : title -> playlist -> bool *)
let song_in_list t p =
  let (_, song_set) = p in
  title_in_songs t song_set
(*@ b = song_in_list t p 
    requires valid_playlist p
    ensures b <-> exists s. List.mem s (snd p) /\ let (t', _, _, _) = s in t' = t
*)

let rec all_with_song t sp =
  match sp with 
  | [] -> []
  | p :: ps -> if song_in_list t p then p::all_with_song t ps else all_with_song t ps 
(*@ sp' = all_with_song t sp 
    requires valid_splay sp
    variant sp
    ensures forall p. List.mem p sp' -> List.mem p sp /\ exists s. List.mem s (snd p) /\ let (t', _, _, _) = s in t' = t 
    ensures valid_splay sp*)

(* all_playlists_song : title -> splaylist -> name set*)
let all_playlists_song t sp =
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
