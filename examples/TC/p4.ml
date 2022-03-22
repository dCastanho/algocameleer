(** For the sack of simplicity, sets are modeled as lists without
    repetitions. For a proper sets implementation, one should use the Set
    functor from the OCaml standard library (cf,
    https://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.html).
    
    Identical to the one in p3.ml, cameleer does not support
    importing of modules very well at this time.*)

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

let [@logic] empty = []
(*@ s = empty 
    ensures list_set s
    ensures s = []  *)
    


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

(** {1 Exercice 1: Social Network} *)

(** {1 Paragraph a & b: define the set LIST and the set NETWORK} *)

type email = string 
type name = string 
type address = string * string 
type info = email * name * address

type contact_list = name * email set 
type user = info * contact_list set 
type network = user set 

(*@ predicate valid_contactL (l : contact_list) = list_set (snd l) *)

(*@ predicate valid_user (u : user) = list_set (snd u) /\ forall l. List.mem l (snd u) -> valid_contactL l *)

(*@ predicate valid_network (s : network) = list_set s /\ forall u. List.mem u s -> valid_user u *)

(** {1 Paragraph c: define a first order predicate that checks if a user with a given email exists in the system }*)

(*@ predicate email_exists (e : email) (s: network) = 
      exists u. List.mem u s /\ let (e', _, _) = fst(u) in e' = e *)

(* function for the above predicate *)

let rec email_exists_fun (e : email) (s: network) = 
  match s with 
  | [] -> false 
  | (info, _)::r -> let (e', _, _) = info in 
      String.equal e' e || email_exists_fun e r
(*@ b = email_exists_fun e s 
      requires valid_network s 
      variant s
      ensures b <-> email_exists e s *)

(** {1 Paragraph d: insert a new user into the system, assuming there isn't one with the same email. Assume their list starts empty }*)


let add_user r i = 
  let (email,_, _) = i in 
    if not (email_exists_fun email r) then union r (singleton (i, empty)) else invalid_arg "email already exists"
(*@ r' = add_user r i
      requires valid_network r
      raises Invalid_argument _ -> let (email,_,_) = i in email_exists email r
      ensures let (email,_,_) = i in 
            not (email_exists email r) /\ r' = union r (singleton (i, empty))
      ensures valid_network r' *)

(** {1 Paragraph e: insert a new email to user's contact list, so long as that email exists }*)

(*@ predicate no_email (r:network) (e:email) = 
      forall u'. List.mem u' r -> let (email, _, _) = fst u' in email <> e *)

exception EmailNotExists 
exception ContactsNotExists

let rec get_user (r:network) e = 
  match r with 
  | [] -> raise EmailNotExists
  | u::r' -> let ((email, _,_),_) = u in 
      if String.equal email e then u else get_user r' e
(*@ u = get_user r e 
      requires valid_network r 
      variant r
      ensures List.mem u r /\ let (email, _, _) = fst u in email = e
      raises EmailNotExists -> no_email r e *)

let rec get_list l n = 
  match l with 
  | [] -> raise ContactsNotExists
  | c:: r -> let (name, _) = c in 
        if String.equal name n then c else get_list r n  
(*@ l' = get_list l n 
      requires list_set l 
      variant l 
      ensures List.mem l' l /\ fst l' = n 
      raises ContactsNotExists -> forall c. List.mem c l -> fst c <> n  *)


let add_email r e e' n =
  if not (email_exists_fun e' r) then raise EmailNotExists else 
    let u = get_user r e in
    let c = get_list (snd u) n in 
    let c' = (fst c, union (snd c) (singleton e')) in 
    let lists = union (dif (snd u) (singleton c)) (singleton c') in
    let u' = (fst u, lists) in 
    union (dif r  (singleton u)) (singleton u')
(*@ r' = add_email r e e' n 
       requires valid_network r
       raises EmailNotExists -> no_email r e \/ no_email r e'
       raises ContactsNotExists -> exists u : user. let (email,_,_) = fst u in email = e /\ forall l. List.mem l (snd u) -> fst l <> n 
       ensures exists u : user, l : contact_list. 
            let (email, _, _) = fst u in 
            let l' = (fst l, union (snd l) (singleton e')) in 
            let lists = union (dif (snd u) (singleton l)) (singleton l') in
            let u' = (fst u, lists) in 
             List.mem u r /\ email = e /\ List.mem l (snd u) /\
             fst l = n /\ r' = union (dif r  (singleton u)) (singleton u')
       ensures valid_network r'*)


(** {2 Paragraph a: define the set SYSTEM} *)

type contrib = int                 
type id = string              
type ntel = int               
type iuser = contrib * id     

type contract = contrib * ntel 
type operator = name * iuser set * contract set  
type system = iuser set * operator set 


(*@ predicate all_snd_different (l : ('a * 'b ) list ) = forall c1, c2. List.mem c1 l /\ List.mem c2 l /\ c1 <> c2 -> snd c1 <> snd c2 *)

(*@ predicate valid_operator (o : operator) = let (_, us, cs) = o in list_set us /\ list_set cs /\ all_snd_different cs  *)

(*@ predicate valid_system (s: system) =
       let (us, ops) = s in 
        list_set us /\ list_set ops /\    
            forall o. List.mem o ops -> valid_operator o
*)

(*@ lemma union_snd: forall l1, l2 : ('a * 'b ) list, x : ('a * 'b). 
       list_set l1 /\ list_set l2 /\ all_snd_different l2 /\ l1 = union l2 (singleton x) /\ (forall c. List.mem c l2 -> snd c <> snd x) -> all_snd_different l1 
       *)


(** {2 Paragraph b: define a function that verifies the existence of a given phone number in an operator} *)

(*@ predicate number_exists (s:system) (nt: ntel) (op:operator) =
      let (_, us, cs) = op in
        exists c. List.mem op (snd s) /\ List.mem c cs /\ snd c = nt *)

let rec ex l t = 
match l with 
| [] -> false 
| (_, t')::r -> t = t' || ex r t
(*@ b = ex l t 
      variant l
      ensures b <-> exists e. List.mem e l /\ snd e = t *)

let number_exists (s:system) nt op = 
   let (_, _, cset ) = op in 
      in_set op (snd s) && ex cset nt
(*@ b = number_exists s nt op
      requires valid_system s 
      requires valid_operator op 
      ensures b <-> number_exists s nt op
*)

(** {2 Paragraph c: Define the function that given a contributor's number, returns all its phone numbers}*)

let [@logic] rec all_num_from_op ncon l = 
    match l with 
    | [] -> []
    | (c, t)::r -> let l' = all_num_from_op ncon r in
            if ncon = c then t::l' else l'
(*@ ts = all_num_from_op ncon l 
      requires list_set l
      requires all_snd_different l
      variant l
      ensures forall t. List.mem t ts -> exists c. List.mem c l /\ fst c = ncon /\ snd c = t
      ensures list_set ts
*)

let rec all_num_from_sys ncon (l:operator list) = 
      match l with 
      | [] -> []
      | op::r -> let (_,_, ops) = op in union (all_num_from_op ncon ops) (all_num_from_sys ncon r)
  (*@ ts = all_num_from_sys ncon l 
        requires list_set l
        requires forall o. List.mem o l -> valid_operator o
        variant l
        ensures forall t. List.mem t ts -> exists c, o. let (_,_, ops) = o in List.mem o l /\ List.mem c ops /\ fst c = ncon /\ snd c = t
        ensures list_set ts
  *)

let all_num_con ncon (s:system) = all_num_from_sys ncon (snd s)
(*@ ts = all_num_con ncon s 
      requires valid_system s 
      ensures forall t. List.mem t ts -> exists c, o. let (_,_, ops) = o in List.mem o (snd s) /\ List.mem c ops /\ fst c = ncon /\ snd c = t *)

(** {2 Paragraph d: Define the function that given the name of an operator, returns all its associated phone numbers}*)

let [@logic] rec to_tlm l =
  match l with 
  | [] -> [] 
  | (_, t)::r -> t::to_tlm r
(*@ l' = to_tlm l 
      variant l 
      ensures forall e. List.mem e l -> exists e'. List.mem e' l' /\ snd e = e'
      ensures forall e. List.mem e l' -> exists e'. List.mem e' l /\ snd e' = e *)

exception OperatorNotExist
exception TooManyOperators

let op_with_name name (s: system) =
      let l = List.filter (fun o -> let (n, _, _) = o in String.equal name n) (snd s) in 
      match l with 
      | [] -> raise OperatorNotExist
      | [x]-> x
      | _ -> raise TooManyOperators
(*@ o = op_with_name n s 
      requires valid_system s 
      ensures List.mem o (snd s) /\ let (name, _, _) = o in name = n
      raises OperatorNotExist -> forall op. List.mem op (snd s) -> let (name, _, _) = op in name <> n
      raises TooManyOperators ->  exists op1, op2.  
              let (name1, _, _) = op1 in 
              let (name2, _, _) = op2 in 
                List.mem op1 (snd s) /\ List.mem op2 (snd s) /\ name1 = name2 /\ name1 = n
            *)

let all_num_op name (s: system) = 
      let (_, _, cs) =  op_with_name name s in to_tlm cs
(*@ ts = all_num_op n s 
      requires valid_system s 
      ensures forall t. List.mem t ts -> exists o, c. let (name, us, cs) = o in List.mem o (snd s) /\ name = n /\ List.mem c cs /\ t = snd c
      raises OperatorNotExist -> forall op. List.mem op (snd s) -> let (name, _, _) = op in name <> n
      raises TooManyOperators ->  exists op1, op2.  
              let (name1, _, _) = op1 in 
              let (name2, _, _) = op2 in 
                List.mem op1 (snd s) /\ List.mem op2 (snd s) /\ name1 = name2 /\ name1 = n
            *)

(** {2 Paragraph e: Define the function that given a contributor's number, returns the name of
                    all operators with which that number has 2 contracts}*)


let rec has_one e l = 
match l with 
| [] -> false 
|  (c, _)::xs -> c = e || has_one e xs
(*@ b = has_one e l 
      requires list_set l 
      variant l
      ensures b <-> exists c. List.mem c l /\ fst c = e *)

let rec has_two e l = 
  match l with 
  | [] -> false 
  |  (c, _)::xs -> if c = e then has_one e xs else has_two e xs
(*@ b = has_two e l 
      requires list_set l 
      variant l
      ensures b <-> exists c1, c2. List.mem c1 l /\ fst c1 = e /\ List.mem c2 l /\ fst c2 = e /\ c1 <> c2 *)

let has_atleast_two (op :operator) contrib = 
      let (_, _, contracts) = op in has_two contrib contracts
(*@ b = has_atleast_two op contrib 
      requires valid_operator op 
      ensures b <-> let (_, _, contracts) = op in exists c1, c2. 
            c1 <> c2 /\ fst c1 = contrib /\ fst c2 = contrib /\ List.mem c1 contracts /\ List.mem c2 contracts *)

(** {2 Paragraph f: Define the function that creates a new contract for a user in an operator, generating a new number }*)

let [@logic] rec bigger t l = 
match l with 
| [] -> true 
| x::xs -> t >= x && bigger t xs
(*@ b = bigger t l
      variant l 
      ensures b <-> forall m. List.mem m l -> m <= t *)

let [@logic] rec max_phone s = 
   match s with 
   | [] -> 0
   | x:: xs -> if bigger x xs then x else max_phone xs
(*@ t = max_phone s 
      variant s
      ensures List.length s = 0 -> t = 0
      ensures List.length s > 0 -> forall m. List.mem m s -> m <= t*)

let rec exists_user l u =
      match l with 
      | [] -> false 
      | (t, _):: us -> u = t || exists_user us u 
(*@ b = exists_user l u 
      variant l
      ensures b <-> exists u'. List.mem u' l /\ fst u' = u *)

exception UserNotExist

let add_num (s: system) c op  : system =
      if not ( exists_user (fst s) c ) then raise UserNotExist else
      let o = op_with_name op s in 
      let (name, us, contracts) = o in 
      let m = (max_phone (to_tlm contracts)) + 1 in
      let contracts' = union contracts (singleton (c, m)) in
      let o' = (name, us, contracts') in 
      let ops = union (dif (snd s) (singleton o)) (singleton o') in 
      (fst s, ops )
(*@ s' = add_num s c n
      requires valid_system s
      raises UserNotExist -> forall u. List.mem u (fst s) -> fst u <> c
      raises OperatorNotExist -> forall op. List.mem op (snd s) -> let (name, _, _) = op in name <> n
      raises TooManyOperators -> exists op1, op2.  
              let (name1, _, _) = op1 in 
              let (name2, _, _) = op2 in 
                List.mem op1 (snd s) /\ List.mem op2 (snd s) /\ name1 = name2 /\ name1 = n
      ensures valid_system s' 
      ensures exists u. List.mem u (fst s) /\ fst u = c 
      ensures exists o. 
            let (name, us, cs ) = o in
            List.mem o (snd s) /\ name = n /\
            s' = (fst s, union (dif (snd s) (singleton o) ) (singleton (name, us, union cs (singleton (c,  (max_phone (to_tlm cs)) + 1 ))))  )
      *)