open Hashtbl

module HashtblFold(Elt : HashedType) = struct 

  module H = Hashtbl.Make(Elt)

  include H

  (** Returns a list of all the keys (including duplicates) *)
  let key_list tbl = 
    H.fold (fun key _ acc -> key :: acc ) tbl []

  (** Returns a list of all the values in the map. 
  Values associated with the same key will appear in reverse order of insertion *)
  let value_list tbl = 
    H.fold (fun _ v acc -> v :: acc) tbl []

  (** Counts the number of entries in the table, including values associated with the same key,
    Should be equal to length *)
  let n_entries tbl =
    H.fold (fun _ _ acc -> acc + 1) tbl 0 
  
  (** Get all distinc keys. Equal to key_list if every key only has one value *)
  let distinct_key_list tbl = 
    let increase k k' l = 
      if Elt.equal k k' then l else k :: l in 
      let res = H.fold (
        fun k v acc -> 
          match acc with 
          | (None, l) -> (Some k, k :: l)
          | (Some k', l) -> (Some k, increase k k' l) 
          ) tbl (None, [])
      in 
      snd res 
  
end

module IntH = struct

  type t = int 

  let equal (i : t) i' = i = i'

  let hash (i : t) : int = i
end

module IFold = HashtblFold(IntH)

let rec print_int_list = function
  | [] -> ()
  | x :: [] -> print_int x 
  | x :: xs-> print_int x ; print_string ", " ; print_int_list xs 

let print_int_list l =
print_string "[" ; print_int_list l ; print_endline "]"

let () =
  let h = IFold.create 10 in 
  IFold.add h 10 10 ;
  IFold.add h 9 10 ;
  IFold.add h 10 11 ;
  IFold.add h 8 10 ;
  IFold.add h 8 11 ;
  IFold.add h 8 13 ;
  print_int_list (IFold.value_list h) ;
  print_int_list (IFold.key_list h) ;
  print_int_list (IFold.distinct_key_list h) ;
  print_int (IFold.n_entries h) ; print_newline () ;
  print_int (IFold.length h) ; print_newline () ;