include Graph
include Path

module IntComparable = struct 
  type t = int;;
  let compare a b = if a = b then 0 else if a < b then -1 else 1
  let equal a b = a = b
  let hash a = a
  let default = 0
end

module DP = Persistent.Digraph.ConcreteLabeled( IntComparable )( IntComparable )

module CheckPathDP = Path.Check(DP)

let () = 
  let g = DP.empty in
  let g = DP.add_vertex g 1 in
  let g = DP.add_vertex g 2 in
  let g = DP.add_vertex g 3 in
  let g = DP.add_edge g 1 2 in 
  let g = DP.add_edge g 2 3 in 
  let finder = CheckPathDP.create g in 
  if CheckPathDP.check_path finder 1 3 then print_string "Path exists" 
  else print_string "Path does not exist"