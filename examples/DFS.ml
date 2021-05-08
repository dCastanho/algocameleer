module DFS =
    struct
        module type G =
            sig 
                type t
                type elt
                val iterAll : t -> (elt  -> unit) -> unit
                val iterAdj : t -> elt  -> (elt -> unit) -> unit
                val v : t -> int
            end

        module Make( Graph : G ) =
            struct
                let dfs g f =
                    let marked = Hashtbl.create (Graph.v g) in
                    let st = Stack.create () in
                    let mark e = Hashtbl.add marked e e in
                    let addStack e = Stack.push e st in
                    let aFunc e = 
                        addStack e ;
                        while not (Stack.is_empty st) do
                        let curr = Stack.pop st in
                        if not (Hashtbl.mem marked curr) then 
                            begin 
                                Graph.iterAdj g curr addStack ; f curr ; mark curr
                            end done
                        in
                    Graph.iterAll g aFunc             
            end
    end