
open Constr
open Names
open Univ
open Constr_reification.ConstrReification

let i63_t = resolve "metacoq.nstring.i63.type"
let str_t = resolve "metacoq.nstring.type"
let str_make = resolve "metacoq.nstring.make"

module Reify = 
struct

    let i63 i = mkInt (Uint63.of_int i)

    let chr c = i63 (Char.code c)

    (* Typing rule for array (u, arr, d, t): 
     * arr[i] : t, d:t
     * t : u (i.e u = Set for t = int63)
     * (See: kernel/typeops.ml)
     *)
    let univ = Instance.of_array [| Level.set |]
        
    let nstr str =
        let def = mkInt (Uint63.of_int 0) in
        let arr = Array.init (String.length str) (fun i -> chr str.[i]) in
        mkApp (Lazy.force str_make, 
            [| mkArray (univ, arr, def, Lazy.force i63_t) |])

    let ident id = nstr (Id.to_string id)

end

module Quote =
struct
    exception Not_a_nstr of string

    let chr term (* of type int *) = 
        match kind term with
        | Int uint -> Char.unsafe_chr (Uint63.to_int_min uint 0xff)
        | _ -> raise (Not_a_nstr "array element not an int")

    let nstr term (* of type nstr *) = 
        match kind term with
        | App (hd, body) when equal hd (Lazy.force str_make) ->
                begin match kind term with
                | Array (_, arr, _, _) ->
                        String.init (Array.length arr) (fun i -> chr arr.(i))
                | _ -> raise (Not_a_nstr "Argument of 'MkStr' is not an array")
                end
        | _ -> raise (Not_a_nstr "Not a application of 'MkStr'")

    let ident term (* of type nstr *) = 
        Id.of_string (nstr term)
end

module Test = 
struct

    let define_id (name : Id.t) (str : Id.t) =
        let env = Global.env () in
        let sigma = Evd.from_env env in
        let body = EConstr.of_constr (Reify.ident str) in
        let cinfo = Declare.CInfo.make ~name:name 
            ~typ:(Some (EConstr.of_constr (Lazy.force str_t))) () in
        let info = Declare.Info.make ~poly:false ~kind:(Decls.IsDefinition Decls.Definition) () in
        ignore (Declare.declare_definition ~cinfo ~info ~opaque:false ~body sigma)
end
