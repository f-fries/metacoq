
open Constr
open Names
open Univ
open Constr_reification.ConstrReification

(* Reify = ML/Ast -> Coq 
 * Quote = Coq -> ML/Ast
 *)

let i63_t = resolve "metacoq.nstring.i63.type"
let str_t = resolve "metacoq.nstring.type"
let str_make = resolve "metacoq.nstring.make"


let print_debug (t : Constr.t) =
    Pp.string_of_ppcmds (Constr.debug_print t)

module Reify = 
struct

    let i63 (i : int) = mkInt (Uint63.of_int i)

    let chr (c : char) = i63 (Char.code c)

    let nstr (str : string) =
        let def = mkInt (Uint63.of_int 0) in
        (* Typing rule for array (u, arr, d, t):  - See: kernel/typeops.ml
         * arr[i] : t, d:t
         * t : u (i.e u = Set for t = int63)
         *)
        let univ = Instance.of_array [| Level.set |] in
        let arr = Array.init (String.length str) (fun i -> chr str.[i]) in
        mkApp (Lazy.force str_make, 
            [| mkArray (univ, arr, def, Lazy.force i63_t) |])

    let ident (id : Id.t) = nstr (Id.to_string id)

end

module Quote =
struct
    let reduce = 
        Run_template_monad.reduce_all

    exception Not_a_nstr of string

    (* Should be sound since term was a char in the first place *)
    let chr (term : Constr.t) (env : Environ.env) (sigma : Evd.evar_map) = (* of type int *)
        match kind (reduce env sigma term) with
        | Int uint -> Char.unsafe_chr (Uint63.to_int_min uint 0xff)
        | _ -> raise (Not_a_nstr "array element not an int")

    (* term must be normalised or the pattern matching
     * will not work. reduce will not normalise the array elements
     *)
    let nstr (term : Constr.t) (env : Environ.env) (sigma : Evd.evar_map) = 
        match kind (reduce env sigma term) with
        | App (hd, body) when equal hd (Lazy.force str_make) ->
                begin match kind body.(0) with
                | Array (_, arr, _, _) ->
                        String.init (Array.length arr) (fun i -> chr arr.(i) env sigma)
                | _ -> raise (Not_a_nstr 
                            (String.concat "Argument of 'MkStr' is not an array" [print_debug body.(0)]))
                end
        | _ -> raise (Not_a_nstr "Not a application of 'MkStr'")

    let ident (term : Constr.t) (env : Environ.env) (sigma : Evd.evar_map) = (* of type nstr *)
        Id.of_string (nstr term env sigma)
end

module Test = 
struct
    
    let run_pgm ~pm env sigma pgm =
        Run_template_monad.run_template_program_rec ~poly:false (fun ~st _ _ _ -> st) ~st:pm env (sigma, pgm)

    let define_id (name : Id.t) (str : Id.t) =
        let env = Global.env () in
        let sigma = Evd.from_env env in
        let body = EConstr.of_constr (Reify.ident str) in
        let cinfo = Declare.CInfo.make ~name:name 
            ~typ:(Some (EConstr.of_constr (Lazy.force str_t))) () in
        let info = Declare.Info.make ~poly:false ~kind:(Decls.IsDefinition Decls.Definition) () in
        ignore (Declare.declare_definition ~cinfo ~info ~opaque:false ~body sigma)

    let print_id (ident : Constrexpr.constr_expr) =
            let env = Global.env () in
            let sigma = Evd.from_env env in
            let (sigma, ident) = Constrintern.interp_open_constr env sigma ident in
            let ident = EConstr.to_constr sigma ident in
            let ident = Run_template_monad.reduce_all env sigma ident in
            let ident = Constr.mkVar (Quote.ident ident env sigma) in
            let (sigma, mqPrint) = EConstr.fresh_global env sigma (Lazy.force Template_monad.ptmPrint) in
            let pgm = Constr.mkApp ((EConstr.to_constr sigma mqPrint), [| Constr.mkSet; ident |]) in
            run_pgm env sigma pgm
end
