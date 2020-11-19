
open Constr
open Names
open Univ
open Constr_reification.ConstrReification

let rd_i63_t = resolve "metacoq.nstring.i63.type"
let rd_nstring_t = resolve "metacoq.nstring.type"
let rd_nstring_con = resolve "metacoq.nstring.str_make"

let reify_i63 i = mkInt (Uint63.of_int i)

let reify_char c = reify_i63 (Char.code c)

let quote_id (id : Id.t) =
    let id = Id.to_string id in
    let def = mkInt (Uint63.of_int 0) in
    let arr = Array.make (String.length id) def in
    String.iteri (fun i c -> arr.(i) <- reify_char c) id; 
    mkApp (Lazy.force rd_nstring_con, 
        [| mkArray (Instance.empty, arr, def, Lazy.force rd_i63_t) |])


let test_make_def_rec ~poly (name : Id.t) (str : Id.t) ~st env (evm : Evd.evar_map)  : Plugin_core.coq_state =
    let k : Constr.t Plugin_core.cont = (fun ~st _ _ _ -> st) in
    let body = EConstr.of_constr (quote_id str) in
    let cinfo = Declare.CInfo.make ~name:name 
        ~typ:(Some (EConstr.of_constr (Lazy.force rd_nstring_t))) () in
    let info = Declare.Info.make ~poly:false ~kind:(Decls.IsDefinition Decls.Definition) () in
    let n = Declare.declare_definition ~cinfo ~info ~opaque:false ~body evm in
    let evm = Evd.from_env env in
    let (evm, c) = Evarutil.new_global evm n in
      k ~st env evm (EConstr.to_constr evm c)

let test_make_def ~pm env evm ~poly name str =
  test_make_def_rec ~poly name str env evm

    
