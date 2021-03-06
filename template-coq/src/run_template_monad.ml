open Univ
open Entries
open Names
open Redops
open Genredexpr
open Pp (* this adds the ++ to the current scope *)

open Tm_util
open Denoter
open Constr_quoter
open Constr_denoter
open Template_monad


let reduce_all env evm trm =
  EConstr.to_constr evm (Reductionops.nf_all env evm (EConstr.of_constr trm))


let unquote_reduction_strategy env evm trm (* of type reductionStrategy *) : Redexpr.red_expr =
  let (trm, args) = app_full trm [] in
  (* from g_tactic.ml4 *)
  let default_flags = Redops.make_red_flag [FBeta;FMatch;FFix;FCofix;FZeta;FDeltaBut []] in
  if constr_equall trm tcbv then Cbv default_flags
  else if constr_equall trm tcbn then Cbn default_flags
  else if constr_equall trm thnf then Hnf
  else if constr_equall trm tall then Cbv all_flags
  else if constr_equall trm tlazy then Lazy all_flags
  else if constr_equall trm tunfold then
    match args with
    | name (* to unfold *) :: _ ->
       let name = reduce_all env evm name in
       let name = unquote_kn name in
       Unfold [Locus.AllOccurrences, Tacred.evaluable_of_global_reference env (GlobRef.ConstRef (Constant.make1 name))]
    | _ -> bad_term_verb trm "unquote_reduction_strategy"
  else not_supported_verb trm "unquote_reduction_strategy"

let denote_mind_entry_finite trm =
  let (h,args) = app_full trm [] in
  match args with
    [] ->
    if constr_equall h cFinite then Declarations.Finite
    else if  constr_equall h cCoFinite then Declarations.CoFinite
    else if  constr_equall h cBiFinite then Declarations.BiFinite
    else not_supported_verb trm "denote_mind_entry_finite"
  | _ -> bad_term_verb trm "denote_mind_entry_finite"


let unquote_map_option f trm =
  let (h,args) = app_full trm [] in
  if constr_equall h cSome then
    match args with
      _ :: x :: [] -> Some (f x)
    | _ -> bad_term trm
  else if constr_equall h cNone then
    match args with
      _ :: [] -> None
    | _ -> bad_term trm
  else
    not_supported_verb trm "unquote_map_option"

let unquote_option = unquote_map_option (fun x -> x)



let unquote_constraint_type trm (* of type constraint_type *) : constraint_type =
  let (h,args) = app_full trm [] in
  match args with
    [] ->
    if constr_equall h tunivLt then Univ.Lt
    else if constr_equall h tunivLe then Univ.Le
    else if constr_equall h tunivEq then Univ.Eq
    else not_supported_verb trm "unquote_constraint_type"
  | _ -> bad_term_verb trm "unquote_constraint_type"


let unquote_univ_constraint evm c (* of type univ_constraint *) : _ * univ_constraint =
  let c, l2 = unquote_pair c in
  let l1, c = unquote_pair c in
  let evm, l1 = unquote_level evm l1 in
  let evm, l2 = unquote_level evm l2 in
  let c = unquote_constraint_type c in
  evm, (l1, c, l2)


(* set given by MSets.MSetWeakList.Make *)
let unquote_set trm =
  let (h, args) = app_full trm [] in
  (* h supposed to be Mkt, the constructor of the record *)
  match args with
  | list :: ok :: [] -> unquote_list list
  | _ -> not_supported_verb trm "unquote_set"


let unquote_constraints evm c (* of type constraints *) : _ * Constraint.t =
  let c = unquote_set c in
  List.fold_left (fun (evm, set) c -> let evm, c = unquote_univ_constraint evm c in evm, Constraint.add c set)
                 (evm, Constraint.empty) c


let denote_variance trm (* of type Variance *) : Variance.t =
  if constr_equall trm cIrrelevant then Variance.Irrelevant
  else if constr_equall trm cCovariant then Variance.Covariant
  else if constr_equall trm cInvariant then Variance.Invariant
  else not_supported_verb trm "denote_variance"


(* let denote_ucontext evm trm (* of type UContext.t *) : _ * UContext.t =
  let i, c = unquote_pair trm in
  let evm, i = unquote_universe_instance evm i in
  let evm, c = unquote_constraints evm c in
  evm, Univ.UContext.make (i, c) *)

let unquote_levelset evm c (* of type LevelSet.t *) : _ * LSet.t =
  let c = unquote_set c in
  List.fold_left (fun (evm, set) c -> let evm, c = unquote_level evm c in evm, LSet.add c set)
                 (evm, LSet.empty) c

let denote_ucontextset evm trm (* of type ContextSet.t *) : _ * ContextSet.t =
  let i, c = unquote_pair trm in
  let evm, i = unquote_levelset evm i in
  let evm, c = unquote_constraints evm c in
  evm, (i, c)

let denote_names evm trm : _ * Name.t array =
  let l = unquote_list trm in
  evm, CArray.map_of_list unquote_name l

let denote_ucontext evm trm (* of type UContext.t *) : _ * UContext.t =
  let l, c = unquote_pair trm in
  let l = unquote_list l in
  let evm, vars = map_evm unquote_level evm l in
  let vars = Instance.of_array (Array.of_list vars) in
  let evm, c = unquote_constraints evm c in
  evm, (UContext.make (vars, c))

let denote_aucontext evm trm (* of type AUContext.t *) : _ * AUContext.t =
  let i, c = unquote_pair trm in
  let l = unquote_list i in
  let vars = List.mapi (fun i l -> Level.var i) l in
  let vars = Instance.of_array (Array.of_list vars) in
  let evm, c = unquote_constraints evm c in
  evm, snd (abstract_universes (CArray.map_of_list unquote_name l) (UContext.make (vars, c)))


let denote_variance evm trm (* of type Variance.t list *) : _ * Variance.t array =
  let variances = List.map denote_variance (unquote_list trm) in
  evm, Array.of_list variances

let denote_variances evm trm : _ * Variance.t array option =
  match unquote_option trm with
  | None -> evm, None
  | Some t -> let evm, v = denote_variance evm t in
      evm, Some v

(* todo : stick to Coq implem *)
type universe_context_type =
  | Monomorphic_uctx of Univ.ContextSet.t
  | Polymorphic_uctx of Univ.AUContext.t

let _to_entry_inductive_universes = function
  | Monomorphic_uctx ctx -> Monomorphic_entry ctx
  | Polymorphic_uctx ctx -> Polymorphic_entry (AUContext.names ctx, AUContext.repr ctx)

let _denote_universes_decl evm trm (* of type universes_decl *) : _ * universe_context_type =
  let (h, args) = app_full trm [] in
  match args with
  | ctx :: [] -> if constr_equall h cMonomorphic_ctx then
                   let evm, ctx = denote_ucontextset evm ctx in
                   evm, Monomorphic_uctx ctx
                 else if constr_equall h cPolymorphic_ctx then
                   let evm, ctx = denote_aucontext evm ctx in
                   evm, Polymorphic_uctx ctx
                 else
                   not_supported_verb trm "denote_universes_decl"
  | _ -> bad_term_verb trm "denote_universes_decl"

let denote_universes_entry evm trm (* of type universes_entry *) : _ * Entries.universes_entry =
  let (h, args) = app_full trm [] in
  match args with
  | ctx :: [] -> if constr_equall h cMonomorphic_entry then
                   let evm, ctx = denote_ucontextset evm ctx in
                   evm, Monomorphic_entry ctx
                 else
                   not_supported_verb trm "denote_universes_entry"
  | names :: ctx :: [] ->
     if constr_equall h cPolymorphic_entry then
       let evm, names = denote_names evm names in
       let evm, ctx = denote_ucontext evm ctx in
        evm, Polymorphic_entry (names, ctx)
     else
      not_supported_verb trm "denote_universes_entry"
  | _ -> bad_term_verb trm "denote_universes_entry"


let unquote_one_inductive_entry evm trm (* of type one_inductive_entry *) : _ * Entries.one_inductive_entry =
  let (h,args) = app_full trm [] in
  if constr_equall h tBuild_one_inductive_entry then
    match args with
    | id::ar::template::cnames::ctms::[] ->
       let id = unquote_ident id in
       let evm, ar = denote_term evm ar in
       let template = unquote_bool template in
       let cnames = List.map unquote_ident (unquote_list cnames) in
       let evm, ctms = map_evm denote_term evm (unquote_list ctms) in
       evm, { mind_entry_typename = id ;
              mind_entry_arity = ar;
              mind_entry_template = template;
              mind_entry_consnames = cnames;
              mind_entry_lc = ctms }
    | _ -> bad_term_verb trm "unquote_one_inductive_entry"
  else
    not_supported_verb trm "unquote_one_inductive_entry"

let map_option f o =
  match o with
  | Some x -> Some (f x)
  | None -> None          

let denote_decl evm d = 
  let (h, args) = app_full d [] in
  if constr_equall h tmkdecl then
    match args with
    | name :: body :: typ :: [] ->
      let name = unquote_name name in
      let evm, ty = denote_term evm typ in
      (match unquote_option body with
      | None -> evm, Context.Rel.Declaration.LocalAssum (Context.annotR name, ty)
      | Some body -> let evm, body = denote_term evm body in
        evm, Context.Rel.Declaration.LocalDef (Context.annotR name, body, ty))
    | _ -> bad_term_verb d "denote_decl"
  else bad_term_verb d "denote_decl"

let denote_context evm ctx =
  map_evm denote_decl evm (unquote_list ctx)
  
let unquote_mutual_inductive_entry evm trm (* of type mutual_inductive_entry *) : _ * Entries.mutual_inductive_entry =
  let (h,args) = app_full trm [] in
  if constr_equall h tBuild_mutual_inductive_entry then
    match args with
    | record::finite::params::inds::univs::variance::priv::[] ->
       let record = map_option (map_option (fun x -> [|x|])) (unquote_map_option (unquote_map_option unquote_ident) record) in
       let finite = denote_mind_entry_finite finite in
       let evm, params = denote_context evm params in
       let evm, inds = map_evm unquote_one_inductive_entry evm (unquote_list inds) in
       let evm, univs = denote_universes_entry evm univs in
       let evm, variance = denote_variances evm variance in
       let priv = unquote_map_option unquote_bool priv in
       evm, { mind_entry_record = record;
              mind_entry_finite = finite;
              mind_entry_params = params;
              mind_entry_inds = inds;
              mind_entry_universes = univs;
              mind_entry_variance = variance;
              mind_entry_private = priv }
    | _ -> bad_term_verb trm "unquote_mutual_inductive_entry"
  else
    not_supported_verb trm "unquote_mutual_inductive_entry"


let declare_inductive (env: Environ.env) (evm: Evd.evar_map) (mind: Constr.t) : unit =
  let mind = reduce_all env evm mind in
  let evm, mind = unquote_mutual_inductive_entry evm mind in
  ignore (DeclareInd.declare_mutual_inductive_with_eliminations mind Names.Id.Map.empty [])

let not_in_tactic s =
  CErrors.user_err  (str ("You can not use " ^ s ^ " in a tactic."))

let rec run_template_program_rec ~poly ?(intactic=false) (k : Environ.env * Evd.evar_map * Constr.t -> unit) env ((evm, pgm) : Evd.evar_map * Constr.t) : unit =
  let (kind, universes) = next_action env evm pgm in
  match kind with
    TmReturn h ->
    let (evm, _) = Typing.type_of env evm (EConstr.of_constr h) in
    k (env, evm, h)
  | TmBind (a,f) ->
    run_template_program_rec ~poly ~intactic:intactic
     (fun (env, evm, ar) -> run_template_program_rec ~poly ~intactic:intactic k env (evm, Constr.mkApp (f, [|ar|]))) env (evm, a)
 | TmVariable (name, typ) ->
    if intactic then not_in_tactic "tmVariable"
    else
      let name = unquote_ident (reduce_all env evm name) in
      let kind = Decls.IsAssumption Decls.Definitional in
      let decl = Declare.SectionLocalAssum {typ; impl = Glob_term.Explicit} in
      (* FIXME: better handling of evm *)
      Declare.declare_variable ~name ~kind decl;
      let env = Global.env () in
      k (env, evm, Lazy.force unit_tt)
  | TmDefinition (opaque,name,s,typ,body) ->
    if intactic
    then not_in_tactic "tmDefinition"
    else
      let name = unquote_ident (reduce_all env evm name) in
      let opaque = unquote_bool (reduce_all env evm opaque) in
      let evm, typ = (match unquote_option s with Some s -> let red = unquote_reduction_strategy env evm s in Plugin_core.reduce env evm red typ | None -> evm, typ) in
      let evm, def = DeclareDef.prepare_definition ~opaque ~allow_evars:true ~poly evm
        UState.default_univ_decl ~types:(Some (EConstr.of_constr typ)) ~body:(EConstr.of_constr body) in
      let n = DeclareDef.declare_definition ~kind:(Decls.IsDefinition Decls.Definition)
         ~scope:(DeclareDef.Global Declare.ImportDefaultBehavior) ~name Names.Id.Map.empty def [] in
      let env = Global.env () in
      let evm, c = Evarutil.new_global evm n in
      k (env, evm, EConstr.to_constr evm c)
  | TmDefinitionTerm (opaque, name, typ, body) ->
    if intactic
    then not_in_tactic "tmDefinition"
    else
      let name = unquote_ident (reduce_all env evm name) in
      let opaque = unquote_bool (reduce_all env evm opaque) in
      let evm,body = denote_term evm (reduce_all env evm body) in
      let evm,typ =
        match unquote_option typ with
        | None -> (evm, None)
        | Some t ->
          let (evm, t) = denote_term evm (reduce_all env evm t) in
          (evm, Some t)
      in
      Plugin_core.run (Plugin_core.tmDefinition name ~poly ~opaque typ body) env evm
        (fun env evm res -> k (env, evm, quote_kn res))
  | TmLemmaTerm (name, typ) ->
    let ident = unquote_ident (reduce_all env evm name) in
    let evm,typ = denote_term evm (reduce_all env evm typ) in
    Plugin_core.run (Plugin_core.tmLemma ident ~poly typ) env evm
      (fun env evm kn -> k (env, evm, quote_kn kn))

  | TmAxiom (name,s,typ) ->
    if intactic
    then not_in_tactic "tmAxiom"
    else
      let name = unquote_ident (reduce_all env evm name) in
      let evm, typ = (match unquote_option s with Some s -> let red = unquote_reduction_strategy env evm s in Plugin_core.reduce env evm red typ | None -> evm, typ) in
      let univs = Evd.univ_entry ~poly evm in
      let param = Declare.ParameterEntry (None, (typ, univs), None) in
      let n = Declare.declare_constant ~name ~kind:Decls.(IsDefinition Definition) param in
      let env = Global.env () in
      k (env, evm, Constr.mkConst n)
  | TmAxiomTerm (name,typ) ->
    if intactic
    then not_in_tactic "tmAxiom"
    else
      let name = unquote_ident (reduce_all env evm name) in
      let evm,typ = denote_term evm (reduce_all env evm typ) in
      Plugin_core.run (Plugin_core.tmAxiom name ~poly typ) env evm
        (fun a b c -> k (a,b,quote_kn c))

  | TmLemma (name,typ) ->
    let name = reduce_all env evm name in
    let kind = Decls.(Definition) in
    let hole = CAst.make (Constrexpr.CHole (None, Namegen.IntroAnonymous, None)) in
    let evm, (c, _) = Constrintern.interp_casted_constr_evars_impls ~program_mode:true env evm hole (EConstr.of_constr typ) in
    let ident = unquote_ident name in
    Obligations.check_evars env evm;
       let obls, _, c, cty = Obligations.eterm_obligations env ident evm 0 c (EConstr.of_constr typ) in
       (* let evm = Evd.minimize_universes evm in *)
       let ctx = Evd.evar_universe_context evm in
       let hook = DeclareDef.Hook.make (fun { DeclareDef.Hook.S.dref = gr } ->
          let env = Global.env () in
          let evm = Evd.from_env env in
          let evm, t = Evd.fresh_global env evm gr in 
          k (env, evm, EConstr.to_constr evm t)) in  (* todo better *)
    ignore (Obligations.add_definition ~name:ident ~term:c cty ctx ~poly ~kind ~hook obls)

  | TmQuote trm ->
    (* user should do the reduction (using tmEval) if they want *)
    let qt = quote_term env trm
    in k (env, evm, qt)
  | TmQuoteRecTransp  (bypass, trm) ->
    let bypass = unquote_bool (reduce_all env evm bypass) in
    let qt = quote_term_rec bypass env trm in
    k (env, evm, qt)
  | TmQuoteInd (name, strict) ->
       let kn = unquote_kn (reduce_all env evm name) in
       let t = quote_mind_decl env (MutInd.make1 kn) in
       let _, args = Constr.destApp t in
       (match args with
        | [|decl|] ->
          k (env, evm, decl)
        | _ -> bad_term_verb t "anomaly in quoting of inductive types")
  | TmQuoteConst (name, bypass, strict) ->
    let name = unquote_kn (reduce_all env evm name) in
    let bypass = unquote_bool (reduce_all env evm bypass) in
    let cd = Environ.lookup_constant (Constant.make1 name) env in
    let cb = quote_constant_body bypass env evm cd in
    k (env, evm, cb)
  | TmQuoteUnivs ->
    let univs = Environ.universes env in
    k (env, evm, quote_ugraph univs)
  | TmPrint trm ->
    Feedback.msg_info (Printer.pr_constr_env env evm trm);
    k (env, evm, Lazy.force unit_tt)
  | TmMsg msg ->
     let msg = unquote_string (reduce_all env evm msg) in
     Plugin_core.run (Plugin_core.tmMsg msg) env evm
      (fun env evm _ -> k (env, evm, Lazy.force unit_tt))
  | TmFail trm ->
    let err = unquote_string (reduce_all env evm trm) in
    CErrors.user_err (str err)
  | TmLocate id ->
    let id = unquote_string (reduce_all env evm id) in
    Plugin_core.run (Plugin_core.tmLocateString id) env evm
      (fun env evm l ->
         let l = List.map quote_global_reference l in
         let l = to_coq_listl tglobal_reference l in
         k (env, evm, l))
  | TmCurrentModPath ->
    let mp = Lib.current_mp () in
    let s = quote_modpath mp in
    k (env, evm, s)
  | TmEval (s, trm) ->
    let red = unquote_reduction_strategy env evm (reduce_all env evm s) in
    let (evm, trm) = Plugin_core.reduce env evm red trm
    in k (env, evm, trm)
  | TmEvalTerm (s,trm) ->
    let red = unquote_reduction_strategy env evm (reduce_all env evm s) in
    let evm,trm = denote_term evm (reduce_all env evm trm) in
    Plugin_core.run (Plugin_core.tmEval red trm) env evm
      (fun env evm trm -> k (env, evm, quote_term env trm))
  | TmMkInductive mind ->
    declare_inductive env evm mind;
    let env = Global.env () in
    k (env, evm, Lazy.force unit_tt)
  | TmUnquote t ->
    begin
       try
         let t = reduce_all env evm t in
         let evm, t' = denote_term evm t in
         let typ = Retyping.get_type_of env evm (EConstr.of_constr t') in
         let evm, typ = Evarsolve.refresh_universes (Some false) env evm typ in
         let make_typed_term typ term evm =
           match Lazy.force texistT_typed_term with
           | GlobRef.ConstructRef ctor ->
              let (evm,c) = Evarutil.new_global evm (Lazy.force texistT_typed_term) in
              let term = Constr.mkApp
               (EConstr.to_constr evm c, [|EConstr.to_constr evm typ; t'|]) in
             let evm, _ = Typing.type_of env evm (EConstr.of_constr term) in
               (env, evm, term)
           | _ -> CErrors.anomaly (str "texistT_typed_term does not refer to a constructor")
         in
           k (make_typed_term typ t' evm)
        with Reduction.NotArity -> CErrors.user_err (str "unquoting ill-typed term")
      end
  | TmUnquoteTyped (typ, t) ->
       let evm, t' = denote_term evm (reduce_all env evm t) in
       (* let t' = Typing.e_solve_evars env evdref (EConstr.of_constr t') in *)
       let evm = Typing.check env evm (EConstr.of_constr t') (EConstr.of_constr typ) in
       k (env, evm, t')
  | TmFreshName name ->
    let name = reduce_all env evm name in
    let name' = Namegen.next_ident_away_from (unquote_ident name) (fun id -> Nametab.exists_cci (Lib.make_path id)) in
    k (env, evm, quote_ident name')
  | TmExistingInstance gr ->
    let gr = reduce_all env evm gr in
    let gr = unquote_global_reference gr in
    let q = Libnames.qualid_of_path (Nametab.path_of_global gr) in
    Classes.existing_instance true q None;
    k (env, evm, Lazy.force unit_tt)
  | TmInferInstance (s, typ) ->
    begin
      let evm, typ =
        match unquote_option s with
          Some s ->
          let red = unquote_reduction_strategy env evm s in
          Plugin_core.reduce env evm red typ
        | None -> evm, typ in
      try
        let (evm,t) = Typeclasses.resolve_one_typeclass env evm (EConstr.of_constr typ) in
        k (env, evm, constr_mkApp (cSome_instance, [| typ; EConstr.to_constr evm t|]))
      with
        Not_found -> k (env, evm, constr_mkApp (cNone_instance, [|typ|]))
    end
  | TmInferInstanceTerm typ ->
    let evm,typ = denote_term evm (reduce_all env evm typ) in
    Plugin_core.run (Plugin_core.tmInferInstance typ) env evm
      (fun env evm -> function
           None -> k (env, evm, constr_mkAppl (cNone, [| tTerm|]))
         | Some trm ->
           let qtrm = quote_term env trm in
           k (env, evm, constr_mkApp (cSome, [| Lazy.force tTerm; qtrm |])))
  | TmPrintTerm trm ->
    let evm,trm = denote_term evm (reduce_all env evm trm) in
    Plugin_core.run (Plugin_core.tmPrint trm) env evm
      (fun env evm _ -> k (env, evm, Lazy.force unit_tt))
