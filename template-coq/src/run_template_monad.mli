val declare_inductive : Environ.env -> Evd.evar_map -> Constr.t -> unit

val reduce_all : Environ.env -> Evd.evar_map -> Constr.t -> Constr.t

val run_template_program_rec :
    poly:bool ->
    ?intactic:bool ->
    Constr.t Plugin_core.cont ->
    st:Plugin_core.coq_state ->
    Environ.env -> Evd.evar_map * Constr.t ->
    Plugin_core.coq_state
