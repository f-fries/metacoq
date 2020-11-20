open Names

module Reify : 
sig
    val i63 : int -> Constr.t
    val chr : char -> Constr.t
    val nstr : string -> Constr.t
    val ident : Id.t -> Constr.t
end

module Quote :
sig
    val chr : Constr.t -> char
    val nstr : Constr.t -> string
    val ident : Constr.t -> Id.t
end

module Test :
sig
    val define_id : Id.t -> Id.t -> unit
end
