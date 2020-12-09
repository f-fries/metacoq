
From Coq Require Import String.
From MetaCoq.Template Require Import utils.

Definition lt {s} cmp (a b : s) := cmp a b = Lt.

Module Type Sig.
    Parameter t : Set.

    Parameter print : t -> string.

    Parameter eqdec : eqdec t.
    Parameter eq : t -> t -> bool.
    Parameter eq_spec : booldec_spec eq.

    Parameter cmp : t -> t -> comparison.
    Parameter cmp_eq : forall x y, cmp x y = Eq <-> x = y.

    Parameter lt_irreflexive : forall a, ~ (lt cmp a a).
    Parameter lt_trans : forall a b c, lt cmp a b -> lt cmp b c -> lt cmp a c.
End Sig.


Module Native <: Sig.
    Definition t := nstring.
    Definition print := nstring_to_string.
    Definition eqdec := nstring_eqdec.
    Definition eq := nstring_eqb.
    Definition eq_spec := nstring_eqb_correct.
    Definition cmp := nstring_compare.
    Definition cmp_eq := nstring_compare_eq.
    Definition lt_irreflexive := nstring_lt_irreflexive.
    Definition lt_trans := nstring_order_trans Lt.
End Native.

Module String <: Sig.
    Definition t := string.
    Definition print (x : string) := x.
    Definition eqdec := String.string_dec.
    Definition eq := String.eqb.
    Definition eq_spec : booldec_spec eq.
    Proof.
        apply bdec_refl_spec. intros x y. apply String.eqb_spec.
    Qed.

    Definition cmp := string_compare.
    Definition cmp_eq := string_compare_eq.
    Definition lt_irreflexive := string_lt_irreflexive.
    Definition lt_trans := transitive_string_lt.
End String.
