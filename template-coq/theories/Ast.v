(* Distributed under the terms of the MIT license.   *)


Require Import List. Import ListNotations.
From MetaCoq.Template Require utils Environment Universes BasicAst.
Import utils Environment.Native.
Export BasicAst.Native Universes.Native.

(** * AST of Coq kernel terms and kernel data structures

    ** Basic data-types:

      We reflect identifiers [ident], sort families [sort_family], names
    [name], cast kinds [cast_kind], inductives [inductive] and primitive
    projections [projection] and (co)-fixpoint blocks [mfixpoint] and
    [def]. These are defined in the [BasicAst] file.

    ** Terms:

      The AST is [term : Set]

      Smart constructors [mkApp], [mkApps] maintain the invariant
    of no nested or empty n-ary applications.
      List in fixpoints and cofixpoint should be non-empty.

    ** Kernel interface: entries and declarations

      Kernel input declarations for constants [constant_entry] and mutual
    inductives [mutual_inductive_entry]. Kernel safe declarations for
    constants [constand_decl] and inductives [minductive_decl].

    ** Environments of declarations

      The global environment [global_env_ext]: a list of [global_decl] and
    a universe graph [constraints].  *)


Inductive term : Type :=
| tRel (n : nat)
| tVar (id : ident) (* For free variables (e.g. in a goal) *)
| tEvar (ev : nat) (args : list term)
| tSort (s : Universe.t)
| tCast (t : term) (kind : cast_kind) (v : term)
| tProd (na : name) (ty : term) (body : term)
| tLambda (na : name) (ty : term) (body : term)
| tLetIn (na : name) (def : term) (def_ty : term) (body : term)
| tApp (f : term) (args : list term)
| tConst (c : kername) (u : Instance.t)
| tInd (ind : inductive) (u : Instance.t)
| tConstruct (ind : inductive) (idx : nat) (u : Instance.t)
| tCase (ind_and_nbparams: inductive*nat) (type_info:term)
        (discr:term) (branches : list (nat * term))
| tProj (proj : projection) (t : term)
| tFix (mfix : mfixpoint term) (idx : nat)
| tCoFix (mfix : mfixpoint term) (idx : nat).

Definition mkApps t us :=
  match us with
  | nil => t
  | _ => match t with
        | tApp f args => tApp f (args ++ us)
        | _ => tApp t us
        end
  end.


Module TemplateTerm <: Term.

Definition term := term.

Definition tRel := tRel.
Definition tSort := tSort.
Definition tProd := tProd.
Definition tLambda := tLambda.
Definition tLetIn := tLetIn.
Definition tInd := tInd.
Definition tProj := tProj.
Definition mkApps := mkApps.

End TemplateTerm.

Ltac unf_term := unfold TemplateTerm.term in *; unfold TemplateTerm.tRel in *;
                 unfold TemplateTerm.tSort in *; unfold TemplateTerm.tProd in *;
                 unfold TemplateTerm.tLambda in *; unfold TemplateTerm.tLetIn in *;
                 unfold TemplateTerm.tInd in *; unfold TemplateTerm.tProj in *.

Module TemplateEnvironment := Environment TemplateTerm.
Include TemplateEnvironment.

Definition mkApp t u := Eval cbn in mkApps t [u].

Definition isApp t :=
  match t with
  | tApp _ _ => true
  | _ => false
  end.

Definition isLambda t :=
  match t with
  | tLambda _ _ _ => true
  | _ => false
  end.

(** Well-formed terms: invariants which are not ensured by the OCaml type system *)

Inductive wf : term -> Prop :=
| wf_tRel n : wf (tRel n)
| wf_tVar id : wf (tVar id)
| wf_tEvar n l : Forall wf l -> wf (tEvar n l)
| wf_tSort u : wf (tSort u)
| wf_tCast t k t' : wf t -> wf t' -> wf (tCast t k t')
| wf_tProd na t b : wf t -> wf b -> wf (tProd na t b)
| wf_tLambda na t b : wf t -> wf b -> wf (tLambda na t b)
| wf_tLetIn na t b b' : wf t -> wf b -> wf b' -> wf (tLetIn na t b b')
| wf_tApp t u : isApp t = false -> u <> nil -> wf t -> Forall wf u -> wf (tApp t u)
| wf_tConst k u : wf (tConst k u)
| wf_tInd i u : wf (tInd i u)
| wf_tConstruct i k u : wf (tConstruct i k u)
| wf_tCase ci p c brs : wf p -> wf c -> Forall (wf ∘ snd) brs -> wf (tCase ci p c brs)
| wf_tProj p t : wf t -> wf (tProj p t)
| wf_tFix mfix k : Forall (fun def => wf def.(dtype) /\ wf def.(dbody) /\ isLambda def.(dbody) = true) mfix ->
                   wf (tFix mfix k)
| wf_tCoFix mfix k : Forall (fun def => wf def.(dtype) /\ wf def.(dbody)) mfix -> wf (tCoFix mfix k).