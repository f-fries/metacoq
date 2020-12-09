(* Distributed under the terms of the MIT license.   *)
From Coq Require Import String Bool List.
From MetaCoq.Template Require Import utils.
From MetaCoq.Template Require Ident.
Local Open Scope string_scope.


(** ** Reification of names ** *)

(** [Comment taken from Coq's code]
    - Id.t is the type of identifiers, that is morally a subset of strings which
      only contains Unicode characters of the Letter kind (and a few more).
      => [ident]
    - Name.t is an ad-hoc variant of Id.t option allowing to handle optionally
      named objects.
      => [name]
    - DirPath.t represents generic paths as sequences of identifiers.
      => [dirpath]
    - Label.t is an equivalent of Id.t made distinct for semantical purposes.
      => [ident]
    - ModPath.t are module paths.
      => [modpath]
    - KerName.t are absolute names of objects in Coq.
      => [kername]

    And also :
    - Constant.t => [kername]
    - variable => [ident]
    - MutInd.t => [kername]
    - inductive => [inductive]
    - constructor => [inductive * nat]
    - Projection.t => [projection]
    - GlobRef.t => global_reference
*)

Module _BasicAst (Ident : Ident.Sig).

Ltac decide_eq_id := try unfold eqdec in *; intros; repeat (apply Ident.eqdec || decide equality).

Definition ident   := Ident.t. (* e.g. nat *)

Definition ident_eq := Ident.eq.
Definition ident_eq_spec := Ident.eq_spec.
Definition string_of_ident := Ident.print.

Definition qualid  := ident. (* e.g. Datatypes.nat *)
Definition string_of_qualid := string_of_ident.


(** Type of directory paths. Essentially a list of module identifiers. The
    order is reversed to improve sharing. E.g. A.B.C is ["C";"B";"A"] *)
Definition dirpath := list ident.

Definition string_of_dirpath : dirpath -> string
  := String.concat "." ∘ map string_of_ident ∘ rev.

Definition dirpath_eq_dec : eqdec dirpath.
Proof.
  decide_eq_id.
Defined.

Fixpoint list_eq {A} (eq : A -> A -> bool) xs ys := 
  match xs, ys with
  | nil, nil => true
  | x::xs, y::ys => eq x y && list_eq eq xs ys
  | _, _ => false
  end.

Definition dirpath_eq : dirpath -> dirpath -> bool := list_eq ident_eq.


(** The module part of the kernel name.
    - MPfile is for toplevel libraries, i.e. .vo files
    - MPbound are parameters of functors
    - MPdot is for submodules
*)
Inductive modpath :=
| MPfile  (dp : dirpath)
| MPbound (dp : dirpath) (id : ident) (i : nat)
| MPdot   (mp : modpath) (id : ident).

Fixpoint string_of_modpath (mp : modpath) : string :=
  match mp with
  | MPfile dp => string_of_dirpath dp
  | MPbound dp id _ => string_of_dirpath dp ++ "." ++ string_of_ident id
  | MPdot mp id => string_of_modpath mp ++ "." ++ string_of_ident id
  end.

Definition modpath_eq_dec : eqdec modpath.
Proof.
  decide_eq_id.
Defined.

Fixpoint modpath_eq mp1 mp2 :=
  match mp1, mp2 with
  | MPfile d1, MPfile d2 => 
      dirpath_eq d1 d2
  | MPbound d1 i1 n1, MPbound d2 i2 n2 => 
      dirpath_eq d1 d2 && ident_eq i1 i2 && Nat.eqb n1 n2
  | MPdot mp1 i1, MPdot mp2 i2 =>
      modpath_eq mp1 mp2 && ident_eq i1 i2
  | _, _ => false
  end.

(** The absolute names of objects seen by kernel *)
Definition kername := modpath × ident.

Definition string_of_kername (kn : kername) :=
  string_of_modpath kn.1 ++ "." ++ string_of_ident kn.2.

Definition kername_eq_dec : eqdec kername.
Proof.
  decide_eq_id.
Defined.

Definition eq_kername (k0 k1 : kername) : bool :=
  if kername_eq_dec k0 k1 then true else false.

(** Identifiers that are allowed to be anonymous (i.e. "_" in concrete syntax). *)
Inductive name : Set :=
| nAnon
| nNamed (_ : ident).

Definition string_of_name (na : name) :=
  match na with
  | nAnon => "_"
  | nNamed n => string_of_ident n
  end.

Definition name_eq_dec : eqdec name.
Proof.
  decide_eq_id.
Defined.


(** Designation of a (particular) inductive type. *)
Record inductive : Set := mkInd { inductive_mind : kername ;
                                  inductive_ind : nat }.
Arguments mkInd _%string _%nat.

Definition string_of_inductive (i : inductive) :=
  string_of_kername (inductive_mind i) ++ "," ++ string_of_nat (inductive_ind i).

Definition inductive_eq_dec : eqdec inductive.
Proof.
  decide_eq_id.
Defined.

Definition eq_inductive i i' :=
  let 'mkInd i n := i in
  let 'mkInd i' n' := i' in
  eq_kername i i' && Nat.eqb n n'.

Definition eq_constant := eq_kername.

Definition projection : Set := inductive * nat (* params *) * nat (* argument *).

Definition eq_projection p p' :=
  let '(ind, pars, arg) := p in
  let '(ind', pars', arg') := p' in
  eq_inductive ind ind' && Nat.eqb pars pars' && Nat.eqb arg arg'.

(** Kernel declaration references [global_reference] *)
Inductive global_reference :=
| VarRef : ident -> global_reference
| ConstRef : kername -> global_reference
| IndRef : inductive -> global_reference
| ConstructRef : inductive -> nat -> global_reference.

Definition string_of_gref gr : string :=
  match gr with
  | VarRef v => string_of_ident v
  | ConstRef s => string_of_kername s
  | IndRef (mkInd s n) =>
    "Inductive " ++ string_of_kername s ++ " " ++ (string_of_nat n)
  | ConstructRef (mkInd s n) k =>
    "Constructor " ++ string_of_kername s ++ " " ++ (string_of_nat n) ++ " " ++ (string_of_nat k)
  end.

Definition gref_eq_Dec : eqdec global_reference.
Proof.
  decide_eq_id.
Defined.

(*
Lemma ident_eq_spec x y : reflect (x = y) (ident_eq x y).
Proof.
  unfold ident_eq. destruct (string_compare_eq x y).
  destruct string_compare; constructor; auto.
  intro Heq; specialize (H0 Heq). discriminate.
  intro Heq; specialize (H0 Heq). discriminate.
Qed.
*)

(*
Lemma eq_kername_refl kn : eq_kername kn kn.
Proof.
  unfold eq_kername. destruct (kername_eq_dec kn kn); cbnr.
  contradiction.
Qed.
*)

(*
Lemma eq_inductive_refl i : eq_inductive i i.
Proof.
  destruct i as [mind k].
  unfold eq_inductive. now rewrite eq_kername_refl, PeanoNat.Nat.eqb_refl.
Qed.

Lemma eq_projection_refl i : eq_projection i i.
Proof.
  destruct i as [[mind k] p].
  unfold eq_projection.
  now rewrite eq_inductive_refl, !PeanoNat.Nat.eqb_refl.
Qed.
*)


(** The kind of a cast *)
Inductive cast_kind : Set :=
| VmCast
| NativeCast
| Cast
| RevertCast.

Inductive recursivity_kind :=
  | Finite (* = inductive *)
  | CoFinite (* = coinductive *)
  | BiFinite (* = non-recursive, like in "Record" definitions *).



(* Parametrized by term because term is not yet defined *)
Record def term := mkdef {
  dname : name; (* the name **)
  dtype : term;
  dbody : term; (* the body (a lambda term). Note, this may mention other (mutually-defined) names **)
  rarg  : nat  (* the index of the recursive argument, 0 for cofixpoints **) }.

Arguments dname {term} _.
Arguments dtype {term} _.
Arguments dbody {term} _.
Arguments rarg {term} _.

Definition string_of_def {A} (f : A -> string) (def : def A) :=
  "(" ++ string_of_name (dname def) ++ "," ++ f (dtype def) ++ "," ++ f (dbody def) ++ ","
      ++ string_of_nat (rarg def) ++ ")".

Definition print_def {A} (f : A -> string) (g : A -> string) (def : def A) :=
  string_of_name (dname def) ++ " { struct " ++ string_of_nat (rarg def) ++ " }" ++
                 " : " ++ f (dtype def) ++ " := " ++ nl ++ g (dbody def).


Definition map_def {A B} (tyf bodyf : A -> B) (d : def A) :=
  {| dname := d.(dname); dtype := tyf d.(dtype); dbody := bodyf d.(dbody); rarg := d.(rarg) |}.

Lemma map_dtype {A B} (f : A -> B) (g : A -> B) (d : def A) :
  f (dtype d) = dtype (map_def f g d).
Proof. destruct d; reflexivity. Qed.

Lemma map_dbody {A B} (f : A -> B) (g : A -> B) (d : def A) :
  g (dbody d) = dbody (map_def f g d).
Proof. destruct d; reflexivity. Qed.

Definition mfixpoint term := list (def term).


Definition test_def {A} (tyf bodyf : A -> bool) (d : def A) :=
  tyf d.(dtype) && bodyf d.(dbody).

Definition tCaseBrsProp {A} (P : A -> Type) (l : list (nat * A)) :=
  All (fun x => P (snd x)) l.

Definition tFixProp {A} (P P' : A -> Type) (m : mfixpoint A) :=
  All (fun x : def A => P x.(dtype) * P' x.(dbody))%type m.

Lemma map_def_map_def {A B C} (f f' : B -> C) (g g' : A -> B) (d : def A) :
  map_def f f' (map_def g g' d) = map_def (f ∘ g) (f' ∘ g') d.
Proof.
  destruct d; reflexivity.
Qed.

Lemma compose_map_def {A B C} (f f' : B -> C) (g g' : A -> B) :
  (map_def f f') ∘ (map_def g g') = map_def (f ∘ g) (f' ∘ g').
Proof. reflexivity. Qed.

Lemma map_def_id {t} x : map_def (@id t) (@id t) x = id x.
Proof. now destruct x. Qed.
Hint Rewrite @map_def_id @map_id : map.

Lemma map_def_spec {A B} (P P' : A -> Type) (f f' g g' : A -> B) (x : def A) :
  P' x.(dbody) -> P x.(dtype) -> (forall x, P x -> f x = g x) ->
  (forall x, P' x -> f' x = g' x) ->
  map_def f f' x = map_def g g' x.
Proof.
  intros. destruct x. unfold map_def. simpl.
  now rewrite !H, !H0.
Qed.

Lemma case_brs_map_spec {A B} {P : A -> Type} {l} {f g : A -> B} :
  tCaseBrsProp P l -> (forall x, P x -> f x = g x) ->
  map (on_snd f) l = map (on_snd g) l.
Proof.
  intros. red in X.
  eapply All_map_eq. eapply All_impl; eauto. simpl; intros.
  apply on_snd_eq_spec; eauto.
Qed.

Lemma tfix_map_spec {A B} {P P' : A -> Type} {l} {f f' g g' : A -> B} :
  tFixProp P P' l -> (forall x, P x -> f x = g x) ->
  (forall x, P' x -> f' x = g' x) ->
  map (map_def f f') l = map (map_def g g') l.
Proof.
  intros.
  eapply All_map_eq. red in X. eapply All_impl; eauto. simpl.
  intros. destruct X0;
  eapply map_def_spec; eauto.
Qed.

Lemma case_brs_forallb_map_spec {A B} {P : A -> Type} {p : A -> bool}
      {l} {f g : A -> B} :
  tCaseBrsProp P l ->
  forallb (test_snd p) l ->
  (forall x, P x -> p x -> f x = g x) ->
  map (on_snd f) l = map (on_snd g) l.
Proof.
  intros.
  eapply All_map_eq. red in X. apply forallb_All in H.
  eapply All_impl. eapply All_prod. exact X. exact H.
  intros [] []; unfold on_snd; cbn. f_equal. now apply H0.
Qed.

Lemma tfix_forallb_map_spec {A B} {P P' : A -> Prop} {p p'} {l} {f f' g g' : A -> B} :
  tFixProp P P' l ->
  forallb (test_def p p') l ->
  (forall x, P x -> p x -> f x = g x) ->
  (forall x, P' x -> p' x -> f' x = g' x) ->
  map (map_def f f') l = map (map_def g g') l.
Proof.
  intros.
  eapply All_map_eq; red in X. apply forallb_All in H.
  eapply All_impl. eapply All_prod. exact X. exact H.
  intros [] [[] ?]; unfold map_def, test_def in *; cbn in *. rtoProp.
  f_equal; eauto.
Qed.

Ltac apply_spec :=
  match goal with
  | H : All _ _, H' : forallb _ _ = _ |- map _ _ = map _ _ =>
    eapply (All_forallb_map_spec H H')
  | H : All _ _, H' : forallb _ _ = _ |- forallb _ _ = _ =>
    eapply (All_forallb_forallb_spec H H')
  | H : tCaseBrsProp _ _, H' : forallb _ _ = _ |- map _ _ = map _ _ =>
    eapply (case_brs_forallb_map_spec H H')
  | H : All _ _, H' : is_true (forallb _ _) |- map _ _ = map _ _ =>
    eapply (All_forallb_map_spec H H')
  | H : All _ _, H' : is_true (forallb _ _) |- forallb _ _ = _ =>
    eapply (All_forallb_forallb_spec H H')
  | H : tCaseBrsProp _ _, H' : is_true (forallb _ _) |- map _ _ = map _ _ =>
    eapply (case_brs_forallb_map_spec H H')
  | H : tCaseBrsProp _ _ |- map _ _ = map _ _ =>
    eapply (case_brs_map_spec H)
  | H : tFixProp _ _ _, H' : forallb _ _ = _ |- map _ _ = map _ _ =>
    eapply (tfix_forallb_map_spec H H')
  | H : tFixProp _ _ _ |- map _ _ = map _ _ =>
    eapply (tfix_map_spec H)
  | H : All _ _ |- map _ _ = map _ _ =>
    eapply (All_map_eq H)
  | H : All _ _ |- map _ _ = _ =>
    eapply (All_map_id H)
  | H : All _ _ |- is_true (forallb _ _) =>
    eapply (All_forallb _ _ H); clear H
  end.

Ltac close_All :=
  match goal with
  | H : Forall _ _ |- Forall _ _ => apply (Forall_impl H); clear H; simpl
  | H : All _ _ |- All _ _ => apply (All_impl H); clear H; simpl
  | H : OnOne2 _ _ _ |- OnOne2 _ _ _ => apply (OnOne2_impl H); clear H; simpl
  | H : All2 _ _ _ |- All2 _ _ _ => apply (All2_impl H); clear H; simpl
  | H : Forall2 _ _ _ |- Forall2 _ _ _ => apply (Forall2_impl H); clear H; simpl
  | H : All _ _ |- All2 _ _ _ =>
    apply (All_All2 H); clear H; simpl
  | H : All2 _ _ _ |- All _ _ =>
    (apply (All2_All_left H) || apply (All2_All_right H)); clear H; simpl
  end.
End _BasicAst.

Module Native := _BasicAst(Ident.Native).
Module String := _BasicAst(Ident.String).

Module Type Sig (I : Ident.Sig).
    Include _BasicAst(I).
End Sig.