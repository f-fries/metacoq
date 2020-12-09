
Require Bool.

Definition transport {A} (P : A -> Type) {x y : A} (e : x = y) : P x -> P y
  := fun u => eq_rect x P u y e.

Notation "p # x" := (transport _ p x) (right associativity, at level 65).

(* to convert some eq_rects into transports *)
Lemma eq_rect_transport A x P u y p
  : @eq_rect A x P u y p = transport P p u.
Proof. reflexivity. Defined.

Definition eqdec A := forall (x y : A), {x = y} + {x <> y}.

Definition booldec_spec {A} (f : A -> A -> bool) := 
  forall x y, f x y = true <-> x = y.

Definition eqdec_bdec {A} (E : eqdec A) : {f | @booldec_spec A f}.
Proof.
  exists (fun x y => if E x y then true else false).
  intros x y. destruct (E x y); firstorder congruence.
Defined.

Definition bdec_eqdec {A} f (H : @booldec_spec A f) : eqdec A.
Proof.
  intros x y. destruct (f x y) eqn:E.
  - left. now apply H.
  - right. intros H2. destruct (H x y) as [_ H3]. specialize (H3 H2). congruence.
Defined.

Definition booldec_refl {A} f := forall (x y : A), Bool.reflect (x = y) (f x y).

Lemma bdec_refl_spec {A} f :
    @booldec_refl A f -> booldec_spec f.
Proof.
  intros H x y. specialize (H x y). enough (x = y <-> f x y = true) by tauto.
  now eapply Bool.reflect_iff. 
Qed.

Lemma bdec_spec_relf {A} f :
    @booldec_spec A f -> booldec_refl f.
Proof.
  intros H x y. specialize (H x y). assert (x = y <-> f x y = true) by tauto.
  now eapply Bool.iff_reflect.
Qed.

