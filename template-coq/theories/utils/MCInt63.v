
Require Import Wf_Z BinInt Int63 Arith Lia.

Open Scope int63_scope.
Delimit Scope int63_scope with i63.

Definition boundZ x := (0 <= x < wB)%Z.

Section Eliminators.

Local Open Scope Z_scope.
Variable p : int -> Type.

Local Definition q x := p (of_Z x).

Definition int63_rectZ (H0 : q 0) (IH : forall z, boundZ z -> q z -> q (Z.succ z)) : forall x, p x. 
Proof.
    enough (forall z, 0 <= z -> z < wB -> q z) as H.
        intros x.  destruct (to_Z_bounded x) as [H1 H2]. specialize (H (to_Z x) H1 H2). unfold q in H. now rewrite of_to_Z in H.
    Check natlike_ind. apply (natlike_rec2 (fun x => x < wB -> q x)).
    - auto.
    - intros z H1 H2 H3. apply IH. split. 3: apply H2. all: lia.
Defined.

Lemma of_Z0:
    of_Z 0 = 0%i63.
Proof.
    rewrite <- of_to_Z. now rewrite to_Z_0.
Qed.

End Eliminators.