
Require Import Array.PArray BinInt Bool.
Require Import Int63 Arith Lia.

Definition string := array int.

Definition mkString n := make n 0.
Arguments mkString n%int63_scope.

Local Open Scope int63_scope.
Local Open Scope array_scope.
Local Open Scope bool_scope.

Local Definition to_N x := Z.to_nat (Int63.to_Z x).
Local Definition of_N n := of_Z (Z.of_nat n).

Local Definition nat_length (x : string) := to_N (length x).
(*
Lemma of_to_N x:
    of_N (to_N x) = x.
Proof.
    unfold of_N, to_N. 
    assert (0 <= to_Z x)%Z by apply to_Z_bounded.
    rewrite (Znat.Z2Nat.id (to_Z x) H).
    apply of_to_Z.
Qed.

Lemma of_N_0 :
    of_N 0 = 0.
Proof.
    unfold of_N. rewrite Znat.Nat2Z.inj_0. rewrite <- of_to_Z. now rewrite to_Z_0.
Qed.

Open Scope int63_scope.

Ltac lift_Z H := 
    lazymatch type of H with
    | _ < _ = true => eapply ltb_spec in H
    | _ <= _ = true => eapply leb_spec in H
    | _ == _ = true => eapply eqb_correct in H
    end.


Definition Dec p:= {p} + {~p}.

Lemma int_greater0 x:
            ~ (x < 0 = true).
Proof.
    intros H. lift_Z H. rewrite to_Z_0 in H. assert (0 <= to_Z x)%Z by apply to_Z_bounded. lia.
Qed.

Lemma int_tricho x y (H: x <= y = true) : {x < y = true} + {x = y}.
Proof.
    lift_Z H. destruct (ZArith_dec.Z_lt_le_dec (to_Z x) (to_Z y)) as [H1 | H1].
    - left. now apply ltb_spec.
    - right. assert (to_Z x = to_Z y) by lia. now apply to_Z_inj.
Qed.

Lemma of_N_gt x n:
        x < of_N (S n) = true -> x <= of_N n = true.
Proof.
    intros H. lift_Z H. unfold of_N in H.
    rewrite (Znat.Nat2Z.inj_succ n) in H.
    rewrite to_of_Z.
    assert ((to_Z x <= Z.of_nat n)%Z) by lia.

Definition string_eqb_elem (a b : string) :
        forall n, Dec (forall i, i < of_N n = true -> a.[i] = b.[i]).
Proof.
    induction n as [|n [IH | IH]].
    - left. intros i H. exfalso. now apply (int_greater0 i).
    - pose (i := of_N n). destruct (eqb a.[i] b.[i]) eqn:H.
        + left. intros k L. change (of_N (S n)) with i in L. destruct (int_tricho k i L).

Definition string_eqb (a b : string) : bool.
Proof.
    refine ((length a == length b) && (default a == default b) && _ (nat_length a) 0).
    refine (fix f fuel i :=
        match fuel with
        | 0 => true
        | S fuel => eqb a.[i] b.[i] && f fuel (i + 1)
        end).
Defined.

Ltac destruct_andb H :=
    lazymatch type of H with
    | ?a && ?b = true =>
        let H1 := fresh in
        let H2 := fresh in
        eapply andb_true_iff in H; 
        destruct H as [H1 H2];
        destruct_andb H1;
        destruct_andb H2
    | _ => idtac
    end.


Lemma string_eq a b:
            string_eqb a b = true <-> a = b.
Proof.
    split; intros H.
    - apply array_ext; unfold string_eqb in H; destruct_andb H.
        1,3: now apply eqb_spec.

        clear H; clear H2. 
        enough (forall n, of_N n = length a -> 
            forall i, (i <? length a) = true -> a.[i] = b.[i])
        as HS . {  intros. apply (HS (nat_length a)). apply of_to_N. auto. }
        induction n as [|n IH]. 
        + intros E i L. rewrite of_N_0 in E. rewrite <- E in L. exfalso. eapply int_greater0. eassumption.
        + 
*)
    
    
Local Fixpoint str_elemeq n (i : int) (a b : string) :=
    match n with
    | 0 => true
    | S n => eqb a.[i] b.[i] && str_elemeq n (i + 1) a b
    end.

Definition string_eqb a b := 
    eqb (length a) (length b) 
    && eqb (default a) (default b) 
    && str_elemeq (nat_length a) 0 a b.
 
Axiom string_eqb_correct:
        forall a b, string_eqb a b = true <-> a = b.

Local Fixpoint copy_from (n : nat) (i k: int) (a b : string) :=
            match n with
            | 0 => b
            | S n => copy_from n (i + 1) (k + 1) a (b.[k <- a.[i]])
            end.

Definition concat a b :=
    let lenA := length a in
    let lenB := length b in
    let arr := make (lenA + lenB) 0 in
    let arr2 := copy_from (to_N lenA) 0 0 a arr in
    copy_from (to_N lenB) 0 lenA b arr.
        