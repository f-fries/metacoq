
Require Import Array.PArray.
Require Import Bool.
Require Import MCInt63.
Require Import Byte.
Require String.

Local Definition char_array := array int.

Inductive nstring := mk_str (_ : char_array).

Declare Scope nstring_scope.
Delimit Scope nstring_scope with nstr.

Local Open Scope int63_scope.
Local Open Scope array_scope.

Local Definition nat_length (x : char_array) := i63_to_nat (length x).
    
(* Equality Decider *)
Local Fixpoint str_elemeq n (i : int) (a b : char_array) :=
    match n with
    | 0 => true
    | S n => eqb a.[i] b.[i] && str_elemeq n (i + 1) a b
    end.

Definition nstring_eqb '(mk_str a) '(mk_str b) := 
    eqb (length a) (length b) 
    && eqb (default a) (default b) 
    && str_elemeq (nat_length a) 0 a b.
Arguments nstring_eqb _%nstr _%nstr.

Axiom nstring_eqb_correct:
        forall a b, nstring_eqb a b = true <-> a = b.

Definition nstring_eqdec (x y : nstring) : {x = y} + {x <> y}.
Proof. destruct (nstring_eqb_correct x y) as [H1 H2]. destruct (nstring_eqb x y); auto.
    right. intros H3 % H2. congruence.
Defined.

(* Concatenation *)
Local Fixpoint copy_from (n : nat) (i k: int) (a b : char_array) :=
            match n with
            | 0 => b
            | S n => copy_from n (i + 1) (k + 1) a (b.[k <- a.[i]])
            end.


(* TODO: This is not super efficient, since the underlying array is filled with 0s *)
Definition nstr_concat '(mk_str a) '(mk_str b) :=
    let lenA := length a in
    let lenB := length b in
    let arr := make (lenA + lenB) 0 in
    let arr' := copy_from (i63_to_nat lenA) 0 0 a arr in
    mk_str (copy_from (i63_to_nat lenB) 0 lenA b arr').
Arguments nstr_concat _%nstr _%nstr.

Notation "a ++ b" := (nstr_concat a b) (right associativity, at level 60) : nstring_scope .

Definition slice '(mk_str A) k := 
    let sz := if length A <= k then length A - 1 else k in
    let B := PArray.make sz 0 in
    mk_str (copy_from (i63_to_nat sz) 0 0 A B).
Arguments slice _%nstr _%int63_scope.

Eval vm_compute in (mk_str [| 0; 1; 2; 3 | 0|] ++ mk_str [| 4; 5; 6 | 0 |])%nstr.
Eval vm_compute in slice (mk_str [| 0; 1; 2; 3; 4; 5  | 0 |]) 3.

(* Conversions from/to byte lists. This can/will be used to define string notations *)
Definition to_byte_list '(mk_str a) :=
    (fix go (n : nat) (i : int) (acc : list byte) :=
        match n with
        | 0 => acc
        | S n => go n (i - 1) (cons (i63_to_byte a.[i]) acc)
        end) (nat_length a) (length a - 1) nil.
Arguments to_byte_list _%nstr.

Local Fixpoint list_length_i63 {A} (xs : list A) := 
            match xs with
            | nil => 0
            | cons _ xs => 1 + list_length_i63 xs
            end.

Definition from_byte_list (xs : list byte) := 
    let arr := make (list_length_i63 xs) 0 in
    mk_str ((fix go i xs acc := 
        match xs with
        | nil => acc
        | cons x xs => go (i + 1) xs (acc.[i <- i63_from_byte x])
        end) 0 xs arr).

Eval vm_compute in from_byte_list (cons x01 (cons x02 (cons x03 nil))).

(* String Notation nstring from_byte_list to_byte_list : nstring_scope. *)

(* This can be used to quickly define nstrings while string notatiosn dont work *)
Record BoxedList := MkBoxedList { unBoxList : list byte}.

String Notation BoxedList MkBoxedList unBoxList : nstring_scope.
Definition make x :=  from_byte_list (unBoxList x).
Arguments make _%nstr.

Definition readable x := MkBoxedList (to_byte_list x).
Arguments make _%nstr.


(* Conversion to Ascii based string, this is used for compatibility *)
Definition nstring_to_string '(mk_str s) :=
    (fix go n i := 
        match n with 
        | 0 => String.EmptyString
        | S n => String.String (i63_to_ascii s.[i]) (go n (i + 1))
        end) (nat_length s) 0.
Arguments nstring_to_string _%nstr.


(* Conversions from nat and int *)
(* We have x <= 2^63 < 10^(max_pos + 1) *)
Local Definition max_pos : nat := 18.

Local Definition mk_digit x : int := x + 48.

Local Fixpoint highest_nonzero_pos (n : nat) (m x : int) : nat :=
    match n with
    | 0 => 0
    | S k => if m <= x then highest_nonzero_pos k (m * 10) x else S (max_pos - n)
    end.

Compute highest_nonzero_pos max_pos 10 0.
Compute highest_nonzero_pos max_pos 10 1444.

Definition i63_to_nstring x := 
    let len := highest_nonzero_pos max_pos 10 x in
    let arr := PArray.make (nat_to_i63 len) 0 in
    mk_str ((fix go n i x arr := 
        match n with
        | 0 => arr
        | S n => 
            let d := mk_digit (x \% 10) in 
            go n (i - 1) (x / 10) arr.[i <- d]
        end) len (length arr - 1) x arr).
Arguments i63_to_nstring _%int63_scope.

Definition nat_to_nstring n := i63_to_nstring (nat_to_i63 n).

Compute readable (i63_to_nstring 9876543).
