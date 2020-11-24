

Add LoadPath "theories" as MetaCoq.Template.
From MetaCoq.Template Require Import All Core monad_utils utils.
From MetaCoq.Template Require Import Pretty.
Check nstring.
Import MonadNotation.
Require String.
Import String.StringSyntax.

Open Scope nstring_scope.
Declare ML Module "template_coq".

(* Test Basics quoting / unquoting*)

MetaCoq nident a := foobar.
Compute a. (* mk_str [| some_array |] *)
Compute (readable a). (* expected: "foobar" *)

Local Definition y := 0 + 1 * 2.
Local Definition quote_nstr := make "nstring"%nstr.
Print quote_nstr.

MetaCoq nident about quote_nstr. (* expected: nstring *)

(* TMonad Commands *)

Local Definition some_fn (x _ z : nat) := 0 + x + z.

(* Print *)
MetaCoq Run (tmPrint some_fn). (* Expected: some_fn *)

(* tmEval *)
Check tmEval.
MetaCoq Run (tmEval all (some_fn 0 0) >>= tmPrint). (* Expected: fun z : nat => z*)

Notation "$ x" := (make x) (at level 50).
Notation "? x" := (readable x) (at level 100).

(* tmLemma *)
MetaCoq Run (tmLemma ($ "t_lemma") Type).
Next Obligation. exact term. Defined.

(* tmDefinition *)
MetaCoq Run (tmDefinition ($ "aaaaaa_a_a_") (cons 42 nil)).
Compute aaaaaa_a_a_. (* expectec [42] *)

(* tmAxiom *)
MetaCoq Run (tmAxiom ($"hoder_Fact0") (True -> True)).
Print hoder_Fact0.


Section V.
   (* tmVariable *)
   MetaCoq Run (tmVariable ($"H") True) .
   Check H.
End V.

(* tmCurrentModPath *)
MetaCoq Run (tmCurrentModPath tt >>= tmPrint).

Print ConstRef.
Print inductive.
(* tmLocate *)
Definition get_kername ident := 
    r <- tmLocate ident ;;
    match r with
    | cons (IndRef mind) _ => tmReturn mind.(inductive_mind)
    | cons (ConstRef kn) _ => tmReturn kn
    | _ => tmFail "not found"
    end.

MetaCoq Run (
    get_kername ($ "nat") >>= tmDefinition ($ "nat_kername")
).
Print nat_kername.

(* tmQuoteInductive *)
MetaCoq Run (tmQuoteInductive nat_kername >>= tmPrint).

(* MetaCoq Run (tmQuoteUniverses >>= tmPrint). *)
MetaCoq Run (
    kn <- get_kername ($ "y" );;
    cst <- tmQuoteConstant kn true ;;
    tmPrint cst).

(* tmQuote(Rec) and associated Vernac Commands *)
MetaCoq Run (tmQuote (fun x : nat => (fun y t => 0%nat) Type) >>= tmPrint).

MetaCoq Test Quote get_kername.
MetaCoq Quote Definition q1 := Eval vm_compute in get_kername.
Print q1.
MetaCoq Quote Recursively Definition q3 := get_kername.
Print q3.

(* tmUnquote and associated Vernac Commands *)
MetaCoq Test Unquote q1.
    
MetaCoq Unquote Definition get_kername' := q1.
Print get_kername'.

MetaCoq Run (
    r <- tmUnquote q1 ;;
    tmPrint (my_projT1 r)
).

MetaCoq Run (
    t <- tmUnquoteTyped (qualid -> TemplateMonad (modpath × nstring)) q1;;
    tmPrint t
).

(* tmInferInstance *)
MetaCoq Run (
    t <- tmInferInstance None (Monad TemplateMonad);;
    match t with
    | my_Some i => tmPrint i
    | _ => tmFail "not instance"
    end
). (* expected output: TemplateMonad_Monad *)


