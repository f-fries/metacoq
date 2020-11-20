
Pwd.
Add LoadPath "theories" as MetaCoq.Template.
From MetaCoq.Template Require Import All.
Check nstring.

Open Scope nstring_scope.
Declare ML Module "template_coq".

MetaCoq nident a := foobar.
Let test := Eval vm_compute in (MkBoxedList (to_byte_list a)).

Print test.
Local Definition y := 0 + 1 * 2.

Local Definition x := make "nstring"%nstr.
Print x.

MetaCoq nident about x.