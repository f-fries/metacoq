(* This file provides the previous interface to the plugin
*
* Previously:
*   From MetaCoq.Template Require Import A B C.
*
* Now:
*   From MetaCoq.Template Require Modules.
*   Import A B C.
*)

From MetaCoq.Template Require Import
    Ident
    BasicAst
    Universes
    uGraph
    Environment
    EnvironmentTyping
    Ast
    AstUtils
    Pretty
    utils
    monad_utils
    Pretty
    TemplateMonad
    LiftSubst
    UnivSubst
    Typing
    TypingWf.


(* For the stuff that's shared with PCUIC, export the versions that are used by the TemplateCoq *)
Module BasicAst := BasicAst.Native.
Module Universes := Universes.Native.
Module uGraph := uGraph.Native.
Module Environment := Environment.Native.
Module EnvironmentTyping := EnvironmentTyping.Native.

(* Reexport the other Module for convinience *)
Module Ast := Ast.
Module Astutils := AstUtils.
Module utils := utils.
Module monad_utils := monad_utils.
Module Pretty := Pretty.
Module TemplateMonad := TemplateMonad.
Module LiftSubst := LiftSubst.
Module UnivSubst := UnivSubst.
Module Typing := Typing.
Module TypingWf := TypingWf.


Module All.
Export
    Ident
    BasicAst
    Universes
    uGraph
    Environment
    EnvironmentTyping
    Ast
    AstUtils
    Pretty
    utils
    monad_utils
    Pretty
    TemplateMonad
    LiftSubst
    UnivSubst
    Typing.
End All.


    


    



    

    
