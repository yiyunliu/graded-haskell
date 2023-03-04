(* Parameterization of the grade total order *)

From mathcomp Require Import ssreflect ssrbool.
  
Module Type GradeSig.

Parameter grade : Set. 

Parameter q_top : grade.
Parameter q_bot : grade.

Notation "⊤" := q_top.
Notation "⊥" := q_bot.

Parameter q_leqb  : grade -> grade -> bool.

Infix "≤" := q_leqb (at level 70).

Axiom q_leqb_refl : reflexive q_leqb.

Axiom q_leqb_trans : transitive q_leqb.

Axiom q_leqb_antisym  : antisymmetric q_leqb.

Axiom q_leqb_total : total q_leqb.

Axiom q_leqb_top : forall a, a ≤ q_top.

Axiom bot_q_leqb : forall a, q_bot ≤ a.

End GradeSig.
