Require Import Qual.grade_sig.
From mathcomp Require Import ssreflect ssrbool ssrnat.
From Hammer Require Import Hammer.

Module grade_facts
  (Import grade : GradeSig).

  Local Open Scope grade_scope.

  Definition q_squash ψ ψ0 :=
    if ψ0 ≤ ψ then ⊥ else ψ0.

  Infix "⤓" := q_squash (at level 75).

  Definition q_eqb ψ ψ0 := (ψ ≤ ψ0) && (ψ0 ≤ ψ).
  Infix "=q?" := q_eqb (at level 80) : grade_scope.

  #[export] Hint Unfold q_eqb q_squash : core.

  Lemma q_eqbP : forall ψ ψ0, reflect (ψ = ψ0) (ψ =q? ψ0).
  Proof.
    move => ψ ψ0.
    case E : (ψ =q? ψ0).
    - hauto l:on use: q_leqb_antisym.
    - move : E.
      rewrite /q_eqb.
      case eq1 : (ψ ≤ ψ0);
        hauto l:on use:q_leqb_refl.
  Qed.

End grade_facts.

(* An opaque implementation of GradeSig with a two-point lattice *)
Module Export grade_impl : GradeSig.
  Variant rel_irrel := q_R | q_I.
  Definition grade := rel_irrel.
  Definition q_leqb ψ ψ0 :=
    match ψ, ψ0 with
    | q_I, q_R => false
    | _, _ => true
    end.

  Definition q_top := q_I.
  Definition q_bot := q_R.

  Lemma q_leqb_refl : reflexive q_leqb.
    hauto lq:on unfold:reflexive inv:rel_irrel.
  Qed.

  Lemma q_leqb_trans : transitive q_leqb.
    rewrite /transitive.
    repeat case => //.
  Qed.

  Lemma q_leqb_antisym  : antisymmetric q_leqb.
    rewrite /antisymmetric.
    repeat case => //.
  Qed.

  Lemma q_leqb_total : total q_leqb.
    rewrite /antisymmetric.
    repeat case => //.
  Qed.

  Lemma q_leqb_top : forall a, q_leqb a q_top.
    repeat case => //.
  Qed.

  Lemma bot_q_leqb : forall a, q_leqb q_bot a.
    repeat case => //.
  Qed.
End grade_impl.

Module Export grade_impl_facts := grade_facts grade_impl.
