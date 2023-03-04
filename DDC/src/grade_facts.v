Require Import Qual.grade_sig.
From mathcomp Require Import ssreflect ssrbool ssrnat.
From Hammer Require Import Hammer.

Module grade_facts
  (Import grade : GradeSig).

  Definition q_squash ψ ψ0 :=
    if ψ0 ≤ ψ then ⊥ else ψ0.

  Infix "⤓" := q_squash (at level 75).

  Definition q_eqb ψ ψ0 := (ψ ≤ ψ0) && (ψ0 ≤ ψ).
  Infix "=?" := q_eqb (at level 80).

  #[export] Hint Unfold q_eqb q_squash : core.

  Lemma q_eqbP : forall ψ ψ0, reflect (ψ = ψ0) (ψ =? ψ0).
  Proof.
    move => ψ ψ0.
    case E : (ψ =? ψ0).
    - hauto l:on use: q_leqb_antisym.
    - move : E.
      rewrite /q_eqb.
      case eq1 : (ψ ≤ ψ0);
        hauto l:on use:q_leqb_refl.
  Qed.

End grade_facts.
