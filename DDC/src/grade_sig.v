(* Parameterization of the grade lattice *)

Require Import Metalib.Metatheory.

Require Import Coq.Structures.Orders.
Require Import Coq.Bool.Sumbool.
Require Import Coq.Program.Equality.
Require Import ssreflect.
From Equations Require Import Equations.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".




Module Type GradeSig.

Parameter grade : Set. 

Parameter q_Top : grade.
Parameter q_Bot : grade.
Parameter q_C   : grade.

Parameter q_R   : grade.

Parameter q_eqb  : grade -> grade -> bool.
Parameter q_leb  : grade -> grade -> bool.
Parameter q_join : grade -> grade -> grade.
Parameter q_meet : grade -> grade -> grade. 

Parameter q_eq   : grade -> grade.

(* Equality *)
Definition t := grade.
Definition eq := @Logic.eq grade.
Definition eqb  := q_eqb.
Parameter q_eq_dec : forall (A : grade) (B : grade), { A = B } + { not (A = B) }.
Instance equ  : @EqDec_eq grade := q_eq_dec. 
Parameter eqb_eq : forall (n m : grade), q_eqb n m = true <-> n = m.
Definition eq_equiv : Equivalence (@Logic.eq grade) := eq_equivalence.
Definition eq_dec := q_eq_dec.
Include BackportEq.

(* Order *)
Definition leb  := q_leb.
Definition le n m := is_true (q_leb n m).
Definition q_lt n m := is_true (q_leb n m) /\ n <> m. 

(* Size *)
Definition size_grade : grade -> nat := fun _ => 1%nat.
Lemma size_grade_min : forall q1, (1 <= size_grade q1). intros. unfold size_grade. auto. Qed.

(* Notation *)
Declare Scope grade_scope.
Bind Scope grade_scope with grade.
Local Open Scope grade_scope.

Infix "=?" := q_eqb (at level 70) : grade_scope.
Infix "<=?" := q_leb (at level 70) : grade_scope.
Notation "q1 <= q2" := (is_true (q_leb q1 q2)) (at level 70)  : grade_scope.
Notation "q1 < q2" := (q_lt q1 q2) (at level 70)  : grade_scope.
Notation "x * y"  := (q_join x y) : grade_scope.  
Notation "x + y " := (q_meet x y)  : grade_scope.

(* join and meet are commutative and associative *)
Axiom join_assoc : forall a b c, a * (b * c) = (a * b) * c.
Axiom join_comm  : forall a b, a * b = b * a.
Axiom meet_assoc : forall a b c, a + (b + c) = (a + b) + c.
Axiom meet_comm : forall a b, a + b = b + a.

(* absorption laws *)
Axiom absorb_meet : forall a b, a * (a + b) = a.
Axiom absorb_join : forall a b, a + (a * b) = a.

(* join and meet are idempotent *)
Axiom join_idem : forall a, a * a = a.
Axiom meet_idem : forall psi, psi + psi = psi.

(* bounded *)
Axiom join_Top_r : forall a, a * q_Top = q_Top.
Axiom meet_Bot_r : forall a, a + q_Bot = q_Bot.

(* Everything is either below or above C, and you can tell which *)
Axiom order_q_C_dec : forall q, { q <= q_C } + { q_C < q }.

(* Pre order *)
Axiom leb_leq  : forall (n m : grade), (n <=? m) = true <-> n <= m.

Axiom join_leq : forall a b,  a <= b -> (a * b) = b.
Axiom leq_join : forall a b, (a * b) = b -> a <= b.

Axiom meet_leq : forall a b,  a <= b -> (a + b) = a.
Axiom leq_meet : forall a b, (a + b) = a -> a <= b.

Lemma q_leb_refl : forall n, is_true (n <=? n).
Proof. intro n. apply leq_join. rewrite join_idem. auto. Qed.

Lemma q_leb_trans: forall m n p, is_true (n <=? m) -> is_true (m <=? p) -> is_true (n <=? p).
Proof. intros. apply leq_join. apply join_leq in H. apply join_leq in H0. rewrite <- H0.
rewrite join_assoc. rewrite -> H. auto. Qed.

Instance le_preorder : PreOrder le.
Proof. split. intro x. apply q_leb_refl. unfold Transitive. intros. eapply q_leb_trans; eauto. Qed.


End GradeSig.

Declare Module Grade : GradeSig.
Export Grade.

Hint Rewrite join_assoc join_Top_r join_idem : grade. 

Section GradeFacts.

(* Properties about the lattice used in the development. *)

Local Open Scope grade_scope.

Lemma q_leb_antisym : forall a b, a <= b -> b <= a -> a = b.
Proof. intros. apply join_leq in H. apply join_leq in H0. rewrite join_comm in H0.
rewrite <- H. symmetry. auto. Qed.

Lemma leq_Top : forall a, a <= q_Top. 
Proof. intros. apply leq_join. rewrite join_Top_r. auto. Qed.

Lemma leq_Bot : forall a, q_Bot <= a. 
Proof. intros. apply leq_meet. rewrite meet_comm. rewrite meet_Bot_r. auto. Qed.

Lemma leq_join_l : forall a b, a <= a * b.
Proof. intros. apply leq_join. rewrite join_assoc. rewrite join_idem. auto. Qed.

Lemma leq_join_r : forall a b, b <= a * b.
Proof. intros. apply leq_join. rewrite join_comm. rewrite <- join_assoc. rewrite join_idem. auto. Qed.

Lemma join_Top_l : forall a, q_Top * a = q_Top. 
Proof. intros. rewrite join_comm. apply join_Top_r. Qed.

Lemma join_idem_l : forall (a b:grade), a * (a * b) = a * b.
Proof. intros. rewrite join_assoc. rewrite join_idem. auto. Qed.

Hint Rewrite join_idem_l join_Top_l : grade.

Lemma po_join_l : forall a b c , a <= b -> a * c <= b * c.
Proof. intros. apply leq_join. apply join_leq in H.
rewrite join_assoc.
replace (a * c * b * c) with (a * (c * b) * c). 2: autorewrite with grade; auto.
rewrite (join_comm c). autorewrite with grade.
rewrite <- join_assoc. rewrite join_idem.
rewrite H. auto. Qed.

Lemma po_join_r : forall a b c , a <= b -> c * a <= c * b.
Proof. 
  intros. apply leq_join. apply join_leq in H.
  rewrite (join_comm c a). rewrite join_assoc.
  replace (a * c * c * b) with (a * (c * c) * b). rewrite join_idem.
  rewrite <- join_assoc. rewrite (join_comm c b). rewrite join_assoc.
  rewrite H. auto. 
  rewrite join_assoc. auto.
Qed.

Lemma join_lub : forall a b c, 
    a <= c -> b <= c -> a * b <= c.
Proof. 
  intros. apply leq_join. apply join_leq in H. apply join_leq in H0.
  rewrite <- join_assoc. rewrite H0. auto. Qed.

From Hammer Require Import Hammer Tactics.

Lemma lub_join : forall a b c,
    a * b <= c -> a <= c /\ b <= c.
Proof.
  sfirstorder use: q_leb_trans, leq_join_l, leq_join_r.
Qed.

Lemma join_lub_iff : forall a b c,
    a <= c /\ b <= c <-> a * b <= c.
Proof.
  strivial use: lub_join, join_lub.
Qed.

Lemma meet_glb : forall a b c,
    a <= b -> a <= c -> a <= b + c.
Proof.
  hauto lq: on drew: off use: leq_meet, meet_assoc, meet_leq.
Qed.

Lemma glb_meet : forall a b c,
    a <= b + c -> a <= b /\ a <= c.
Proof.
  hauto drew: off use: meet_comm, meet_assoc, meet_idem, meet_leq, leq_meet.
Qed.

Lemma meet_glb_iff : forall a b c,
    a <= b /\ a <= c <-> a <= b + c.
Proof.
  sfirstorder use: glb_meet, meet_glb.
Qed.

Lemma leq_meet_l : forall a b, a + b <= a.
Proof.
  qauto use: absorb_meet, leq_join, join_comm.
Qed.

Lemma leq_meet_r : forall a b, a + b <= b.
Proof.
  scongruence use: leq_meet_l, meet_comm.
Qed.

Lemma po_meet_l : forall a b c , a <= b -> a + c <= b + c.
Proof.
  hauto use: leq_meet_l, q_leb_trans, meet_glb, leq_meet_r.
Qed.

Lemma po_meet_r : forall a b c , a <= b -> c + a <= c + b.
Proof.
  hauto use: meet_comm, po_meet_l.
Qed.

Lemma still_higher : forall a b c,
  c < a -> b <= c -> c < a * b.
Proof.
  qauto use: join_comm, po_join_r, join_leq, q_leb_trans unfold: q_lt.
Qed.

Lemma meet_mult : forall {a b}, 
      a <= q_C -> 
      q_C + (b * a) = (q_C + b) * a.
Proof.
  intros.
  destruct (order_q_C_dec b).
  + move: (meet_leq _ _ i) => h1. rewrite meet_comm in h1. rewrite h1.
    have LT: (a * b <= q_C). apply join_lub; auto.
    rewrite meet_comm. 
    move: (meet_leq _ _ LT) => h2. rewrite join_comm in h2. rewrite h2.
    rewrite join_comm. auto.
  + inversion q. clear q. clear H1.
    move: (meet_leq _ _ H0) => h1. rewrite h1.
    have LT: (q_C <= a * b).
    transitivity (a * q_C). eapply leq_join_r. eapply po_join_r. auto.
    apply meet_leq in LT. rewrite join_comm in LT. rewrite LT.
    apply join_leq in H. rewrite <- H at 1. rewrite join_comm. auto.
Qed.

Lemma lt_not_leq : forall {psi psi0},
 psi < psi0 -> ~ psi0 <= psi.
Proof.
  intros psi psi0 H. inversion H. move=>h. apply H1. eapply q_leb_antisym; auto. Qed.

Lemma not_leq_lower : forall {psi psi0 phi},
    psi <= phi -> ~ psi0 <= phi -> ~ psi0 <= psi.
Proof.
  intros. move=> h. apply H0. transitivity psi; auto. 
Qed.

Lemma top_leq_eq : forall a,
    q_Top <= a -> a = q_Top.
Proof.
  sfirstorder use: join_Top_l, join_leq.
Qed.

Lemma leq_meet_prime (e1 e2 e3 : grade) :
  e1 <= e3 \/ e2 <= e3 -> (e1 + e2) <= e3.
Proof.
  qauto use: meet_assoc, meet_comm, absorb_join, leq_meet, meet_leq, join_leq.
Qed.

Lemma leq_join_prime (e1 e2 e3 : grade) :
  e1 <= e2 \/ e1 <= e3 -> e1 <= (e2 * e3).
Proof.
  intros.
  hecrush l:on use: join_assoc, leq_join, join_leq, join_comm.
Qed.

End GradeFacts.



Inductive lexp : Set :=
| Var : grade -> lexp
(* | Q_C : lexp *)
| Q_Top : lexp
| Meet : lexp -> lexp -> lexp
| Join : lexp -> lexp -> lexp.

Fixpoint denoteLexp (e : lexp) : grade :=
  match e with
  | Var a => a
  | Meet e1 e2 => denoteLexp e1 + denoteLexp e2
  | Join e1 e2 => denoteLexp e1 * denoteLexp e2
  | Q_Top => q_Top
  (* | Q_C => q_C *)
  end.

Fixpoint lexp_size (e : lexp) :=
  match e with
  | Var _ => 0
  (* | Q_C => 0 *)
  | Q_Top => 0
  | Meet e1 e2 => 1 + lexp_size e1 + lexp_size e2
  | Join e1 e2 => 1 + lexp_size e1 + lexp_size e2
  end.

Local Open Scope grade_scope.

#[tactic="sfirstorder"] Equations splitLeq (e1 : lexp) (e2 : lexp) : Prop
  by wf ((lexp_size e1 + lexp_size e2)%nat) lt :=
  splitLeq _ Q_Top =>  True;
  splitLeq Q_Top e => q_Top = denoteLexp e;
  splitLeq (Var a1) (Var a2) => a1 <= a2;
  splitLeq (Join e11 e12) e2 => splitLeq e11 e2 /\ splitLeq e12 e2;
  splitLeq e1 (Meet e21 e22) => splitLeq e1 e21 /\ splitLeq e1 e22;
  splitLeq e1 (Join e21 e22) => splitLeq e1 e21 \/ splitLeq e1 e22 \/ (denoteLexp e1) <= (denoteLexp (Join e21 e22)) ;
  splitLeq (Meet e11 e12) e2 => splitLeq e11 e2 \/ splitLeq e12 e2 \/ (denoteLexp (Meet e11 e12)) <= (denoteLexp e2).

#[tactic="sfirstorder"] Equations splitLeqForward (e1 : lexp) (e2 : lexp) : Prop
  by wf ((lexp_size e1 + lexp_size e2)%nat) lt :=
  splitLeqForward _ Q_Top =>  True;
  splitLeqForward Q_Top e => q_Top = denoteLexp e;
  splitLeqForward (Var a1) (Var a2) => a1 <= a2;
  splitLeqForward (Join e11 e12) e2 => splitLeqForward e11 e2 /\ splitLeqForward e12 e2;
  splitLeqForward e1 (Meet e21 e22) => splitLeqForward e1 e21 /\ splitLeqForward e1 e22;
  splitLeqForward e1 e2 => denoteLexp e1 <= denoteLexp e2.


#[export] Hint Rewrite <- join_lub_iff meet_glb_iff : lat_2.
#[export] Hint Resolve leq_join_prime leq_meet_prime : lat_db.

(* Transforming goal *)
Theorem splitLeq_sound (e1 e2 : lexp) :
  splitLeq e1 e2 ->  (denoteLexp e1) <= (denoteLexp e2).
Proof.
  intros.
  Check splitLeq_graph_correct.
  have h0 := splitLeq_graph_correct e1 e2.
  remember (splitLeq e1 e2) as p.
  induction h0 using splitLeq_graph_rect;
    sauto use: leq_meet_prime, leq_join_prime, join_lub_iff, meet_glb_iff, leq_Top, top_leq_eq.
 Qed.

Theorem splitLeq_complete (e1 e2 : lexp) :
  (denoteLexp e1) <= (denoteLexp e2) -> splitLeq e1 e2.
Proof.
  intros.
  have h0 := splitLeq_graph_correct e1 e2.
  remember (splitLeq e1 e2) as p.
  induction h0 using splitLeq_graph_rect;
    sauto use: leq_meet_prime, leq_join_prime, join_lub_iff, meet_glb_iff, leq_Top, top_leq_eq.
Qed.

Theorem splitLeqForward_complete  (e1 e2 : lexp) :
   (denoteLexp e1) <= (denoteLexp e2) -> splitLeqForward e1 e2.
Proof.
  move => H0.
  have h0 := splitLeqForward_graph_correct e1 e2.
  remember (splitLeqForward e1 e2) as p.
  induction h0 using splitLeqForward_graph_rect;
    sauto lq: on use: leq_meet_prime, leq_join_prime, join_lub_iff, meet_glb_iff, leq_Top, top_leq_eq.
Qed.

Ltac2 rec reify_lexp (e : constr) :=
  lazy_match! e with
  | ?a1 + ?a2 =>
    let e1 := reify_lexp a1 in
    let e2 := reify_lexp a2 in
    '(Meet $e1 $e2)
  | ?a1 * ?a2 =>
    let e1 := reify_lexp a1 in
    let e2 := reify_lexp a2 in
    '(Join $e1 $e2)
  | q_Top =>
    'q_Top
  | ?e => '(Var $e)
  end.

Ltac2 simplify_lattice_hyp (id : ident) (ty : constr) : unit :=
  simpl in $id;
  lazy_match! ty with
  | ?a1 <= ?a2 =>
      let e1 := reify_lexp a1 in
      let e2 := reify_lexp a2 in
      apply (splitLeqForward_complete $e1 $e2) in $id;
      ltac1:(h1 |- simp splitLeqForward in h1) (Ltac1.of_ident id);
      simpl in $id
  (* TODO: keep the equalities about lattices *)
  | _ => clear id
  end.

Ltac2 simplify_lattice_hyps () : unit :=
  (* iterate through the list of hypotheses *)
  List.iter
    (fun (id, _, ty) =>
       simplify_lattice_hyp id ty)
    (Control.hyps ()).

Ltac2 simplify_lattice_goal () : unit :=
  simpl; intros;
  lazy_match! goal with
  | [|- ?a1 <= ?a2] =>
    let e1 := reify_lexp a1 in
    let e2 := reify_lexp a2 in
    apply (splitLeq_sound $e1 $e2); ltac1:(simp splitLeq)
  | [|- _] =>
      ltac1:(exfalso)
  end.

(* TODO: parameterize solve_lattice by a base case tactic for handling the leaves? *)
Ltac2 solve_lattice () :=
  solve [
  simplify_lattice_goal ();
  simplify_lattice_hyps ();
  ltac1:(eauto using q_leb_refl, q_leb_trans, q_leb_antisym)].

Ltac2 Notation "solve_lattice" := solve_lattice ().

Ltac solve_lattice := ltac2:(solve_lattice).
