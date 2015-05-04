Require Import Lib.

Module HeytingTerms.

  (*************************************************)
  (* Identifiers *)

  (* Identifiers are indexed by natural numbers *)
  Definition X := nat.

  (* Decidability of identifier equality; this is identical to a similar theorem
   * for nats in Coq's standard library. *)
  Theorem eq_id_dec : forall x y : X, {x = y} + {x <> y}.
  Proof.
    intros x. induction x as [|x'].
    Case "x = 0". destruct y as [|y'].
    SCase "y = 0". left. reflexivity.
    SCase "y > 0". right. intros c. inversion c.
    Case "x > 0". intros y. destruct y as [|y'].
    SCase "y = 0". right. intros c. inversion c.
    SCase "y > 0". destruct IHx' with (y := y') as [eq|neq].
    SSCase "x' = y'". subst. left. reflexivity.
    SSCase "x' <> y'". right. unfold not in neq. intros c. inversion c.
      apply neq. apply H0.
  Defined.

  (*************************************************)
  (* Terms *)

  (* Terms may be nats, variables, +, *, and successor. Note that Kanckos
   * defines successor for both numerals and terms; this is important because
   * it's used to find inconsistencies (∀t, Suc t ⊃ 0 ⇒ ⊥).  *)
  Inductive T: Set :=
  | Nat: nat -> T
  | Var: X -> T
  | Plus: T -> T -> T
  | Mult: T -> T -> T
  | Suc : T -> T.  (* note that Kanckos defines succ for both nats and terms *)

  Notation "t1 + t2"  := (Plus t1 t2)
                           (at level 50, left associativity) : hterm_scope.
  Notation "t1 * t2"  := (Mult t1 t2)
                           (at level 40, left associativity) : hterm_scope.

  Bind Scope hterm_scope with T.  (* this doesn't help too much *)
  Delimit Scope hterm_scope with hterm. (* needed when a term isn't a fn arg *)

  (*************************************************)
  (* Decidability of term equality. Note that this is syntactic equality:
   * Nat O + Nat O is not the same as Nat O. *)

  Tactic Notation "hterm_cases" tactic(first) ident(c) :=
    first;
    [Case_aux c "Nat" | Case_aux c "Var" | Case_aux c "Plus"
     | Case_aux c "Mult" | Case_aux c "Suc"].

  Tactic Notation "wrong_shape" :=
    solve [right; intros contra; inversion contra].
  Tactic Notation "dest_ind" ident(hyp) ident(hypvar) ident(cvar) ident(c):=
    destruct hyp with (hypvar:=cvar) as [eq|neq];
    [Case_aux c "eq" | Case_aux c "neq"].
  Tactic Notation "eq_case" :=
    solve [left; inversion eq; subst; reflexivity].

  (* Proof that term equality is decidable. *)
  Open Scope hterm_scope.
  Theorem term_eq_dec : forall (t1 t2: T), {t1 = t2} + {t1 <> t2}.
  Proof.
    intros t1.
    hterm_cases (induction t1 as [n1|x1|r Hr r' Hr'|r Hr r' Hr'|t1])
                Case;
      intros t2;
      hterm_cases (destruct t2 as [n2|x2|s s'|s s'|t2]) SCase;
      try wrong_shape.
    Case "Nat".
    SCase "Nat". generalize dependent n2.
      induction n1 as [|n1']; destruct n2 as [|n2'];
        try wrong_shape; try (left; reflexivity).
      dest_ind IHn1' n2 n2' SSCase; try eq_case.
      SSCase "neq". right. unfold not in neq. intros c. inversion c.
        apply neq. apply f_equal. apply H0.
    Case "Var".
    SCase "Var". generalize dependent x2.
      induction x1 as [|x1']; destruct x2 as [|x2'];
      try wrong_shape; try (left; reflexivity).
      dest_ind IHx1' x2 x2' SSCase; try eq_case.
      SSCase "neq". right. unfold not in neq. intros c. inversion c. apply neq.
        subst. reflexivity.
    Case "Plus".
    destruct Hr with (t2:=s) as [eq|neq];
      destruct Hr' with (t2:=s') as [eq'|neq']; subst.
    SSCase "both equal". left. reflexivity.
    SSCase "r' <> s'". right. intros contra. unfold not in neq'. apply neq'.
    inversion contra. reflexivity.
    SSCase "r <> s". right. intros contra. unfold not in neq. apply neq.
    inversion contra. reflexivity.
    SSCase "r' <> s', r <> s".
    (* Note: this is syntactic equality, not equality of the evaluated term. *)
    right. intros contra. inversion contra. unfold not in neq.
    apply neq. apply H0.
    Case "Mult".
    destruct Hr with (t2:=s) as [eq|neq];
      destruct Hr' with (t2:=s') as [eq'|neq']; subst.
    SSCase "both equal". left. reflexivity.
    SSCase "r' <> s'". right. intros contra. unfold not in neq'. apply neq'.
    inversion contra. reflexivity.
    SSCase "r <> s". right. intros contra. unfold not in neq. apply neq.
    inversion contra. reflexivity.
    SSCase "r' <> s', r <> s".
    (* Note: this is syntactic equality, not equality of the evaluated term. *)
    right. intros contra. inversion contra. unfold not in neq.
    apply neq. apply H0.
    Case "Suc". destruct IHt1 with (t2 := t2).
    SSCase "eq". left. subst. reflexivity.
    SSCase "neq". right. intros c. inversion c. apply n. apply H0.
  Defined.

  (* Substitution: var <-> term *)
  Fixpoint subst_t (x : X) (value : T) (term : T) : T :=
    match term with
      | Nat _ => term
      | Var y => if eq_id_dec x y then value else term
      | Plus t1 t2 => Plus (subst_t x value t1) (subst_t x value t2)
      | Mult t1 t2 => Mult (subst_t x value t1) (subst_t x value t2)
      | Suc t => Suc (subst_t x value t)
    end.

  Fixpoint abstract_t (value : T) (x : X) (term : T) : T :=
    if (term_eq_dec value term) then (Var x) else
      match term with
        | Plus t1 t2 => Plus (abstract_t value x t1) (abstract_t value x t2)
        | Mult t1 t2 => Mult (abstract_t value x t1) (abstract_t value x t2)
        | Suc t => Suc (abstract_t value x t)
        | _ => term
      end.

  (*************************************************)

  (* Arithmetic Equality *)
  Open Scope hterm_scope.

  (* Equality rules from Kanckos page 3, except for Inf1, defined below. *)
  Inductive eqha : T -> T -> Set :=
  | t_refl    : forall t, eqha t t
  | t_symm    : forall t1 t2, eqha t1 t2 -> eqha t2 t1
  | t_trans   : forall t1 t2 t3, eqha t1 t2 -> eqha t2 t3 -> eqha t1 t3
  | t_plus_id : forall t, eqha (t + Nat O) t
  | t_plus_rec: forall t1 t2, eqha (t1 + Suc(t2)) (Suc(t1 + t2))
  | t_mult_0  : forall t, eqha (t * Nat O) (Nat O)
  | t_mult_rec: forall t1 t2, eqha (t1 * Suc(t2)) (t1 + (t1 * t2))
  | t_rep_s   : forall t1 t2, eqha t1 t2 -> eqha (Suc t1) (Suc t2)
  | t_rep_plus_l : forall t1 t2 t3, eqha t1 t2 -> eqha (t1 + t3) (t2 + t3)
  | t_rep_plus_r : forall t1 t2 t3, eqha t2 t3 -> eqha (t1 + t2) (t1 + t3)
  | t_rep_mult_l : forall t1 t2 t3, eqha t1 t2 -> eqha (t1 * t3) (t2 * t3)
  | t_rep_mult_r : forall t1 t2 t3, eqha t2 t3 -> eqha (t1 * t2) (t1 * t3)
  | t_inf2    : forall t1 t2, eqha (Suc t1) (Suc t2) -> eqha t1 t2
  | t_suc     : forall n, eqha (Nat (S n)) (Suc (Nat n)).

  (* Kanckos also includes a proof of falsity, if Suc t = 0. This will be
   * included in the later definition of formulas Φ. *)

  Definition n0 := Nat O.
  Definition n1 := Suc n0.
  Definition n2 := Suc n1.
  Definition v0 := Var 0.
  Definition v1 := Var 1.
  Definition v2 := Var 2.

  (* Some example arithmetic derivations. *)
  Fact haf1 : eqha (n0 + n0) (n1 * n0).
  Proof.
    apply t_trans with (t2 := n0).
    apply t_plus_id.
    apply t_symm. apply t_mult_0.
  Defined.
  Print haf1.

  Lemma plus_id_r : forall t : T, eqha t (t + n0).
  Proof.
    intros t. apply t_symm. apply t_plus_id.
  Qed.
  Print plus_id_r.

  Lemma mult1 : forall t:T, eqha (t*n1) t.
  Proof.
    intros t. unfold n1. apply t_trans with (t2:=t+(t*n0)).
    apply t_mult_rec. apply t_trans with (t2:=t+n0).
    apply t_rep_plus_r. apply t_mult_0.
    apply t_plus_id.
  Qed.
  Print mult1.

End HeytingTerms.

Module HeytingProps.

  Export HeytingTerms.
  Require Export List.


  (* Formulas and Atomic Propositions *)
  (* For the Kanckos paper, basic connectives are ∨, ∧, ⊃ (aka ⇒), ∃, ∀.
     Negation is derived as ¬A ≡ A ⊃ ⊥. *)
  Inductive Φ: Set :=
  | bot  : Φ
  | teq  : T -> T -> Φ
  | Disj : Φ -> Φ -> Φ
  | Conj : Φ -> Φ -> Φ
  | Imp  : Φ -> Φ -> Φ
  | Ex   : X -> Φ -> Φ
  | All  : X -> Φ -> Φ.

  Notation "⊥" := bot.

  Definition Neg (φ:Φ) := Imp φ bot.

  Tactic Notation "formula_cases" tactic(first) ident(c) :=
    first;
    [Case_aux c "bot" | Case_aux c "teq" | Case_aux c "disj" | Case_aux c "conj"
     | Case_aux c "imp" | Case_aux c "ex" | Case_aux c "all"].


  Fixpoint subst_φ (x : X) (t : T) (φ : Φ) : Φ :=
    match φ with
      | bot        => bot
      | teq t1 t2  => teq  (subst_t x t t1) (subst_t x t t2)
      | Disj φ1 φ2 => Disj (subst_φ x t φ1) (subst_φ x t φ2)
      | Conj φ1 φ2 => Conj (subst_φ x t φ1) (subst_φ x t φ2)
      | Imp φ1 φ2  => Imp  (subst_φ x t φ1) (subst_φ x t φ2)
      | Ex x' φ'   => if eq_id_dec x x' then φ else Ex  x' (subst_φ x t φ')
      | All x' φ'  => if eq_id_dec x x' then φ else All x' (subst_φ x t φ')
    end.

  Fixpoint abstract_φ (t : T) (x : X) (φ : Φ) : Φ :=
    match φ with
      | bot        => bot
      | teq t1 t2  => teq  (abstract_t t x t1) (abstract_t t x t2)
      | Disj φ1 φ2 => Disj (abstract_φ t x φ1) (abstract_φ t x φ2)
      | Conj φ1 φ2 => Conj (abstract_φ t x φ1) (abstract_φ t x φ2)
      | Imp φ1 φ2  => Imp  (abstract_φ t x φ1) (abstract_φ t x φ2)
      | Ex x' φ'   => if eq_id_dec x x' then φ else Ex  x' (abstract_φ t x φ')
      | All x' φ'  => if eq_id_dec x x' then φ else All x' (abstract_φ t x φ')
    end.

  Inductive unbound : Φ -> X -> Prop :=
  | ub_bot  : forall x', unbound bot x'
  | ub_teq  : forall t1 t2 x', unbound (teq t1 t2) x'
  | ub_disj : forall φ1 φ2 x',
                unbound φ1 x' -> unbound φ2 x' -> unbound (Disj φ1 φ2) x'
  | ub_conj : forall φ1 φ2 x',
                unbound φ1 x' -> unbound φ2 x' -> unbound (Conj φ1 φ2) x'
  | ub_imp  : forall φ1 φ2 x',
                unbound φ1 x' -> unbound φ2 x' -> unbound (Imp φ1 φ2) x'
  | ub_ex   : forall φ x x',
                x <> x' -> unbound φ x -> unbound (Ex x' φ) x
  | ub_all  : forall φ x x',
                x <> x' -> unbound φ x -> unbound (All x' φ) x.


  (* Logical Rules and Derivations *)
  (* structure for derivation trees *)
  Inductive proves: Φ -> Set :=
  | p_bot   : forall φ, proves bot -> proves φ
  | p_andi  : forall φ1 φ2, proves φ1 -> proves φ2 -> proves (Conj φ1 φ2)
  | p_ander : forall φ1 φ2, proves (Conj φ1 φ2) -> proves φ1
  | p_andel : forall φ1 φ2, proves (Conj φ1 φ2) -> proves φ2
  | p_oril  : forall φ1 φ2, proves φ1 -> proves (Disj φ1 φ2)
  | p_orir  : forall φ1 φ2, proves φ2 -> proves (Disj φ1 φ2)
  | p_ore   : forall φ1 φ2 φ3, proves (Disj φ1 φ2) -> proves_mstep φ1 φ3
                               -> proves_mstep φ2 φ3 -> proves φ3
  | p_impi  : forall φ1 φ2, proves_mstep φ1 φ2 -> proves (Imp φ1 φ2)
  | p_impe  : forall φ1 φ2, proves (Imp φ1 φ2) -> proves φ1 -> proves φ2
  | p_alli  : forall φ x, proves φ -> unbound φ x -> proves (All x φ)
  | p_alle  : forall φ x t, proves (All x φ) -> proves (subst_φ x t φ)
  | p_exi   : forall φ x t, proves φ -> proves (Ex x (abstract_φ t x φ))
  | p_exe   : forall φ1 x t φ2, proves (Ex x φ1)
                                -> proves_mstep (subst_φ x t φ1) φ2
                                -> proves φ2
  | p_arith : forall t1 t2, eqha t1 t2 -> proves (teq t1 t2)
  | p_ind   : forall φ x t, proves (subst_φ x (Nat O) φ)
                            -> proves_mstep φ (subst_φ x (Suc (Var x)) φ)
                            -> proves (subst_φ x t φ)
  | p_false : forall t, proves (teq (Suc t) (Nat O)) -> proves bot

  (* relation indicating that A proves B in multiple steps - problem! *)
  with proves_mstep : Φ -> Φ -> Set :=
  | ps_base : forall φ1 φ2, proves φ1 -> proves φ2 -> proves_mstep φ1 φ2
  | ps_step : forall φ1 φ2 φ3, proves φ1 -> proves φ2 ->
                               (proves_mstep φ2 φ3) -> (proves_mstep φ1 φ3).

  Definition atom1 := p_arith (n0+n0) (n1*n0) haf1.
  Print atom1.

  Definition ex_disj := p_oril (teq (n0+n0) (n1*n0)) bot atom1.
  Print ex_disj.

  Eval compute in ex_disj.



End HeytingProps.

Module TestHeytingProps.
  (* Unit tests for HeytingProps. *)

  Import HeytingProps.

  Theorem test_unbound_1 : unbound atom1 0.
  Proof. apply ub_teq. Qed.

  Theorem test_unbound_2 : unbound atom3 2.
  Proof. constructor. Qed.

  Theorem test_unbound_3 : unbound (Conj atom1 atom3) 0.
  Proof.
    apply ub_conj.
    Case "atom1". apply ub_teq.
    Case "atom3". apply ub_teq.
    (* automated: repeat constructor. Qed. *)
  Qed.

  Theorem test_unbound_4: unbound (All 1 (Ex 2 atom4)) 0.
  Proof.
    constructor.
    Case "1 <> 0". intros contra. inversion contra.
    Case "Ex 2". constructor.
    SCase "2 <> 1". intros contra. inversion contra.
    SCase "atom4". constructor.
  Qed.

  Theorem test_unbound_5: ~(unbound (All 1 (Ex 2 atom4)) 1).
  Proof.
    intros contra. inversion contra. subst. apply H1. reflexivity.
  Qed.

  Theorem test_unbound_6: ~(unbound (All 1 (Ex 2 atom4)) 2).
  Proof.
    intros contra. inversion contra. subst.
    inversion H3. subst. apply H2. reflexivity.
  Qed.
End TestHeytingProps.
