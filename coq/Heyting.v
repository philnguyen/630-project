Require Import Lib.

Module HeytingTerms.

  (* Variables, identified by natural numbers *)
  Definition X := nat.

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
  Qed.

  (* Terms *)
  Inductive T: Set :=
  | Nat: nat -> T
  | Var: X -> T
  | Plus: T -> T -> T
  | Mult: T -> T -> T
  | Suc : T -> T.  (* note that Kanckos defines succ for both nats and terms *)

  Check S (S O) :                   nat.
  Check Nat (S (S O)):              T.
  Check Var 3:                      T.
  Check Suc (Plus (Var 0) (Nat O)): T.

  Notation "t1 + t2"  := (Plus t1 t2)
                           (at level 50, left associativity) : hterm_scope.
  Notation "t1 * t2"  := (Mult t1 t2)
                           (at level 40, left associativity) : hterm_scope.

  Bind Scope hterm_scope with T.  (* this doesn't help too much *)
  Delimit Scope hterm_scope with hterm. (* but this does, see below *)

  Check (3 + 3)                     : nat.
  Check ((Nat O + Nat O)%hterm)     : T.
  Check (Suc (Nat O + Nat O))%hterm : T.

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
  Qed.

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

End HeytingTerms.

Module HeytingProps.

  Export HeytingTerms.
  Require Export List.

  (* Arithmetic Equality *)
  Open Scope hterm_scope.

  (* Equality rules from Kanckos page 3, except for Inf1, defined below. *)
  Inductive aderiv : T -> T -> Set :=
  | t_refl    : forall t, aderiv t t
  | t_symm    : forall t1 t2, aderiv t1 t2 -> aderiv t2 t1
  | t_trans   : forall t1 t2 t3, aderiv t1 t2 -> aderiv t2 t3 -> aderiv t1 t3
  | t_plus_id : forall t, aderiv (t + Nat O) t
  | t_plus_rec: forall t1 t2, aderiv (t1 + Suc(t2)) (Suc(t1 + t2))
  | t_mult_0  : forall t, aderiv (t * Nat O) (Nat O)
  | t_mult_rec: forall t1 t2, aderiv (t1 * Suc(t2)) ((t1 * t2) + t1)
  | t_rep_s   : forall t1 t2, aderiv t1 t2 -> aderiv (Suc t1) (Suc t2)
  | t_rep_plus_l : forall t1 t2 t3, aderiv t1 t2 -> aderiv (t1 + t3) (t2 + t3)
  | t_rep_plus_r : forall t1 t2 t3, aderiv t2 t3 -> aderiv (t1 + t2) (t1 + t3)
  | t_rep_mult_l : forall t1 t2 t3, aderiv t1 t2 -> aderiv (t1 * t3) (t2 * t3)
  | t_rep_mult_r : forall t1 t2 t3, aderiv t2 t3 -> aderiv (t1 * t2) (t1 * t3)
  | t_inf2    : forall t1 t2, aderiv (Suc t1) (Suc t2) -> aderiv t1 t2.


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

  (* atomic propositions for use in testing *)
  Definition n0 := Nat O.
  Definition n1 := Suc n0.
  Definition n2 := Suc n1.
  Definition v0 := Var 0.
  Definition v1 := Var 1.
  Definition v2 := Var 2.
  Definition atom1 := teq (n0 + n0) (n1 * n0).
  Definition atom2 := teq (Suc v0) n0.
  Definition atom3 := teq v0 v1.
  Definition atom4 := teq n2 (v1 + v2).
  Check atom1 : Φ.
  Check atom2 : Φ.
  Check atom3 : Φ.
  Check atom4 : Φ.

  (* TODO proof of falsity: forall n, teq (Suc n) (O) -> false *)
  (* I'll implement that as a separate Set alongside "proves" *)

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
  | p_indi  : forall φ1 φ2, proves_mstep φ1 φ2 -> proves (Imp φ1 φ2)
  | p_impe  : forall φ1 φ2, proves (Imp φ1 φ2) -> proves φ1 -> proves φ2
  | p_alli  : forall φ x, proves φ -> unbound φ x -> proves (All x φ)
  | p_alle  : forall φ x t, proves (All x φ) -> proves (subst_φ x t φ)
  | p_exi   : forall φ x t, proves φ -> proves (Ex x (abstract_φ t x φ))
  | p_exe   : forall φ1 x t φ2, proves (Ex x φ1)
                                -> proves_mstep (subst_φ x t φ1) φ2
                                -> proves φ2
  | p_arith : forall φ1 φ2, aderiv φ1 φ2 -> proves (teq φ1 φ2)
  | p_ind   : forall φ x t, proves (subst_φ x (Nat O) φ)
                            -> proves_mstep φ (subst_φ x (Suc (Var x)) φ)
                            -> proves (subst_φ x t φ)

  (* relation indicating that A proves B in multiple steps *)
  with proves_mstep : Φ -> Φ -> Set :=
  (* TODO this is broken, I'm not thinking right somehow *)
  | ps_base : forall p, proves p -> proves_mstep p p
  | ps_step : forall φ1 φ2, proves φ1 -> proves φ2 -> proves_mstep φ1 φ2.

  Definition dv1 := p_arith (n0 + n0) (n1 * n0).
  Definition dv2 := p_arith v0 n0.
  Print dv1. Print dv2.
(*  Definition dv12 := p_oril (Disj dv1 dv2). *)

  Definition t2a := Nat (S (S O)).
  Definition t2b := (Nat (S O) + Nat (S O))%hterm.
  Definition eq2rec := t_plus_rec t2a t2b.
  Definition proves2 := p_arith t2a t2b.

  (*

  (* Unused function definitions *)

  Fixpoint bound_vars (φ : Φ) : list X :=
    match φ with
      | Ex x φ
      | All x φ => x::(bound_vars φ)
      | Disj φ1 φ2
      | Conj φ1 φ2
      | Imp φ1 φ2 => (bound_vars φ1) ++ (bound_vars φ2)
      | _ => nil
    end.

  Fixpoint unbound_f (φ : Φ) (x : X) : Prop :=
    match φ with
      | Ex x' φ
      | All x' φ =>
        if eq_id_dec x x' then True else unbound_f φ x
      | Disj φ1 φ2
      | Conj φ1 φ2
      | Imp φ1 φ2 => (unbound_f φ1 x) /\ (unbound_f φ2 x)
      | _ => True
    end.
*)

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
