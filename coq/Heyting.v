Require Import Lib.

Module HeytingTerms.

  (* Numerals *)
  Inductive ℕ: Set :=
  | O: ℕ
  | S: ℕ -> ℕ.

  (* Variables, identified by natural numbers *)
  Definition X := nat.

  (* Terms *)
  Inductive T: Set :=
  | Nat: ℕ -> T
  | Var: X -> T
  | Plus: T -> T -> T
  | Mult: T -> T -> T
  | Suc : T -> T.

  Check S (S O).                     (* ℕ *)
  Check Nat (S (S O)).               (* T *)
  Check Var 3.                       (* T *)
  Check Suc (Plus (Var 0) (Nat O)).  (* T *)

  Notation "t1 + t2"  := (Plus t1 t2)
                           (at level 50, left associativity) : hterm_scope.
  Notation "t1 * t2"  := (Mult t1 t2)
                           (at level 40, left associativity) : hterm_scope.

  Bind Scope hterm_scope with T.  (* TODO this doesn't work *)
  Delimit Scope hterm_scope with hterm. (* but this does, see below *)

  Check 3 + 3.  (* nat *)
  Check (Nat O + Nat O)%hterm.  (* term *)

End HeytingTerms.

Module HeytingProps.

  Export HeytingTerms.
  Require Export List.

  (* Atomic Propositions *)
  (* Presumably we could manipulate Heyting arithmetic formulas as Props, but
     for now I'm more confident about manipulating them on the computational
     side. So rather than defining an equality relation, I'm defining atomic
     propositions that include equality claims. *)
  (* It may be unnecessary to define these separately--maybe they should be
     in Φ. *)
  Inductive atom: Set :=
  | teq   : T -> T -> atom
  | bot   : atom
  | top   : atom.
  (* The lexer complains about ⊥, ⊤ *)

  Check (teq (Nat O + Nat O) (Nat (S O) * Nat O))%hterm.

  (* Formulas *)
  (* For the Kanckos paper, basic connectives are ∧, ∨, ⊃ (aka ⇒), ∀, ∃.
     Negation is derived as ¬A ≡ A ⊃ ⊥. *)
  Inductive Φ: Set :=
  | A   : atom -> Φ
  | Disj: Φ -> Φ -> Φ
  | Conj: Φ -> Φ -> Φ
  | Imp : Φ -> Φ -> Φ
  | Ex  : X -> Φ -> Φ
  | All : X -> Φ -> Φ.

  Definition Neg (φ:Φ) := Imp φ (A bot).
  Check Neg. Check Disj. Check (A bot).

  (* Rules and Derivations *)
  (* May need to include arithmetic axioms here as well. *)
  (* I started this with a bunch of different constructors (commented below)
     but I'm not it'll be useful to have a bunch of different constructors
     with the same shape, unless we can do some dependent-type magic to make
     the type checker ensure that derivations are well-formed. *)
  (* deriv shapes are: conclusion, premise/s (except for axiom). *)
  Inductive deriv : Set :=
  | d_ax : Φ -> deriv
  | d_un : Φ -> deriv -> deriv
  | d_bi : Φ -> deriv * deriv -> deriv
  | d_tn : Φ -> deriv * deriv * deriv -> deriv.

  Check d_ax (A (teq (Nat O) (Nat O + Nat O)))%hterm.

  (*  (* first attempt *)
  Inductive deriv : Set :=
  | Ebot : Φ -> deriv (* implicit bot in the premise *)
  | Iconj  : deriv * deriv -> Φ -> deriv
  | Econjl : deriv -> Φ -> deriv
  | Econjr : deriv -> Φ -> deriv
  | Idisjl : deriv -> Φ -> deriv
  | Idisjr : deriv -> Φ -> deriv
  | Edisj  : deriv * deriv * deriv -> Φ -> deriv
  | Iimpl  : deriv -> Φ -> deriv
  | Eimpl  : deriv * deriv -> Φ -> deriv
  | ... others too
  Check Econjl.
  Check Ebot (A bot).
  Check Econjl (Ebot (A bot)) (A bot).
   *)

End HeytingProps.