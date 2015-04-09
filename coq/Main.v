Require Export List.

Inductive ℕ: Set :=
| One: ℕ
| Suc: ℕ -> ℕ.

Definition X := nat.

Inductive T: Set := 
| Nat: ℕ -> T
| Var: X -> T.

(* TODO: all of these, or just a minimal set? *)
Inductive Φ: Set :=
| Disj: Φ -> Φ -> Φ
| Conj: Φ -> Φ -> Φ
| Imp : Φ -> Φ -> Φ
| Neg : Φ -> Φ
| Ex  : X -> Φ -> Φ
| All : X -> Φ -> Φ.

Definition A := list Φ.


(** Inference Rules *)

Inductive Deriv: A -> Φ -> Prop :=
| interchange:
    forall A₁ A₂ Φ₁ Φ₂ Φ,
      Deriv (A₁ ++ Φ₁ :: Φ₂ :: A₂) Φ -> Deriv (A₁ ++ Φ₂ :: Φ₁ :: A₂) Φ
| omit:
    forall A Ψ Φ,
      Deriv (Ψ :: Ψ :: A) Φ -> Deriv (Ψ :: A) Φ
| conjunction:
    forall A Φ₁ Φ₂ Φ,
      Deriv (Φ₁ :: Φ₂ :: A) Φ -> Deriv (Conj Φ₁ Φ₂ :: A) Φ
| conj_intro:
    forall A₁ A₂ Φ₁ Φ₂,
      Deriv A₁ Φ₁ -> Deriv A₂ Φ₂ -> Deriv (A₁ ++ A₂) (Conj Φ₁ Φ₂)
| conj_elim_L:
    forall A Φ₁ Φ₂, Deriv A (Conj Φ₁ Φ₂) -> Deriv A Φ₁
| conj_elim_R:
    forall A Φ₁ Φ₂, Deriv A (Conj Φ₁ Φ₂) -> Deriv A Φ₂
| disj_intro_L: (* TODO or R? *)
    forall A Φ₁ Φ₂, Deriv A Φ₂ -> Deriv A (Disj Φ₁ Φ₂)
| disj_intro_R: (* TODO or L? *)
    forall A Φ₁ Φ₂, Deriv A Φ₁ -> Deriv A (Disj Φ₁ Φ₂)
| disj_elim:
    forall A₁ A₂ A₃ Φ₁ Φ₂ Φ₃,
      Deriv A₁ (Disj Φ₁ Φ₂) -> Deriv (Φ₁ :: A₂) Φ₃ -> Deriv (Φ₂ :: A₃) Φ₃
      -> Deriv (A₁ ++ A₂ ++ A₃) Φ₃
(* TODO
| all_intro:
| all_elim:
| ex_intro:
| ex_elim:
| imp_intro:
| imp_elim:
| reduction:
| double_negation:
*)
.


(** Proof outline *)



