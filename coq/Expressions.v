Require Import Lib.
Require Import Relation_Definitions Setoid.

Module Expressions.

  Require Export Heyting.
  Export HeytingTerms.

(* Expressions, as defined in Kanckos section 5.1 *)
Inductive expr : Set :=
| E0 : expr
| E1 : expr
| Eω : expr
| EX : X -> expr
| Eplus : expr -> expr -> expr
| Epair : expr -> expr -> expr.

Notation "( e1 , e2 )" := (Epair e1 e2).
Notation "e1 # e2"     := (Eplus e1 e2) (at level 50, left associativity).

Inductive eeq : expr -> expr -> Prop :=
| eeq_refl  : forall f,     eeq f f                            (* text *)
| eeq_pluss : forall f g,   eeq (f # g) (g # f)                (* 3 *)
| eeq_plust : forall f g h, eeq ((f # g) # h) (f # (g # h))    (* 3 *)
| eeq_id1   : forall f,     eeq (f # E0) f                     (* 5 *)
| eeq_id2   : forall f g,   eeq (f # g) f -> eeq g E0          (* 5 *)
| eeq_pr0   : forall f,     eeq (E0, f) f                      (* 12 *)
| eeq_pair1 : forall f g h, eeq (f, (g # h)) ((f, g) # (f, h)) (* 8 *)
| eeq_pair2 : forall f g h, eeq (f, (g, h)) ((f # g), h)       (* 13 *)
| eeq_symm  : forall f g,   eeq f g -> eeq g f                 (* ADDED *)
| eeq_trans : forall f g h, eeq f g -> eeq g h -> eeq f h      (* ADDED *)
.

Notation "e1 == e2" := (eeq e1 e2) (at level 70).

(* Additional axioms required for rewriting tactics. *)
Axiom plus_compat : forall f1 f2, f1 == f2 ->
                    forall g1 g2, g1 == g2 ->
                    f1 # g1 == f2 # g2.
Axiom pair_compat : forall f1 f2, f1 == f2 ->
                    forall g1 g2, g1 == g2 ->
                    (f1, g1) == (f2, g2).

(* this is blatantly copied without understanding from
   https://coq.inria.fr/refman/Reference-Manual029.html *)
Add Parametric Relation : expr eeq
    reflexivity proved by eeq_refl
    symmetry proved by eeq_symm
    transitivity proved by eeq_trans
  as eeq_rel.

Add Parametric Morphism : Eplus with
signature eeq ==> eeq ==> eeq as eplus_mor.
Proof.
  exact plus_compat.
Qed.

Add Parametric Morphism : Epair with
signature eeq ==> eeq ==> eeq as epair_mor.
Proof.
  exact pair_compat.
Qed.

Inductive elt : expr -> expr -> Prop :=
| elt_01    : elt E0 E1                                        (* 6 *)
| elt_1ω    : elt E1 Eω                                        (* 6 *)
| elt_trans : forall f g h, elt f g -> elt g h -> elt f h      (* 1 *)
| elt_plus  : forall f g h, elt f g -> elt (f # h) (g # h)     (* 4 *)
| elt_lim   : forall f g, elt f Eω -> elt g Eω
                          -> elt (f # g) Eω                    (* 7 *)
| elt_pair1 : forall f g h, elt f g -> elt (h, f) (h, g)       (* 10 *)
| elt_pair2 : forall f g h, elt f g -> elt E0 h
                            -> elt (f, h) (g, h)               (* 11 *)
.

Notation "e1 ≺ e2"  := (elt e1 e2) (at level 70).

(* Axiom 2: if f ≺ g then ¬(f == g), doesn't fit in inductive definitions *)
Axiom elt_neq : forall f g: expr, f ≺ g -> ~(f == g).

(* does this make any difference? should/can I declare it as a partial order? *)
Add Parametric Relation : expr elt
    transitivity proved by elt_trans
  as elt_rel.

Inductive ele : expr -> expr -> Prop :=
| ele_lt    : forall f g, f ≺ g -> ele f g                     (* text *)
| ele_eq    : forall f g, f == g -> ele f g                    (* text *)
| ele_0     : forall f, ele E0 f                               (* 6 *)
| ele_pair  : forall f g h c, g ≺ c -> h ≺ c
                              -> ele ((g, f) # (h, f)) (c, f)  (* 9 *)
.

Notation "e1 ≼ e2"  := (ele e1 e2) (at level 70).

(* A basic theorem that should expose the need for axioms that are left
   implicit in the paper. (Question: is there an easier way here?!) *)
Theorem ele_eq_lt : forall f g : expr, f ≼ g -> f == g \/ f ≺ g.
Proof.
  intros f g H.
  induction H as [f g | f g | f | f g h c].
  Case "f ≺ g". right. apply H.
  Case "f == g". left. apply H.
  Case "0 ≼ f". induction f. (* originally I thought I could just destruct f *)
  SCase "f == 0". left. reflexivity.
  SCase "f == 1". right. apply elt_01.
  SCase "f == ω". right. apply elt_trans with (E1). apply elt_01. apply elt_1ω.
  (* For the next subcases, ;: I want to substitute E0 for f1 and f2
   * but don't know how to get that from eeq. *)
  SCase "f == f1 + f2". inversion IHf1.
  inversion IHf2.
  SSCase "f == 0 + 0". left. rewrite <- H. rewrite <- H0. rewrite eeq_id1.
    reflexivity.
  SSCase "f == 0 + <0". right.
    (* PROBLEM: can't rewrite, replace wants = not == *)
    (* maybe need to declare properties of ≺ similar to morphisms # and (,) *)
    replace (f1) with (E0). replace (E0 # f2) with (f2 # E0).
    replace (f2 # E0) with f2. apply H0.
    (* just admitting all the replacements *)
    admit. admit. admit.
  (* TODO the rest - presently just admitted *)
  inversion IHf2.
  SSCase "f == >0 + 0". right. admit. SSCase "f == <0 + <0". right. admit.
  SCase "f == (f1, f2)". inversion IHf1.
  inversion IHf2.
  SSCase "f == (0, 0)". left. admit. SSCase "f == (0, <0)". right. admit.
  inversion IHf2.
  SSCase "f == (>0, 0)". right. admit. SSCase "f == (<0, <0)". right. admit.
  Case "(g, f) # (h, f)". admit.
Qed.

Theorem elt_eeq_trans : forall f g h: expr, f ≺ g -> g == h -> f ≺ h.
Proof.
Admitted. (* TODO *)

Theorem eeq_elt_trans : forall f g h: expr, f == g -> g ≺ h -> f ≺ h.
Proof.
Admitted. (* TODO *)

Theorem ele_trans : forall f g h: expr, f ≼ g -> g ≼ h -> f ≼ h.
Proof.
  intros f g h Hfg Hgh.
  apply ele_eq_lt in Hfg. apply ele_eq_lt in Hgh.
  inversion Hfg. inversion Hgh.
  Case "f == g == h".
    apply ele_eq. apply eeq_trans with (g). apply H. apply H0.
  Case "f == g ≺ h".
    (* BASED ON TODO *)
    apply ele_lt. apply eeq_elt_trans with (g). apply H. apply H0.
  inversion Hgh.
  Case "f ≺ g == h".
    (* BASED ON TODO *)
    apply ele_lt. apply elt_eeq_trans with (g). apply H. apply H0.
  Case "f ≺ g ≺ h". apply ele_lt. apply elt_trans with (g). apply H. apply H0.
Qed.


(* A theorem stated at the end of section 5.1. Not sure about its use, but
 * but it's a good start at using these axioms. *)

Theorem th51 : forall f g h,
                 E0 ≺ f -> E0 ≺ h -> (f, g) # h ≺ (f, g # h).
Proof.
  intros f g h H1 H2.
  (* TODO make the rewriting rules work. *)
  (* rewrite eeq_pair1. *)
Abort.



End Expressions.
