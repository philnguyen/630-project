Module Expressions.

(* Expressions, as defined in Kanckos section 5.1 *)
Inductive expr : Type :=
| E0 : expr
| E1 : expr
| Eω : expr
(* TODO: variables *)
| Eplus : expr -> expr -> expr
| Epair : expr -> expr -> expr.

Notation "( e1 , e2 )" := (Epair e1 e2).
Notation "e1 # e2"     := (Eplus e1 e2) (at level 50, left associativity).

Inductive eeq : expr -> expr -> Prop :=
(* TODO missing <- in iff for axiom 5 *)
| eeq_refl  : forall f,     eeq f f                            (* text *)
| eeq_plus  : forall f g,   eeq (f # g) (g # f)                (* 3 *)
| eeq_trans : forall f g h, eeq ((f # g) # h) (f # (g # h))    (* 3 *)
| eeq_id    : forall f,     eeq (f # E0) f                     (* 5 *)
| eeq_pr0   : forall f,     eeq (E0, f) f                      (* 12 *)
| eeq_pr1   : forall f g h, eeq (f, (g # h)) ((f, g) # (f, h)) (* 8 *)
| eeq_pr2   : forall f g h, eeq (f, (g, h)) ((f # g), h)       (* 13 *)
.

End Expressions.