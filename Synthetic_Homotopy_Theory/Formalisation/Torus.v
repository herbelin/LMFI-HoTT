Require Import HoTT.
Require Import Reals.
Require Import Arith.
Require Import Coq.Reals.Reals.
Open Scope nat_scope.
Require Import Bool.


Lemma refl {A} (x : A) : x=x.
Proof.
reflexivity.
Defined.

Lemma compose_path {A} {x y z : A} (p : x=y) (q: y=z ):   x=z.
Proof.
induction p. exact q.
Defined.

Lemma compose_path_with_refl {A : Type} {x y : A} (p : x=y) : compose_path (refl x) p = p.
Proof.
unfold compose_path. simpl. apply refl.
Defined.

Notation "p ° q " := (compose_path p q)(at level 40).

(* We now defined the Torus, you can find it in section 5.4 *)
Module Export Torus.

Private Inductive T_2 : Type :=
| b : T_2.

Axiom loop_T_1 : b = b. (* p *)
Axiom loop_T_2 : b = b. (* q *)


Axiom loop_T_3 :  (loop_T_1 ° loop_T_2)= (loop_T_2 ° loop_T_1). (*s*)


End Torus.