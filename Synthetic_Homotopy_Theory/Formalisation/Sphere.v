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

Definition compose_function {A B C} (g : B -> C) (f : A -> B) :=
  fun x : A => g (f x).

Notation " g ¤ f ":= (compose_function g f)(at level 40).

Definition Id (A : Type) :=
fun x: A => x.

Lemma Tr { A : Type} (B : A -> Type) (x y : A) (p : x=y) :
B x -> B y.
Proof.
induction p. intro H. apply H.
Defined.

Lemma apd {A : Type } (B : A -> Type) {x y : A}(p : x=y)(f :forall x:A, B x) :
Tr B x y p (f x) = f y.
Proof.
induction p. unfold Tr. simpl. apply refl.
Defined.

(* We define the sphere S2, which can be find in 5.4 *)
Module Export Sphere .

Private Inductive S2 : Type :=
bases : S2.

Axiom h : refl bases = refl bases.


(*
Definition S2_ind (P : S2 -> Type)
 (b : P (bases)) (l :Tr P (refl bases) (refl bases) h b = b) l est pas le bon type 

  : forall (x:(bases = bases)), P x.
Proof.
intros.
Admitted. *)

(*
Axiom S2_ind_beta_loop
  : forall (P : (bases = bases) -> Type) (b : P (refl bases)) (l : Tr P (refl bases) (refl bases) h b = b),
 forall x : S2, apd P h (S2_ind P b l )  = l. *)

End Sphere.