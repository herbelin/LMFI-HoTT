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

Definition homotopy {A B : Type}( f g : A -> B ):=
forall x :A , f x = g x.

Notation "f =~ g " := (homotopy f g)(at level 40).
Record isequiv (A B : Type) (f : A-> B) : Type :=
MakeEquiv {g1 : B->A ; g2 : B-> A ; inv_l : ( f¤g1)=~(Id B); inv_r : (g2¤f) =~(Id A)}.

Record Type_equiv (A B : Type) :=
Make_Type_equiv { first : A-> B ; second : isequiv A B first}.

Notation " A ~=~ B" := (Type_equiv A B)(at level 40).

Inductive Unit_Type :=
| stars : Unit_Type.

Inductive empty : Type :=.

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

(* We now define the suspension, correspond to the part 5.3 *)
Module Export Suspension.

Private Inductive Sus (A : Type) : Type :=
| N : Sus A
| S : Sus A.

Axiom Merid  :forall A : Type, forall x : A, (N A)= (S A).

Definition Sus_ind (A : Type) (P : Sus A -> Type)
 (b : P (N A)) ( c : P (S A))(l :forall x :A, (Tr P (N A) (S A) (Merid A x) b )= c) :
forall x : Sus A, P x.
Proof.
intros. destruct x. 
- apply b.
- apply c.
Defined.

Axiom Sus_ind_beta_loop
  : forall (A : Type) (P : Sus A -> Type) 
(b : P (N A))(c : P (S A)) 
(l : forall x : A, Tr P (N A) (S A) (Merid A x) b = c),
forall x : A, apd P (Merid A x) (Sus_ind A P b c l )  = l x.

End Suspension. 