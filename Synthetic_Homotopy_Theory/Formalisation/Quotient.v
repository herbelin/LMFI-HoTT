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

(* We now define the quotient, which can be find in 5.4 *)

Module Export Quotient.

Private Inductive qunt  (A : Type)( tild : A -> A -> Type) :=
class_equi : A -> qunt A tild.

Axiom quo :
forall A : Type , forall tild : A -> A -> Type,
 forall x y : A, forall p : tild x y,
 class_equi A tild x = class_equi A tild y.

Definition qunt_ind (A : Type) (tild : A -> A -> Type)(P : qunt A tild -> Type) 
(f:  forall x :A, P (class_equi A tild x ))
(l : forall x y : A, forall p : tild x y ,Tr P (class_equi A tild x) (class_equi A tild y) (quo A tild x y p) (f x) = f y) :
forall x : qunt A tild, P x.
Proof.
intros. destruct x. apply f.
Defined.
 
(*
Definition qunt_ind_2 (A B: Type) (tild : A -> A -> Type) (f : A -> B)
 (l : forall x y : A,  tild x y -> f x = f y)
: qunt A tild -> B. *)

Axiom qunt_ind_beta_quo : forall A : Type, forall tild : A -> A -> Type, 
forall P : qunt A tild -> Type,
forall f : forall x :A,
 P (class_equi A tild x ), 
forall l :( forall x y : A, 
forall p : tild x y ,
Tr P (class_equi A tild x) (class_equi A tild y) (quo A tild x y p) (f x) = f y ),
 forall x y : A, forall p : tild x y, 
apd P  (quo A tild x y p) (qunt_ind A tild P f l )  = l x y p.

End Quotient.