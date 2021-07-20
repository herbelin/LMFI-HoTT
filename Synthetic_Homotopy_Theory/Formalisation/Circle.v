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

Notation " g \u00a4 f ":= (compose_function g f)(at level 40).

Definition Id (A : Type) :=
fun x: A => x.

Definition homotopy {A B : Type}( f g : A -> B ):=
forall x :A , f x = g x.

Notation "f =~ g " := (homotopy f g)(at level 40).
Record isequiv (A B : Type) (f : A-> B) : Type :=
MakeEquiv {g1 : B->A ; g2 : B-> A ; inv_l : ( f\u00a4g1)=~(Id B); inv_r : (g2\u00a4f) =~(Id A)}.

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

(* We now defined the circle, part 5.1, i skipped part 5.2 *)
Module Export Circle.

Private Inductive S1 : Type :=
| base : S1.

Axiom loop : base = base.

Definition S1_ind (P : S1 -> Type) (b : P base) (l :Tr P base base loop b = b)
  : forall (x:S1), P x.
Proof.
intros. 
destruct x. apply b.
Defined.  

Axiom S1_ind_beta_loop
  : forall (P : S1 -> Type) (b : P base) (l : Tr P base base loop b = b),
 forall x : S1, apd P loop (S1_ind P b l ) = l.

End Circle.
