(* This files contains the definition of HITs presented in Section 5 *)
(* Section 5.2 was not formalised, as well as some parts from 5.4 *)


(* Section 5.0 : Preliminaries *)

Lemma refl {A} (x : A) : x=x.
Proof.
reflexivity.
Defined.

Lemma Tr { A : Type} (B : A -> Type) (x y : A) (p : x=y) :
B x -> B y.
Proof.
induction p. intro H. apply H.
Defined.

Lemma apd {A : Type } (B : A -> Type) {x y : A}(p : x=y)(f :forall x:A, B x) :
Tr B x y p (f x) = f y.
Proof.
destruct p. unfold Tr. simpl. apply refl.
Defined.


(* Section 5.1 : Definition_of_the_circle *)

Module Export Circle.

Private Inductive S1 : Type :=
| base : S1.

Axiom loop : base = base.

Definition S1_ind (P : S1 -> Type) (b : P base) (l :Tr P base base loop b = b)
  : forall (x:S1), P x.
Proof.
intros. destruct x. apply b.
Defined.

Axiom S1_ind_beta_loop
  : forall (P : S1 -> Type) (b : P base) (l : Tr P base base loop b = b),
 forall x : S1, apd P loop (S1_ind P b l ) = l.

End Circle.


(* Section 5.3 : Definition_of_suspensions *)

Module Export Suspension.

Private Inductive Sus (A : Type) : Type :=
| N : Sus A
| S : Sus A.

Axiom Merid : forall A : Type, forall x : A, (N A)= (S A).

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


(* Section 5.4 : Definition_of_quotients *)

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
