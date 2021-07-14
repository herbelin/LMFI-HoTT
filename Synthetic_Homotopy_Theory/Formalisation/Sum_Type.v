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

Section Sum_Type.

Inductive Sum_Type (A B : Type) :=
lft : A -> Sum_Type A B 
|rght : B -> Sum_Type A B.

Definition lft_inj (A B : Type) : forall x y : A, lft A B x = lft A B y -> x=y.
Proof.
intros. inversion X. apply refl.
Defined.

Definition rght_inj (A B : Type) : forall x y : B, rght A B x = rght A B y -> x=y.
Proof.
intros. inversion X. apply refl.
Defined.

Lemma e_f_t_o {A B} (a a' : A) (b b' : B) : ( lft A B a = lft A B a' ) -> (a=a').
Proof.
intros. apply (lft_inj A B). exact X.
Defined.

Lemma d_f_t_o {A B} (a a': A) (b b':B) : (a=a')-> ( lft A B a = lft A B a' ).
Proof.
intros. induction X. apply refl. 
Defined.

Lemma twenty_one {A B} (a a': A) ( b b' : B) :( lft A B a = lft A B a' )~=~ (a=a').
Proof.
exists (e_f_t_o a a' b b'). exists (d_f_t_o a a' b b') (d_f_t_o a a' b b').
- unfold "=~". intros. destruct x. unfold Id. unfold "¤". unfold d_f_t_o. unfold e_f_t_o. unfold paths_rect. unfold paths_ind. unfold refl. 
unfold lft_inj. unfold refl. apply refl.
- unfold "=~". intros. unfold "¤". unfold e_f_t_o. unfold d_f_t_o. unfold Id. unfold paths_rect. unfold paths_ind. unfold refl. unfold lft_inj. unfold refl. 
Admitted.

Lemma e_f_t_t {A B} (a a' : A) (b b' : B) : (lft A B a = rght A B b') -> Empty.
Proof.
intros. easy.
Defined.

Lemma d_f_t_t {A B} (a a' : A) (b b': B) : Empty -> (lft A B a = rght A B b').
Proof.
intro x; destruct x.
Defined.

Lemma twenty_two {A B} (a a'  : A) (b b' :B) : (lft A B a = rght A B b' )~=~ Empty.
Proof.
exists (e_f_t_t a a' b b'). exists ( d_f_t_t a a' b b') (d_f_t_t a a' b b').
- unfold "=~". unfold "¤". unfold d_f_t_t. unfold e_f_t_t. intros. destruct x.
- intros. easy.
Defined.

Lemma e_f_t_th {A B} (a a' : A) (b b' : B) : (rght A B b = lft A B a') -> Empty.
Proof.
easy.
Defined.

Lemma d_f_t_th {A B} (a a' : A) (b b' : B) : Empty -> (rght A B b = lft A B a').
Proof.
intro x; destruct x.
Defined.

Lemma twenty_three {A B} (a a' : A) (b b' : B) : (rght A B b = lft A B a') ~=~ Empty.
Proof.
exists (e_f_t_th a a' b b') ; exists (d_f_t_th a a' b b') (d_f_t_th a a' b b').
- easy.
- intro . easy.
Defined.

Lemma e_f_t_f {A B} (a a' : A) (b b' : B) : rght A B b = rght A B b' -> b = b'.
Proof.
apply rght_inj.
Defined.

Lemma d_f_t_f {A B} ( a a' : A) (b b' : B) : b=b' -> rght A B b = rght A B b'.
Proof.
intros. induction X.
apply refl.
Defined.

Lemma twenty_four {A B} (a a' : A) (b b' : B) : (rght A B b = rght A B b')~=~ (b = b').
Proof.
exists (e_f_t_f a a' b b'). exists (d_f_t_f a a' b b') (d_f_t_f a a' b b').
- unfold "=~". unfold "¤". intros. induction x. apply refl.
- unfold "=~". unfold "¤". intros. 
Admitted.


 End Sum_Type.