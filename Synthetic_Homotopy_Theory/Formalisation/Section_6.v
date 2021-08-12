(* This file present Section 6.1 and 6.2 from the lecture notes, which introduce contractible types and propositions *)


(* Section 6.0 : Preliminaries *)


(* 0.1 : Basics on identity *)

Lemma refl {A} (x : A) : x=x.
Proof.
reflexivity.
Defined.

Lemma inv {A} {x y : A} : x = y -> y = x.
Proof.
intro X. destruct X. apply refl.
Defined.

Lemma eq_transitive {A} {x z : A} (y : A) (p : x=y) (q: y=z ):   x=z.
Proof.
destruct p. exact q.
Defined.

Lemma Tr { A : Type} (B : A -> Type) (x y : A) (p : x=y) :
B x -> B y.
Proof.
induction p. intro H. apply H.
Defined.


(* 0.2 : Basics on functions *)

Definition Id (A : Type) :=
fun x: A => x.

Definition compose_function {A B C} (g : B -> C) (f : A -> B) :=
  fun x : A => g (f x).

Notation " g $ f ":= (compose_function g f)(at level 40).

Definition homotopy {A B : Type}( f g : A -> B ):=
forall x :A , f x = g x.

Notation "f =~ g " := (homotopy f g)(at level 40).

Definition ap {A B : Type} (f : A -> B) {x y : A} : x = y -> f x = f y.
Proof.
intro H. destruct H. apply refl.
Defined. 


(* 0.3 : Basics on equivalence *)

Record isequiv (A B : Type) (f : A-> B) : Type :=
MakeEquiv {g1 : B->A ; g2 : B-> A ; inv_l : f $ g1 =~ Id B ; inv_r : g2 $ f =~ Id A }.

Record Type_equiv (A B : Type) :=
Make_Type_equiv { first : A-> B ; second : isequiv A B first}.

Notation " A ~=~ B" := (Type_equiv A B)(at level 40).

Lemma equiv_compose {A B C : Type} (f : A -> B) (g : B -> C) :
isequiv A B f -> isequiv B C g -> isequiv A C (g $ f).
Proof.
intros e1 e2. destruct e1 as (f1,f2,i1,i2). destruct e2 as (g1,g2,j1,j2). exists (f1 $ g1) (f2 $ g2).
- intro x. apply (fun p => eq_transitive _ p (j1 x)). apply (ap g). apply (i1 (g1 x)).
- intro x. apply (fun p => eq_transitive _ p (i2 x)). apply (ap f2). apply (j2 (f x)).
Defined.

Lemma equiv_transitive {A C : Type} (B : Type) : A~=~B -> B~=~C -> A~=~C.
Proof.
intros e1 e2. destruct e1 as (e1,eqe1). destruct e2 as (e2,eqe2).
exists (e2 $ e1). apply equiv_compose.
- apply eqe1.
- apply eqe2.
Defined.

Lemma equiv_sym {A B : Type} : A ~=~ B -> B ~=~ A.
Proof.
Admitted.


(* 0.4 : Extensionnality for dependent functions *)

Lemma weak_dependent_extensionality {A} {B : A -> Type} (f g : forall x:A, B x) : f=g -> forall x : A, f x = g x.
Proof.
intro p. destruct p. intros. apply refl.
Defined.

Axiom dependent_extensionality : forall {A:Type} {B : A -> Type} (f g : forall x:A, B x), isequiv (f=g) (forall x : A, f x = g x)(weak_dependent_extensionality f g).

Lemma functional_extensionality {A} {B : A -> Type} (f g : forall x:A, B x) : (forall x : A, f x = g x) -> f = g.
Proof.
intro X. apply dependent_extensionality. exact X.
Defined.


(* 0.5 : Univalence *)

Definition ua {A B} :   A = B -> A ~=~ B.
Proof.
intros f. 
destruct f. 
exists (Id A).
now exists (Id A) (Id A).
Defined.

Axiom univalence  : forall A B : Type, isequiv (A=B) (A~=~B) ua. 

Lemma weak_univalence : forall A B : Type, A~=~B -> A=B.
Proof.
intros A B X. apply univalence. apply X.
Defined.

Lemma transport_equiv (P : Type -> Type) {A B} : A~=~B -> P A -> P B.
Proof.
intro H. apply Tr. apply (weak_univalence _ _ H).
Defined.


(* 0.6 : Some Inductive types, with analysed identity types *)

Record prodpp {A : Type} (B : A -> Type) :=
prodpp_def {fst_2 : A ; snd_2 : B fst_2 }.

Inductive Unit_Type :=
stars : Unit_Type.

Inductive Empty : Type :=.

(* The following results are proven in Section 3 and 4 *)

Definition Eq (A B : Type) (z z' : A * B) := prod (fst z=fst z') (snd z=snd z').

Proposition pair_equal (A B : Type) (z z' : prod A B): (z=z') ~=~ Eq A B z z'.
Proof.
Admitted.

Definition Eq_bis {A : Type} ( B : A -> Type) (z z' :  prodpp B) :=
prodpp (fun p : fst_2 B z = fst_2 B z' => Tr B _ _ p (snd_2 B z) = snd_2 B z').

Lemma prodpp_equal {A : Type} (B : A-> Type) (z z' : prodpp B) :
(z=z') ~=~ Eq_bis B z z'.
Proof.
Admitted.

Lemma Unit_to_Unit : forall x y : Unit_Type, (x=y) ~=~ Unit_Type.
Proof.
Admitted.


(* Section 6.1 : Contractible types *)

(* Definition 11 *)
Definition contractible (X : Type) : Type :=
prodpp (fun y : X => forall x : X, x=y).

(* Proposition 4 *)
Proposition unit_contractible : contractible (Unit_Type).
Proof.
exists stars. intros. destruct x. apply refl.
Defined.

Definition decode_for_P_five (X : Type)  :contractible X -> ( Unit_Type -> X).
Proof.
intros. destruct X0 as (c,_). apply c. 
Defined.

Definition encode_for_P_five (X : Type) : contractible X -> (X -> Unit_Type).
Proof.
intros. exact stars.
Defined.

(* Proposition 5 *)
Proposition contractible_and_Unit ( X : Type )  : contractible X -> (X ~=~ Unit_Type) .
Proof.
intro X0. exists (encode_for_P_five X X0). exists (decode_for_P_five X X0) (decode_for_P_five X X0).
- intro x. destruct x. apply refl.
- intro x. destruct X0 as (c,contr). simpl. apply inv. apply contr.
Defined.

(* We generalize proposition 5 using univalence *)
Proposition contractible_elim {X : Type} (P : Type -> Type) : contractible X -> P Unit_Type -> P X.
Proof.
intro H. apply (transport_equiv P (equiv_sym (contractible_and_Unit X H))).
Defined.

(* Proposition 6 *)
Proposition Contractible_prodpp (X : Type) (x : X) : contractible (prodpp (fun y : X => x=y)).
Proof.
unfold contractible. exists (@prodpp_def X (fun y : X => x = y) x (refl x)).
intro z. destruct z as (x',e). destruct e. apply refl.
Defined.


(* Section 6.2 : Propositions *)

(* Definition 12 *)
Definition proposition (X : Type) : Type := forall x y : X , x=y.

(* Proposition 7 *)
Proposition Contractible_prop (X : Type) : contractible X -> proposition X.
Proof.
unfold contractible. unfold proposition.
intros X0 x y. destruct X0 as (x',eq). apply (eq_transitive x').
- apply eq.
- apply inv. apply eq. 
Defined. 

(* Proposition 8 *)
Proposition prop_empty : proposition Empty.
Proof.
intro. intro.  destruct x.
Defined.

(* Proposition 9 *)
Proposition dependent_on_prop (A : Type) (P :A -> Type) : (forall x : A, proposition (P x))  -> proposition (forall x :A, P x).
Proof. 
unfold proposition. intros X x y. apply (dependent_extensionality x y). intro. apply (X x0 (x x0) (y x0)).
Defined. 

(* Proposition 10 *)
Proposition proposition_on_prod (A B : Type) : proposition A -> proposition B -> proposition (prod A B ).
Proof.
intros X Y z z'.  apply pair_equal. apply (fun x y => (x,y)).
- apply X. 
- apply Y.
Defined.

(* Proposition 11 *)
Proposition proposition_prodpp (A : Type) (B : A -> Type) :proposition A ->(forall x : A, proposition (B x)) ->  proposition (prodpp B). 
Proof.
intros X Y z z'.  apply (prodpp_equal B _ _). unfold Eq_bis. apply (prodpp_def _ _ (X _ _)). apply Y.
Defined.

(* Auxiliary result for proposition 12 *)
Proposition prop_contractible (A : Type) : proposition A -> A -> contractible A.
Proof.
intros. unfold contractible. unfold proposition in X. exact (prodpp_def A (fun y : A => forall x :A , x=y) (X0) (fun y : A => X y X0 )).
Defined.

(* Proved with univalence *)
Proposition contractible_equiv {X Y : Type}  : (X ~=~ Y) -> contractible X -> contractible Y.
Proof.
apply (transport_equiv contractible).
Defined.

Proposition contractible_arrow_eq (A : Type) : contractible A -> forall x y : A, contractible (x=y).
Proof.
intro H. apply (contractible_elim (fun A => forall x y:A, contractible (x=y))).
- apply H.
- intros x y. apply (contractible_equiv (equiv_sym (Unit_to_Unit x y))). apply unit_contractible.
Defined.

(* Poposition 12 *)
Proposition proposition_contrac (A : Type) : proposition A -> forall x y : A, contractible (x=y).
Proof.
intros. unfold proposition in X. apply (contractible_arrow_eq A). apply (prop_contractible A X x).
Defined. 

(* Proposition 13 for contractible families *)
Lemma contractible_families {A} {P : A -> Type} : (forall x:A, contractible (P x)) -> prodpp P ~=~ A.
Proof.
intro H. exists (fst_2 P). exists (fun x : A => prodpp_def _ _ x (fst_2 _ (H x))) (fun x : A => prodpp_def _ _ x (fst_2 _ (H x))).
- intro x. unfold "$". simpl. apply refl.
- intro x. destruct x as (a,b). simpl. apply prodpp_equal. unfold Eq_bis. simpl. apply (prodpp_def _ _ (refl _)). apply (Contractible_prop _ (H a)).
Defined.

(* Proposition 13 *)
Proposition contractible_with_prodpp (A : Type) (P :A -> Type) (a a' : A)(p : P a) (p' : P a') : 
(forall x : A, proposition (P x)) -> (prodpp_def A P a p = prodpp_def A P a' p' ) ~=~ (a=a').
Proof.
intro H. apply (equiv_transitive (prodpp (fun r : a = a' => Tr _ _ _ r p = p'))). 
- apply prodpp_equal.
- apply contractible_families. intros. apply proposition_contrac. apply H.
Defined.

