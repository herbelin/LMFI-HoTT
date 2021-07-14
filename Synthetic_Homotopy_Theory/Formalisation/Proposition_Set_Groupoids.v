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

Inductive Empty : Type :=.

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

Lemma number_four {A : Type} {x y: A} (p : x=y) : y=x.
Proof.
induction p. apply refl.
Defined.

Axiom dependant_functional_extensionality : forall {A } (P P' : A -> Type) , (forall x, P x = P' x) -> P = P'.

Lemma weak_dependant_functional_extensionality {A} (P P' : A -> Type) : (P = P') -> (forall x, P x = P' x).
Proof.
intro. destruct X. intro. apply refl.
Defined.

Axiom dependant_extensionality : forall {A} {P : A -> Type}( f g : forall x : A, P x), (forall x, f x = g x) -> f = g.

Record Eq( A B : Type) (z z' : A * B) :=
Eq_def {fst_1 : fst z=fst z' ; snd_1 : snd z=snd z'}.

Definition Encode { A B } : forall z z'  : prod A B, z=z'->Eq A B z z'.
Proof.
intros. induction X. apply Eq_def.
- apply refl. 
- apply refl.
Defined.

Definition decode {A B} : forall z z' : prod A B, Eq A B z z' -> z=z'.
Proof.
intros. induction z. induction z'. destruct X. simpl in fst_2. simpl in snd_2. induction fst_2. induction snd_2. apply refl.
Defined.

Proposition pair_equal (A B : Type) (z z' : prod A B): (z=z') ~=~ Eq A B z z'.
Proof.
exists (Encode z z').  exists (decode z z') (decode z z').
- unfold "=~". intros. induction z. induction z'. destruct x. simpl in fst_2. simpl in snd_2. simpl.
induction fst_2. induction snd_2. apply refl. 
- unfold "=~". intros. induction x. apply refl.
Defined.


Record prodpp {A : Type} (B : A -> Type) :=
prodpp_def {fst_2 : A ; snd_2 : B fst_2 }.

Record Eq_bis {A : Type} ( B : A -> Type) (z z' :  prodpp B) :=
Eq_bis_def { fst_3 : fst_2 B z=fst_2 B z' ; snd_3 : Tr B (fst_2 B z) (fst_2 B z') fst_3 (snd_2 B z) =snd_2 B z' }.

Lemma encode_bis {A} (B : A -> Type) : forall z z' : prodpp B, z=z' -> Eq_bis B z z'.
Proof.
intros. induction X. apply (Eq_bis_def A B z z (refl (fst_2 B z))). apply refl.
Defined.

Lemma decode_bis {A} (B : A -> Type) : forall z z' : prodpp B, Eq_bis B z z' -> z=z'.
Proof.
intros. induction z. induction z'. destruct X. 
simpl in fst_6. simpl in snd_6. induction fst_6. induction snd_6. apply refl.
Defined.

Lemma prodpp_equal {A : Type} (B : A-> Type) (z z' : prodpp B) :
(z=z') ~=~ Eq_bis B z z'.
Proof.
exists (encode_bis B z z'). exists (decode_bis B z z') (decode_bis B z z'). 
- unfold "=~". intro. induction z. induction z'. destruct x. simpl in fst_6. simpl in snd_6. simpl. induction fst_6. induction snd_6. apply refl.
- unfold "=~". intro X. destruct X. apply refl.
Defined.

Inductive Nat : Type :=
zero : Nat
| Sj : Nat-> Nat.

Inductive Nat_Stars : Type :=
one : Nat_Stars
| Sk : Nat_Stars -> Nat_Stars.

Inductive Ent_Rel : Type :=
zero_bis : Ent_Rel 
| Sl : Ent_Rel -> Ent_Rel
|Predl : Ent_Rel -> Ent_Rel.

Notation "Z/" := Ent_Rel.

Inductive Booleans_Type :=
zeero: Booleans_Type
|onee : Booleans_Type.

 Section Truncation_properties.

(* Definition eleven : *)

Definition contractible (X : Type) : Type :=
prodpp (fun y : X => forall x : X, x=y).

Proposition four : contractible (Unit_Type).
Proof.
exists stars. intros. destruct x. apply refl.
Defined.

Definition decode_for_P_five (X : Type)  :contractible X ->( Unit_Type -> X).
Proof.
intros. destruct X0. apply fst_4. 
Defined.

Definition encode_for_P_five (X : Type) : contractible X -> (X -> Unit_Type).
Proof.
intros. exact stars.
Defined.

(* Proposition five : *)
Proposition contractible_and_Unit ( X : Type )  :contractible X -> (X ~=~ Unit_Type) .
Proof.
intros. exists (encode_for_P_five X X0). exists (decode_for_P_five X X0) (decode_for_P_five X X0).
- unfold "=~". unfold "¤". unfold decode_for_P_five. unfold encode_for_P_five. intros. unfold Id. destruct x. apply refl.
- unfold "=~". unfold "¤". unfold decode_for_P_five. unfold encode_for_P_five. unfold contractible in X0.  unfold Id. intros. destruct X0. apply number_four. apply (snd_4 x). 
Defined.

Proposition Unit_and_contractible (X : Type) : (X ~=~ Unit_Type) -> contractible X.
Proof.
intro. destruct X0. destruct second0. unfold contractible. unfold "=~" in inv_l0.
Admitted.

(* Proposition six : *)
Proposition Contractible_prodpp (X : Type) (x : X) : contractible (prodpp (fun y : X => x=y)).
Proof.
unfold contractible. exists (@prodpp_def X (fun y : X => x = y) x (refl x)).
intros. destruct x0. destruct snd_4. apply refl.
Defined.

 End Truncation_properties.

Section Propositions.

(* Definition twelve *)
Definition proposition (X : Type) : Type := forall x y : X , x=y.

(* Proposition seven *)
Proposition Contractible_prop (X : Type) : contractible X -> proposition X.
Proof.
unfold contractible. unfold proposition.
intros. destruct X0. rewrite snd_4. apply snd_4.
Defined. 

(* Proposition eight : *)
Proposition prop_empty : proposition Empty.
Proof.
intro. intro.  destruct x.
Defined.

Lemma dependent_equal (A : Type) (x y : A) (P : A -> Type) : (x=y) -> (P x = P y).
Proof.
intros. destruct X. apply refl.
Defined.

Lemma equal_arrow_dependant ( A: Type)(P : A -> Type) : 
forall x y : A, x=y -> P x = P y.
Proof.
intros. apply dependent_equal. exact X.
Defined.

(*
Lemma dependant_arrow_equal (A : Type) (P : A -> Type) (f g : forall x :A, P x) :(forall x y : A,  x =  y )-> f = g.
Proof.
intros. apply (dependant_extensionality f g).  intro.
 Admitted. *)

Lemma for_P_nine (A : Type) (P :A -> Type) (f g : forall x: A, P x) : (forall x : A, proposition (P x)) -> f=g.
Proof.
unfold proposition. intro. apply (dependant_extensionality f g). intro. apply (X x (f x) (g x)).
Defined. 

(* Proposition nine : *)
Proposition dependent_on_prop (A : Type) (P :A -> Type) : (forall x : A, proposition (P x))  -> proposition (forall x :A, P x).
Proof. 
unfold proposition. intros. apply (dependant_extensionality x y). intro. apply (X x0 (x x0) (y x0)).
Defined. 

(* Proposition ten : *)
Proposition proposition_on_prod (A B : Type) : proposition A -> proposition B -> proposition (prod A B ).
Proof.
intros X Y. unfold proposition in X. unfold proposition in Y. unfold proposition. 
intros. apply pair_equal. apply Eq_def.
- apply X. 
- apply Y.
Defined.

(* Proposition eleven : *)
Proposition proposition_prodpp (A : Type) (B : A -> Type) :proposition A ->(forall x : A, proposition (B x)) ->  proposition (prodpp B). 
Proof.
intros. unfold proposition in X. unfold proposition. intros. destruct x. destruct y.  apply (prodpp_equal B _ _). unfold proposition in X0. 
Admitted.

(* Proposition twelve : *)
Proposition prop_contractible (A : Type) : proposition A -> A -> contractible A.
Proof.
intros.  unfold contractible. unfold proposition in X. exact (prodpp_def A (fun y : A => forall x :A , x=y) (X0) (fun y : A => X y X0 )).
Defined.

Lemma encode_2 : forall x y : Unit_Type, ( x = y )-> Unit_Type.
Proof.
intros. destruct X. exact stars.
Defined.

Lemma decode_2 : forall x y : Unit_Type, Unit_Type -> (x = y).
Proof.
intros. destruct X. destruct x. destruct y.
apply refl.
Defined.

Lemma Id_Unit : forall x : Unit_Type, Id Unit_Type x = stars.
Proof.
intros. destruct x. apply refl.
Defined.

Lemma For_Unit_to_Unit : forall x y :Unit_Type, forall p : x = y, encode_2 x y p = stars.
Proof.
intros. unfold encode_2. destruct p. apply refl.
Defined.

Lemma Unit_to_Unit : forall x y : Unit_Type, (x=y) ~=~ Unit_Type.
Proof.
intros. exists (encode_2 x y). exists (decode_2 x y) (decode_2 x y).
- unfold "=~". intros. destruct x0. unfold "¤". unfold decode_2. unfold encode_2. destruct x. destruct y. unfold Id. apply refl.
- unfold "=~". intros. destruct x0. destruct x. unfold encode_2. unfold decode_2. unfold "¤". unfold Id. apply refl.
Defined. 
Proposition contractible_eg : forall x y : Unit_Type, contractible (x = y).
Proof.
intros. apply Unit_and_contractible. exact (Unit_to_Unit x y).
Defined.

Proposition inter (A : Type) (P : Type -> Type) : contractible A -> P Unit_Type -> P A.
Proof.
intros. unfold contractible in X. 
Admitted. (* en utilisant l'univalence + lemme five*)

Proposition contractible_arrow_eq (A : Type) : contractible A -> forall x y : A, contractible (x=y).
Proof.
intros. apply (inter A (fun A : Type => forall x y :A,contractible (x=y))). 
- exact X.
- apply contractible_eg.
Defined.

Proposition proposition_contrac (A : Type) : proposition A -> forall x y : A, contractible (x=y).
Proof.
intros. unfold proposition in X. apply (contractible_arrow_eq A). apply ( prop_contractible A X x).
Defined. 

Lemma encode_b (A : Type ) (P : A -> Type) (a a' : A) (p : P a) (p' : P a') :
(forall x : A, proposition (P x))->
((prodpp_def A P a p) = (prodpp_def A P a' p' ))-> (a=a').
Proof.
intros. unfold proposition in X. apply prodpp_equal in X0. destruct X0. destruct snd_4.
easy.
Defined.

Lemma decode_b (A : Type ) (P : A -> Type) (a a' : A) (p : P a) (p' : P a') :
(forall x : A, proposition (P x))-> (a= a') -> ((prodpp_def A P a p) = (prodpp_def A P a' p' )).
Proof.
intro. unfold proposition in X. intro. destruct X0. 
apply prodpp_equal. exact (Eq_bis_def _ _ {| fst_2 := a; snd_2 := p |} {| fst_2 := a; snd_2 := p' |} (refl a) (X a p p')).
Defined.

(* Proposition thirteen : *)
Proposition contractible_with_prodpp (A : Type) (P :A -> Type) (a a' : A)(p : P a) (p' : P a') : 
(forall x : A, proposition (P x))-> (prodpp_def A P a p = prodpp_def A P a' p' )~=~ (a=a').
Proof.
intros. exists (encode_b A P a a' p p' X). exists (decode_b A P a a' p p' X) (decode_b A P a a' p p' X).
- intro. destruct x. unfold proposition in X. unfold decode_b. unfold encode_b. unfold "¤". unfold Id. simpl. (* utiliser Eq_bis que P est contractible, prodpp a=a' et Unit ~=~ a=a' *)
Admitted. 

(* End Propositions *)

(* You will notice that it's becoming litle hard for me.
 I wrote following lemmas but couldn't prove majority of them. *)

(* Section Sets *)

Definition set (A : Type) := forall x y : A, proposition (x=y).

Proposition eg_refl (A : Type) : forall x y : A, x=y <-> y=x.
Proof.
intros. split.
- intro. destruct X. apply refl.
- intro. destruct X. apply refl.
Defined.

Proposition for_fourteen (A : Type) (x y : A) (p q : x=y) :(forall x y : A, x=y) -> p=q.
Proof.
intros. destruct p. (* utiliser les lemmes du dessus *)
Admitted.

Proposition contractible_prop (A : Type) : contractible A -> proposition A.
Proof.
intros. destruct X. unfold proposition. intros. rewrite snd_4. apply (snd_4).
Defined.

Proposition proposition_set: forall A : Type, proposition A -> set A.
Proof.
intros.  unfold set.  intros. apply contractible_prop. apply (proposition_contrac). exact X.
Defined. 

Proposition set_Nat : set Nat.
Proof. (*on a montré 0 =0 ~=~Unit_Type *)
unfold set. intros. unfold proposition. intros. destruct x. 
- destruct y. 
+ Admitted.


Proposition set_R : set Ent_Rel.
Proof.
unfold set; intros. unfold proposition; intros. destruct x0. apply eg_refl . 
Admitted.

Proposition set_Bool : set (Booleans_Type).
Proof.
unfold set ;intros ; unfold proposition ; intros ; destruct x0 ; apply eg_refl . Admitted.


Proposition set_dependant (A : Type) (P : A -> Type) : set A -> set (forall x :A, P x).
Proof.
intro. unfold set in X. unfold set. intros. unfold proposition . intros. unfold proposition in X. destruct x0.
apply eg_refl. Admitted.

Proposition set_prodpp (A : Type) (P : A -> Type) : set A -> set (prodpp P).
Proof.
intros. unfold set.  intros. unfold proposition. intros. destruct x0.
apply eg_refl. Admitted.


(* End Set *)

(* Section Groupoids *)

Definition groupoids (A : Type) :=
forall x y : A, set (x=y).

Proposition groupoids_dependant (A : Type) (P : A -> Type) : groupoids A -> groupoids (forall x :A, P x).
Proof.
unfold groupoids. intros. unfold set. intros. unfold proposition. intros. destruct x1. apply eg_refl. Admitted. 


Proposition groupoids_prodpp(A : Type) (P : A -> Type) : groupoids A -> groupoids (prodpp P).
Proof.
unfold groupoids. intros. unfold set. intros. unfold proposition. intros. destruct x1. apply eg_refl. Admitted. 
(* End Groupoids *)

(* Section The_Types_Prop_Set_And_GPD *)

(* A vérifier définition et proposition : *)

Definition Prop_Type :=
prodpp (fun X : Type => proposition X).

Definition  Groupoids_Type :=
prodpp (fun X : Type => groupoids X).

Definition Set_Type :=
prodpp (fun X : Type => set X).


Proposition proposition_eg (X : Type) (p q : proposition X) : p=q.
Proof. 
unfold proposition in p. unfold proposition in q. 
Admitted.

Proposition set_eg (X : Type) (p q : set X) : p=q.
Proof.
unfold set in p. unfold set in q. simpl in p. unfold proposition in p. unfold proposition in q.
Admitted.

Proposition groupoids_eg (X : Type) (p q : groupoids X) : p=q.
Proof. 
unfold groupoids in p.
Admitted.

(* problème au niveau de l'égalité 
Proposition twenty_one_for_prop (X Y : Prop_Type) : X=Y ~=~  *)


Proposition set_prop : set Prop_Type.
Proof. 
unfold set. unfold Prop_Type. unfold proposition. intros. 
destruct x0. destruct x.  apply eg_refl.   
Admitted.

Proposition groupoids_set: groupoids Set_Type.
Proof.
unfold groupoids. unfold Set_Type. unfold set. unfold proposition.  intros.
destruct x. destruct y. destruct x0. destruct x1.  Admitted.

Proposition eg_eq (X Y : Prop) : (X = Y) ~=~(X <-> Y).
Proof.
Admitted.

(* End The_Types_Prop_Set_And_GPD *)

(* Section Propositionnal_Truncations *) (* Passé *)

(* Inductive Propositionnal_Truncation (A : Type) : Type := *)

(* End Propositionnal_Truncations *)

(* Section Set_Truncations_And_Beyond *)

(* Passé *)

(* End Set_Truncations_And_Beyond *)

(* 7 : Homotopy Groups And Fiber Sequences *)

(* Section Pointed_Types *)

Record Pointed_Types :=
Pointed_Types_def { fst_4 : Type ; star : fst_4}. (* Comment faire avec prdopp ? *)


Definition Maps (X Y : Pointed_Types) := 
prodpp (fun (f : fst_4 X -> fst_4 Y) => f (star X) = (star Y)). 

(* Lemma twenty_five (X Y : Pointed_Types) : (X=Y) ~=~ (X~=~ Y).
Proof.
Admitted. *)

Record Eq_Pointed_Types (X Y : Pointed_Types) (f g : fst_4 X -> fst_4 Y) :=
Eq_Pointed_Types_def { h : f=~g ; h_stars : f (star X) = g (star X)}.

Lemma twenty_six (X Y : Pointed_Types) ( f g : fst_4 X-> fst_4 Y) :
(f=g)~=~ Eq_Pointed_Types X Y f g.
Proof.
Admitted. 


Inductive sigma (A :Type)(B : A-> Type) : Type :=
pairs :forall x: A, B x -> sigma A B.

(* 
Lemma twenty_six (X Y : Pointed_Types) (f g : X -> Y) :
(f=g)~=~ prodpp (fun h : f=~g => *)

(* End Pointed_Types *)


(* Section Homotopy_Groups_Suspension_And_Sphere *)

(*
Definition Omega_Point_Types (X : Pointed_Types) :=
prodpp (fun (star X = star X : X=X ) => refl star). fonctionne pas *)

Record Loop_Space (X : Pointed_Types) :=
Loop_Space_def { preuve : star X = star X ; cue := refl star  }.

(* Record Suspension (X : Pointed_Types) :=
Suspension_def { suspension X ; N X} *)