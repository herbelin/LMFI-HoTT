Require Import HoTT.
Require Import Reals.
Require Import Arith.
Require Import Coq.Reals.Reals.
Open Scope nat_scope.
Require Import Bool.

(* To begin, we introduce a few definitions 
that will be useful for the rest of the program. *)

(* I named Section in "()" because inside section, 
definition that you make are local definition 
and we want them as global definition *)

(* The section below corresponds to definition and to the chapter 3.1 
of notations *)

(* Section Some_Inf_Groupoid_By_Path_Induction. *)

Lemma refl {A} (x : A) : x=x.
Proof.
reflexivity.
Defined.

(* Number one : *)
Lemma compose_path {A} {x y z : A} (p : x=y) (q: y=z ):   x=z.
Proof.
induction p. exact q.
Defined.

Notation "p ° q " := (compose_path p q)(at level 40).
(* Number two *)
Lemma compose_path_with_refl {A : Type} {x y : A} (p : x=y) : compose_path (refl x) p = p.
Proof.
unfold compose_path. simpl. apply refl.
Defined.

(* number three *)
Lemma asso_compose_path {A : Type} { a b c d : A} ( p : a=b)(q : b=c)(r : c=d) :(p°q)°r = p °(q°r).
Proof.
induction p. induction q. induction r. simpl. apply refl.
Defined.

(* Number four : *)
Lemma inverse_path {A : Type} {x y: A} (p : x=y) : y=x.
Proof.
induction p. apply refl.
Defined.

Notation " p ^(-1) " := (inverse_path p)( at level 40).

(* Lemma number five *)
Lemma compose_with_inverse (A : Type) ( x y : A) (p : x=y) :  p°(p^(-1)) =refl x.
Proof.
induction p. simpl. apply refl. 
Defined.

(* Bonus : *)
Lemma inverse_refl (A : Type) (x: A) :  (refl x)^(-1) = refl x.
Proof.
simpl. apply refl.
Defined.

(* End Some_Inf_Groupoid_By_Path_Induction. *)

(* The section below corresponds to the part 3.2 *)
(* Section Function_As_Morphisms_Of_Inf_Groupoid. *)

(* number six :*)
Lemma ap {A B: Type} {x y : A} (f : A-> B ) ( p : x = y) : f x = f y.
Proof.
induction p. apply refl.
Defined.

(* Number seven : *)
Lemma ap_distrib {A B : Type} {x y z: A} (f : A -> B)(p : x=y) (q : y=z) :
 ap f (p ° q) = (ap f p) ° (ap f q).
Proof.
induction p. induction q. simpl. apply refl.
Defined. 

(* Number eight *)
Lemma ap_inverse { A B : Type } (f : A -> B) {x y :A } (p : x=y) :
 ap f (p ^(-1)) = (ap f p)^(-1).
Proof.
induction p. simpl. apply refl. 
Defined.

(* End Function_As_Morphisms_Of_Inf_Groupoid *)

(* The section below correspond to the part 3.3 of the courses *)
(* Section Type_Families_As_Families_Of_Inf_groupoids *)

(* Lemma number_nine *)
Lemma Tr { A : Type} (B : A -> Type) (x y : A) (p : x=y) :
B x -> B y.
Proof.
induction p. intro H. apply H.
Defined.

Definition compose_function {A B C} (g : B -> C) (f : A -> B) :=
  fun x : A => g (f x).

Notation " g ¤ f ":= (compose_function g f)(at level 40).

(* Lemma number ten *)
Lemma Tr_with_compose { A : Type} (B : A -> Type) {x y z :A }(p : x=y)(q : y=z) :
forall b : B x, ((Tr B y z q)¤(Tr B x y p)) b  = (Tr B x z (p°q)) b .
Proof.
intro. 
induction p. 
induction q. unfold compose_function. simpl. apply refl.
Defined.


(*Lemma Number_eleven *)
Lemma apd {A : Type } (B : A -> Type) {x y : A}(p : x=y)(f :forall x:A, B x) :
Tr B x y p (f x) = f y.
Proof.
induction p. unfold Tr. simpl. apply refl.
Defined.


 (* End Type_Families_As_Families_Of_Inf_Groupoids *)

(* The section below correspond to the part 3.4 *)
(* Section Identities_In_Dependent_Function_Types*)

(* Definition three *)
Definition homotopy {A B : Type}( f g : A -> B ):=
forall x :A , f x = g x.

Notation "f =~ g " := (homotopy f g)(at level 40).

(* Bonus *)
Definition homotopy_2 {A : Type}(B : A -> Type) ( f g : forall x: A, B x):=
forall x : A, f x = g x. 

Notation " f =~2 g" := (homotopy_2 _ f g)(at level 40).

Definition Id (A : Type) :=
fun x: A => x.

(* End Identities_In_Dependent_Function_Types *)

(* The section below corresponds to the part 3.5 *)
(* Section Univalence_Axiom *)

(* Intituively, an equivalence between two 
Type is a bijection between those two types,
 that's what we defined here : *)

Record isequiv (A B : Type) (f : A-> B) : Type :=
MakeEquiv {g1 : B->A ; g2 : B-> A ; inv_l : ( f¤g1)=~(Id B); inv_r : (g2¤f) =~(Id A)}.

(* We will use the lemma number twelve a litle bit later so i skipped it for the moment, 
if you want to find it you can search near the extensionality *)
(* Lemma number thirteen , it is a litle bit tricky so we admitted it *)
Lemma proof_on_equiv {A B : Type} (f : A -> B) : forall e1 e2 : isequiv A B f, e1 = e2.
Proof.
intros. induction e1. induction e2. simpl.  Admitted.

(* We define isquasiequiv, two types 
which are "quasiequiv" have a bijection with the same inverse function : *)
Record isquasiequiv (A B : Type) (f : A-> B ):=
MakeQuasiEquiv {iqe_l : B ->A ;iqe_mid : forall x : A,( iqe_l ¤ f ) (x) = x ; iqe_r : forall y : B, (f ¤ iqe_l) (y)=y}.

(* An useful one : *)
Lemma asso_compose_function (A B C D: Type) (f : A -> B) (g : B-> C) (h : C -> D) :forall x : A, ( h¤(g¤f))x =( (h¤g)¤f)x.
Proof.
intros. unfold "¤". apply refl.
Defined.

(* Lemma twelve : *)
Lemma weak_functional_extensionality {A B} (f g : A -> B) : f=g -> forall x : A, f x = g x.
Proof.
intros. destruct X. apply refl.
Defined.

(* We now define the extensionality axiom, you always need to use it 
when you want to show that two function are equal :*)
Axiom extensionality : forall A B : Type, forall f g : A -> B, isequiv (f=g) (forall x : A, f x = g x)(weak_functional_extensionality f g).

(* Consequences of extensionality : *)
Lemma functional_extensionality{A B} (f g : A -> B) : (forall x : A, f x = g x) -> f = g.
Proof.
intros. apply extensionality . exact X.
Defined.

(* When you see "for" in a lemma, 
it means that this lemma is useful for a bigger one, 
it's just an intermediate outcome.
 The name after the "for" is the name of the lemma where we use it *)

Lemma for_link (A B : Type) (f : A -> B) ( g1 g2 : B -> A)
 (p : (forall x :B ,(f¤g1) x= Id B x )) (q : (forall x : A, (g2¤f) x=Id A x )) : g1=g2.
Proof.
intros.  unfold "¤" in p. unfold "¤" in q.  unfold Id in p. unfold Id in q. apply functional_extensionality.
intros. apply (@compose_path A (g1 x) (g2 (f (g1 x))) (g2 x)  ).
- apply inverse_path. apply (q (g1 x)).
- rewrite (p x). apply refl.
Defined.

Lemma for_link_2 (A B : Type) (f : A -> B) ( g1 g2 : B -> A)
 (p : (forall x :B ,(f¤g1) x= Id B x )) (q : (forall x : A, (g2¤f) x=Id A x )) : 
(g1 = g2) -> (forall x : A,(g1 ¤ f) x = Id A x).
Proof.
intro X. destruct X. exact q.
Defined.

(* The previous lemma stand for : *)
Lemma link_bewtween_isequiv_isquasiequiv (A B : Type) (f : A -> B) : isquasiequiv A B f <-> isequiv A B f.
Proof.
split. 
- intros. destruct X. apply (MakeEquiv A B f iqe_l0 iqe_l0 ). 
+ unfold "=~". exact iqe_r0.
+ unfold "=~". exact iqe_mid0.
- intros. destruct X. unfold "=~" in inv_l0. unfold "=~" in inv_r0. 
exists g3. 
+ apply (for_link_2 A B f g3 g4 inv_l0 inv_r0 (for_link A B f g3 g4 inv_l0 inv_r0)).
+ exact inv_l0.
Defined.

(* Definition Six *)
(* Two types are called equivalents when there is a bijection between them *)
Record Type_equiv (A B : Type) :=
Make_Type_equiv { first : A-> B ; second : isequiv A B first}.

Notation " A ~=~ B" := (Type_equiv A B)(at level 40).

(* This one is just a trivial results : *)
Lemma homotpy_for_id (A : Type) : (Id A) ¤ (Id A) =~ Id A.
Proof.
intro. unfold compose_function. unfold Id. apply refl.
Defined.

(* Now, as we did with the extensionality,
 we defined a function who would be an equivalence *)
Definition ua {A B} :   A = B -> A ~=~ B.
Proof.
intros f.
destruct f.
exists (Id A).
now exists (Id A) (Id A).
Defined.

(* The very important univalence Axiom : *)
Axiom univalence  : forall A B : Type, isequiv (A=B) (A~=~B) ua. 

(* Consequence of this axiom : *)
Lemma weak_univalence : forall A B : Type, A~=~B -> A=B.
Proof.
intros. apply univalence. apply X.
Defined.

(* Useful later, it's the same that ua, juste because i needed it to be organised *)
Lemma weak_univalence_2 : forall A B : Type, A = B -> A ~=~B.
Proof.
intros.
destruct X. 
exists (Id A). exists (Id A) (Id A).
- unfold "=~". apply refl.
- unfold "=~". apply refl.
Defined.

(* End Univalence_Axiom *)

(* Now, we're going to see when can we say that two elements of Types can be equal *)
(* The section below correspond to the section 3.6 *)
(* Section Identities_In_Dependent_Product_Types *)

(* We defined Eq to prove that
 two elements (x ; y) (x' ; y') are equal when x=x' and y = y'*)
Record Eq( A B : Type) (z z' : A * B) :=
Eq_def {fst_1 : fst z=fst z' ; snd_1 : snd z=snd z'}.

(* When we want to prove equivalent between types, 
we use the "encode-decode method" wich
 create a bijection between them both *)
Lemma encode { A B } : forall z z'  : prod A B, z=z'->Eq A B z z'.
Proof.
intros. induction X. apply Eq_def.
- apply refl. 
- apply refl.
Defined.

Lemma decode {A B} : forall z z' : prod A B, Eq A B z z' -> z=z'.
Proof.
intros. induction z. induction z'. destruct X. simpl in fst_2. simpl in snd_2. induction fst_2. induction snd_2. apply refl.
Defined.

(* Now, we show that 2 pair are equal if their composants are equal : *)
(* That's proposition One *)
Proposition pair_equal (A B : Type) (z z' : prod A B): (z=z') ~=~ Eq A B z z'.
Proof.
exists (encode z z').  exists (decode z z') (decode z z').
- unfold "=~". intros. induction z. induction z'. destruct x. simpl in fst_2. simpl in snd_2. simpl.
induction fst_2. induction snd_2. apply refl. 
- unfold "=~". intros. induction x. apply refl.
Defined.

(* This definition is very important and will be pretty useful. 
We defined dependents Types as : *)
Record prodpp {A : Type} (B : A -> Type) :=
prodpp_def {fst_2 : A ; snd_2 : B fst_2 }.

(* In order to caracterize dependants Types inside this new Types,
 we need to do as prod with Eq : *)
(* It means that (z ; B z) = (z' ; B z') if only (z = z')
 and the transport long that (z = z') of B z is equal to B z' *)
Record Eq_bis {A : Type} ( B : A -> Type) (z z' :  prodpp B) :=
Eq_bis_def { fst_3 : fst_2 B z=fst_2 B z' ; snd_3 : Tr B (fst_2 B z) (fst_2 B z') fst_3 (snd_2 B z) =snd_2 B z' }.

(* We define encode and decode, as prod *)
Lemma encode_bis {A} (B : A -> Type) : forall z z' : prodpp B, z=z' -> Eq_bis B z z'.
Proof.
intros. induction X. apply (Eq_bis_def A B z z (refl (fst_2 B z))). apply refl.
Defined.

Lemma decode_bis {A} (B : A -> Type) : forall z z' : prodpp B, Eq_bis B z z' -> z=z'.
Proof.
intros. induction z. induction z'. destruct X. 
simpl in fst_6. simpl in snd_6. induction fst_6. induction snd_6. apply refl.
Defined.

(* And now we show that encode and decode are inverse to get our equivalence *)
(* Lemma fourteen *)
Lemma prodpp_equal {A : Type} (B : A-> Type) (z z' : prodpp B) :
(z=z') ~=~ Eq_bis B z z'.
Proof.
exists (encode_bis B z z'). exists (decode_bis B z z') (decode_bis B z z'). 
- unfold "=~". intro. induction z. induction z'. destruct x. simpl in fst_6. simpl in snd_6. simpl. induction fst_6. induction snd_6. apply refl.
- unfold "=~". intro X. destruct X. apply refl.
Defined.

(* End Identities_In_Dependent_Product_Types *)

(* We Now ended the part 3.6. The following part "Using Univalences "
 is a big tricky and is useful to the Grothendieck's theorem, 
so you can find the following parts in "Grothendieck.v" *)
