(* Section 3 : Identity_Types_and_Grothendieck_Correspondance *)


(*Section 3.1: Types_As_Infty_Groupoids*)

Lemma refl {A} (x : A) : x=x.
Proof.
reflexivity.
Defined.

(* Lemma 1 *)
Lemma compose_path {A} {x y z : A} (p : x=y) (q: y=z ):   x=z.
Proof.
induction p. exact q.
Defined.

Notation "p  #  q " := (compose_path p q)(at level 40).
(* Lemma 2 *)
Lemma compose_path_with_refl {A : Type} {x y : A} (p : x=y) : compose_path (refl x) p = p.
Proof.
apply refl.
Defined.

(* Lemma 3 *)
Lemma asso_compose_path {A : Type} { a b c d : A} ( p : a=b)(q : b=c)(r : c=d) :(p # q) # r = p  # (q # r).
Proof.
destruct p. apply refl.
Defined.

(* Lemma 4 *)
Lemma inverse_path {A : Type} {x y: A} (p : x=y) : y=x.
Proof.
destruct p. apply refl.
Defined.

Notation " p ^(-1) " := (inverse_path p)( at level 40).

(* Lemma 5 *)
Lemma compose_with_inverse (A : Type) ( x y : A) (p : x=y) :  p # (p^(-1)) =refl x.
Proof.
destruct p. simpl. apply refl. 
Defined.

(* Bonus *)
Lemma inverse_refl (A : Type) (x: A) :  (refl x)^(-1) = refl x.
Proof.
simpl. apply refl.
Defined.


(* Section 3.2: Function_As_Morphisms_Of_Inf_Groupoid.*)

(* Lemma 6 *)
Lemma ap {A B: Type} {x y : A} (f : A-> B ) ( p : x = y) : f x = f y.
Proof.
destruct p. apply refl.
Defined.

(* Lemma 7 *)
Lemma ap_distrib {A B : Type} {x y z: A} (f : A -> B)(p : x=y) (q : y=z) :
 ap f (p  #  q) = (ap f p)  #  (ap f q).
Proof.
destruct p. apply refl.
Defined. 

(* Lemma 8 *)
Lemma ap_inverse { A B : Type } (f : A -> B) {x y :A } (p : x=y) :
 ap f (p ^(-1)) = (ap f p)^(-1).
Proof.
destruct p. apply refl.
Defined.


(* Section 3.3 : Type_Families_As_Families_Of_Inf_groupoids *)

(* Lemma 9 *)
Lemma Tr { A : Type} (B : A -> Type) (x y : A) (p : x=y) :
B x -> B y.
Proof.
destruct p. intro H. apply H.
Defined.

Definition compose_function {A B C} (g : B -> C) (f : A -> B) :=
  fun x : A => g (f x).

Notation " g $ f ":= (compose_function g f)(at level 40).

(* Lemma 10 *)
Lemma Tr_with_compose { A : Type} (B : A -> Type) {x y z :A }(p : x=y)(q : y=z) :
forall b : B x, ((Tr B y z q) $ (Tr B x y p)) b  = (Tr B x z (p # q)) b .
Proof.
intro. destruct p. apply refl. 
Defined.

(* Lemma 11 *)
Lemma apd {A : Type } (B : A -> Type) {x y : A}(p : x=y)(f :forall x:A, B x) :
Tr B x y p (f x) = f y.
Proof.
destruct p. apply refl.
Defined.


(* Section 3.4: Identities_In_Dependent_Function_Types*)

(* Definition 3 *)
Definition homotopy {A B : Type}( f g : A -> B ):=
forall x :A , f x = g x.

Notation "f =~ g " := (homotopy f g)(at level 40).

(* Definition 4 *)
Definition homotopy_2 {A : Type}(B : A -> Type) ( f g : forall x: A, B x):=
forall x : A, f x = g x. 

Notation " f =~2 g" := (homotopy_2 _ f g)(at level 40).

Definition Id (A : Type) :=
fun x: A => x.


(* Section 3.5 : Univalence_Axiom *)

(* Defintion 5 *)
Record isequiv (A B : Type) (f : A-> B) : Type :=
MakeEquiv {g1 : B->A ; g2 : B-> A ; inv_l : f $ g1 =~ Id B ; inv_r : g2 $ f =~ Id A }.

(* Lemma 12 *)
Lemma weak_functional_extensionality {A B} (f g : A -> B) : f=g -> forall x : A, f x = g x.
Proof.
intro p. destruct p. intros. apply refl.
Defined.

(* We now define the extensionality axiom, 
you always need to use it when you want to show that two function are equal *)
Axiom extensionality : forall A B : Type, forall f g : A -> B, isequiv (f=g) (forall x : A, f x = g x)(weak_functional_extensionality f g).

(* Consequences of extensionality : *)
Lemma functional_extensionality{A B} (f g : A -> B) : (forall x : A, f x = g x) -> f = g.
Proof.
intro X. apply extensionality. exact X.
Defined.

(* Lemma 13 , it is a litle bit tricky so we admit it *)
Lemma proof_on_equiv {A B : Type} (f : A -> B) : forall e1 e2 : isequiv A B f, e1 = e2.
Proof.
Admitted.

(* Remark 11 *)

(* We define isquasiequiv, two types which are "quasiequiv" have a bijection with the same inverse function *)
Record isquasiequiv (A B : Type) (f : A-> B ):=
MakeQuasiEquiv {iqe_l : B ->A ;iqe_mid : forall x : A,( iqe_l $ f ) (x) = x ; iqe_r : forall y : B, (f $ iqe_l) (y)=y}.

(* When you see "for_X" as the name of a lemma, it is an auxilary lemma useful for "X" *)

Lemma for_link (A B : Type) (f : A -> B) (g1 g2 : B -> A) :
(f $ g1 =~ Id B) -> (g2 $ f =~ Id A) -> g1 = g2.
Proof.
intros H H'. apply functional_extensionality.
intros. apply (@compose_path A (g1 x) (g2 (f (g1 x))) (g2 x)  ).
- apply inverse_path. apply (H' (g1 x)).
- apply (ap g2). exact (H x).
Defined.

Lemma for_link_2 (A B : Type) (f : A -> B) ( g1 g2 : B -> A) :
(g2 $ f) =~ Id A ->  g1 = g2 -> (g1 $ f) =~ Id A.
Proof.
intros H p. destruct p. exact H.
Defined.

Lemma isquasiequiv_imply_equiv (A B : Type) (f : A -> B) : (isquasiequiv A B f) -> (isequiv A B f).
Proof.
 intro X. destruct X. apply (MakeEquiv A B f iqe_l0 iqe_l0 ). 
+ unfold "=~". exact iqe_r0.
+ unfold "=~". exact iqe_mid0.
Defined.

Lemma isequiv_imply_isquasiequiv (A B : Type) (f : A -> B) : (isequiv A B f) -> (isquasiequiv A B f).
Proof.
intro X. destruct X. unfold "=~" in inv_l0. unfold "=~" in inv_r0. exists g3. 
+ apply (for_link_2 A B f g3 g4 inv_r0 (for_link A B f g3 g4 inv_l0 inv_r0)).
+ exact inv_l0.
Defined.

(* Definition 6 *)
(* Two types are called equivalent when there is a bijection between them *)

Record Type_equiv (A B : Type) :=
Make_Type_equiv { first : A-> B ; second : isequiv A B first}.

Notation " A ~=~ B" := (Type_equiv A B)(at level 40).

(* Now, as we did with the extensionality, we defined a function who would be an equivalence *)
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
intros A B X. apply univalence. apply X.
Defined.


(* Section 3.6 : Identities_In_Dependent_Product_Types *)

(* We defined Eq (x ; y) (x' ; y') as inhabited by proofs that x=x' and y = y'*)
Definition Eq (A B : Type) (z z' : A * B) := prod (fst z=fst z') (snd z=snd z').

(* When we want to prove equivalent for identity types, we use the "encode-decode method" *)
Lemma encode { A B } : forall z z'  : prod A B, z=z'-> Eq A B z z'.
Proof.
intros z z' X. induction X. split.
- apply refl. 
- apply refl.
Defined.

Lemma decode {A B} : forall z z' : prod A B, Eq A B z z' -> z=z'.
Proof.
intros z z' X. induction z. induction z'. 
destruct X as (x,x'). simpl in x. simpl in x'.
destruct x. destruct x'. apply refl.
Defined.

(* Proposition 1 *)
(* Pairs of elements are equal iff their components are equal *)
Proposition pair_equal (A B : Type) (z z' : prod A B): (z=z') ~=~ Eq A B z z'.
Proof.
exists (encode z z').  exists (decode z z') (decode z z').
- unfold "=~". intro X. induction z. induction z'. destruct X as (x,x'). 
simpl in x. simpl in x'.
destruct x. destruct x'. apply refl. 
- unfold "=~". intro X. destruct X. destruct z. apply refl.
Defined.

(* Definition of the dependent product *)
(* This definition is very important and will be pretty useful *)
Record prodpp {A : Type} (B : A -> Type) :=
prodpp_def {fst_2 : A ; snd_2 : B fst_2 }.

(* We use "encode-decode" to analyse identity types in dependent products *)

(* We define Eq_bis ( x ; y ) ( x' ; y' ) as the type of proofs that x = x' and y = y', which require a transport to be well-typed *)
Definition Eq_bis {A : Type} ( B : A -> Type) (z z' :  prodpp B) :=
prodpp (fun p : fst_2 B z = fst_2 B z' => Tr B _ _ p (snd_2 B z) = snd_2 B z').

(* We define encode and decode, as for prod *)
Lemma encode_bis {A} (B : A -> Type) : forall z z' : prodpp B, z=z' -> Eq_bis B z z'.
Proof.
intros z z' X. induction X. exists (refl _). apply refl.
Defined.

Lemma decode_bis {A} (B : A -> Type) : forall z z' : prodpp B, Eq_bis B z z' -> z=z'.
Proof.
intros z z' X. induction z. induction z'. destruct X as (fst_6,snd_6). 
simpl in fst_6. simpl in snd_6. destruct fst_6. destruct snd_6. apply refl.
Defined.

(* And now we show that encode and decode are inverses to get our equivalence *)
(* Lemma 14 *)
Lemma prodpp_equal {A : Type} (B : A-> Type) (z z' : prodpp B) :
(z=z') ~=~ Eq_bis B z z'.
Proof.
exists (encode_bis B z z'). exists (decode_bis B z z') (decode_bis B z z'). 
- unfold "=~". intro. induction z. induction z'. destruct x as (fst_6,snd_6). simpl in fst_6. simpl in snd_6. simpl. destruct fst_6. destruct snd_6. apply refl.
- unfold "=~". intro X. destruct X. destruct z. apply refl.
Defined.


(* Section 3.7 : Using_univalence *)

(* We need many auxilary lemma about equivalences in this section *)

Lemma equiv_compose {A B C : Type} (f : A -> B) (g : B -> C) :
isequiv A B f -> isequiv B C g -> isequiv A C (g $ f).
Proof.
intros e1 e2. destruct e1 as (f1,f2,i1,i2). destruct e2 as (g1,g2,j1,j2). exists (f1 $ g1) (f2 $ g2).
- intro x. apply (fun p => compose_path p (j1 x)). apply (ap g). apply (i1 (g1 x)).
- intro x. apply (fun p => compose_path p (i2 x)). apply (ap f2). apply (j2 (f x)).
Defined.

Lemma equiv_transitivity {A B C : Type} : A~=~B -> B~=~C -> A~=~C.
Proof.
intros e1 e2. destruct e1 as (e1,eqe1). destruct e2 as (e2,eqe2).
exists (e2 $ e1). apply equiv_compose.
- apply eqe1.
- apply eqe2.
Defined.

Lemma equiv_sym {A B : Type} : A ~=~ B -> B ~=~ A.
Proof.
Admitted.

Lemma equiv_prodpp_left {A A' : Type} (B : A' -> Type) (f : A -> A') :
isequiv A A' f -> prodpp (B $ f) ~=~ prodpp B.
Proof.
Admitted.

Lemma equiv_prodpp_right {A : Type} (B B' : A -> Type) :
(forall x:A, B x ~=~ B' x) -> prodpp B ~=~ prodpp B'.
Proof.
intro H. apply ua. apply (ap prodpp). apply functional_extensionality. intro x. apply (weak_univalence (B x) (B' x)). apply (H x).
Defined.

(* Definition 7 *)
Definition U_over (B : Type) :=
prodpp (fun A : Type => A -> B).

Definition elmt_U_over {B A: Type} (f : A -> B) :=
prodpp_def Type (fun A : Type  => (A -> B)) A f.

(* In the end we want identity types in U_over equivalent to Eq_U_over*)
Definition Eq_U_over {A A' B} (f : A -> B) (g : A' -> B): Type :=
prodpp (fun e : A~=~ A' => f =~ (g $ (first A A' e))).

(* We give some auxiliary types *)
Definition Eq_U_over_1 {A A' B} (f : A -> B) (g : A' -> B) :=
prodpp (fun e : A = A' => Tr (fun C : Type => C -> B) A A' e f  = g).

Definition Eq_U_over_2 {A A' B} (f : A -> B) (g : A' -> B) :=
prodpp (fun e : A = A' => f  = g $ (first A A' (ua e))).

Definition Eq_U_over_3 {A A' B} (f : A -> B) (g : A' -> B) :=
prodpp (fun e : A ~=~ A' => f  = g  $  (first A A' e)).

(* Now we prove a chain of equivalence *)
Lemma for_fifteen_1  {A A' B} (f : A -> B) (g : A' -> B) :
(elmt_U_over f = elmt_U_over g) ~=~ Eq_U_over_1 f g.
Proof.
apply prodpp_equal.
Defined.

Lemma for_fifteen_2  {A A' B} (f : A -> B) (g : A' -> B) :
Eq_U_over_1 f g ~=~ Eq_U_over_2 f g.
Proof.
apply equiv_prodpp_right. intro x. destruct x. apply (ua (refl _)).
Defined.

Lemma for_fifteen_3 {A A' B} (f : A -> B) (g : A' -> B) :
Eq_U_over_2 f g ~=~ Eq_U_over_3 f g.
Proof.
apply (equiv_prodpp_left (fun e:A ~=~ A' =>  f  = g  $  (first A A' e)) ua). apply univalence.
Defined.

Lemma for_fifteen_4 {A A' B} (f : A -> B) (g : A' -> B) :
Eq_U_over_3 f g ~=~ Eq_U_over f g.
Proof.
apply equiv_prodpp_right. intro x. 
exists (weak_functional_extensionality f (g  $  first A A' x)). apply extensionality.
Defined.

(* Lemma 15 *)
Lemma fifteen { A A' B} (f : A -> B) (g : A' -> B) :
((elmt_U_over f) = (elmt_U_over g) )~=~ Eq_U_over f g.
Proof.
apply (equiv_transitivity (for_fifteen_1 f g)).
apply (equiv_transitivity (for_fifteen_2 f g)).
apply (equiv_transitivity (for_fifteen_3 f g)).
apply (for_fifteen_4 f g).
Defined.



(* Section 3.8 : Grothendieck_correspondance_for_type.*)

Definition p1 {Y}(P : Y -> Type) :=
fun z : prodpp P => fst_2 P z.

(* Function psi from Lemma 16 *)
Definition psi (Y : Type) (P : Y -> Type) (b  : Y) : 
prodpp (fun z : prodpp P => p1 P z = b) -> (P b).
Proof.
intro X. destruct X as (fst_4,snd_4). destruct snd_4. destruct fst_4 as (fst_3,snd_3). unfold p1. exact snd_3.
Defined.

(* Function phi from Lemma 16 *)
Definition phi (Y : Type) (P : Y -> Type) (b  : Y) :
(P b) -> prodpp (fun z : prodpp P => p1 P z = b). 
Proof.
intros. apply (prodpp_def (prodpp P) (fun z : prodpp P => p1 P z = b) (prodpp_def Y P b X) (refl b)).
Defined.

(* Lemma 16, useful for the Grothendieck's theorem *)
Lemma sixteen (Y : Type) ( P : Y -> Type) ( b : Y) :
prodpp (fun z : prodpp P => p1 P z = b) ~=~ (P b).
Proof.
exists (psi Y P b ). exists (phi Y P b ) (phi Y P b ).
- unfold "=~". intros. apply refl.
- unfold "=~". intro X. destruct X as (fst_4,snd_4). destruct snd_4. destruct fst_4. apply refl.
Defined.

(* We strenghten Lemma 16 using univalence *)
Lemma sixteen_b (Y : Type) (P : Y -> Type) ( b y : Y) :
prodpp (fun z : prodpp P => p1 P z = b) = (P b).
Proof.
apply univalence. apply (sixteen Y P b ).
Defined.

(* Definition 8 *)
Definition fib (X Y : Type) (f : X -> Y)(y : Y) :=
prodpp (fun x: X => f x = y). 

(* Function psi from Theorem 1 *)
Definition phi_bis (Y : Type) : U_over Y  -> (Y -> Type).
Proof.
intro. destruct X as (fst_4,snd_4). exact (fib fst_4 Y snd_4).
Defined.

(* Function phi from Theorem 1 *)
Definition psi_bis (Y : Type) : (Y -> Type) -> U_over Y.
Proof.
intro. unfold U_over. exists (prodpp X). exact (p1 X).
Defined.

(* Function epsilon from Theorem 1 *)
Definition epsilon {X Y}(f : X -> Y) : X -> prodpp (fib X Y f).
Proof.
intro x. unfold fib. exact ( prodpp_def  _ _ (f x) (prodpp_def X (fun x0 : X => f x0 = f x)  (x) (refl (f x)))).
Defined.

(* Inverse to epsilon *)
Definition epsilon_inv {X Y} (f : X -> Y) : prodpp (fib X Y f) -> X.
Proof.
intro H. destruct H as (fst_4,snd_4). unfold fib in snd_4. destruct snd_4 as(fst_5,snd_5). exact fst_5.
Defined.

Lemma epsi_and_inv {X Y} (f : X -> Y) (z : prodpp (fib X Y f)) : ((epsilon f)  $  (epsilon_inv f)) z = z.
Proof.
unfold " $ ". unfold epsilon. unfold epsilon_inv. destruct z as (fst_4,snd_4). destruct snd_4 as (fst_5,snd_5). destruct snd_5. apply refl.
Defined.

Lemma inv_and_epsi {X Y} (f : X -> Y) (x : X) :(( epsilon_inv f ) $  (epsilon f )) x = x.
Proof.
unfold " $ ". unfold epsilon. unfold epsilon_inv. apply refl.
Defined.

Lemma for_Grothendieck_2 (Y : Type) (X: Type) (f : X -> Y) :
X~=~prodpp (fib X Y f).
Proof.
exists (epsilon f). exists (epsilon_inv f) (epsilon_inv f).
- unfold "=~". intros. unfold Id. apply epsi_and_inv.
- unfold "=~". intros. unfold Id. apply inv_and_epsi.
Defined.

Lemma for_Grothendieck_2_2 (Y : Type) (X: Type) (f : X -> Y) :
prodpp (fib X Y f) ~=~ X.
Proof.
exists (epsilon_inv f). exists (epsilon f) (epsilon f).
- unfold "=~". intros. unfold Id. apply inv_and_epsi.
- unfold "=~". intros. unfold Id. apply epsi_and_inv.
Defined.

Lemma for_Grothendieck_1  (Y : Type) (X: Type) ( f : X -> Y) :
prodpp (fib X Y f) = X .
Proof.
apply inverse_path. apply univalence. exact (for_Grothendieck_2 Y X f).
Defined.

Lemma for_Grothendieck_3 (Y : Type)(fst_4 : Type) (snd_4 : fst_4 -> Y)(e := for_Grothendieck_2_2 Y fst_4 snd_4):
p1 (fib fst_4 Y snd_4) =~
   (snd_4  $  first (prodpp (fib fst_4 Y snd_4)) fst_4 e). 
Proof.
intro. destruct x as (fst_5,snd_5). unfold " $ ". unfold p1. unfold fib. destruct snd_5 as (fst_6,snd_6). destruct snd_6. simpl.
 apply refl. 
Defined.

Lemma for_Grothendieck_4 (Y : Type) (P : Y -> Type) (x : Y) :
(prodpp (fun x0 : prodpp P => fst_2 P x0 = x) )~=~ (P x).
Proof.
apply (fun z => equiv_transitivity z (sixteen Y P x)). 
unfold p1. exists (Id _). exists (Id _) (Id _).
+ intro. apply refl.
+ intro. apply refl.
Defined.

Lemma for_Grothendieck_5 (Y : Type) (x : Y -> Type) :
(fun y : Y => prodpp (fun x0 : prodpp x => fst_2 x x0 = y)) = x.
Proof.
apply functional_extensionality. intro. apply univalence. apply for_Grothendieck_4.
Defined.

(* Grothendieck's Theorem, theorem 1 in courses *)
Theorem Grothendieck { Y}  : (Y -> Type) ~=~ U_over Y.
Proof.
exists (psi_bis Y). exists (phi_bis Y) (phi_bis Y).
- intro. unfold " $ ". destruct x as (fst_4,snd_4). unfold psi_bis. unfold phi_bis. unfold p1. unfold fib. unfold Id.
apply fifteen. exact (prodpp_def _ _ (for_Grothendieck_2_2 Y fst_4 snd_4) (for_Grothendieck_3 Y fst_4 snd_4 )).
- unfold "=~". intro. unfold " $ ". unfold psi_bis. unfold phi_bis. unfold p1. unfold fib. unfold Id.  apply for_Grothendieck_5.
Defined.
