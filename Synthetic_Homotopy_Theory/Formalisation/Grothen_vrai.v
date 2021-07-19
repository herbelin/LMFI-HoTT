Require Import Beginning_until_Grothendieck.

(* I couldn't do a makefile so i took previous definition, 
i also add a few of them, which are pretty useful to prove things *)

(* Begin definition *)
Lemma refl {A} (x : A) : x=x.
Proof.
reflexivity.
Defined.

Definition homotopy {A B : Type}( f g : A -> B ):=
forall x :A , f x = g x.

Notation "f =~ g " := (homotopy f g)(at level 40).

Definition compose_function {A B C} (g : B -> C) (f : A -> B) :=
  fun x : A => g (f x).

Notation " g \u00a4 f ":= (compose_function g f)(at level 40).

Definition Id (A : Type) :=
fun x: A => x.

Record isequiv (A B : Type) (f : A-> B) : Type :=
MakeEquiv {g1 : B->A ; g2 : B-> A ; inv_l : ( f\u00a4g1)=~(Id B); inv_r : (g2\u00a4f) =~(Id A)}.

Lemma weak_functional_extensionality {A B} (f g : A -> B) : f=g -> forall x : A, f x = g x.
Proof.
intros. destruct X. apply refl.
Defined.

Axiom extensionality : forall A B : Type, forall f g : A -> B, isequiv (f=g) (forall x : A, f x = g x)(weak_functional_extensionality f g).

Lemma functional_extensionality{A B} (f g : A -> B) : (forall x : A, f x = g x) -> f = g.
Proof.
intros. apply extensionality . exact X.
Defined.

Lemma compose_asso {A B C D} (f : A -> B) ( g : B -> C) (h : C -> D) : h \u00a4 (g \u00a4 f ) = (h \u00a4 g) \u00a4 f.
Proof.
unfold "\u00a4".
apply refl.
Defined.

Lemma compose_asso_2 {A B C D} (f : A -> B) ( g : B -> C) (h : C -> D) :(h \u00a4 g) \u00a4 f = h \u00a4 (g \u00a4 f ).
Proof.
unfold "\u00a4".
apply refl.
Defined.

Record Type_equiv (A B : Type) :=
Make_Type_equiv { first : A-> B ; second : isequiv A B first}.

Notation " A ~=~ B" := (Type_equiv A B)(at level 40).

Lemma equiv_refle {A} : A~=~A.
Proof.
exists (Id A). exists (Id A) (Id A).
- intro ; apply refl.
- intro ; apply refl.
Defined.

Lemma Id_and_hom {A B} (f : A -> B)(g : B -> A) :  (f \u00a4 g)  =~ Id B -> (f \u00a4 g) = Id B.
Proof.
intros. apply functional_extensionality. unfold "=~" in X. exact X.
Defined.

Lemma compose_with_Id {A B C} (f : B -> A)(g : C -> B) : (f \u00a4 (Id B \u00a4 g)) = (f \u00a4 g).
Proof. 
apply functional_extensionality. intro. unfold "\u00a4". apply refl.
Defined.

Lemma compose_with_Id_2 {A B } (f : A -> B) : f\u00a4Id A = f.
Proof. 
unfold "\u00a4". unfold Id. apply functional_extensionality. intro ; apply refl.
Defined.

Lemma equiv_transitivity (A B C : Type) : A~=~B -> B~=~C -> A~=~C.
Proof. 
intros. destruct X. destruct X0. destruct second0. destruct second1. unfold "=~" in inv_l0. unfold "=~" in inv_r1. 
exists (first1 \u00a4 first0). exists (g3 \u00a4 g5) (g4 \u00a4 g6).
- unfold "=~". intro. rewrite (compose_asso g5 g3 (first1 \u00a4 first0)). 
rewrite (compose_asso_2  g3 first0 first1). apply weak_functional_extensionality. 
apply Id_and_hom in inv_l0. rewrite inv_l0. rewrite compose_asso_2. rewrite compose_with_Id. apply functional_extensionality. exact inv_l1.
- unfold "=~". intro. rewrite (compose_asso_2 (first1 \u00a4 first0) g6 g4). 
rewrite (compose_asso first0 first1 g6). apply weak_functional_extensionality. 
apply Id_and_hom in inv_r1. rewrite inv_r1. rewrite compose_with_Id. apply functional_extensionality.
exact inv_r0.
Defined.

Definition ua {A B} :   A = B -> A ~=~ B.
Proof.
intros f.
destruct f.
exists (Id A).
now exists (Id A) (Id A).
Defined.

Axiom univalence  : forall A B : Type, isequiv (A=B) (A~=~B) ua. 

Definition uni {A B} : A~=~ B -> A = B.
Proof.
intro. apply univalence in X. exact X.
Defined.

Lemma eg_refl {A B : Type} : A = B <-> B = A.
Proof.
split. 
- intro ; destruct X ; apply refl.
- intro ; destruct X ; apply refl.
Defined.

Lemma equiv_refl {A B : Type} : A~=~B <-> B~=~A.
Proof.
split.
- intro. apply univalence in X. apply eg_refl in X. apply (ua X).
- intro. apply univalence in X. apply eg_refl in X. apply (ua X).
Defined.

Record prodpp {A : Type} (B : A -> Type) :=
prodpp_def {fst_2 : A ; snd_2 : B fst_2 }.

Lemma Tr { A : Type} (B : A -> Type) (x y : A) (p : x=y) :
B x -> B y.
Proof.
induction p. intro H. apply H.
Defined.

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

(* End of definition *)


(* We now defined new type to prove the lemma fifteen *)
(* In order to prove it, we are going to 
create new type to show that there are equivalent to each other *)

Definition eq_with_equiv {A A' B} (f : A -> B) (g : A' -> B): Type :=
prodpp (fun e : A~=~ A' => f=~ (g\u00a4(first A A' e))).

Definition eq_with_eq {A A' B} (f : A -> B) (g : A' -> B) :=
prodpp (fun e : A = A' => Tr (fun C : Type => C -> B) A A' e f  = g).

Definition U_over_set (B : Type) :=
prodpp (fun A : Type => A -> B).

Definition elmt_U_ov_set (B A: Type) (f : A -> B) :=
prodpp_def Type (fun A : Type  => (A -> B)) A f.

Lemma encode_1 {A A' B} ( f : A -> B) (g : A' -> B) :
((elmt_U_ov_set B A f) = (elmt_U_ov_set B A' g) ) -> eq_with_eq f g.
Proof.
intro. unfold elmt_U_ov_set in X. apply prodpp_equal in X. destruct X. simpl in fst_4. simpl in snd_4. unfold eq_with_eq. 
exact (prodpp_def _ (fun e : A = A' => Tr (fun C : Type => C -> B) A A' e f = g) fst_4 snd_4).
Defined.

Lemma decode_1 {A A' B} ( f : A -> B) (g : A' -> B) :
eq_with_eq f g -> ((elmt_U_ov_set B A f) = (elmt_U_ov_set B A' g) ).
Proof.
intros. unfold eq_with_eq in X. unfold elmt_U_ov_set. apply prodpp_equal. destruct X. exact (Eq_bis_def Type (fun C : Type => C -> B) {| fst_2 := A; snd_2 := f |}
  {| fst_2 := A'; snd_2 := g |} fst_4 snd_4).
Defined.

Lemma for_for_fifteen_1 {A A' B}(f : A -> B) ( g : A' -> B):
((prodpp_def Type (fun X : Type => X -> B) A f) = (prodpp_def Type (fun X : Type => X -> B) A' g))~=~ (Eq_bis (fun X : Type => X -> B) (prodpp_def Type (fun X : Type => X -> B) A f) (prodpp_def Type (fun X : Type => X -> B) A' g)).
Proof.
apply prodpp_equal.
Defined.

Lemma for_for_fifteen_2 {A A' B}(f : A -> B) ( g : A' -> B):
((prodpp_def Type (fun X : Type => X -> B) A f) = (prodpp_def Type (fun X : Type => X -> B) A' g)) -> (Eq_bis (fun X : Type => X -> B) (prodpp_def Type (fun X : Type => X -> B) A f) (prodpp_def Type (fun X : Type => X -> B) A' g)).
Proof.
apply prodpp_equal.
Defined.

Lemma encodee_1 {A A' B} (f : A -> B) (g : A' -> B) : 
Eq_bis (fun X : Type => X -> B) {| fst_2 := A; snd_2 := f |} {| fst_2 := A'; snd_2 := g |}
-> prodpp (fun e : A = A' => Tr (fun C : Type => C -> B) A A' e f = g).
Proof.
intro X; destruct X. simpl in fst_4. simpl in snd_4. exact (prodpp_def _ _ fst_4 snd_4).
Defined.


Lemma decodee_1 {A A' B} (f : A -> B) (g : A' -> B) : 
prodpp (fun e : A = A' => Tr (fun C : Type => C -> B) A A' e f = g) -> Eq_bis (fun X : Type => X -> B) {| fst_2 := A; snd_2 := f |} {| fst_2 := A'; snd_2 := g |}.
Proof.
intro. destruct X. exact (Eq_bis_def Type (fun X : Type => X -> B) {| fst_2 := A; snd_2 := f |} {| fst_2 := A'; snd_2 := g |} fst_4 snd_4).
Defined.

Lemma Eq_bis_eq_with_eq {A A' B} (f : A -> B) (g : A' -> B) : Eq_bis (fun X : Type => X -> B) {| fst_2 := A; snd_2 := f |}
  {| fst_2 := A'; snd_2 := g |} ~=~
prodpp (fun e : A = A' => Tr (fun C : Type => C -> B) A A' e f = g).
Proof.
exists (encodee_1 f g). exists (decodee_1 f g) (decodee_1 f g). 
- intro. destruct x. destruct fst_4. apply refl.
- intro. destruct x. simpl in fst_4. destruct fst_4. apply refl.
Defined.

Lemma for_fifteen_1 {A A' B} (f : A -> B)(g : A' -> B) :
((elmt_U_ov_set B A f) = (elmt_U_ov_set B A' g) ) ~=~ eq_with_eq f g.
Proof.
unfold elmt_U_ov_set. apply (equiv_transitivity ({| fst_2 := A; snd_2 := f |} = {| fst_2 := A'; snd_2 := g |}) (Eq_bis (fun X : Type => X -> B) {| fst_2 := A; snd_2 := f |} {| fst_2 := A'; snd_2 := g |}) (eq_with_eq f g)).
- apply prodpp_equal.
- unfold eq_with_eq. apply Eq_bis_eq_with_eq.
Defined. 

Lemma for_fifteen_2 {A A' B} (f : A -> B)(g : A' -> B)(e : A = A') : 
(Tr (fun C : Type => C -> B) A A' e f = g) ~=~ (f = (g \u00a4 (first A A' (ua e)))).
Proof.
induction e. apply ua. apply refl.
Defined.

Definition eq_with_eg {A A' B} (f : A -> B)(g : A' -> B) :=
prodpp (fun e : A=A' => f = g \u00a4 (first A A' (ua e))).

Lemma encode_3 { A A' B} (f : A -> B) (g : A' -> B) :
prodpp (fun e : A = A' => Tr (fun C : Type => C -> B) A A' e f = g) ->
prodpp (fun e : A = A' => f = g \u00a4 first A A' (ua e)).
Proof.
intro X. destruct X. destruct fst_4. destruct snd_4.  simpl. exact (prodpp_def _ (fun e : A = A => f = f \u00a4 first A A (ua e)) (refl A) (refl f)).
Defined.

Lemma decode_3 { A A' B} (f : A -> B) (g : A' -> B) :
prodpp (fun e : A=A' => f = g \u00a4 first A A' (ua e) ) -> prodpp (fun e : A = A' => Tr (fun C : Type => C -> B) A A' e f = g).
Proof.
intro X. destruct X. destruct fst_4. rewrite snd_4.  exact (prodpp_def _ (fun e : A = A => Tr (fun C : Type => C -> B) A A e (g \u00a4 first A A (ua 1)) = g) (refl A) (refl g)).
Defined.

Lemma inv_en_de { A B} (f : A -> B) (g : A -> B) (snd_4 : f = g ) :
(encode_3 f g (decode_3 f g {| fst_2 := 1%path; snd_2 := snd_4 |})) =
{| fst_2 := 1%path; snd_2 := snd_4 |}.
Proof.
destruct snd_4. apply refl.
Defined.

Lemma for_for_fifteen_3 {A A' B} (f : A -> B) (g : A' -> B) :
prodpp (fun e : A = A' => Tr (fun C : Type => C -> B) A A' e f = g) ~=~
prodpp (fun e : A = A' => f = g \u00a4 first A A' (ua e)).
Proof.
exists (encode_3 f g). exists (decode_3 f g) (decode_3 f g).
- intro. destruct x. unfold "\u00a4". unfold Id. destruct fst_4. simpl in snd_4. apply inv_en_de.
- intro. destruct x. destruct fst_4. destruct snd_4. apply refl.
Defined.

Lemma for_fifteen_3 {A A' B} (f : A -> B)(g : A' -> B) : 
((elmt_U_ov_set B A f) = (elmt_U_ov_set B A' g) ) ~=~ eq_with_eg f g.
Proof. 
unfold eq_with_eg.
unfold elmt_U_ov_set.
apply (equiv_transitivity ((prodpp_def Type (fun X : Type => X -> B) A f )= (prodpp_def Type (fun X : Type => X -> B) A' g)) (eq_with_eq f g) (eq_with_eg f g)).
- unfold eq_with_eq. apply for_fifteen_1.
- unfold eq_with_eq. unfold eq_with_eg. apply for_for_fifteen_3. 
Defined.

Definition eqi_with_eg {A A' B} (f : A -> B)(g : A' -> B) :=
prodpp (fun e : A~=~A' => f = g \u00a4 (first A A' e)).

Lemma use (A B : Type) :
ua \u00a4 uni  =~ Id (A~=~B).
Proof.
unfold "\u00a4". unfold Id. unfold uni. unfold ua. apply (inv_l (A=B) (A~=~B) ua (univalence A B)).
Defined.

Lemma use_2 { A B} (e : A~=~ B) :
ua (uni e ) = e.
Proof.
apply use .
Defined.

Lemma for_function { A A' B} (f : A -> B) (g : A' -> B)(e : A~=~A') :
( f = g \u00a4 first A A' e) = (f = g \u00a4 first A A' (ua (uni e))).
Proof.
rewrite use_2. apply refl.
Defined.

Lemma function { A A' B} (f : A -> B) (g : A' -> B) :
prodpp (fun e : A = A' => f = g \u00a4 first A A' (ua e)) ->
prodpp (fun e : A ~=~ A' => f = g \u00a4 first A A' e).
Proof.
intro. destruct X. destruct fst_4. simpl in snd_4. exact (prodpp_def _ (fun e : A ~=~ A => f = g \u00a4 first A A e) (equiv_refle ) (snd_4)).
Defined.

Lemma inv_function  { A A' B} (f : A -> B) (g : A' -> B) :
prodpp (fun e : A ~=~ A' => f = g \u00a4 first A A' e) -> prodpp (fun e : A = A' => f = g \u00a4 first A A' (ua e)) .
Proof.
intro. destruct X. rewrite for_function in snd_4. exact (prodpp_def  _ (fun e : A = A'  => f = g \u00a4 first A A' (ua e)) (uni fst_4) (snd_4)).
Defined. 


(* J'ai pas r\u00e9ussi ! *)
Lemma goal_1 { A A' B} (f : A -> B) ( g : A' -> B) (fst_4 :A~=~ A') (snd_4 : f = g \u00a4 first A A' fst_4) :
 (function f g \u00a4 inv_function f g) {| fst_2 := fst_4; snd_2 := snd_4 |} =
Id (prodpp (fun e : A ~=~ A' => f = g \u00a4 first A A' e))
  {| fst_2 := fst_4; snd_2 := snd_4 |}.
Proof.
unfold Id.
Admitted.

Lemma goal_2 { A B} (f g : A -> B) (snd_4 : f = g \u00a4 Id A) :
(inv_function f g \u00a4 function f g) {| fst_2 := 1%path; snd_2 := snd_4 |} =
{| fst_2 := 1%path; snd_2 := snd_4 |}.
Proof.
Admitted.


Lemma for_for_fifteen_4 {A A' B} (f : A -> B) (g : A' -> B) :
prodpp (fun e : A = A' => f = g \u00a4 first A A' (ua e)) ~=~
prodpp (fun e : A ~=~ A' => f = g \u00a4 first A A' e).
Proof.
exists (function f g). exists (inv_function f g) (inv_function f g).
- intro. destruct x. exact (goal_1 f g fst_4 snd_4).
- intro. destruct x. destruct fst_4. simpl in snd_4. unfold Id. exact (goal_2 f g snd_4).
Defined.

Lemma for_fifteen_4 {A A' B} (f : A -> B)(g : A' -> B) : 
((elmt_U_ov_set B A f) = (elmt_U_ov_set B A' g) ) ~=~ eqi_with_eg f g.
Proof.
apply (equiv_transitivity (elmt_U_ov_set B A f = elmt_U_ov_set B A' g) (eq_with_eg f g) (eqi_with_eg f g)).
- apply for_fifteen_3. 
- unfold eq_with_eg. unfold eqi_with_eg. apply for_for_fifteen_4.
Defined.

Lemma sympa {A B : Type} : A~=~ B -> A = B.
Proof.
intros. apply univalence in X. exact X.
Defined.

Lemma encode_5 {A A' B} (f : A -> B) (g : A' -> B) :
eqi_with_eg f g -> eq_with_equiv f g.
Proof.
intros X . unfold eqi_with_eg in X. unfold eq_with_equiv. destruct X.
exact (prodpp_def _ (fun e : A~=~A' => f =~ (g\u00a4first A A' e)) fst_4 (weak_functional_extensionality f (g\u00a4first A A' fst_4) snd_4)).
Defined.

Lemma decode_5 {A A' B} (f : A -> B) (g : A' -> B) :
eq_with_equiv f g -> eqi_with_eg f g.
Proof.
intros X . unfold eqi_with_eg . unfold eq_with_equiv in X. destruct X.
exact (prodpp_def _ (fun e : A~=~A' => f = (g\u00a4first A A' e)) fst_4 (functional_extensionality f (g\u00a4first A A' fst_4) snd_4)).
Defined.

Lemma weak_with_extensionality{ A B} (f g: A -> B) :
 weak_functional_extensionality f g \u00a4 functional_extensionality f g  =~ Id (forall x : A, f x = g x).
Proof.
unfold weak_functional_extensionality.  unfold functional_extensionality. apply (inv_l (f=g) (forall x : A, f x= g x)(weak_functional_extensionality f g) (extensionality A B f g)).
Defined.

Lemma weak_with_extensionality_2 {A B} (f g : A -> B) (e : forall x : A, f x = g x) :
 (weak_functional_extensionality f g ( functional_extensionality f g e)) = Id (forall x : A, f x = g x) e.
Proof. 
apply weak_with_extensionality.
Defined.


(* Pas r\u00e9ussi nan plus ! *)
Lemma extensionality_with_weak { A B} (f g: A -> B):
 functional_extensionality f g \u00a4
      weak_functional_extensionality f g =~ Id (f = g).
Proof.
unfold "\u00a4". intro. unfold functional_extensionality. 
Admitted.

Lemma extensionality_with_weak_2 {A B} ( f g : A -> B) (e : f = g):
(functional_extensionality f g (weak_functional_extensionality f g e)) = Id (f = g ) e.
Proof.
apply (extensionality_with_weak f g).
Defined.

Lemma for_fifteen_5 {A A' B} (f : A -> B)(g : A' -> B) : 
eqi_with_eg f g ~=~ eq_with_equiv f g.
Proof.
unfold eqi_with_eg. unfold eq_with_equiv. exists (encode_5 f g). exists (decode_5 f g) (decode_5 f g).
- intro. destruct x. unfold eq_with_equiv. unfold eqi_with_eg. unfold "\u00a4". unfold Id. simpl. unfold decode_5. unfold encode_5. 
rewrite (weak_with_extensionality_2 f (g\u00a4 first A A' fst_4) snd_4). apply refl.
- unfold "\u00a4". intro. destruct x. unfold Id. unfold encode_5. unfold decode_5. rewrite extensionality_with_weak_2. apply refl.
Defined. 

Lemma fifteen { A A' B} (f : A -> B) (g : A' -> B) :
((elmt_U_ov_set B A f) = (elmt_U_ov_set B A' g) )~=~ eq_with_equiv f g.
Proof.
Print equiv_transitivity. apply (equiv_transitivity ((elmt_U_ov_set B A f) = (elmt_U_ov_set B A' g)) (eqi_with_eg f g) (eq_with_equiv f g)).
- apply for_fifteen_4.  
- apply for_fifteen_5.
Defined. 


(* What we did is that we said that 
(elmt_U_ov_set B A f) = (elmt_U_ov_set B A' g) ~=~ eq_with_eq, (in for_fifteen_1)

but (Tr (fun C : Type => C -> B) A A' e f = g) ~=~ (f = (g \u00a4 (first A A' (ua e)))) so :
 
eq_with_eq ~=~ eq_with_eg, (in for_fifteen_2)

but eq_with_eq ~=~ eq_with_eg (for_for_fifteen_3) so :

(elmt_U_ov_set B A f) = (elmt_U_ov_set B A' g) ~=~ eq_with_eg, (for_fifteen_3)

but eq_with_eg ~=~ eqi_with_eg so :

(elmt_U_ov_set B A f) = (elmt_U_ov_set B A' g) ~=~ eqi_with_eg,(for_fifteen_4)

but eqi_with_eg ~=~ eq_with_equiv (for_fifteen_5) so :

(elmt_U_ov_set B A f) = (elmt_U_ov_set B A' g) ~=~ eq_with_equiv (fifteen)

what we wanted *)



(* We now begin the section 3.8 *)
Section Grothendieck_correspondance_for_type.

Definition p1 (X : Type) (B : X -> Type)  :=
fun z :prodpp B => X.

Definition p1_bis {Y}(P : Y -> Type) :=
fun z : prodpp P => fst_2 P z.

(* Function we define for lemma sixteen *)
Definition psi (Y : Type) (P : Y -> Type) (b  : Y) : 
prodpp (fun z : prodpp P => p1_bis P z = b) -> (P b).
Proof.
intros. destruct X. destruct snd_4. destruct fst_4. unfold p1_bis. exact snd_4.
Defined.

Definition phi (Y : Type) (P : Y -> Type) (b  : Y) :
(P b) -> prodpp (fun z : prodpp P => p1_bis P z = b). 
Proof.
intros. apply (prodpp_def (prodpp P) (fun z : prodpp P => p1_bis P z = b) (prodpp_def Y P b X) (refl b)).
Defined.

(* Will be useful for the Grothendieck's theorem *)
(* Lemma sixteen *)
Lemma sixteen (Y : Type) ( P : Y -> Type) ( b : Y) :
prodpp (fun z : prodpp P => p1_bis P z = b) ~=~ (P b).
Proof.
exists (psi Y P b ). exists (phi Y P b ) (phi Y P b ).
- unfold "=~". intros. unfold phi. unfold "\u00a4". unfold psi. unfold Id. apply refl.
- unfold "=~". intros. destruct x. unfold "\u00a4". unfold phi. unfold psi. unfold Id. unfold refl. destruct snd_4.
destruct fst_4. apply refl.
Defined.

(* Will be useful *)
Lemma sixteen_b (Y : Type) (P : Y -> Type) ( b y : Y) :
prodpp (fun z : prodpp P => p1_bis P z = b) = (P b).
Proof.
apply univalence. apply (sixteen Y P b ).
Defined.

(* Definition eight *)
Definition fib (X Y : Type) (f : X -> Y)(y : Y) :=
prodpp (fun x: X => f x = y). 

Definition p1_bbis (X Y : Type) ( f : X -> Y) (y : Y) :=
fun (z : prodpp (fun x : X => f x = y) )=> X.

Definition phii_bis (Y : Type) : U_over_set Y  -> (Y -> Type).
Proof.
intro. destruct X. exact (fib fst_4 Y snd_4).
Defined.

Definition psii_bis (Y : Type) : (Y -> Type) -> U_over_set Y.
Proof.
intro. unfold U_over_set. exists (prodpp X). exact (p1_bis X).
Defined.

Definition epsilon_f_p {X Y}(f : X -> Y) : X -> prodpp (fib X Y f).
Proof.
intro x. unfold fib. exact ( prodpp_def  _ _ (f x) (prodpp_def X (fun x0 : X => f x0 = f x)  (x) (refl (f x)))).
Defined.

Definition a_epsilon_f_p {X Y} (f : X -> Y) : prodpp (fib X Y f) -> X.
Proof.
intros. induction X0. unfold fib in snd_4. destruct snd_4. exact fst_5.
Defined.

Lemma epsi_and_a {X Y} (f : X -> Y) (z : prodpp (fib X Y f)) : ((epsilon_f_p f) \u00a4 (a_epsilon_f_p f)) z = z.
Proof.
unfold "\u00a4". unfold epsilon_f_p. unfold a_epsilon_f_p. induction z. induction snd_4. destruct snd_4. apply refl.
Defined.

Lemma a_and_epsi {X Y} (f : X -> Y) (x : X) :(( a_epsilon_f_p f )\u00a4 (epsilon_f_p f )) x = x.
Proof.
unfold "\u00a4". unfold epsilon_f_p. unfold a_epsilon_f_p. apply refl.
Defined.

Lemma for_Grothendieck_2 (Y : Type) (X: Type) (f : X -> Y) :
X~=~prodpp (fib X Y f).
Proof.
exists (epsilon_f_p f). exists (a_epsilon_f_p f) (a_epsilon_f_p f).
- unfold "=~". intros. unfold Id. apply epsi_and_a.
- unfold "=~". intros. unfold Id. apply a_and_epsi.
Defined.

Lemma for_Grothendieck_2_2 (Y : Type) (X: Type) (f : X -> Y) :
prodpp (fib X Y f) ~=~ X.
Proof.
exists (a_epsilon_f_p f). exists (epsilon_f_p f) (epsilon_f_p f).
- unfold "=~". intros. unfold Id. apply a_and_epsi.
- unfold "=~". intros. unfold Id. apply epsi_and_a.
Defined.

Lemma for_Grothendieck_1  (Y : Type) (X: Type) ( f : X -> Y) :
prodpp (fib X Y f) = X .
Proof.
apply eg_refl. apply univalence. exact (for_Grothendieck_2 Y X f).
Defined.

Lemma tring {A B : Type} : A ~=~ B -> A = B.
Proof.
intro. apply univalence in X. exact X.
Defined.

Lemma for_Grothendieck_3 (Y : Type)(fst_4 : Type) (snd_4 : fst_4 -> Y)(e := for_Grothendieck_2_2 Y fst_4 snd_4):
p1_bis (fib fst_4 Y snd_4) =~
   (snd_4 \u00a4 first (prodpp (fib fst_4 Y snd_4)) fst_4 e). 
Proof.
intro. destruct x. unfold "\u00a4". unfold p1_bis. unfold fib. destruct snd_5. destruct snd_5. simpl.
 apply refl. 
Defined.

Lemma for_Grothendieck_4 (Y : Type) (P : Y -> Type) (x : Y) :
(prodpp (fun x0 : prodpp P => fst_2 P x0 = x) )~=~ (P x).
Proof.
apply (equiv_transitivity (prodpp (fun x0 : prodpp P => fst_2 P x0 = x)) (prodpp (fun z : prodpp P => p1_bis P z = x))  (P x)).
- unfold p1_bis. exists (Id _). exists (Id _) (Id _).
+ intro. apply refl.
+ intro. apply refl.
- exact (sixteen Y P x). 
Defined.

Lemma for_Grothendieck_5 (Y : Type) (x : Y -> Type) :
(fun y : Y => prodpp (fun x0 : prodpp x => fst_2 x x0 = y)) = x.
Proof.
apply functional_extensionality. intro. apply univalence. apply for_Grothendieck_4.
Defined.

(* Grothendieck's Theorem, theorem 1 in courses *)
Theorem Grothendieck { Y}  : (Y -> Type) ~=~ U_over_set Y.
Proof.
exists (psii_bis Y). exists (phii_bis Y) (phii_bis Y).
- intro. unfold "\u00a4". destruct x. unfold phii_bis. unfold psii_bis. unfold Id. 
apply fifteen. unfold eq_with_equiv. exact (prodpp_def _ _ (for_Grothendieck_2_2 Y fst_4 snd_4) (for_Grothendieck_3 Y fst_4 snd_4 )).
- unfold "=~". intro. unfold "\u00a4". unfold psii_bis. unfold phii_bis. unfold p1_bis. unfold fib. unfold Id.  apply for_Grothendieck_5.
Defined.

End  Grothendieck_correspondance_for_type.