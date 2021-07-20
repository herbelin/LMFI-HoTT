(* This file present TD1, which cover most of Section 4 from the notes *)


(* 0 : Preliminary *)


(* 0.1 Basics on Id types *)

Lemma refl {A} (x : A) : x=x.
Proof.
reflexivity.
Defined.

Lemma eq_transitive {A} {x z : A} (y : A) (p : x=y) (q: y=z ):   x=z.
Proof.
destruct p. exact q.
Defined.

Lemma Tr {A} (B : A -> Type) {x y : A} (p : x = y) : B x -> B y.
Proof.
destruct p. intro b. apply b.
Defined.


(* 0.2 Basics on functions *)

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


(* 0.3 Basics on equivalence *)

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


(* 0.4 Univalence *)

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


(* 0.5 Extensionnality for functions *)

Lemma weak_functional_extensionality {A B} (f g : A -> B) : f=g -> forall x : A, f x = g x.
Proof.
intro p. destruct p. intros. apply refl.
Defined.

Axiom extensionality : forall A B : Type, forall f g : A -> B, isequiv (f=g) (forall x : A, f x = g x)(weak_functional_extensionality f g).

Lemma functional_extensionality {A B} (f g : A -> B) : (forall x : A, f x = g x) -> f = g.
Proof.
intro X. apply extensionality. exact X.
Defined.


(* Exercice 1 : Unit_Type *)

Inductive Unit_Type :=
stars : Unit_Type.

Definition Eq_Unit (x y : Unit_Type) := Unit_Type.

Lemma prop_unit (x y : Unit_Type) : x=y.
Proof.
destruct x. destruct y. apply refl.
Defined.


(* Exercise 1, Question 1 *)

Lemma encode_1 (A : Type) : prod A Unit_Type -> A.
Proof.
intro. destruct X as (a,b). apply a.
Defined.

Lemma decode_1 (A : Type) : A -> prod A Unit_Type.
Proof.
intro. exists.
- exact X.
- exact stars.
Defined.

Lemma prod_Type_Unit (A : Type) : prod A Unit_Type ~=~ A.
Proof.
exists (encode_1 A). exists (decode_1 A) (decode_1 A).
- intro. apply refl.
- intro x. destruct x as (a,b). simpl. destruct b. apply refl.
Defined.

Lemma encode_1_1 (A: Type)(x: A): (A -> Unit_Type) -> Unit_Type.
Proof. 
intro X. apply X. exact x.
Defined.

Lemma decode_1_1 (A : Type)(x: A) : Unit_Type -> (A -> Unit_Type).
Proof.
intros. exact stars.
Defined.

Lemma Type_arrow_Unit (A : Type) (x :A) : (A -> Unit_Type) ~=~ (Unit_Type).
Proof.
exists (encode_1_1 A x). exists (decode_1_1 A x) (decode_1_1 A x). 
- unfold "=~". intro s. destruct s. unfold "$". unfold decode_1_1. simpl. unfold encode_1_1. unfold Id. apply refl. 
- unfold "=~". unfold encode_1_1. unfold decode_1_1. unfold "$". intro s.  unfold Id. 
apply functional_extensionality. intro. apply prop_unit.
Defined. 

 
(* Exercise 1, Question 2 *)

Lemma encode_2 : forall x y : Unit_Type, ( x = y ) -> Eq_Unit x y.
Proof.
intros. exact stars.
Defined.


(* Exercise 1, Question 3 *)

Lemma decode_2 : forall x y : Unit_Type, Eq_Unit x y -> (x = y).
Proof.
intros. apply prop_unit.
Defined.


(* Exercise 1, Question 4 *)

Lemma Unit_to_Unit : forall x y : Unit_Type, (x=y) ~=~ Unit_Type.
Proof.
intros. exists (encode_2 x y). exists (decode_2 x y) (decode_2 x y).
- unfold "=~". intros. apply prop_unit.
- unfold "=~". intros H. destruct H. destruct x. apply refl.
Defined. 

Lemma stars_refl_to_Unit :forall x y : Unit_Type,(stars = stars) ~=~ Unit_Type.
Proof.
intros. apply Unit_to_Unit.
Defined.


(* Exercice 2 : Empty_Type *)

Inductive Empty : Type :=.


(* Exercise 2, Question 1 *)

Lemma encode_1_a (A : Type) : prod A Empty -> Empty.
Proof.
intro x. destruct x as (a,b). destruct b.
Defined.

Lemma decode_1_a (A : Type) : Empty -> prod A Empty.
Proof.
intro x. destruct x.
Defined.

Lemma prod_Empty_to_Empty (A : Type) : prod A Empty ~=~ Empty.
Proof.
exists (encode_1_a A ). exists (decode_1_a A) (decode_1_a A). 
- unfold "=~". intro x. destruct x. 
- unfold "=~". intro x. destruct x as (a,b). destruct b.
Defined.

Lemma encode_1_b (A : Type): (Empty -> A) -> Unit_Type.
Proof.
intros. exact stars.
Defined.

Lemma decode_1_b (A : Type) : Unit_Type -> ( Empty -> A).
Proof.
intros x y. destruct y.
Defined.

Lemma Empty_arrow_Type (A : Type) : (Empty -> A)~=~ Unit_Type.
Proof.
exists (encode_1_b A). exists (decode_1_b A) (decode_1_b A).
- unfold "=~". intro x. destruct x. apply refl.
- unfold "=~". intro x. apply functional_extensionality. intro y. destruct y.
Defined.


(* Exercise 2, Question 2 *)

Lemma question_2 : forall x y : Empty, x=y.
Proof.
intros x y. destruct x.
Defined.


(* Exercise 2, Question 3 *)

Lemma question_3 : forall x y : Empty, x=y -> Empty.
Proof.
intros x y H. destruct x.
Defined.

(* Exercise 2, Question 4 *)

Lemma question_4 (x y : Empty) (e : x=y) (P : x=y -> Type) : P e.
Proof.
destruct x.
Defined.


(* Exercise 2, Question 5 *)

Definition for_question_5 (A : Type) : Empty -> A.
Proof.
intro x. destruct x.
Defined.

Lemma Type_to_Empty (A : Type) (f : A -> Empty) : isequiv A Empty f. 
Proof.
exists (for_question_5 A) (for_question_5 A).
- unfold "=~". intro x. destruct x.
- unfold "=~". intro x. destruct (f x).
Defined.


(* Exercice 3 : Booleans *)

Inductive Booleans_Type :=
zeero: Booleans_Type
|onee : Booleans_Type.

Definition Eq_Bool (x: Booleans_Type) (y :Booleans_Type) : Type :=
match x with
zeero => match y with 
            zeero => Unit_Type
            | _ =>  Empty end
| _ => match y with 
        zeero => Empty
        |_ => Unit_Type end
end.


(* Exercise 3, Question 1 *)

Lemma encode_2_1 (x y : Booleans_Type) : (x=y) -> Eq_Bool x y.
Proof.
intro X. induction X. unfold Eq_Bool. simpl. destruct x.
- exact stars.
- exact stars.
Defined.


(* Exercise 3, Question 2 *)

Lemma decode_2_1 ( x y : Booleans_Type) : Eq_Bool x y -> (x=y).
Proof.
intro X. induction y.
- induction x. 
+ apply refl.
+ destruct X.
- induction x.
+ induction X.
+ apply refl.
Defined.


(* Exercise 3, Question 3 *)

Lemma Booleans_Type_Eq_Bool (x y : Booleans_Type) : (x=y) ~=~ Eq_Bool x y.
Proof.
exists (encode_2_1 x y). exists (decode_2_1 x y) (decode_2_1 x y).
- unfold "=~". intro H. destruct x. 
+ destruct y. 
++ destruct H. apply refl.
++ destruct  H. 
+ destruct y.
++ destruct H. 
++ destruct H. apply refl.
- intro H. destruct H. destruct x.
+ apply refl.
+ apply refl.
Defined.

Lemma zeero_not_oone : zeero = onee -> Empty.
Proof.
apply (Booleans_Type_Eq_Bool zeero onee).
Defined.


(* Exercice 4.: Sum_Types *)

Inductive Sum_Type (A B : Type) :=
lft : A -> Sum_Type A B 
|rght : B -> Sum_Type A B.


(* Exercise 4, Question 1 *)

Lemma psi_1_ST {A B C} : ((Sum_Type A B) -> C)-> prod (A -> C)(B-> C).
Proof.
intros. split.
- exact ( X $ lft A B ).
- exact (X $ rght A B).
Defined.

Lemma phi_1_ST { A B C } : prod (A -> C)(B-> C) -> ((Sum_Type A B) -> C).
Proof.
intros X X'. destruct X as (X1,X2). destruct X' as [a|b]. 
- exact (X1 a).
- exact (X2 b).
Defined.

Lemma Sum_Type_prod {A B C} : ((Sum_Type A B) -> C) ~=~ prod (A -> C)(B-> C).
Proof.
exists (psi_1_ST ). exists (phi_1_ST) (phi_1_ST).
- unfold "=~". intro x. destruct x. apply refl.
- unfold "=~". intro x. apply functional_extensionality. intro y. destruct y. 
+ apply refl.
+ apply refl.
Defined.


(* Exercise 4, Question 2 *)

Lemma psi_2_ST {A} : Sum_Type A Empty -> A.
Proof.
intro X. destruct X as [a|e].
- exact a.
- destruct e.
Defined.

Lemma phi_2_ST {A} : A -> Sum_Type A Empty.
Proof.
exact (lft A Empty).
Defined.

Lemma Sum_Type_with_Empty {A} : Sum_Type A Empty ~=~ A.
Proof.
exists psi_2_ST. exists (phi_2_ST) (phi_2_ST).
- intro. apply refl.
- intro x. destruct x as [a|e].
+ apply refl.
+ destruct e.
Defined.


(* Exercise 4, Question 3 *)

Lemma psi_3_ST : Sum_Type Unit_Type Unit_Type -> Booleans_Type.
Proof.
intro X. destruct X.
- exact zeero.
- exact onee.
Defined.

Lemma phi_3_ST : Booleans_Type -> Sum_Type Unit_Type Unit_Type.
Proof.
intro H. destruct H.
- exact (lft Unit_Type Unit_Type stars).
- exact (rght Unit_Type Unit_Type stars).
Defined.

Lemma Sum_Type_Unit_Bool : Sum_Type Unit_Type Unit_Type ~=~ Booleans_Type.
Proof.
exists (psi_3_ST). exists (phi_3_ST) (phi_3_ST).
- intro x. destruct x.
+ apply refl.
+ apply refl.
- intro x. destruct x as [u|u].
+ destruct u. apply refl.
+ destruct u. apply refl.
Defined.


(* Exercise 4, Question 4 *)

Definition Eq_Sum_Type {A B} (x y : Sum_Type A B) : Type :=
match x with 
| lft _ _ x=> match y with 
        | lft _ _ y=> x=y
        | rght _ _ y=> Empty 
         end
| rght _ _ x=> match y with 
        | lft _ _ y=> Empty
        | rght _ _ y => x=y
        end
end.

Lemma encode_ST (A B : Type) (z z' :  Sum_Type A B) : (z=z') -> Eq_Sum_Type z z'.
Proof.
intros. destruct H. destruct z.
- apply refl.
- apply refl.
Defined.

Lemma decode_ST (A B : Type) (z z' :  Sum_Type A B) : Eq_Sum_Type z z' -> (z=z').
Proof.
intros.
destruct z.
- destruct z'.
+ destruct X . apply refl.
+ destruct X.
- destruct z'.
+ destruct X.
+ destruct X. apply refl.
Defined.

Lemma Sum_Type_equal {A B} (z z' :  Sum_Type A B) : (z=z')~=~ Eq_Sum_Type z z'.
Proof.
exists (encode_ST A B z z'). exists (decode_ST A B z z') (decode_ST A B z z').
- unfold "=~". unfold "$". intro x. unfold Id. destruct z. 
+ unfold Eq_Sum_Type in x. destruct z'.
++ destruct x. apply refl.
++ destruct x.
+ unfold Eq_Sum_Type in x. destruct z'. 
++ destruct x.
++ destruct x. apply refl.
- intro H. destruct H. destruct z.
+ apply refl.
+ apply refl.
Defined.


(* Exercice 5 : natural numbers *)

Inductive Nat :=
zero : Nat
| Sj : Nat -> Nat.

(*Fixpoint Eq_Nat (n: Nat) (m :Nat)  :=
match n with
zero => match m with 
            zero => Unit_Type
            | Sj n =>  Empty 
             end
| Sj m => match m with 
        zero => Empty
        |Sj n => Eq_Nat n m end
end.*)

Fixpoint Eq_Nat (n : Nat) (m : Nat) : Type.
Proof.
destruct n.
- destruct m.
+ exact Unit_Type.
+ exact Empty.
- destruct m. 
+ exact Empty.
+ exact (Eq_Nat n m).
Defined.

Lemma encode_for_q_5_1 (m n : Nat) : ( m = n ) -> Eq_Nat m n.
Proof.
intro X. destruct X.  induction m. 
- exact stars.
- apply IHm.
Defined.

Lemma encode_ap_Sj (m n : Nat) (p : m = n) : encode_for_q_5_1 _ _ (ap Sj p) = encode_for_q_5_1 _ _ p.
Proof.
destruct p. apply refl.
Defined.

Lemma decode_for_q_5_1  : forall m n : Nat, Eq_Nat m n -> (m = n ).
Proof.
intro n.  induction n.
- intro m. induction m. 
  + intro. apply refl.
  + intro X. destruct X.
- intro m. induction m.
 + intro X. destruct X.
 + intro. apply (ap Sj). apply IHn. apply X.
Defined. 

Lemma Nat_encode_decode : forall (m n : Nat) (x : Eq_Nat m n), encode_for_q_5_1 m n (decode_for_q_5_1 m n x) = x.
Proof.
intro n.  induction n.
- intro m. induction m. 
  + intro x. destruct x. apply refl.
  + intro x. destruct x.
- intro m. induction m.
 + intro x. destruct x.
 + intro x. simpl. Check (IHn _ x). apply (eq_transitive (encode_for_q_5_1 n m (decode_for_q_5_1 n m x))). 
  ++ apply encode_ap_Sj.
  ++ apply IHn.
Defined. 

Lemma Nat_decode_encode : forall (m n : Nat) (x : m = n), decode_for_q_5_1 m n (encode_for_q_5_1 m n x) = x.
Proof.
intros m n x. destruct x. induction m.
- apply refl.
- apply (eq_transitive (ap Sj (refl _))). 
  + apply (ap (ap Sj)). apply IHm.
  + apply refl.
Defined.

Lemma Nat_equal (m n :Nat) : ( m = n ) ~=~ Eq_Nat m n.
Proof.
exists (encode_for_q_5_1 m n). exists (decode_for_q_5_1 m n) (decode_for_q_5_1 m n).
- intro. apply Nat_encode_decode.
- intro. apply Nat_decode_encode.
Defined.


(* Exercise 5, Question 2 *)

Lemma question_5_2 (m n : Nat) : (m = n) ~=~ (Sj m = Sj n).
Proof.
apply (equiv_transitive (Eq_Nat m n)).
- apply Nat_equal.
- apply equiv_sym. apply (Nat_equal (Sj m) (Sj n)).
Defined.


(* Exercise 6 : Univalence_contradicts_UIP*)


(* Exercise 6, Question 1*)

Lemma function_for_swap : Booleans_Type -> Booleans_Type.
Proof.
intros. destruct H.
- exact (onee).
- exact (zeero).
Defined.

Definition swap : Booleans_Type ~=~ Booleans_Type.
Proof.
exists function_for_swap. exists function_for_swap function_for_swap.
- unfold "=~". unfold "$". intro x. destruct x. 
+ apply refl.
+ apply refl.
- unfold "=~". unfold "$". intro x. destruct x. 
+ apply refl.
+ apply refl.
Defined.


(* Exercise 6, Question 2 *)

Lemma eq_for_swap_aux : swap = ua (refl _) -> zeero = onee.
Proof.
intro H.
apply (fun x => weak_functional_extensionality function_for_swap (Id _) x onee).
apply (ap (first _ _) H).
Defined.

Lemma eq_for_swap : (swap = ua (refl _)) -> Empty.
Proof.
intro H. apply zeero_not_oone. apply eq_for_swap_aux. apply H.
Defined.


(* Exercise 6, Question 3 *)

Definition isProp (A : Type) := forall (x y : A), x = y. 

Definition UIP := forall (A : Type) (x y : A), isProp (x=y).

Lemma isPropEquiv (A B : Type) : A ~=~ B -> isProp A -> isProp B.
Proof.
intro e. destruct e as (f,H). destruct H as (g1,g2,invl,invr). 
intro H2. intros x y. 
apply (Tr (fun x => x = _) (invl x)). apply (Tr (fun y => _ = y) (invl y)).
apply (ap f). apply H2.
Defined.

Lemma UIP_imply_equivalence (A B : Type) : UIP -> isProp (A ~=~ B).
Proof.
intro H. apply (isPropEquiv (A=B)).
- exists ua. apply univalence.
- apply H.
Defined.

Lemma UIP_false : UIP -> Empty.
Proof.
intro H. apply eq_for_swap. apply (UIP_imply_equivalence _ _ H).
Defined.


