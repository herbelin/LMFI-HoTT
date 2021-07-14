Require Import HoTT.
Require Import Reals.
Require Import Arith.
Require Import Coq.Reals.Reals.
Open Scope nat_scope.
Require Import Bool.

(* First a few definitions  : *)
Lemma refl {A} (x : A) : x=x.
Proof.
reflexivity.
Defined.

Definition homotopy {A B : Type}( f g : A -> B ):=
forall x :A , f x = g x.

Notation "f =~ g " := (homotopy f g)(at level 40).

Definition compose_function {A B C} (g : B -> C) (f : A -> B) :=
  fun x : A => g (f x).

Notation " g ¤ f ":= (compose_function g f)(at level 40).


Definition Id (A : Type) :=
fun x: A => x.

Record isequiv (A B : Type) (f : A-> B) : Type :=
MakeEquiv {g1 : B->A ; g2 : B-> A ; inv_l : ( f¤g1)=~(Id B); inv_r : (g2¤f) =~(Id A)}.

Record Type_equiv (A B : Type) :=
Make_Type_equiv { first : A-> B ; second : isequiv A B first}.

Notation " A ~=~ B" := (Type_equiv A B)(at level 40).

Lemma weak_functional_extensionality {A B} (f g : A -> B) : f=g -> forall x : A, f x = g x.
Proof.
intros. destruct X. apply refl.
Defined.

Axiom extensionality : forall A B : Type, forall f g : A -> B, isequiv (f=g) (forall x : A, f x = g x)(weak_functional_extensionality f g).

Lemma functional_extensionality{A B} (f g : A -> B) : (forall x : A, f x = g x) -> f = g.
Proof.
intros. apply extensionality . exact X.
Defined.

Definition ua {A B} :   A = B -> A ~=~ B.
Proof.
intros f.
destruct f.
exists (Id A).
now exists (Id A) (Id A).
Defined.

Axiom univalence  : forall A B : Type, isequiv (A=B) (A~=~B) ua.

Definition homotopy_function (A B : Type) (f g : A -> B) : f=g -> f =~ g.
Proof.
intros.
destruct X.
intro x.
apply (refl (f x)).
Defined.

Lemma compose_path {A} {x y z : A} (p : x=y) (q: y=z ):   x=z.
Proof.
induction p. exact q.
Defined.

Lemma inverse_path {A : Type} {x y: A} (p : x=y) : y=x.
Proof.
induction p. apply refl.
Defined.

Lemma for_link (A B : Type) (f : A -> B) ( g1 g2 : B -> A)
 (p : (forall x :B ,(f¤g1) x= Id B x )) (q : (forall x : A, (g2¤f) x=Id A x )) : g1=g2.
Proof.
intros.  unfold "¤" in p. unfold "¤" in q.  unfold Id in p. unfold Id in q. apply functional_extensionality.
intros. apply (@compose_path A (g1 x) (g2 (f (g1 x))) (g2 x)  ).
- apply inverse_path. apply (q (g1 x)).
- rewrite (p x). apply refl.
Defined.

Axiom fonction_homotopy : forall A B : Type, forall f g : A-> B, isequiv (f=g) (f=~g) (homotopy_function A B f g).
 
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
exists (Encode z z'). exists (decode z z') (decode z z').
- unfold "=~". intros. induction z. induction z'. destruct x. simpl in fst_2. simpl in snd_2. simpl.
induction fst_2. induction snd_2. apply refl. 
- unfold "=~". intros. induction x. apply refl.
Defined.

Lemma compose_asso {A B C D} (f : A -> B) ( g : B -> C) (h : C -> D) : h ¤ (g ¤ f ) = (h ¤ g) ¤ f.
Proof.
unfold "¤".
apply refl.
Defined.

Lemma compose_asso_2 {A B C D} (f : A -> B) ( g : B -> C) (h : C -> D) :(h ¤ g) ¤ f = h ¤ (g ¤ f ).
Proof.
unfold "¤".
apply refl.
Defined.

Lemma compose_with_Id {A B C} (f : B -> A)(g : C -> B) : (f ¤ (Id B ¤ g)) = (f ¤ g).
Proof. 
apply functional_extensionality. intro. unfold "¤". apply refl.
Defined.

Lemma aux {A B} (f : A -> B)(g : B -> A) :  (f ¤ g)  =~ Id B -> (f ¤ g) = Id B.
Proof.
intros. apply functional_extensionality. unfold "=~" in X. exact X.
Defined.

Lemma equiv_transitivity (A B C : Type) : A~=~B -> B~=~C -> A~=~C.
Proof. 
intros. destruct X. destruct X0. destruct second0. destruct second1. unfold "=~" in inv_l0. unfold "=~" in inv_r1. 
exists (first1 ¤ first0). exists (g3 ¤ g5) (g4 ¤ g6).
- unfold "=~". intro. rewrite (compose_asso g5 g3 (first1 ¤ first0)). 
rewrite (compose_asso_2  g3 first0 first1). apply weak_functional_extensionality. 
apply aux in inv_l0. rewrite inv_l0. rewrite compose_asso_2. rewrite compose_with_Id. apply functional_extensionality. exact inv_l1.
- unfold "=~". intro. rewrite (compose_asso_2 (first1 ¤ first0) g6 g4). 
rewrite (compose_asso first0 first1 g6). apply weak_functional_extensionality. 
apply aux in inv_r1. rewrite inv_r1. rewrite compose_with_Id. apply functional_extensionality.
exact inv_r0.
Defined.

(* We now begin exercice 1 : *)

Section Exercice_1.

Inductive Unit_Type :=
stars : Unit_Type.

(* Question 1 *)

Lemma encode_1 (A : Type) : prod A Unit_Type -> A.
Proof.
intro. induction X. apply fst.
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
- intro. induction x. simpl. destruct snd. apply refl.
Defined.

Lemma encode_1_1 (A: Type)(x: A): (A -> Unit_Type) -> Unit_Type.
Proof. 
intros. destruct X.
- apply x.
- exists.
Defined.

Lemma decode_1_1 (A : Type)(x: A) : Unit_Type -> (A -> Unit_Type).
Proof.
intros. destruct X. exact stars.
Defined.

Lemma Type_arrow_Unit (A : Type) (x :A) : (A-> Unit_Type) ~=~ (Unit_Type).
Proof.
exists (encode_1_1 A x). exists (decode_1_1 A x) (decode_1_1 A x). 
- unfold "=~". intros. destruct x0. unfold "¤". unfold decode_1_1. simpl. unfold encode_1_1. unfold Id. apply refl. 
-  unfold "=~". unfold encode_1_1. unfold decode_1_1. unfold "¤". intros. destruct x0.  unfold Id. apply functional_extensionality. intros. induction x0. apply refl.
Defined. 

 
(* Question 2 *)

Definition Eq_1_bis (x y : Unit_Type) := Unit_Type.

Lemma g (x : Unit_Type) : x=stars.
Proof.
destruct x. apply refl.
Defined.

Lemma psyi (x y : Unit_Type) : Eq_1_bis x y -> Unit_Type.
Proof.
intros. destruct X. exact stars.
Defined.

Lemma phyi (x y : Unit_Type) : Unit_Type -> Eq_1_bis x y.
Proof.
intros. unfold Eq_1_bis. exact stars.
Defined.

Lemma Eq_with_Unit  : forall x y : Unit_Type, Eq_1_bis x y ~=~ Unit_Type.
Proof.
intros. exists (psyi x y). exists (phyi x y) (phyi x y).
- unfold "=~". intros. unfold "¤". unfold phyi. unfold psyi. unfold Id. induction x0. apply refl.
- unfold "=~". intros. unfold "¤". unfold psyi. unfold phyi. unfold Id. induction x0. apply refl.
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


Lemma stars_refl_to_Unit :forall x y : Unit_Type,(stars = stars) ~=~ Unit_Type.
Proof.
intros. apply Unit_to_Unit.
Defined.

End Exercice_1.

Section Exercice_2.

Inductive Empty : Type :=.

(* Question 1 : *)

Lemma encode_1_a (A : Type) : prod A Empty -> Empty.
Proof.
intros. destruct X. destruct snd.
Defined.

Lemma decode_1_a (A : Type) : Empty -> prod A Empty.
Proof.
intros. destruct X.
Defined.


Lemma prod_Empty_to_Empty (A : Type) : prod A Empty ~=~ Empty.
Proof.
exists (encode_1_a A ). exists (decode_1_a A) (decode_1_a A). 
- unfold "=~". intros. destruct x. 
- unfold "=~". intros. destruct x. destruct snd.
Defined.


Lemma encode_1_b (A : Type): (Empty -> A) -> Unit_Type.
Proof.
intros. exact stars.
Defined.

Lemma decode_1_b (A : Type) : Unit_Type -> ( Empty -> A).
Proof.
intros. destruct X0.
Defined.

Lemma Empty_arrow_Type (A : Type) : (Empty -> A)~=~ Unit_Type.
Proof.
exists (encode_1_b A). exists (decode_1_b A) (decode_1_b A).
- unfold "=~". intros. destruct x. unfold "¤". unfold decode_1_b. unfold encode_1_b. unfold Id. apply refl.
- unfold "=~". intros. unfold "¤". unfold encode_1_b. unfold decode_1_b. simpl. unfold Id. apply functional_extensionality. intros. induction x0.
Defined.

(* Question 2 : *)

Lemma question_2 : forall x y : Empty, x=y.
Proof.
intros. induction x.
Defined.

(* Question 3 : *)
Lemma question_3 : forall x y : Empty, x=y -> Empty.
Proof.
intros. induction x.
Defined.

(* Question 4 pas compris ^^ *)

(* Question 5 : *)

Definition for_question_5 (A : Type) : Empty -> A.
Proof.
intro. destruct X.
Defined.

Lemma Type_to_Empty (A : Type) : forall f : A -> Empty, isequiv A Empty f. 
Proof.
intros. exists (for_question_5 A) (for_question_5 A).
- unfold "=~". intro. destruct x.
- unfold "=~". intros. destruct f. apply x.
Defined.

End Exercice_2.

Section Exercice_3.

Inductive Booleans_Type :=
zeero: Booleans_Type
|onee : Booleans_Type.

Definition Eq_2 (x: Booleans_Type) (y :Booleans_Type) : Type :=
match x with
zeero => match y with 
            zeero => Unit_Type
            | _ =>  Empty end
| _ => match y with 
        zeero => Empty
        |_ => Unit_Type end
end.

(* Question 1 : *)

Lemma encode_2_1 (x y : Booleans_Type) : (x=y) -> Eq_2 x y.
Proof.
intro. induction X. unfold Eq_2. simpl. destruct x.
- exact stars.
- exact stars.
Defined.

(* Question 2 : *)

Lemma decode_2_1 ( x y : Booleans_Type) : Eq_2 x y -> (x=y).
Proof.
intros. induction y.
- induction x. 
+ apply refl.
+ destruct X.
- induction x.
+ induction X.
+ apply refl.
Defined.

(* Question 3 *)

Lemma Booleans_Type_Eq_2 (x y : Booleans_Type) : (x=y) ~=~ Eq_2 x y.
Proof.
exists (encode_2_1 x y). exists (decode_2_1 x y) (decode_2_1 x y).
- unfold "=~". unfold "¤". unfold encode_2_1. unfold decode_2_1. unfold Id. destruct x. 
+ intros. destruct y. 
++ destruct x. apply refl.
++ destruct  x. 
+ intros. destruct y.
++ destruct x. 
++ destruct x. apply refl.
- unfold "=~". unfold "¤". unfold encode_2_1. unfold decode_2_1. intros. unfold Id. destruct x0.
destruct x.
+ apply refl.
+ apply refl.
Defined.
 
End Exercice_3.

Section Exercice_4.

Inductive Sum_Type (A B : Type) :=
lft : A -> Sum_Type A B 
|rght : B -> Sum_Type A B.

Lemma psi_1_ST {A B C} : ((Sum_Type A B) -> C)-> prod (A -> C)(B-> C).
Proof.
intros.
exists.
- exact ( X ¤ lft A B ).
- exact (X ¤ rght A B).
Defined.

Lemma phi_1_ST { A B C } : prod (A -> C)(B-> C) -> ((Sum_Type A B) -> C).
Proof.
intros.
destruct X ; destruct X0. 
-  exact (fst a).
- exact (snd b).
Defined.

Lemma Sum_Type_prod {A B C} : ((Sum_Type A B) -> C)~=~ prod (A -> C)(B-> C).
Proof.
exists (psi_1_ST ). exists (phi_1_ST) (phi_1_ST).
- unfold "=~". unfold "¤". unfold psi_1_ST. unfold phi_1_ST. unfold Id. apply refl.
- unfold "=~". unfold "¤". unfold psi_1_ST. unfold phi_1_ST. unfold Id. unfold "¤". intros.
apply functional_extensionality. intros. destruct x0. 
+ apply refl.
+ apply refl.
Defined.

(* Question 2 : *)

Lemma psi_2_ST {A} : Sum_Type A Empty -> A.
Proof.
intros. 
destruct X.
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
- unfold "=~". unfold "¤". unfold psi_2_ST. unfold phi_2_ST. unfold Id. apply refl.
- unfold "=~". unfold "¤". unfold psi_2_ST. unfold phi_2_ST. unfold Id. intros.
induction x.
+ apply refl.
+ easy.
Defined.

(* Question 3 : *)

Lemma psi_3_ST : Sum_Type Unit_Type Unit_Type -> Booleans_Type.
Proof.
intros. destruct X.
- exact zeero.
- exact onee.
Defined.

Lemma phi_3_ST : Booleans_Type -> Sum_Type Unit_Type Unit_Type.
Proof.
intros. destruct H.
- exact (lft Unit_Type Unit_Type stars).
- exact (rght Unit_Type Unit_Type stars).
Defined.

Lemma Sum_Type_Unit_Bool : Sum_Type Unit_Type Unit_Type ~=~ Booleans_Type.
Proof.
exists (psi_3_ST). exists (phi_3_ST) (phi_3_ST).
- unfold "=~". unfold "¤". unfold psi_3_ST. unfold phi_3_ST. unfold Id. intros. destruct x.
+ apply refl.
+ apply refl.
-  unfold "=~". unfold "¤". intros. destruct x.
+ destruct u. apply refl.
+ destruct u. apply refl.
Defined.

(* Question 4 *)

Definition Eq_Sum_Type {A B} (x y : Sum_Type A B) : Type :=
match x with 
| lft x=> match y with 
        | lft y=> x=y
        | rght y=> Empty 
         end
| rght x=> match y with 
        | lft y=> Empty
        | rght y => x=y
        end
end.

Definition lft_inj : forall A B : Type, forall a a0 : A, lft A B a = lft A B a0 -> a=a0.
Proof.
intros.  inversion X.
apply refl.
Defined.

Definition rght_inj : forall A B : Type, forall b b0 : B, rght A B b = rght A B b0 -> b=b0.
Proof.
intros. inversion X.
apply refl.
Defined. 

Lemma encode_ST (A B : Type) (z z' :  Sum_Type A B) : (z=z') -> Eq_Sum_Type z z'.
Proof.
intros. destruct z.
- unfold Eq_Sum_Type.  destruct z'. 
+ apply (lft_inj A B a a0 X).
+ easy. 
- unfold Eq_Sum_Type. destruct z'.
+ easy.
+ apply (rght_inj A B b b0 X).
Defined.

Lemma decode_ST (A B : Type) (z z' :  Sum_Type A B) : Eq_Sum_Type z z' -> (z=z').
Proof.
intros.
destruct z.
- unfold Eq_Sum_Type in X. 
destruct z'.
+ rewrite X . apply refl.
+ destruct X.
- destruct z'.
+ unfold Eq_Sum_Type in X. destruct X.
+ unfold Eq_Sum_Type in X. rewrite X. apply refl.
Defined.

Lemma Sum_Type_equal {A B} (z z' :  Sum_Type A B) : (z=z')~=~ Eq_Sum_Type z z'.
Proof.
exists (encode_ST A B z z'). exists (decode_ST A B z z') (decode_ST A B z z').
- unfold "=~". unfold "¤". intros. unfold Id. destruct z. 
+ unfold Eq_Sum_Type in x. destruct z'.
++ unfold decode_ST; unfold encode_ST . unfold internal_paths_rew_r ; unfold refl. unfold lft_inj. 
simpl. destruct x. apply refl.
++ destruct x.
+ unfold Eq_Sum_Type in x. destruct z'. 
++ destruct x.
++ destruct x. apply refl.
- unfold "=~". intros. destruct x. unfold "¤". unfold Id. destruct z.
+ apply refl.
+ apply refl.
Defined.

End Exercice_4.

Section Exercice_5.

Inductive Nat :=
zero : Nat
| Sj : Nat -> Nat.


Fixpoint Eq_5 (n: Nat) (m :Nat)  :=
match n with
zero => match m with 
            zero => Unit_Type
            | Sj n =>  Empty 
             end
| Sj m => match m with 
        zero => Empty
        |Sj n => Eq_5 n m end
end.

Fixpoint Eq_5_b (n : Nat) (m : Nat) : Type.
Proof.
destruct n.
- destruct m.
+ exact Unit_Type.
+ exact Empty.
- destruct m. 
+ exact Empty.
+ exact (Eq_5_b n m).
Defined.

Definition predc (m : Nat) :=
match m with 
zero => m
| Sj u => u
end.

Lemma predc_with_suc (m : Nat) : predc (Sj m) = m.
Proof.
unfold predc. apply refl.
Defined.

Lemma pouf (m : Nat) : Eq_5_b (Sj m) (Sj m) = Eq_5_b m m.
Proof.
unfold Eq_5_b. apply refl.
Defined. 

Lemma Eq_5_with_same : forall m : Nat, Eq_5_b m m = Unit_Type.
Proof.
intro.  induction m.
- apply refl.
- unfold Eq_5_b. apply IHm. 
Defined.

Lemma encode_for_q_5_1 (m n : Nat) : ( m = n ) -> Eq_5_b m n.
Proof.
intros. destruct X.  induction m. 
- exact stars.
- unfold Eq_5_b.  apply IHm.
Defined.

Lemma encode_5_2 (m n : Nat) : ( m = n ) -> (Sj m = Sj n).
Proof.
intro. destruct X. apply refl. 
Defined.

Lemma decode_for_q_5_1  : forall m n : Nat, Eq_5_b m n -> (m = n ).
Proof.
intro n.  induction n.
-  intro.  induction n. 
+ intro. 
apply refl.
+ intro. destruct X.
- intro. induction n0.
+ intro. destruct X.
+ intro. apply (encode_5_2 n n0 (IHn n0 X)).
Defined. 

Lemma Nat_equal (m n : Nat) : ( m = n ) ~=~ Eq_5_b m n.
Proof.
exists (encode_for_q_5_1 m n). exists (decode_for_q_5_1 m n) (decode_for_q_5_1 m n).
- intro. induction n.
+ induction m. 
++ unfold Id. unfold Eq_5_b in x.  unfold decode_for_q_5_1. unfold "¤". unfold encode_for_q_5_1. simpl. destruct x. apply refl.
++ destruct x.
+ induction m.
++ destruct x.
++ unfold "¤".  
Admitted.

Lemma decode_5_2 (m n : Nat) : (Sj m = Sj n) -> ( m = n ).
Proof.
intros. inversion X. apply refl.
Defined. 

Lemma Eq_succ (m n : Nat) : Eq_5_b m n = Eq_5_b (Sj m) (Sj n).
Proof.
unfold Eq_5_b. apply refl.
Defined. 

Lemma for_equiv_refl {A B}(first0 : A -> B) (g3 g4 : B -> A)(inv_l0 : (first0 ¤ g3) =~ Id B) (inv_r0 : (g4 ¤ first0) =~ Id A) :g3 = g4 ->  first0 ¤ g4 = Id B .
Proof.
intro. destruct X. apply functional_extensionality. unfold "=~" in inv_l0. apply inv_l0.
Defined.

Lemma equiv_refl (A B : Type) : A ~=~ B -> B~=~ A.
Proof.
intros. destruct X. destruct second0. exists g4. exists first0 first0.
- apply inv_r0. 
- unfold "=~". intro. apply (weak_functional_extensionality (first0¤g4) (Id B) ). apply (for_equiv_refl first0 g3 g4). 
+ exact inv_l0.
+ exact inv_r0.
+ apply (for_link A B first0 g3 g4). 
++ exact inv_l0.
++ exact inv_r0.
Defined.
 
Lemma question_5_2_1 : forall m n : Nat, (m = n )~=~ (Sj m = Sj n).
Proof. 
intros. apply (equiv_transitivity (m = n)  (Eq_5_b m n) (Sj m = Sj n)).
- apply Nat_equal.
- rewrite (Eq_succ m n) . apply equiv_refl. apply (Nat_equal (Sj m) (Sj n)).
Defined.

End Exercice_5.

Section Exercice_6. 

Lemma function_for_swap : Booleans_Type -> Booleans_Type.
Proof.
intros. destruct H.
- exact (onee).
- exact (zeero).
Defined.

Definition swap : Booleans_Type ~=~ Booleans_Type.
Proof.
exists function_for_swap. exists function_for_swap function_for_swap.
- unfold "=~". unfold "¤". intros. destruct x. 
+ apply refl.
+ apply refl.
- unfold "=~". unfold "¤". intros. destruct x. 
+ apply refl.
+ apply refl.
Defined.

Lemma function_for_swap_2 : Booleans_Type -> Booleans_Type.
Proof.
intros. destruct H.
- exact (zeero).
- exact (onee).
Defined.

Lemma no_swap : Booleans_Type ~=~Booleans_Type.
Proof.
exists function_for_swap_2. exists function_for_swap_2 function_for_swap_2.
- unfold "=~". unfold "¤". intros. destruct x. 
+ apply refl.
+ apply refl.
- unfold "=~". unfold "¤". intros. destruct x. 
+ apply refl.
+ apply refl.
Defined.

Lemma eq_for_swap_no_swap : (swap = no_swap) -> Empty.
Proof.
intro. 
Admitted.

End Exercice_6.

Section Exercice_7.


Record isquasiequiv (A B : Type) (f : A-> B ):=
MakeQuasiEquiv {iqe_l : B ->A ;iqe_mid : forall x : A,( iqe_l ¤ f ) (x) = x ; iqe_r : forall y : B, (f ¤ iqe_l) (y)=y}.

(*Lemma q_1 (A B : Type) (f : A  -> B) :  *)

End Exercice_7.

Section Exercice_8.

Inductive list (A : Type) : Type :=
 | nil : list A
 | cons : A -> list A -> list A.

Definition cons_inj : forall A : Type, forall a a' : A, forall l : list A,  cons A a l = cons A a' l -> a=a'.
Proof.
intros. inversion X. apply refl.
Defined.

Definition cons_inj_2 : forall A : Type, forall a : A, forall l l' : list A, cons A a l = cons A a l' -> l = l'.
Proof.
intros. inversion X. apply refl.
Defined.

Definition cons_inj_3 : forall A : Type, forall a a': A, forall l l' : list A, cons A a l = cons A a' l' -> prod (a=a')(l = l').
Proof.
intros. inversion X. split.
- apply refl.
- apply refl.
Defined.

Record Eq_list (A : Type) (a a' : A) (l l' : list A) : Type :=
Eq_list_def {p1 : a=a' ; p2 : l=l'}.

Lemma encode_q_1 (A : Type) ( a a' : A) (l l': list A) : (cons A a l = cons A a' l') -> Eq_list A a a' l l'.
Proof.
intros. apply cons_inj_3 in X. destruct X. split.
- exact fst.
- exact snd.
Defined.

Lemma decode_q_1 (A : Type) (a a' :A) (l l' : list A) : Eq_list A a a' l l' -> (cons A a l = cons A a' l').
Proof.
intros. destruct X. destruct p3. destruct p4. 
apply refl.
Defined.

Lemma q_1 (A : Type) (a a' : A) (l l' : list A) : (cons A a l = cons A a' l') ~=~ Eq_list A a a' l l'.
Proof.
exists (encode_q_1 A a a' l l'). exists (decode_q_1 A a a' l l') (decode_q_1 A a a' l l').
- unfold "=~". unfold "¤". intros. destruct x. destruct p3. destruct p4. unfold Id. apply refl.
- unfold "=~". unfold "¤". intros. unfold Id. 
Admitted.


Definition P_nat_to_Type : Nat -> Type .
Proof.
intros. destruct H.
- exact Empty.
- exact Unit_Type.
Defined.

Lemma zeronot_equal_to_one : (zero = (Sj zero)) -> Empty.
Proof.
intros. easy.
Defined.