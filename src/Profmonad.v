(** * Profmonads *)

(** Some naming conventions:
  - [M]: a monad
  - [P]: a promonad
  - [A], [B]: "view types", covariant parameters of [P] and [M]
  - [U], [V]: "pre-view types", contravariant parameters of [P]
  - [Q], [Q_A], [Q_B]: a property on (pre-)views [A -> Prop], [B -> Prop]
  - [R]: a property on (pro)monadic values, possibly indexed by [Q]
 *)

From Coq Require Import Unicode.Utf8.

Generalizable Variables M P.
Implicit Type M : Type -> Type.
Implicit Type P : Type -> Type -> Type.

(* begin hide *)
Require Import Unicode.Utf8.
From Coq Require Import
  FunctionalExtensionality
  List
  Setoid Morphisms.
Import ListNotations.

From Profmonad Require Import
  Utils.
(* end hide *)

Notation TyCon2 := (Type -> Type -> Type).

(** ** Monads ***)

(** *** Operations *)

Class Monad (M : Type -> Type) :=
  { ret : forall A, A -> M A;
    bind : forall A B, M A -> (A -> M B) -> M B;
  }.

#[global] Hint Mode Monad ! : typeclass_instances.

Arguments ret {M _ A}.
Arguments bind {M _ A B}.

Notation "x <- m ;; k" := (bind m (fun x => k))
(at level 90, right associativity).
Infix ">>=" := bind (at level 61, left associativity).

Class Setoid (A : Type) : Type :=
  { equiv : A -> A -> Prop
  ; equivalence_equiv :: Equivalence equiv
  }.

Notation Eq1 M := (forall A, Setoid (M A)).
Notation Eq2 P := (forall U A, Setoid (P U A)).

Declare Scope equiv_scope.
#[global] Open Scope equiv_scope.

Infix "==" := equiv (at level 90) : equiv_scope.


#[global]
Instance Setoid_Fun (A B : Type) `{Setoid_B : Setoid B} : Setoid (A -> B) :=
  {| equiv := pointwise_relation A equiv
  ;  equivalence_equiv := _
  |}.

(** *** Laws *)

Class MonadLaws (M : Type -> Type) {Monad_M : Monad M} {Eq_M : Eq1 M} : Prop :=
  { bind_ret : forall A (m : M A), bind m ret == m;
    ret_bind : forall A B (a : A) (k : A -> M B), bind (ret a) k == k a;
    bind_bind : forall A B C (m : M A) (k : A -> M B) (h : B -> M C),
      bind (bind m k) h == bind m (fun a => bind (k a) h);
    Proper_bind :: forall A B,
      Proper (equiv ==> pointwise_relation A equiv ==> equiv) (bind (A := A) (B := B))
  }.

(** *** Derived operations and laws *)

Definition map {M : Type -> Type} `{Monad_M : Monad M} {A B : Type}
           (f : A -> B) (m : M A) :=
  x <- m;; ret (f x).

Lemma map_id `{MonadLaws M} :
  forall A, map (@id A) == @id (M A).
Proof.
  intros A x. apply bind_ret.
Qed.

Lemma map_map `{Monad M} `{MonadLaws M} :
  forall A B C (f : A -> B) (g : B -> C),
    compose (map (M := M) g) (map f) == map (compose g f).
Proof.
  intros A B C f g u.
  unfold map, compose. rewrite bind_bind.
  setoid_rewrite ret_bind.
  reflexivity.
Qed.

Lemma map_ret `{MonadLaws M} :
  forall A B (f : A -> B) (x : A),
    map (M := M) f (ret x) == ret (f x).
Proof.
  intros *; unfold map. rewrite ret_bind. reflexivity.
Qed.

(** ** Monads with failure *)

Definition String := unit.

Class MonadFail M `{Monad M} :=
  { fail : forall A, String -> M A }.

Arguments fail {M _ _ A}.

Class MonadFailLaws (M : Type -> Type)
      `{MonadFail_M : MonadFail M}
      `{Eq1_M : Eq1 M} : Prop :=
  { partial_MonadLaws :: MonadLaws _;
    partial_left_zero : forall A B (k : A -> M B) (s : String),
      bind (fail s) k == fail s;
  }.

Definition ret_opt {M : Type -> Type}
           `{Monad_M : Monad M} `{MonadFail_M : MonadFail M}
           {A : Type}
           (oa : option A) : M A :=
  match oa with
  | None => fail tt
  | Some a => ret a
  end.

Definition map_opt {M : Type -> Type}
           `{Monad_M : Monad M} `{MonadFail_M : MonadFail M}
           {A B : Type}
           (f : A -> option B) (m : M A) :=
  x <- m;; ret_opt (f x).

Lemma map_fail {M} `{MonadFailLaws M} {A B} (f : A -> B) (s : String)
  : map f (fail s) == (fail s).
Proof.
  unfold map.
  apply partial_left_zero.
Qed.

#[global]
Instance Eq1_default (M : Type -> Type) : Eq1 M | 9 :=
  fun A => {| equiv := eq |}.

(** ** Example: the [option] monad **)

#[global]
Instance Monad_option : Monad option :=
  {| ret _ a := Some a;
     bind := @bind_option;
  |}.

#[global]
Instance MonadLaws_option : MonadLaws option.
Proof.
  constructor; unfold equiv, Eq1_default; cbn.
  - intros A []; auto.
  - intros; auto.
  - intros A B C m k h; simpl.
    destruct m as [a|]; simpl; auto;
      destruct (k a) as [b|]; simpl; auto;
        destruct (h b); simpl; auto.
  - unfold Proper, respectful. intros * <- * Hf. destruct x; cbn; [apply Hf | reflexivity].
Qed.

#[global]
Instance MonadFail_option : MonadFail option :=
  { fail _ s := None }.

Instance MonadFailLaws_option : MonadFailLaws option.
Proof.
  constructor.
  - typeclasses eauto.
  - cbn; reflexivity.
Qed.

Fixpoint traverse_option {A B} (f : A -> option B) (xs : list A) : option (list B) :=
  match xs with
  | [] => Some []
  | x :: xs =>
    y <- f x;;
    ys <- traverse_option f xs;;
    ret (y :: ys)
  end.

Lemma traverse_option_pure {A B} (f : A -> option B) (xs : list A) :
  traverse_option (fun x => Some (f x)) xs = Some (List.map f xs).
Proof.
  induction xs; auto.
  simpl; rewrite IHxs; auto.
Qed.

(** ** Monad morphisms ***)

(** *** Laws *)

Class MonadMorphism {M N} `{Monad M} `{Monad N} `{Eq1 M} `{Eq1 N}
      (f : forall {A}, M A -> N A) :=
  { morph_ret : forall A (a : A), f (ret a) == ret a;
    morph_bind : forall A B (m : M A) (k : A -> M B),
        f (bind m k) == bind (f m) (fun a => f (k a));
    Proper_morph : forall A, Proper (equiv ==> equiv) (@f A)
  }.

(** ** Profunctors *)

(** *** Operations *)

(** Contravariant functor in its left parameter,
  covariant functor in its second parameter. *)
Class Profunctor (P : Type -> Type -> Type) : Type :=
  dimap :
    forall {U V A B : Type}, (U -> V) -> (A -> B) -> P V A -> P U B.

(** *** Laws *)

Class ProfunctorLaws (P : Type -> Type -> Type) {Profunctor_P : Profunctor P} {Eq2_P : Eq2 P} : Prop :=
  { dimap_id : forall U A, dimap (@id U) (@id A) == @id (P U A)
  ; dimap_compose :
      forall U V W A B C
        (f1 : W -> V) (f2 : V -> U)
        (g1 : B -> C) (g2 : A -> B),
        (compose (dimap f1 g1) (dimap f2 g2)) == dimap (compose f2 f1) (compose g1 g2)
  ; Proper_dimap :: forall U V A B,
      Proper (pointwise_relation U eq ==> pointwise_relation A eq ==> equiv ==> equiv)
             (dimap (U := U) (V := V) (A := A) (B := B))
  }.

(** ** Partial profunctors *)

(** *** Operations *)

Class PartialProfunctor (P : Type -> Type -> Type) : Type :=
  { asProfunctor :: Profunctor P
  ; internaliseMaybe :
      forall {A B : Type}, P A B -> P (option A) B
  }.

Arguments Build_PartialProfunctor {P} &.

(** *** Laws *)

Class PartialProfunctorLaws (P : Type -> Type -> Type) {PartialProfunctor_P : PartialProfunctor P} {Eq2_P : Eq2 P} : Prop :=
  { asProfunctorLaws :: ProfunctorLaws P
  ; internaliseMaybe_dimap :
       forall U V A B (f : U -> V) (g : A -> B) (u : P V A),
         internaliseMaybe (dimap f g u) == dimap (option_map f) g (internaliseMaybe u)
  ; Proper_internaliseMaybe :: forall A B, Proper (equiv ==> equiv) (internaliseMaybe (A := A) (B := B))
  }.


(** ** Profmonads *)

(** *** Operations *)

(** ("Profmonad" in the paper) *)
(** A promonad is a partial profunctor that's also a monad in its second
  argument. *)
Class Profmonad (P : Type -> Type -> Type) :=
  { asMonad :: forall U, Monad (P U)
  ; asPartialProfunctor :: PartialProfunctor P
  }.

Definition comap {P} `{PartialProfunctor P} {U V A : Type}
  (f : U -> option V) (u : P V A) : P U A :=
  dimap f (fun x => x) (internaliseMaybe u).

Notation "x <-( f ?) m ;; m2" := (x <- comap f m ;; m2)
(at level 90, right associativity).

Notation "x <- m 'upon' f ;; m2" := (x <- comap f m ;; m2)
(at level 90, right associativity).

Notation "x <-( f ) m ;; m2" :=
  (x <- comap (fun z => Some (f z)) m ;; m2)
(at level 90, right associativity).

(** *** Laws *)

Class ProfmonadLaws (P : Type -> Type -> Type)
      {Profmonad_P : Profmonad P} {Eq2_P : Eq2 P} :=
  { asMonadLaws : forall U, MonadLaws (P U)
  ; asPartialProfunctorLaws : PartialProfunctorLaws P
  ; map_dimap : forall U A B (f : A -> B) (u : P U A), map f u == dimap id f u
  ; comap_morphism : forall U V (f : U -> V),
      MonadMorphism (fun A => comap (fun u => Some (f u)));
  }.

#[global]
Existing Instance comap_morphism.
#[global]
Existing Instance asMonadLaws.
#[global]
Existing Instance asPartialProfunctorLaws.

(** *** Derived laws *)

#[global]
Instance Proper_comap {P} `{PartialProfunctorLaws P} {U V A} : Proper (pointwise_relation U eq ==> equiv ==> equiv) (comap (U := U) (V := V) (A := A)).
Proof.
  unfold Proper, respectful.
  intros * Hf * Hp. unfold comap. apply Proper_dimap; reflexivity + auto.
  apply Proper_internaliseMaybe; assumption.
Qed.

Lemma comap_morph_ret {P} `{ProfmonadLaws P} U V A
      (f : U -> V) (a : A) :
  comap (fun u => Some (f u)) (ret a) == ret a.
Proof.
  apply (morph_ret (f := fun A x => comap (fun u => Some (f u)) x)).
Qed.

Lemma comap_morph_bind {P} `{ProfmonadLaws P} U V A B
      (f : V -> U) (m : P U A) (k : A -> P U B) :
  let h A := comap (fun u => Some (f u)) : P U A -> P V A in
  h B (bind m k)
  == bind (h A m) (fun a => h B (k a)).
Proof.
  apply morph_bind.
Qed.

Lemma equiv_apply {A B} `{Setoid B} (f g : A -> B) (x : A)
  : f == g -> f x == g x.
Proof.
  intros Hf; apply Hf.
Qed.

Lemma natural_comap {P} `{ProfmonadLaws P} U U' A B
    (f : U -> option U') (u : P U' A) (k : A -> B)
  : comap f (bind u (fun x => ret (k x))) == bind (comap f u) (fun x => ret (k x)).
Proof.
  do 2 change (bind ?u _) with (map k u).
  rewrite 2 map_dimap.
  unfold comap. rewrite internaliseMaybe_dimap.
  do 2 change (dimap ?f ?f' (?g ?x)) with (compose (dimap f f') g x).
  apply equiv_apply.
  rewrite 2 dimap_compose.
  intros p.
  apply Proper_dimap; try reflexivity.
  intros x; unfold compose, id; destruct (f x); reflexivity.
Qed.

(** ** Profmonad morphisms *)

(** *** Laws *)

Class ProfmonadMorphism {P Q : TyCon2}
      `{Profmonad P} `{Profmonad Q} `{Eq2 P} `{Eq2 Q}
      (phi : forall U V, P U V -> Q U V) : Prop := {
    asMonadMorphism :: forall U, MonadMorphism (phi U);
    morph_comap : forall U U' V (f : U -> option U') (m : P U' V),
        phi _ _ (comap f m) == comap f (phi _ _ m);
  }.

(** ** [Fwd] promonad ***)

(** *** Definition *)

Definition Fwd (M : Type -> Type) : TyCon2 :=
  fun U A => M A.

(** *** Instances *)

#[global]
Instance Monad_Fwd (M : Type -> Type) `{Monad M} :
  forall U, Monad (Fwd M U) :=
  fun U => _.

#[global]
Instance MonadLaws_Fwd (M : Type -> Type) `{MonadLaws M} :
  forall U, MonadLaws (Fwd M U).
Proof.
  intro U; constructor; apply H.
Defined.

#[global]
Instance MonadFail_Fwd (M : Type -> Type) `{MonadFail M} :
  forall U, MonadFail (Fwd M U) :=
  { fail _ := fail }.

#[global]
Instance MonadFailLaws_Fwd (M : Type -> Type)
         `{MonadFailLaws M} :
  forall U, MonadFailLaws (Fwd M U).
Proof.
  constructor.
  - typeclasses eauto.
  - intros; simpl; apply partial_left_zero.
Defined.

#[global]
Instance Profunctor_Fwd (M : Type -> Type) `{Monad M} :
  Profunctor (Fwd M) :=
  fun U V A B _f g m => map g m.

#[global]
Instance PartialProfunctor_Fwd (M : Type -> Type) `{Monad M} :
  PartialProfunctor (Fwd M) :=
  {| internaliseMaybe := fun _ _ m => m |}.

#[global]
Instance Profmonad_Fwd (M : Type -> Type) `{Monad M} :
  Profmonad (Fwd M) :=
  Build_Profmonad _ _ _.

#[global]
Instance Setoid_Fwd (M : Type -> Type) `{H : Eq1 M} U : Eq1 (Fwd M U) :=
  H.

#[global]
Instance Proper_map {M : Type -> Type} `{MonadLaws M} {A B}
  : Proper (pointwise_relation A eq ==> equiv ==> equiv) (map (A := A) (B := B)).
Proof.
  unfold Proper, respectful, map.
  intros * Hf * Hm; apply Proper_bind; auto.
  intros ?; rewrite Hf; reflexivity.
Qed.

#[global]
Instance PartialProfunctorLaws_Fwd (M : Type -> Type) `{MonadLaws M} : PartialProfunctorLaws (Fwd M).
Proof.
  constructor.
  - constructor.
    + Set Printing All. intros U A x. unfold dimap. unfold asProfunctor. Set Printing All. cbn. unfold Profunctor_Fwd.
      apply map_id.
    + intros. cbv [ dimap asProfunctor PartialProfunctor_Fwd Profunctor_Fwd ].
      rewrite map_map.
      reflexivity.
    + intros *. unfold Proper, respectful. intros * Hf * Hg * Hx. cbv [dimap asProfunctor PartialProfunctor_Fwd Profunctor_Fwd].
      apply Proper_map; auto.
  - intros. reflexivity.
  - intros. unfold Proper, respectful. intros * Hf; apply Hf.
Qed.

Instance ProfmonadLaws_Fwd (M : Type -> Type) `{MonadLaws M} :
  ProfmonadLaws (Fwd M).
Proof.
  constructor.
  - exact (MonadLaws_Fwd M).
  - exact (PartialProfunctorLaws_Fwd M).
  - reflexivity.
  - constructor.
    + intros A a.
      cbv [comap dimap asProfunctor asPartialProfunctor Profmonad_Fwd PartialProfunctor_Fwd Profunctor_Fwd internaliseMaybe map].
      rewrite ret_bind.
      reflexivity.
    + intros.
      cbv [comap dimap asProfunctor asPartialProfunctor Profmonad_Fwd PartialProfunctor_Fwd Profunctor_Fwd internaliseMaybe map].
      rewrite bind_bind.
      f_equal.
      rewrite bind_ret.
      reflexivity.
    + intros A. unfold Proper, respectful; intros. eapply Proper_comap; reflexivity + auto.
Qed.

(** ** [Bwd] promonad ***)

(** *** Definition *)

Definition Bwd (M : Type -> Type) : Type -> Type -> Type :=
  fun U A => U -> M A.

(** *** Instances *)

#[global]
Instance Monad_Bwd (M : Type -> Type) `{Monad M} :
  forall U, Monad (Bwd M U) :=
  { ret A a := fun u => ret a;
    bind A B m k := fun u => bind (m u) (fun a => k a u);
  }.

#[global]
Instance Setoid_Bwd {M} `{Eq1 M} : Eq2 (Bwd M) :=
  fun _ _ => _.

#[global]
Instance MonadLaws_Bwd (M : Type -> Type) `{MonadLaws M} :
  forall U, MonadLaws (Bwd M U).
Proof.
  constructor; intros; intros ?; cbn.
  - apply bind_ret.
  - rewrite ret_bind. reflexivity.
  - rewrite bind_bind. reflexivity.
  - unfold respectful. intros. intros u; cbn.
    apply Proper_bind; auto.
    intros a. apply H1.
Defined.

Instance MonadFail_Bwd (M : Type -> Type) `{MonadFail M} :
  forall U, MonadFail (Bwd M U) :=
  { fail _ s := fun _ => fail s }.

Instance MonadFailLaws_Bwd (M : Type -> Type)
         `{MonadFailLaws M} :
  forall U, MonadFailLaws (Bwd M U).
Proof.
  constructor; try typeclasses eauto.
  intros. intros u; cbn. apply partial_left_zero.
Defined.

Instance Profunctor_Bwd (M : Type -> Type) `{MonadFail M} :
  Profunctor (Bwd M) :=
  fun U V A B f g m => fun v => map g (m (f v)).

Instance PartialProfunctor_Bwd M `{MonadFail M} :
  PartialProfunctor (Bwd M) :=
  {| internaliseMaybe := fun U A (u : Bwd M U A) ox =>
       match ox with
       | None => fail tt
       | Some x => u x
       end
  |}.

Instance Profmonad_Bwd (M : Type -> Type) `{MonadFail M} :
  Profmonad (Bwd M) :=
  Build_Profmonad _ _ _.

Instance PartialProfunctorLaws_Bwd M `{MonadFailLaws M} :
  PartialProfunctorLaws (Bwd M).
Proof.
  constructor.
  - constructor.
    + intros; cbn; unfold Profunctor_Bwd. intros m u.
      apply map_id.
    + intros; cbn; unfold Profunctor_Bwd, compose.
      change (map ?f (map ?g ?x)) with (compose (map f) (map g) x).
      intros m w.
      apply map_map.
    + intros *. unfold Proper, respectful. cbn. unfold pointwise_relation, Profunctor_Bwd. cbn. intros.
      apply Proper_map; eauto.
      rewrite H1; auto.
  - intros; cbn; unfold Profunctor_Bwd.
    intros [ x | ]; cbn.
    + reflexivity.
    + rewrite map_fail; reflexivity.
  - unfold Proper, respectful; cbn. intros. intros []; cbn; auto. reflexivity.
Qed.

Lemma map_id' {M} `{MonadLaws M} {A} (m : M A) : map id m == m.
Proof.
  apply map_id.
Qed.

#[global]
Instance ProfmonadLaws_Bwd (M : Type -> Type) `{MonadFailLaws M} :
  ProfmonadLaws (Bwd M).
Proof.
  constructor.
  - exact (MonadLaws_Bwd _).
  - exact (PartialProfunctorLaws_Bwd _).
  - reflexivity.
  - constructor.
    + intros; cbn. cbv [Profunctor_Bwd].
      intros u. apply map_id.
    + intros; cbn. cbv [Profunctor_Bwd]. intros u. rewrite 2 map_id'.
      apply Proper_bind; [ reflexivity | intros ? ].
      rewrite map_id'. reflexivity.
    + intros A. apply Proper_comap. reflexivity.
Qed.

(** ** Product promonad ***)

(** *** Definition *)

Definition Product (P1 P2 : Type -> Type -> Type) :=
  fun U A => (P1 U A * P2 U A)%type.

(** *** Instances *)

Instance Monad_Product P1 P2 U
         `{Monad (P1 U), Monad (P2 U)} :
  Monad (Product P1 P2 U) :=
  { ret A a := (ret a, ret a);
    bind A B m k :=
      (bind (fst m) (fun a => fst (k a)),
       bind (snd m) (fun a => snd (k a)));
  }.

Definition equiv_prod {A B} (RA : relation A) (RB : relation B) : relation (A * B) :=
  fun a b => RA (fst a) (fst b) /\ RB (snd a) (snd b).

#[local] Instance Equivalence_equiv_prod {A B} {RA : relation A} {RB : relation B}
  `(!Equivalence RA) `(!Equivalence RB) : Equivalence (equiv_prod RA RB).
Proof.
  constructor.
  - intros; split; reflexivity.
  - intros ? ? Hxy; split; symmetry; apply Hxy.
  - intros ? ? ? Hxy Hyz; split; etransitivity; apply Hxy + apply Hyz.
Qed.

#[global]
Instance Setoid_Product `(Eq2 P1) `(Eq2 P2) : Eq2 (Product P1 P2) :=
  fun U A => {| equiv := equiv_prod equiv equiv |}.

#[global]
Instance Proper_pair {P Q} `{Eq2 P, Eq2 Q} {U V} : Proper (equiv ==> equiv ==> equiv) (@pair (P U V) (Q U V)).
Proof.
  unfold Proper, respectful; constructor; auto.
Qed.

#[global]
Instance MonadLaws_Product P1 P2 U
         `{Monad (P1 U), Monad (P2 U)}
         `{Eq2 P1, Eq2 P2}
         `{!MonadLaws (P1 U), !MonadLaws (P2 U)} :
  MonadLaws (Product P1 P2 U).
Proof.
  constructor.
  - intros A []; constructor; cbn; apply bind_ret.
  - intros A B a k; simpl. do 2 rewrite ret_bind; destruct (k a); reflexivity.
  - intros A B C m k h; simpl; rewrite 2 bind_bind; reflexivity.
  - intros A B; simpl; unfold Proper, respectful; intros; constructor; apply Proper_bind.
    + apply H1.
    + intros ?; apply H2.
    + apply H1.
    + intros ?; apply H2.
Qed.

Instance MonadFail_Product P1 P2 U
         `{MonadFail (P1 U),
           MonadFail (P2 U)} :
  MonadFail (Product P1 P2 U) :=
  { fail _ s := (fail s, fail s) }.

Instance MonadFailLaws_Product P1 P2 U
         `{Eq2 P1, Eq2 P2}
         `{MonadFail (P1 U), MonadFail (P2 U)}
         `{!MonadFailLaws (P1 U),
           !MonadFailLaws (P2 U)} :
  MonadFailLaws (Product P1 P2 U).
Proof.
  constructor; try typeclasses eauto.
  intros. simpl. constructor; apply partial_left_zero.
Defined.

Instance Profunctor_Product P1 P2 `{Profunctor P1} `{Profunctor P2} : Profunctor (Product P1 P2) :=
  fun U V A B f g u => (dimap f g (fst u), dimap f g (snd u)).

Instance PartialProfunctor_Product P1 P2 `{PartialProfunctor P1} `{PartialProfunctor P2} : PartialProfunctor (Product P1 P2) :=
  {| asProfunctor := Profunctor_Product P1 P2
   ; internaliseMaybe := fun A B u => (internaliseMaybe (fst u), internaliseMaybe (snd u)) |}.

Instance Profmonad_Product P1 P2
         `{Profmonad P1, Profmonad P2} :
  Profmonad (Product P1 P2) :=
  Build_Profmonad _ _ _.

Lemma comap_as_morph P `{Profmonad P} U V A f :
  comap f = (fun A => @comap P _ U V A f) A.
Proof. auto. Qed.

Instance PartialProfunctorLaws_Product P1 P2
         `{PartialProfunctorLaws P1, PartialProfunctorLaws P2} :
  PartialProfunctorLaws (Product P1 P2).
Proof.
  constructor.
  - constructor.
    + intros; cbn; unfold Profunctor_Product.
      intros p; constructor; cbn; apply dimap_id.
    + intros; cbn; unfold Profunctor_Product.
      unfold compose; cbn. constructor; cbn; apply dimap_compose.
    + unfold Proper, respectful; cbn; constructor; cbn.
      * apply Proper_dimap; auto. apply H3.
      * apply Proper_dimap; auto. apply H3.
  - intros; cbn; unfold Profunctor_Product.
    f_equal; rewrite 2 internaliseMaybe_dimap; reflexivity.
  - constructor; cbn; apply Proper_internaliseMaybe; apply H1.
Qed.

Instance LawfulProfmonad_Product P1 P2
         `{ProfmonadLaws P1, ProfmonadLaws P2} :
  ProfmonadLaws (Product P1 P2).
Proof.
  constructor.
  - exact (fun U => MonadLaws_Product P1 P2 U).
  - exact (PartialProfunctorLaws_Product P1 P2).
  - unfold map, dimap, asProfunctor, asPartialProfunctor, Profmonad_Product, PartialProfunctor_Product, Profunctor_Product; cbn.
    intros; constructor; apply map_dimap.
  - constructor.
    + intros; cbn. cbv [Profunctor_Product].
      constructor; apply comap_morph_ret + apply comap_morph_bind; auto.
    + intros; cbn; cbv [Profunctor_Product].
      constructor; apply comap_morph_ret + apply comap_morph_bind; auto.
    + intros; apply Proper_comap; reflexivity.
Qed.

(*****)


(* Common combinators *)

Fixpoint replicate `{Profmonad P} {U A} (n : nat) (m : P U A)
  : P (list U) (list A) :=
  match n with
  | O => ret []
  | S n' =>
    x  <- m  upon head;;
    xs <- (replicate n' m)  upon tail;;
    ret (x :: xs)
  end.

Arguments replicate {P _ U A}.

Definition hom (P1 P2 : Type -> Type -> Type) : Type :=
  forall A B, P1 A B -> P2 A B.

Definition pfunction (A B : Type) : Type := A -> option B.

#[global] Instance Setoid_pfunction {A B} : Setoid (pfunction A B) :=
  {| equiv := pointwise_relation A eq |}.

#[global] Instance Monad_pfunction {A} : Monad (pfunction A) := {|
  ret _ a := fun _ => Some a;
  bind _ _ m k u := x <- m u;; k x u;
|}.

#[global] Instance Profunctor_pfunction : Profunctor pfunction :=
  fun _ _ _ _ f g u x =>
    option_map g (u (f x)).

#[global] Instance PartialProfunctor_pfunction : PartialProfunctor pfunction :=
  {| internaliseMaybe := fun U A (u : pfunction U A) (x : option U) => bind_option x u |}.

#[global] Instance Profmonad_pfunction : Profmonad pfunction :=
  Build_Profmonad _ _ _.

Arguments Profunctor_pfunction _ _ _ _ _ _ _ _ /.
Arguments compose _ _ _ _ _ _ /.
Arguments id _ _ /.

#[global] Instance ProfmonadLaws_pfunction : ProfmonadLaws pfunction.
Proof.
  constructor.
  - constructor.
    + intros a m x; cbn. destruct m; reflexivity.
    + intros *; reflexivity.
    + intros * x; cbn. destruct m; reflexivity.
    + unfold Proper, respectful; cbn. intros. intros u.
      rewrite H. destruct y; cbn; [ rewrite H0 | ]; reflexivity.
  - constructor.
    + constructor.
      * intros U A x; cbn.
        unfold Profunctor_pfunction. intros u.
        destruct x; reflexivity.
      * intros * x u; cbn; destruct x; reflexivity.
      * unfold Proper, respectful. cbv. intros. rewrite H, H1. destruct y1; auto. rewrite H0; auto.
    + cbv. intros. destruct a; auto.
    + cbv; intros; destruct a; auto.
  - cbv; intros; auto.
  - constructor.
    + cbv; intros; auto.
    + cbv; intros; destruct m; auto.
    + cbv; intros; rewrite H; auto.
Qed.

(*** Compositionality ***)

Class Compositional
      {P : Type -> Type -> Type}
      `{ProfmonadLaws P}
      (R : forall A B, P A B -> Prop) : Prop :=
  {
    ret_comp :
      forall U A (a : A), R U A (ret a : P U A);
    bind_comp :
      forall U A B (m : P U A) (k : A -> P U B) ,
        R U A m ->
        (forall a, R U B (k a)) ->
        R U B (bind m k);
    comap_comp :
      forall U V A (f : U -> option V) (m : P V A),
        R V A m ->
        R U A (comap f m);
  }.

(*** Quasicompositionality ***)

Class Quasicompositional
      {P : Type -> Type -> Type}
      `{ProfmonadLaws P}
      (R : forall A B, P A B -> Prop) : Prop :=
  {
    ret_comp' :
      forall A0 A a, R A0 A (ret a);
    bind_comp' :
      forall U A B (m : P U A) (k : A -> P U B) (f : B -> option A),
        (forall a, (x <- k a;; ret (f x)) == (x <- k a;; ret (Some a))) ->
        R U A m ->
        (forall a, R U B (k a)) ->
        R U B (bind m k);
    comap_comp' :
      forall U V A (f : U -> option V) (m : P V A),
        R V A m -> R U A (comap f m)
  }.

Lemma bind_comap_comp' {P} {R : forall A B, P A B -> Prop}
    `{Quasicompositional P R}
  : forall A B (m : P A A) (k : A -> P B B) (f : B -> option A),
      (forall a, (x <- k a;; ret (f x)) == (x <- k a;; ret (Some a))) ->
      R A A m ->
      (forall a, R B B (k a)) ->
      R B B (bind (comap f m) k).
Proof.
  intros. apply (bind_comp' _ _ _ _ _ f); auto.
  apply comap_comp'; auto.
Qed.

#[global]
Instance Quasicompositional_Compositional {P} (R : forall A B, P A B -> Prop) `{Compositional P R}
  : Quasicompositional R.
Proof.
  destruct H0; constructor; auto.
Qed.

Definition mrange {M} `{MonadFail M} {A} (p : A -> bool) (u : M A) : Prop
  := u = (u >>= fun x => if p x then ret x else fail tt).

(*
Class Compositional' (P : Type -> Type -> Type) (R : forall A B, P A B -> Prop)
    `{forall U, Monad (P U)}
    `{forall U, @MonadFail (P U) _}
    `{forall U, @MonadFailLaws (P U) _ _} : Prop :=
  { fail_comp : forall U A, R U A fail
  }.

Lemma bind_comp_range {P} {R : forall A B, P A B -> Prop}
    `{Compositional P R}
    `{!forall U, @MonadFail (P U) _}
    `{!forall U, @MonadFailLaws (P U) _ _}
    `{!Compositional' P R}
  : forall U A B (p : A -> bool) (m : P U A) (k : A -> P U B) ,
      mrange p m ->
      R U A m ->
      (forall a, p a = true -> R U B (k a)) ->
      R U B (bind m k).
Proof.
  intros * Hmrange Hm Hk.
  rewrite Hmrange, bind_bind.
  apply bind_comp; [ auto | ].
  intros; destruct (p a) eqn:Hpa.
  - rewrite ret_bind; auto.
  - rewrite partial_left_zero.
    apply fail_comp.
Qed.

Lemma bind_comp_range' {P} {R : forall A B, P A B -> Prop}
    `{Quasicompositional P R}
    `{!forall U, @MonadFail (P U) _}
    `{!forall U, @MonadFailLaws (P U) _ _}
    `{!Compositional' P R}
  : forall U A B (p : A -> bool) (m : P U A) (k : A -> P U B) (f : B -> option A),
      mrange p m ->
      (forall a, (x <- k a;; ret (f x)) = (x <- k a;; ret (Some a))) ->
      R U A m ->
      (forall a, p a = true -> R U B (k a)) ->
      R U B (bind m k).
Proof.
  intros * Hmrange Hsag Hm Hk.
  rewrite Hmrange, bind_bind.
  eapply bind_comp'; [ | auto | ].
  { intros; destruct (p a).
    - rewrite ret_bind; auto.
    - rewrite 3 partial_left_zero. reflexivity. }
  intros; destruct (p a) eqn:Hpa.
  - rewrite ret_bind; auto.
  - rewrite partial_left_zero.
    apply fail_comp.
Qed.
*)

(**)

(* replicate preserves quasicompositional properties *)
Lemma replicate_comp {P}
      {R : forall U A, P U A -> Prop}
      `{Quasicompositional _ R}
      U A (n : nat) (m : P U A)
  : R _ _ m ->
    R _ _ (replicate n m).
Proof.
  intro Hm.
  induction n.
  - apply ret_comp'.
  - cbn [replicate].
    apply bind_comp' with (f := head); auto.
    { intros a.
      rewrite 2 bind_bind.
      apply Proper_bind; [ reflexivity | ]. intros ?.
      rewrite 2 ret_bind.
      reflexivity.
    }
    { apply comap_comp'; auto. }
    { intros a.
      apply bind_comp' with (f := tail); auto.
      { intros xs.
        rewrite 2 ret_bind.
        reflexivity.
      }
      { apply comap_comp'. auto. }
      { intros a'. apply ret_comp'. }
    }
Qed.

Lemma eta_option {A} (ox : option A) : match ox with Some a => Some a | None => None end = ox.
Proof.
  destruct ox; reflexivity.
Qed.

Lemma comap_apply {U V A} (f : U -> option V) (u : pfunction V A) (x : U) :
  comap f u x = bind_option (f x) u.
Proof.
  cbv. apply eta_option.
Qed.

Lemma bind_cong `{Monad M} {A B} (u1 u2 : M A) (k1 k2 : A -> M B) :
  u1 = u2 ->
  (forall a, k1 a = k2 a) ->
  bind u1 k1 = bind u2 k2.
Proof.
  intros; f_equal; auto.
  apply functional_extensionality. auto.
Qed.

Lemma f_equal2 {A B C} (f : A -> B -> C) a1 a2 b1 b2 :
  a1 = a2 ->
  b1 = b2 ->
  f a1 b1 = f a2 b2.
Proof.
  intros; f_equal; auto.
Qed.

(*
Lemma purify_replicate P
      `{Profmonad P}
      `{Eq2 P}
      (phi : forall U A, P U A -> pfunction U A) (* promonad morphism *)
      `{@ProfmonadMorphism _ _ _ _ _ _ phi}
      U A (n : nat) (m : P U A) (xs : list U) :
  length xs = n ->
  phi _ _ (replicate n m) xs == traverse_option (phi _ _ m) xs.
Proof.
  intros Hn; subst; induction xs.
  - cbn [replicate length].

  - cbn [length replicate traverse_option].
    rewrite morph_bind, morph_comap.
    cbn [ bind asMonad Profmonad_pfunction Monad_pfunction ].
    rewrite comap_apply. cbn [head bind_option].
    apply f_equal.
    apply functional_extensionality. intro y.
    rewrite morph_bind, morph_comap.
    cbn [ bind asMonad Profmonad_pfunction Monad_pfunction ].
    rewrite comap_apply. cbn [tail bind_option].
    rewrite IHxs.
    f_equal. apply functional_extensionality. intro ys.
    rewrite morph_ret; auto.
Qed.

Instance Monad_list : Monad list :=
  {| ret := fun A x => x :: nil
  ;  bind := fun A B xs k => List.flat_map k xs
  |}.

Instance MonadLaws_list : MonadLaws list.
Proof.
  constructor; cbn; intros.
  - induction m; cbn; f_equal; auto.
  - apply app_nil_r.
  - induction m; cbn; f_equal; auto.
    rewrite flat_map_app; f_equal; auto.
Qed.
*)

Class Idiomcompositional
      {P : Type -> Type -> Type}
      `{ProfmonadLaws P}
      (R : forall A, P A A -> Prop) : Prop :=
  {
    ret_idiomcomp :
      forall A a, R A (ret a);
    bind_idiomcomp :
      forall A B (m : P A A) (k : A -> P B B) (f : B -> option A),
        (forall a, (x <- k a;; ret (f x)) == (x <- k a;; ret (Some a))) ->
        R A m ->
        (forall a, R B (k a)) ->
        R B (bind (Profmonad.comap f m) k);
  }.
