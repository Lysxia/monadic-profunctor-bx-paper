(** * Profmonads *)

(** Some naming conventions:
  - [M]: a monad
  - [P]: a promonad
  - [A], [B]: "view types", covariant parameters of [P] and [M]
  - [U], [V]: "pre-view types", contravariant parameters of [P]
  - [Q], [Q_A], [Q_B]: a property on (pre-)views [A -> Prop], [B -> Prop]
  - [R]: a property on (pro)monadic values, possibly indexed by [Q]
 *)

Generalizable Variables M P.
Implicit Type M : Type -> Type.
Implicit Type P : Type -> Type -> Type.

(* begin hide *)
From Coq Require Import
  FunctionalExtensionality
  List.
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

#[global] Hint Mode Monad ! .

Arguments ret {M _ A}.
Arguments bind {M _ A B}.

Notation "x <- m ;; k" := (bind m (fun x => k))
(at level 90, right associativity).
Infix ">>=" := bind (at level 61, left associativity).

(** *** Laws *)

Class MonadLaws (M : Type -> Type) {Monad_M : Monad M} : Prop :=
  { bind_ret : forall A (m : M A), bind m ret = m;
    ret_bind : forall A B (a : A) (k : A -> M B), bind (ret a) k = k a;
    bind_bind : forall A B C (m : M A) (k : A -> M B) (h : B -> M C),
      bind (bind m k) h = bind m (fun a => bind (k a) h);
  }.

(** *** Derived operations and laws *)

Definition map {M : Type -> Type} `{Monad_M : Monad M} {A B : Type}
           (f : A -> B) (m : M A) :=
  x <- m;; ret (f x).

Lemma map_id `{MonadLaws M} :
  forall A, map (@id A) = @id (M A).
Proof.
  intros A; apply functional_extensionality; intros u.
  unfold map. rewrite bind_ret.
  reflexivity.
Qed.

Lemma map_map `{MonadLaws M} :
  forall A B C (f : A -> B) (g : B -> C),
    map g \u2218 map f = map (g \u2218 f).
Proof.
  intros A B C f g. apply functional_extensionality; intros u.
  unfold map, compose. rewrite bind_bind.
  f_equal.
  apply functional_extensionality; intros a.
  rewrite ret_bind.
  reflexivity.
Qed.

Lemma map_ret `{MonadLaws M} :
  forall A B (f : A -> B) (x : A),
    map f (ret x) = ret (f x).
Proof.
  intros. unfold map. rewrite ret_bind. reflexivity.
Qed.

(** ** Monads with failure *)

(* String data type that is just unit since we don't
care about the actual content of strings *)
Definition String := unit.

Class MonadFail M `{Monad M} :=
  { fail : forall A, String -> M A }.

Arguments fail {M _ _ A}.

Class MonadFailLaws (M : Type -> Type)
      `{MonadFail_M : MonadFail M} : Prop :=
  { partial_MonadLaws :> MonadLaws _;
    partial_left_zero : forall A B (k : A -> M B) (s : String),
      bind (fail s) k = fail s;
  }.

Arguments MonadFailLaws {_ _} MonadFail_M.

(** ** Example: the [option] monad **)

Instance Monad_option : Monad option :=
  {| ret _ a := Some a;
     bind := @bind_option;
  |}.

Instance MonadLaws_option : MonadLaws option.
Proof.
  constructor.
  - intros A []; auto.
  - intros; auto.
  - intros A B C m k h; simpl.
    destruct m as [a|]; simpl; auto;
      destruct (k a) as [b|]; simpl; auto;
        destruct (h b); simpl; auto.
Qed.

Instance MonadFail_option : MonadFail option :=
  { fail _ _ := None }.

Instance MonadFailLaws_option :
  MonadFailLaws MonadFail_option.
Proof.
  constructor.
  - typeclasses eauto.
  - auto.
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

Class MonadMorphism {M N} `{Monad M} `{Monad N}
      (f : forall {A}, M A -> N A) :=
  { morph_ret : forall A (a : A), f (ret a) = ret a;
    morph_bind : forall A B (m : M A) (k : A -> M B),
        f (bind m k) = bind (f m) (fun a => f (k a));
  }.

(** ** Profunctors *)

(** *** Operations *)

(** Contravariant functor in its left parameter,
  covariant functor in its second parameter. *)
Class Profunctor (P : Type -> Type -> Type) : Type :=
  dimap :
    forall {U V A B : Type}, (U -> V) -> (A -> B) -> P V A -> P U B.

(** *** Laws *)

Class ProfunctorLaws (P : Type -> Type -> Type) {Profunctor_P : Profunctor P} : Prop :=
  { dimap_id : forall U A, dimap (@id U) (@id A) = @id (P U A)
  ; dimap_compose :
      forall U V W A B C
        (f1 : W -> V) (f2 : V -> U)
        (g1 : B -> C) (g2 : A -> B),
        (dimap f1 g1 \u2218 dimap f2 g2) = dimap (f2 \u2218 f1) (g1 \u2218 g2)
  }.

(** ** Partial profunctors *)

(** *** Operations *)

Class PartialProfunctor (P : Type -> Type -> Type) : Type :=
  { asProfunctor :> Profunctor P
  ; internaliseMaybe :
      forall {A B : Type}, P A B -> P (option A) B
  }.

(** *** Laws *)

Class PartialProfunctorLaws (P : Type -> Type -> Type) {PartialProfunctor_P : PartialProfunctor P} : Prop :=
  { asProfunctorLaws :> ProfunctorLaws P
  ; internaliseMaybe_dimap :
       forall U V A B (f : U -> V) (g : A -> B) (u : P V A),
         internaliseMaybe (dimap f g u) = dimap (option_map f) g (internaliseMaybe u)
  }.


(** ** Profmonads *)

(** *** Operations *)

(** ("Profmonad" in the paper) *)
(** A promonad is a partial profunctor that's also a monad in its second
  argument. *)
Class Profmonad (P : Type -> Type -> Type) :=
  { asMonad :> forall U, Monad (P U)
  ; asPartialProfunctor :> PartialProfunctor P
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
      {Profmonad_P : Profmonad P} :=
  { asMonadLaws : forall U, MonadLaws (P U)
  ; asPartialProfunctorLaws : PartialProfunctorLaws P
  ; map_dimap : forall U A B (f : A -> B) (u : P U A), map f u = dimap id f u
  ; comap_morphism : forall U V (f : U -> V),
      MonadMorphism (fun A => comap (fun u => Some (f u)));
  }.

Existing Instance comap_morphism.
Existing Instance asMonadLaws.
Existing Instance asPartialProfunctorLaws.


(** *** Derived laws *)

Lemma comap_morph_ret {P} `{ProfmonadLaws P} U V A
      (f : U -> V) (a : A) :
  comap (fun u => Some (f u)) (ret a) = ret a.
Proof.
  match goal with
  | [ |- ?comap1 _ = _ ] =>
    let comap' := (eval pattern A in comap1) in
    change (comap' (ret a) = ret a)
  end.
  apply morph_ret.
Qed.

Lemma comap_morph_bind {P} `{ProfmonadLaws P} U V A B
      (f : V -> U) (m : P U A) (k : A -> P U B) :
  let h A := comap (fun u => Some (f u)) : P U A -> P V A in
  h B (bind m k)
  = bind (h A m) (fun a => h B (k a)).
Proof.
  apply morph_bind.
Qed.

Lemma natural_comap {P} `{ProfmonadLaws P} U U' A B
    (f : U -> option U') (u : P U' A) (k : A -> B)
  : comap f (bind u (fun x => ret (k x))) = bind (comap f u) (fun x => ret (k x)).
Proof.
  do 2 change (bind ?u _) with (map k u).
  rewrite 2 map_dimap.
  unfold comap. rewrite internaliseMaybe_dimap.
  do 2 change (dimap ?f ?f' (?g ?x)) with (compose (dimap f f') g x).
  rewrite 2 dimap_compose. f_equal.
  apply functional_extensionality; intros x; unfold compose, id.
  destruct (f x); reflexivity.
Qed.

(** ** Profmonad morphisms *)

(** *** Laws *)

Class ProfmonadMorphism {P Q : TyCon2}
      `{Profmonad P} `{Profmonad Q}
      (phi : forall U V, P U V -> Q U V) : Prop := {
    asMonadMorphism :> forall U, MonadMorphism (phi U);
    morph_comap : forall U U' V (f : U -> option U') (m : P U' V),
        phi _ _ (comap f m) = comap f (phi _ _ m);
  }.

(** ** [Fwd] promonad ***)

(** *** Definition *)

Definition Fwd (M : Type -> Type) : TyCon2 :=
  fun U A => M A.

(** *** Instances *)

Instance Monad_Fwd (M : Type -> Type) `{Monad M} :
  forall U, Monad (Fwd M U) :=
  fun U => _.

Instance MonadLaws_Fwd (M : Type -> Type) `{MonadLaws M} :
  forall U, MonadLaws (Fwd M U).
Proof.
  intro U; constructor; apply H.
Defined.

Instance MonadFail_Fwd (M : Type -> Type) `{MonadFail M} :
  forall U, MonadFail (Fwd M U) :=
  { fail _ s := fail s }.

Instance MonadFailLaws_Fwd (M : Type -> Type)
         `{MonadFailLaws M} :
  forall U, MonadFailLaws (MonadFail_Fwd M U).
Proof.
  constructor.
  - typeclasses eauto.
  - intros; simpl; apply partial_left_zero.
Defined.

Instance Profunctor_Fwd (M : Type -> Type) `{Monad M} :
  Profunctor (Fwd M) :=
  fun U V A B _f g m => map g m.

Instance PartialProfunctor_Fwd (M : Type -> Type) `{Monad M} :
  PartialProfunctor (Fwd M) :=
  {| internaliseMaybe := fun _ _ m => m |}.

Instance Profmonad_Fwd (M : Type -> Type) `{Monad M} :
  Profmonad (Fwd M) :=
  Build_Profmonad _ _ _.

Instance PartialProfunctorLaws_Fwd (M : Type -> Type) `{MonadLaws M} : PartialProfunctorLaws (Fwd M).
Proof.
  constructor.
  - constructor.
    + intros U A. unfold dimap. unfold asProfunctor. cbn. unfold Profunctor_Fwd.
      apply map_id.
    + intros. cbv [ dimap asProfunctor PartialProfunctor_Fwd Profunctor_Fwd ].
      rewrite map_map.
      reflexivity.
  - intros. reflexivity.
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
Qed.

(** ** [Bwd] promonad ***)

(** *** Definition *)

Definition Bwd (M : Type -> Type) : Type -> Type -> Type :=
  fun U A => U -> M A.

(** *** Instances *)

Instance Monad_Bwd (M : Type -> Type) `{Monad M} :
  forall U, Monad (Bwd M U) :=
  { ret A a := fun u => ret a;
    bind A B m k := fun u => bind (m u) (fun a => k a u);
  }.

Instance MonadLaws_Bwd (M : Type -> Type) `{MonadLaws M} :
  forall U, MonadLaws (Bwd M U).
Proof.
  constructor;
    intros;
    apply functional_extensionality; intro u; simpl;
    apply H.
Defined.

Instance MonadFail_Bwd (M : Type -> Type) `{MonadFail M} :
  forall U, MonadFail (Bwd M U) :=
  { fail _ s := fun _ => fail s }.

Instance MonadFailLaws_Bwd (M : Type -> Type)
         `{MonadFailLaws M} :
  forall U, MonadFailLaws (MonadFail_Bwd M U).
Proof.
  constructor; try typeclasses eauto.
  intros.
  apply functional_extensionality; intro u.
  simpl; apply partial_left_zero.
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
    + intros; cbn; unfold Profunctor_Bwd.
      rewrite map_id.
      reflexivity.
    + intros; cbn; unfold Profunctor_Bwd, compose.
      change (map ?f (map ?g ?x)) with (compose (map f) (map g) x).
      rewrite map_map.
      reflexivity.
  - intros; cbn; unfold Profunctor_Bwd.
    apply functional_extensionality; intros [ x | ]; cbn.
    + reflexivity.
    + rewrite map_fail; reflexivity.
Qed.

Instance ProfmonadLaws_Bwd (M : Type -> Type) `{MonadFailLaws M} :
  ProfmonadLaws (Bwd M).
Proof.
  constructor.
  - exact (MonadLaws_Bwd _).
  - exact (PartialProfunctorLaws_Bwd _).
  - reflexivity.
  - constructor.
    + intros; cbn. cbv [Profunctor_Bwd].
      apply functional_extensionality; intros u.
      rewrite map_id.
      reflexivity.
    + intros; cbn. cbv [Profunctor_Bwd].
      apply functional_extensionality; intros u.
      rewrite !map_id.
      reflexivity.
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

Instance MonadLaws_Product P1 P2 U
         `{MonadLaws (P1 U),
           MonadLaws (P2 U)} :
  MonadLaws (Product P1 P2 U).
Proof.
  constructor.
  - intros A []; simpl; f_equal; apply bind_ret.
  - intros A B a k; simpl; do 2 rewrite ret_bind; destruct (k a); auto.
  - intros A B C m k h; simpl; f_equal; rewrite bind_bind; auto.
Qed.

(* TODO  - may not need
Instance MonadFail_Product P1 P2 U
         `{MonadFail (P1 U),
           MonadFail (P2 U)} :
  MonadFail (Product P1 P2 U) :=
  { fail _ s := (fail s, fail s) }.

Instance MonadFailLaws_Product P1 P2 U
         `{MonadFailLaws (P1 U),
           MonadFailLaws (P2 U)} :
  MonadFailLaws (MonadFail_Product P1 P2 U).
Proof.
  constructor; try typeclasses eauto.
  intros. simpl. f_equal; apply partial_left_zero.
Defined.
*)

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
      rewrite 2 dimap_id.
      apply functional_extensionality; intros []; reflexivity.
    + intros; cbn; unfold Profunctor_Product.
      unfold compose; cbn.
      change (dimap ?f1 ?g1 (dimap ?f2 ?g2 ?x)) with (compose (dimap f1 g1) (dimap f2 g2) x).
      rewrite 2 dimap_compose.
      reflexivity.
  - intros; cbn; unfold Profunctor_Product.
    f_equal; rewrite internaliseMaybe_dimap; reflexivity.
Qed.

Instance LawfulProfmonad_Product P1 P2
         `{ProfmonadLaws P1, ProfmonadLaws P2} :
  ProfmonadLaws (Product P1 P2).
Proof.
  constructor.
  - exact (fun U => MonadLaws_Product P1 P2 U).
  - exact (PartialProfunctorLaws_Product P1 P2).
  - unfold map, dimap, asProfunctor, asPartialProfunctor, Profmonad_Product, PartialProfunctor_Product, Profunctor_Product; cbn.
    intros; f_equal; apply map_dimap.
  - constructor.
    + intros; cbn. cbv [Profunctor_Product].
      f_equal; apply comap_morph_ret + apply comap_morph_bind; auto.
    + intros; cbn; cbv [Profunctor_Product].
      f_equal; apply comap_morph_ret + apply comap_morph_bind; auto.
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
    + intros a m; apply functional_extensionality; intros x; cbn.
      destruct m; reflexivity.
    + intros *; reflexivity.
    + intros *; apply functional_extensionality; intros x; cbn.
      destruct m; reflexivity.
  - constructor.
    + constructor.
      * intros; apply functional_extensionality; intros x; cbn.
        unfold Profunctor_pfunction. apply functional_extensionality; intros.
        destruct x; reflexivity.
      * intros; apply functional_extensionality; intros; cbn.
        apply functional_extensionality; intros; cbn. destruct x; reflexivity.
    + intros. apply functional_extensionality; intros; cbn.
      destruct x; cbn; reflexivity.
  - intros *; apply functional_extensionality; intros; cbn.
    destruct u; reflexivity.
  - constructor.
    + reflexivity.
    + intros. apply functional_extensionality; intros; cbn. destruct m; cbn; reflexivity.
Qed.

(*** Compositionality ***)

Class Compositional
      {P : Type -> Type -> Type}
      `{Profmonad P}
      (R : forall A B, P A B -> Prop) : Prop :=
  {
    CompositionalWithLawful :> ProfmonadLaws _;
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
      `{Profmonad P}
      (R : forall A B, P A B -> Prop) : Prop :=
  {
    ret_comp' :
      forall A0 A a, R A0 A (ret a);
    bind_comp' :
      forall U A B (m : P U A) (k : A -> P U B) (f : B -> option A),
        (forall a, (x <- k a;; ret (f x)) = (x <- k a;; ret (Some a))) ->
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
      (forall a, (x <- k a;; ret (f x)) = (x <- k a;; ret (Some a))) ->
      R A A m ->
      (forall a, R B B (k a)) ->
      R B B (bind (comap f m) k).
Proof.
  intros. apply (bind_comp' _ _ _ _ _ f); auto.
  apply comap_comp'; auto.
Qed.

Instance Quasicompositional_Compositional {P} (R : forall A B, P A B -> Prop) `{Compositional P R}
  : Quasicompositional R.
Proof.
  destruct H0; constructor; auto.
Qed.

Definition mrange {M} `{MonadFail M} {A} (p : A -> bool) (u : M A) : Prop
  := u = (u >>= fun x => if p x then ret x else empty).

Class Compositional' (P : Type -> Type -> Type) (R : forall A B, P A B -> Prop)
    `{forall U, Monad (P U)}
    `{forall U, @MonadFail (P U) _}
    `{forall U, @MonadFailLaws (P U) _ _} : Prop :=
  { empty_comp : forall U A, R U A empty
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
    apply empty_comp.
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
    apply empty_comp.
Qed.

(**)

(* replicate preserves quasicompositional properties *)
Lemma replicate_comp P
      (R : forall U A, P U A -> Prop)
      `{ProfmonadLaws P}
      `{@Quasicompositional P _ R}
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
      f_equal.
      apply functional_extensionality; intros a0.
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
      { auto using comap_comp'. }
      { auto using ret_comp'. }
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

Lemma purify_replicate P
      `{Profmonad P}
      (phi : forall U A, P U A -> pfunction U A) (* promonad morphism *)
      `{@ProfmonadMorphism _ _ _ _ phi}
      U A (n : nat) (m : P U A) (xs : list U) :
  length xs = n ->
  phi _ _ (replicate n m) xs = traverse_option (phi _ _ m) xs.
Proof.
  intros Hn; subst; induction xs.
  - simpl; rewrite morph_ret; auto.
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
