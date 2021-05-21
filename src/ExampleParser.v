(** * Biparsers *)

(* The main results formalized here are
   [Compositional_weak_backward]:
     weak backward round tripping is compositional;
     in particular it is preserved by [bind] ([weak_backward_bind]).
   [Quasicompositional_weak_forward]:
     weak forward round tripping is quasicompositional;
     in particular it is preserved by [bind]
     when the continuation is an injective arrow
     ([weak_forward_bind]). *)

Generalizable Variables P.

(* begin hide *)
From Coq Require Import
  FunctionalExtensionality
  PeanoNat
  List.
Import ListNotations.

From Promonad Require Import
  Promonad
  Utils.
(* end hide *)

(** ** Parser primitives *)

(** Type of tokens *)
Definition t : Type := nat.

(** Parse a token using [biparse_token].
  More complex biparsers are defined using promonadic operations. *)
Class Biparser (P : Type -> Type -> Type) :=
  { Biparser_Promonad :> Promonad P;
    Biparser_Partial :> forall U, MonadPartial (P U);
    biparse_token : P t t;
  }.

Arguments biparse_token {P _}.

(** ** Example biparsers *)

(** Get a single [nat] token less than b. *)
Definition biparse_digit `{Biparser P} (b : nat) : P nat nat :=
  x <- biparse_token ;;
  if Nat.leb b x then
    empty
  else
    ret x.

(** Parse a k-digit number in base b *)
Fixpoint biparse_nat `{Biparser P} (b : nat) (k : nat)
  : P nat nat :=
  match k with
  | O => ret 0
  | S k' =>
    x <-( fun z => Nat.div z b ) biparse_nat b k';;
    y <-( fun z => Nat.modulo z b ) biparse_digit b ;;
    ret (b * x + y)
  end.

(** Parse a length n followed by a list of nat-tokens ("string"). *)
Definition biparse_string `{Biparser P} : P (list nat) (list nat) :=
  n <-( @length _ ) biparse_nat 10 3;;
  replicate n biparse_token.

(** ** Instances *)

(** *** Products *)

Instance Biparser_product P1 P2 `{Biparser P1, Biparser P2} :
  Biparser (Product P1 P2) :=
  { biparse_token := (biparse_token, biparse_token);
  }.

(** *** Parser promonad ***)

(** Input streams *)
Definition stream := list t.

(** **** Parser monad *)

Definition parser (A : Type) : Type := stream -> option (A * stream).

Instance Monad_parser : Monad parser :=
  { ret A x := fun s => Some (x, s);
    bind A B m k := fun s =>
      bind (m s) (fun '(a, s') => k a s')
  }.

Instance MonadLaws_parser : MonadLaws parser.
Proof.
  constructor.

  - intros.
    apply functional_extensionality.
    intro s.
    simpl.
    destruct (m s) as [ [ ] | ]; auto.

  - intros.
    apply functional_extensionality.
    intro s.
    simpl.
    auto.

  - intros.
    apply functional_extensionality.
    intro s.
    simpl.
    destruct (m s) as [ [ ] | ]; simpl; auto.
Qed.

Instance MonadPartial_parser : MonadPartial parser :=
  { empty := fun _ _ => None }.

(** **** Parser promonad *)

Definition parser2 := Fwd parser.

Definition Promonad_parser2 := Promonad_Fwd parser.

Instance Biparser_parser2 : Biparser parser2 :=
  { biparse_token s :=
      match s with
      | [] => None
      | n :: s' => Some (n, s')
      end
  }.


(** *** Printer promonad ***)

(** **** Printer monad *)

Definition printer (A : Type) := option (stream * A).

Instance Monad_printer : Monad printer :=
  { ret A a := Some ([], a);
    bind A B m k :=
      @bind option _ _ _ m (fun '(s, a) =>
      @bind option _ _ _ (k a) (fun '(s', b) =>
      Some (s ++ s', b)));
  }.

Instance MonadLaws_printer : MonadLaws printer.
Proof.
  constructor.

  - intros.
    destruct m as [[]|]; auto.
    simpl.
    rewrite app_nil_r.
    auto.

  - intros.
    simpl.
    destruct (k a) as [[]|]; simpl; auto.

  - intros. simpl.
    destruct m as [[]|]; simpl; auto.
    destruct (k a) as [[]|]; simpl; auto.
    destruct (h b) as [[]|]; simpl; auto.
    rewrite app_assoc.
    auto.
Qed.

Instance MonadPartial_printer : MonadPartial printer :=
  { empty A := None }.

Instance MonadPartialLaws_printer :
  MonadPartialLaws (MonadPartial_printer).
Proof.
  constructor; try typeclasses eauto; auto.
Qed.

(** **** Printer promonad *)

Definition printer2 := Bwd printer.

Instance Biparser_printer2 : Biparser printer2 :=
  { biparse_token := (fun n => Some ([n], n));
  }.

Instance Biparser_pure : Biparser pfunction :=
  {|
    biparse_token := (fun n => Some n) : pfunction nat nat;
  |}.

(* Extract the pure component of the printer *)
Definition printer_to_pure {U A} : printer2 U A -> pfunction U A :=
  fun m u =>
    match m u with
    | None => None
    | Some (_, a) => Some a
    end.

(* printer_to_pure is a monad homomorphism. *)
Lemma ptp_ret_hom U A (a : A)
  : forall u, printer_to_pure (ret a) u = (ret a : pfunction U A) u.
Proof. intro; auto. Qed.

Lemma ptp_bind_hom U A B (m : printer2 U A) (k : A -> printer2 U B)
  : forall u,
    printer_to_pure (bind m k) u
    = bind (printer_to_pure m) (fun a => printer_to_pure (k a)) u.
Proof.
  intro.
  unfold printer_to_pure; simpl.
  destruct (m u) as [ [ ? a ] | ].
  - simpl; destruct (k a u) as [ [ ? b ] | ]; auto.
  - auto.
Qed.

(** *** The biparser promonad *)

(** The product of parser and printer promonads *)
Definition biparser : Type -> Type -> Type := Product parser2 printer2.

(** ** Roundtrip properties *)

(** *** Strong roundtrip properties *)

Definition left_round_trip A (P : A -> Prop)
           (pa : parser2 A A) (pr : printer2 A A)
  : Prop :=
  forall a, P a ->
    match pr a with
    | None => True
    | Some (s, _) => pa s = Some (a, [])
    end.

(* We have proved [biparse_string_left_round_trip] *)

Definition right_round_trip A (pa : parser2 A A) (pr : printer2 A A)
  : Prop :=
  forall s,
    match pa s with
    | None => True
    | Some (a, []) =>
      match pr a with
      | None => False
      | Some (s', _) => s = s'
      end
    | Some _ => True
    end.

Definition backward {A} (p : biparser A A) : Prop :=
  forall (a : A) (s s' : list t),
    (exists a', snd p a = Some (s, a')) ->
    fst p (s ++ s') = Some (a, s').

Definition forward {A} (p : biparser A A) : Prop :=
  forall (a : A) (s01 s1 s0 : list t),
    fst p s01 = Some (a, s1) ->
    (exists a', snd p a = Some (s0, a')) ->
    s01 = s0 ++ s1.

(** *** Weak but compositional roundtrip properties *)

Definition weak_backward {U A} (p : biparser U A) : Prop :=
  forall (u : U) (a : A) (s s' : list t),
    snd p u = Some (s, a) ->
    fst p (s ++ s') = Some (a, s').

Definition weak_forward {U A} (p : biparser U A) : Prop :=
  forall (u : U) (a : A) (s01 s1 s0 : list t),
    fst p s01 = Some (a, s1) ->
    snd p u = Some (s0, a) ->
    s01 = s0 ++ s1.

(** *** Purification, alignment *)

Definition purify {U V} (p : biparser U V) : pfunction U V :=
  fun a => option_map snd (snd p a).

Definition aligned {A} (p : biparser A A) : Prop :=
  forall (a : A),
    exists s0, snd p a = Some (s0, a).

Definition aligned_ {U A} (f : U -> A) (p : biparser U A) : Prop :=
  forall (u : U),
    (exists s0, snd p u = Some (s0, f u)).

Definition aligned' {A} (p : pfunction A A) : Prop :=
  forall (a : A), p a = Some a.

Theorem aligned_equiv {A} (p : biparser A A)
  : aligned p <-> aligned' (purify p).
Proof.
  split; intros H a; unfold aligned, aligned', purify in *.
  - destruct (H a) as [s E].
    rewrite E; reflexivity.
  - specialize (H a).
    destruct (snd p a) as [ [] | ]; cbn in H; try discriminate.
    injection H; intros []; eauto.
Qed.

(** ** Connection between strong and weak roundtrip properties **)

Theorem backward_aligned {A} (p : biparser A A) :
  aligned p ->
  weak_backward p ->
  backward p.
Proof.
  intros ALIGNED WBWD a s s' [a' Ea].
  destruct (ALIGNED a).
  rewrite Ea in H.
  injection H; intros [] [].
  apply (WBWD _ _ _ _ Ea).
Qed.

Theorem forward_aligned {A} (p : biparser A A) :
  aligned p ->
  weak_forward p ->
  forward p.
Proof.
  intros ALIGNED WFWD a s01 s1 s0 E01 [a' E0].
  destruct (ALIGNED a).
  rewrite E0 in H.
  injection H. intros; subst.
  eapply WFWD; eauto.
Qed.

(** ** Compositionality of weak roundtrip properties *)

Lemma weak_backward_ret U A (a : A) : @weak_backward U A (ret a).
Proof.
  intros u b s s' e; inversion_clear e; reflexivity.
Qed.

Lemma weak_backward_comap U U' A (f : U -> option U')
      (m : biparser U' A)
      (Hm : weak_backward m) :
  weak_backward (comap f m).
Proof.
  intros u b s s' e.
  cbn in *.
  destruct (f u) eqn:ef; try discriminate.
  destruct snd as [[] | ] eqn:E.
  - cbn in e. rewrite app_nil_r in e. injection e. intros ? ?; subst. clear e.
    eapply Hm in E.
    rewrite E.
    eauto.
  - discriminate.
Qed.

Lemma weak_backward_bind U A B
      (m : biparser U A) (k : A -> biparser U B)
      (Hm : weak_backward m)
      (Hk : forall a, weak_backward (k a)) :
  weak_backward (bind m k).
Proof.
  intros u b s s'.
  simpl.
  destruct (snd m u) as [ [s1 a] | ] eqn:em; simpl; try discriminate.
  destruct (snd (k a) u) as [ [s2 b'] | ] eqn:ek; simpl; try discriminate.
  intros Hmk.
  inversion Hmk.
  eapply Hm in em.
  eapply Hk in ek.
  rewrite <- app_assoc.
  rewrite em; simpl.
  rewrite ek.
  subst; reflexivity.
Qed.

Instance Compositional_weak_backward :
  Compositional (@weak_backward) := {
  ret_comp := weak_backward_ret;
  bind_comp := weak_backward_bind;
  comap_comp := weak_backward_comap;
}.

Lemma weak_backward_empty U A :
  weak_backward (@empty (biparser U) _ _ A).
Proof.
  discriminate.
Qed.

Lemma weak_backward_token :
  weak_backward biparse_token.
Proof.
  intros u b s s' H; inversion H; subst; reflexivity.
Qed.

Lemma weak_forward_ret U A (a : A) : @weak_forward U A (ret a).
Proof.
  intros u b s s' s'' e e';
    inversion_clear e; inversion_clear e'; reflexivity.
Qed.

Lemma weak_forward_comap U U' A (f : U -> option U')
      (m : biparser U' A)
      (Hm : weak_forward m) :
  weak_forward (comap f m).
Proof.
  intros u b s s' s'' e e'.
  cbn in *.
  destruct (f u) eqn:ef; try discriminate.
  destruct fst as [[]|] eqn:E1; try discriminate.
  destruct snd as [[]|] eqn:E2; try discriminate.
  cbn in *.
  injection e; injection e'; intros; subst; clear e e'.
  rewrite app_nil_r.
  eapply Hm; eassumption.
Qed.

Lemma weak_forward_bind U A B
      (m : biparser U A) (k : A -> biparser U B) (f : B -> option A)
      (Hf : forall a, (x <- k a;; ret (f x)) = (x <- k a;; ret (Some a)))
      (Hm : weak_forward m)
      (Hk : forall a, weak_forward (k a)) :
  weak_forward (bind m k).
Proof.
  intros u b s01 s1 s0 Hparse Hprint.
  simpl in *.
  destruct fst as [ [a1 s__m1] | ] eqn:em1 in Hparse; try discriminate;
    simpl in Hparse;
    destruct fst as [ [b1 s__mk1] | ] eqn:ek1 in Hparse; try discriminate;
    inversion Hparse; clear Hparse; subst.
  destruct snd as [ [s__m2 a2] | ] eqn:em2 in Hprint; try discriminate;
    simpl in Hprint;
    destruct snd as [ [s__mk2 b2] | ] eqn:ek2 in Hprint; try discriminate;
    inversion Hprint; clear Hprint; subst.
  assert (ea : a2 = a1).
  { pose proof (Hf a1) as Hf1.
    apply (f_equal (fun f => fst f s__m1)) in Hf1; simpl in Hf1.
    rewrite ek1 in Hf1; inversion Hf1.
    pose proof (Hf a2) as Hf2.
    apply (f_equal (fun f => snd f u)) in Hf2; simpl in Hf2.
    rewrite ek2 in Hf2; inversion Hf2.
    rewrite H0 in H1; inversion H1.
    reflexivity.
  }
  subst.
  specialize (Hm u a1 s01 s__m1 s__m2 em1 em2).
  specialize (Hk a1 u b s__m1 s1 s__mk2 ek1 ek2).
  subst.
  apply app_assoc.
Qed.

Instance Quasicompositional_weak_forward :
  Quasicompositional (@weak_forward) := {
  ret_comp' := weak_forward_ret;
  bind_comp' := weak_forward_bind;
  comap_comp' := weak_forward_comap;
}.

Lemma weak_forward_empty U A :
  weak_forward (@empty (biparser U) _ _ A).
Proof.
  discriminate.
Qed.

Lemma weak_forward_token :
  weak_forward biparse_token.
Proof.
  intros u b s s' s'' H1 H2.
  destruct s; simpl in *.
  - discriminate.
  - inversion H1; inversion H2; subst.
    reflexivity.
Qed.

(**)

Lemma weak_forward_digit {b} : weak_forward (biparse_digit b).
Proof.
  unfold biparse_digit, weak_forward.
Abort.

Lemma weak_backward_digit {b} : weak_backward (biparse_digit b).
Proof.
  unfold biparse_digit.
  apply bind_comp.
  - apply weak_backward_token.
  - intros a.
    destruct (Nat.leb_spec b a).
    + apply weak_backward_empty.
    + apply weak_backward_ret.
Qed.

Lemma weak_backward_replicate {A} {n} {p : biparser A A}
  : weak_backward p ->
    weak_backward (replicate n p).
Proof.
  apply replicate_comp; typeclasses eauto.
Qed.

Lemma weak_forward_replicate {A} {n} {p : biparser A A}
  : weak_forward p ->
    weak_forward (replicate n p).
Proof.
  apply replicate_comp; typeclasses eauto.
Qed.

Lemma weak_forward_nat b k : weak_forward (biparse_nat b k).
Proof.
Admitted.

Lemma fmap_fmap_ {M} `{MonadLaws M} A B C (u : M A) (f : A -> B) (g : B -> C)
  : (u >>= fun x => ret (g (f x))) = ((u >>= fun x => ret (f x)) >>= fun y => ret (g y)).
Proof.
  rewrite bind_bind.
  f_equal. apply functional_extensionality. intros x.
  rewrite ret_bind.
  reflexivity.
Qed.

Lemma comap_bind_morph' {U U' A B} (f : U -> option U') (u : Product parser2 printer2 U' A) (k : A -> B)
  : comap f (bind u (fun x => ret (k x))) = bind (comap f u) (fun x => ret (k x)).
Proof.
  cbn. unfold Profunctor_Product; cbn.
  f_equal.
  - apply functional_extensionality; intros s.
    destruct (fst u s) as [ [] | ]; cbn; auto.
  - apply functional_extensionality; intros s; cbn.
    destruct (f s) as [ | ]; cbn; auto.
    destruct (snd u u0) as [ [] | ]; cbn; auto.
Qed.

Class PLaw' P `{Biparser P} : Prop :=
  plaw' : forall U U' A B (f : U -> option U') (u : P U' A) (k : A -> B),
    comap f (bind u (fun x => ret (k x))) = bind (comap f u) (fun x => ret (k x)).

Instance PLaw'_biparser : PLaw' (Product parser2 printer2).
Proof.
  exact @comap_bind_morph'.
Qed.

Lemma replicate_length {P} `{Biparser P} `{PLaw' P} {PL : PromonadLaws P} (n : nat)
  : replicate (P := P) n biparse_token >>= (fun x : list t => ret (List.length x))
  = replicate n biparse_token >>= (fun _ : list t => ret n).
Proof.
  induction n; cbn.
  - rewrite 2 ret_bind. reflexivity.
  - rewrite !bind_bind. f_equal. apply functional_extensionality. intros x.
    rewrite !bind_bind.
    transitivity (comap (P := P) tail (replicate n biparse_token >>= fun x => ret (length x)) >>= fun n => ret (S n)).
    + rewrite plaw'. rewrite !bind_bind. f_equal; apply functional_extensionality; intros xs.
      rewrite 2 ret_bind. reflexivity.
    + rewrite IHn. rewrite plaw', !bind_bind. f_equal; apply functional_extensionality; intros xs.
      rewrite 2 ret_bind. reflexivity.
Qed.

Lemma replicate_length_ {P} `{Biparser P} {PL : PromonadLaws P} `{!PLaw' P} (n : nat)
  : replicate (P := P) n biparse_token >>= (fun x : list t => ret (Some (List.length x)))
  = replicate n biparse_token >>= (fun _ : list t => ret (Some n)).
Proof.
  rewrite fmap_fmap_.
  rewrite fmap_fmap_ with (f := fun _ => n).
  f_equal.
  apply replicate_length.
Qed.

Theorem weak_forward_string
  : weak_forward biparse_string.
Proof.
  unfold biparse_string.
  eapply bind_comp' with (f := fun x => Some (List.length x)).
  2:{ apply comap_comp'. apply weak_forward_nat. }
  2:{ intros a; apply weak_forward_replicate. apply weak_forward_token. }
  { apply replicate_length_. }
Qed.
