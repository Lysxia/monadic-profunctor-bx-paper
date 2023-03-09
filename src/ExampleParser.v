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

Ltac inv H := inversion H; subst; clear H.

Generalizable Variables P.

(* begin hide *)
From Coq Require Import
  FunctionalExtensionality
  Arith
  List.
Import ListNotations.

From Profmonad Require Import
  Profmonad
  Utils.
(* end hide *)

(** ** Parser primitives *)

(** Type of tokens *)
Definition t : Type := nat.

(** Parse a token using [biparse_token].
  More complex biparsers are defined using promonadic operations. *)
Class Biparser (P : Type -> Type -> Type) :=
  { Biparser_Profmonad :> Profmonad P;
    Biparser_Partial :> forall U, MonadPartial (P U);
    biparse_token : P t t;
  }.

Arguments biparse_token {P _}.

(** ** Example biparsers *)

Definition digit (b : nat) : Type := { n | n < b }.

Definition to_digit {b} (n : nat) (H : n < b) : digit b := exist _ n H.

Definition modulo_d (z : nat) (b : nat) : digit (S b).
Proof.
  apply (exist _ (Nat.modulo z (S b))).
  apply Nat.mod_upper_bound. discriminate.
Defined.

(** Get a single [nat] token less than b. *)
Definition biparse_digit `{Biparser P} (b : nat) : P (digit b) (digit b) :=
  x <-( fun d => proj1_sig d ) biparse_token ;;
  match lt_dec x b with
  | left Hlt => ret (to_digit x Hlt)
  | right _ => empty
  end.

(** Parse a k-digit number in base b *)
Fixpoint biparse_nat `{Biparser P} (b : nat) (k : nat)
  : P nat nat :=
  match k with
  | O => ret 0
  | S k' =>
    x <-( fun z => Nat.div z b ) biparse_nat b k';;
    y <-( fun z => Nat.modulo z b ) biparse_token ;;
    if y <? b then ret (S b * x + y)
    else empty
  end.

(** Parse a length n followed by a list of nat-tokens ("string"). *)
Definition biparse_string `{Biparser P} : P (list nat) (list nat) :=
  n <-( @length _ ) biparse_nat 9 3;;
  replicate n biparse_token.

(** ** Instances *)

(** *** Products *)

#[global]
Instance Biparser_product P1 P2 `{Biparser P1, Biparser P2} :
  Biparser (Product P1 P2) :=
  { biparse_token := (biparse_token, biparse_token);
  }.

(** *** Parser promonad ***)

(** Input streams *)
Definition stream := list t.

(** **** Parser monad *)

Definition parser (A : Type) : Type := stream -> option (A * stream).

#[global]
Instance Monad_parser : Monad parser :=
  { ret A x := fun s => Some (x, s);
    bind A B m k := fun s =>
      bind (m s) (fun '(a, s') => k a s')
  }.

#[global]
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

#[global]
Instance MonadPartial_parser : MonadPartial parser :=
  { empty := fun _ _ => None }.

(** **** Parser promonad *)

Definition parser2 := Fwd parser.

Definition Profmonad_parser2 := Profmonad_Fwd parser.

#[global]
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

#[global]
Instance Monad_printer : Monad printer :=
  { ret A a := Some ([], a);
    bind A B m k :=
      @bind option _ _ _ m (fun '(s, a) =>
      @bind option _ _ _ (k a) (fun '(s', b) =>
      Some (s ++ s', b)));
  }.

#[global]
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

#[global]
Instance MonadPartial_printer : MonadPartial printer :=
  { empty A := None }.

#[global]
Instance MonadPartialLaws_printer :
  MonadPartialLaws (MonadPartial_printer).
Proof.
  constructor; try typeclasses eauto; auto.
Qed.

(** **** Printer promonad *)

Definition printer2 := Bwd printer.

#[global]
Instance Biparser_printer2 : Biparser printer2 :=
  { biparse_token := (fun n => Some ([n], n));
  }.

#[global]
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

Definition backward {A} (P : A -> Prop) (p : biparser A A) : Prop :=
  forall (a : A),
    P a ->
    exists s,
    (exists a', snd p a = Some (s, a')) /\
    (forall s', fst p (s ++ s') = Some (a, s')).

Definition forward {A} (P : A -> Prop) (p : biparser A A) : Prop :=
  forall (a : A) (s01 s1 : list t),
    fst p s01 = Some (a, s1) ->
    forall s0,
    ((exists a', snd p a = Some (s0, a')) ->
    s01 = s0 ++ s1).

(** *** Weak but compositional roundtrip properties *)

Definition weak_backward {U A} (P : U -> Prop) (p : biparser U A) : Prop :=
  forall (u : U) (a : A) (s s' : list t),
    P u ->
    snd p u = Some (s, a) ->
    fst p (s ++ s') = Some (a, s').

Definition satisfies {U A} (P : A -> Prop) (p : biparser U A) : Prop :=
  (forall (a : A) s01 s1, fst p s01 = Some (a, s1) -> P a) /\
  (forall (a : A) (u : U) s0, snd p u = Some (s0, a) -> P a).

Definition weak_forward {U A} (p : biparser U A) : Prop :=
  forall (a : A) (u : U) (s01 s0 s1 : list t),
    fst p s01 = Some (a, s1) ->
    snd p u = Some (s0, a) ->
    s01 = s0 ++ s1.

(** *** Purification, alignment *)

Definition purify {U V} (p : biparser U V) : pfunction U V :=
  fun a => option_map snd (snd p a).

Definition aligned {A} (P : A -> Prop) (p : biparser A A) : Prop :=
  forall (a : A), P a -> purify p a = Some a.

Definition aligned_ {U A} (P : U -> Prop) (f : U -> A) (p : biparser U A) : Prop :=
  forall (u : U), P u -> purify p u = Some (f u).

(** ** Connection between strong and weak roundtrip properties **)

Theorem backward_aligned {A} (P : A -> Prop) (p : biparser A A) :
  aligned P p ->
  weak_backward P p ->
  backward P p.
Proof.
  intros ALIGNED WBWD a Pa.
  specialize (ALIGNED a Pa).
  unfold purify in ALIGNED.
  destruct (snd p a) as [[s a']|] eqn:Esnd; inversion ALIGNED; subst.
  exists s.
  split; [ eauto | ].
  intros s'.
  eapply WBWD; eauto.
Qed.

Theorem forward_aligned {A} (P : A -> Prop) (p : biparser A A) :
  satisfies P p ->
  aligned P p ->
  weak_forward p ->
  forward P p.
Proof.
  intros SAT ALIGNED WFWD a s01 s1 E01 s0 [a' H3].
  assert (Pa := proj1 SAT a _ _ E01).
  specialize (ALIGNED a Pa).
  unfold purify in ALIGNED.
  rewrite H3 in ALIGNED; inversion ALIGNED; clear ALIGNED; subst.
  apply (WFWD a a _ _ _ E01 H3).
Qed.

(** ** Compositionality of weak roundtrip properties *)

Lemma weak_backward_ret U A (P : U -> Prop) (a : A) : weak_backward P (ret a).
Proof.
  intros u b s s' Pu e; inversion_clear e; reflexivity.
Qed.

Definition comapProp {U U'} (f : U -> option U') (P : U -> Prop) (u' : U') : Prop :=
  exists u, f u = Some u' /\ P u.

Lemma weak_backward_comap U U' A (P : U -> Prop) (f : U -> option U')
      (m : biparser U' A)
      (Hm : weak_backward (comapProp f P) m) :
  weak_backward P (comap f m).
Proof.
  intros u b s s' Pu e.
  cbn in *.
  destruct (f u) eqn:ef; try discriminate.
  destruct snd as [[] | ] eqn:E.
  - cbn in e. rewrite app_nil_r in e. injection e. intros ? ?; subst. clear e.
    eapply Hm in E.
    + rewrite E; eauto.
    + red. exists u; auto.
  - discriminate.
Qed.

Lemma weak_backward_bind U A B (P : U -> Prop)
      (m : biparser U A) (k : A -> biparser U B)
      (Hm : weak_backward P m)
      (Hk : forall a, weak_backward P (k a)) :
  weak_backward P (bind m k).
Proof.
  intros u b s s' Pu.
  cbn in *.
  destruct (snd m u) as [ [s1 a] | ] eqn:em; simpl; try discriminate.
  destruct (snd (k a) u) as [ [s2 b'] | ] eqn:ek; simpl; try discriminate.
  intros Hmk.
  inversion Hmk.
  eapply (Hm _ _ _ _ Pu) in em.
  eapply (Hk _ _ _ _ _ Pu) in ek.
  rewrite <- app_assoc.
  rewrite em; simpl.
  rewrite ek.
  subst; reflexivity.
Qed.

Class Compositional
      {P : Type -> Type -> Type}
      `{Profmonad P}
      (R : forall A B, (A -> Prop) -> P A B -> Prop) : Prop :=
  {
    CompositionalWithLawful :> ProfmonadLaws _;
    ret_comp :
      forall U A (F : U -> Prop) (a : A), R U A F (ret a : P U A);
    bind_comp :
      forall U A B (F : U -> Prop) (m : P U A) (k : A -> P U B) ,
        R U A F m ->
        (forall a, R U B F (k a)) ->
        R U B F (bind m k);
    comap_comp :
      forall U V A (F : U -> Prop) (f : U -> option V) (m : P V A),
        R V A (comapProp f F) m ->
        R U A F (comap f m);
  }.

#[global]
Instance Compositional_weak_backward :
  Compositional (@weak_backward) := {
  ret_comp := weak_backward_ret;
  bind_comp := weak_backward_bind;
  comap_comp := weak_backward_comap;
}.

Lemma weak_backward_empty U A P :
  weak_backward P (@empty (biparser U) _ _ A).
Proof.
  discriminate.
Qed.

Lemma weak_backward_token P :
  weak_backward P biparse_token.
Proof.
  intros u b s s' Pu H; inversion H; subst; reflexivity.
Qed.

Lemma weak_forward_ret U A (a : A) : @weak_forward U A (ret a).
Proof.
  intros a' b s01 s0 s1 e1 e2; inv e1; inv e2; reflexivity.
Qed.

Lemma weak_forward_comap U U' A (f : U -> option U')
      (m : biparser U' A) (Hm : weak_forward m) :
  weak_forward (comap f m).
Proof.
  intros a u s01 s0 s1 e1 e2.
  cbn in *.
  destruct (fst m) as [[]|] eqn:E1; cbn in e1; inv e1.
  destruct (f u) eqn:ef; try discriminate.
  destruct (snd m) as [[]|] eqn:E2; cbn; inv e2.
  rewrite app_nil_r.
  eapply Hm; eauto.
Qed.

Lemma weak_forward_bind U A B (P : A -> Prop)
      (m : biparser U A) (k : A -> biparser U B) (f : B -> option A)
      (Sm : satisfies P m)
      (Hm : weak_forward m)
      (Hf : forall a, P a -> (x <- k a;; ret (f x)) = (x <- k a;; ret (Some a)))
      (Hk : forall a, P a -> weak_forward (k a)) :
  weak_forward (bind m k).
Proof.
  intros b u s01 s0 s1 Hparse Hprint.
  simpl in *.
  destruct fst as [ [a1 s__m1] | ] eqn:em1 in Hparse; try discriminate;
    simpl in Hparse;
    destruct fst as [ [b1 s__mk1] | ] eqn:ek1 in Hparse; try discriminate;
    inversion Hparse; clear Hparse; subst.
  destruct snd as [ [s__m2 a2] | ] eqn:em2 in Hprint; try discriminate;
    simpl in Hprint;
    destruct snd as [ [s__mk2 b2] | ] eqn:ek2 in Hprint; try discriminate;
    inversion Hprint; clear Hprint; subst.
  assert (Pa1 : P a1). { apply (proj1 Sm _ _ _ em1). }
  assert (Pa2 : P a2). { apply (proj2 Sm _ _ _ em2). }
  assert (ea : a2 = a1); [ | subst a2 ].
  { pose proof (Hf a1 Pa1) as Hf1.
    apply (f_equal (fun f => fst f s__m1)) in Hf1. simpl in Hf1.
    rewrite ek1 in Hf1; inversion Hf1.
    pose proof (Hf a2 Pa2) as Hf2.
    apply (f_equal (fun f => snd f u)) in Hf2; simpl in Hf2.
    rewrite ek2 in Hf2; inversion Hf2.
    rewrite H0 in H1; inversion H1.
    reflexivity.
  }
  specialize (Hm _ _ _ _ _ em1 em2).
  specialize (Hk _ Pa1 _ _ _ _ _ ek1 ek2).
  rewrite <- app_assoc, <- Hk, <- Hm. reflexivity.
Qed.

Class WP (P : Type -> Type -> Type) `{Profmonad P} (S : forall A B, (B -> Prop) -> P A B -> Prop)
  : Prop :=
  { ret_wp : forall U A a, S U A (eq a) (ret a);
    bind_wp : forall U A B (F G : _ -> Prop) (m : P U A) (k : A -> P U B),
      S U A F m -> (forall a, F a -> S U B G (k a)) -> S U B G (bind m k);
    comap_wp : forall U V A (F : _ -> Prop) (f : U -> option V) (m : P V A),
      S V A F m -> S U A F (comap f m);
    mono_wp : forall U A (F G : A -> Prop) (m : P U A),
      (forall a, F a -> G a) ->
      S U A F m -> S U A G m
  }.

Class Quasicompositional'
      (P : Type -> Type -> Type)
      `{Profmonad P}
      (S : forall A B, (B -> Prop) -> P A B -> Prop)
      `{WP P S}
      (R : forall A B, P A B -> Prop) : Prop :=
  {
    ret_comp' :
      forall A0 A a, R A0 A (ret a);
    bind_comp' :
      forall U A B (F : _ -> Prop) (m : P U A) (k : A -> P U B) (f : B -> option A),
        S U A F m ->
        R U A m ->
        (forall a, F a -> (x <- k a;; ret (f x)) = (x <- k a;; ret (Some a))) ->
        (forall a, F a -> R U B (k a)) ->
        R U B (bind m k);
    comap_comp' :
      forall U V A (f : U -> option V) (m : P V A),
        R V A m -> R U A (comap f m)
  }.

Class Quasicompositional (P : Type -> Type -> Type) `{Profmonad P} (R : forall {A B}, (B -> Prop) -> P A B -> Prop) : Prop :=
  { ret_qcomp : forall U A a, @R U A (eq a) (ret a)
  ; bind_qcomp : forall U A B (F G : _ -> Prop) (m : P U A) (k : A -> P U B) (f : B -> option A),
      R F m ->
      (forall a, F a -> (x <- k a;; ret (f x)) = (x <- k a;; ret (Some a))) ->
      (forall a, F a -> R G (k a)) ->
      R G (bind m k)
  ; comap_qcomp : forall U V A F (f : U -> option V) (m : P V A),
      R F m -> R F (comap f m)
  ; mono_qcomp : forall U A (F G : A -> Prop) (m : P U A),
      (forall a, F a -> G a) -> R F m -> R G m
  }.

Definition wp_roundtrip {P : Type -> Type -> Type} (S : forall A B, (B -> Prop) -> P A B -> Prop) (R : forall A B, P A B -> Prop) : forall A B, (B -> Prop) -> P A B -> Prop :=
  fun A B F m => S A B F m /\ R A B m.

Lemma Quasi {P : Type -> Type -> Type} `{Profmonad P} S `{HS : WP P S} R
  : Quasicompositional' P S R -> Quasicompositional P (wp_roundtrip S R).
Proof.
  intros QC; constructor.
  - constructor; [ apply HS | apply QC ].
  - intros * Hm Hinj Hk. constructor; [ eapply bind_wp; [apply Hm | apply Hk] | eapply bind_comp'; [apply Hm| apply Hm | apply Hinj | apply Hk] ].
  - intros * Hm. constructor; [ apply comap_wp | apply comap_comp' ]; apply Hm.
  - intros * HF Hm; split; [ eapply mono_wp |]; [ apply HF | apply Hm .. ].
Qed.

Lemma bind_comap_comp' {P} {R : forall A B, (B -> Prop) -> P A B -> Prop}
    `{Quasicompositional P R}
  : forall A B (F G : _ -> Prop) (m : P A A) (k : A -> P B B) (f : B -> option A),
      (forall a, F a -> (x <- k a;; ret (f x)) = (x <- k a;; ret (Some a))) ->
      R A A F m ->
      (forall a, F a -> R B B G (k a)) ->
      R B B G (bind (comap f m) k).
Proof.
  intros. eapply (bind_qcomp _ _ _ _ _ _ _ f); eauto.
  apply comap_qcomp; eauto.
Qed.

Definition weak_forward' {A B} := wp_roundtrip (@satisfies) (@weak_forward) A B.

Section A.
#[local]
Instance WP_satisfies : WP biparser (@satisfies).
Proof.
  constructor.
  - split; intros * Hret; inv Hret; auto.
  - intros * Hm Hk; split; intros *; cbn.
    + destruct (fst m) as [[a' s]|] eqn:Em1; cbn; try discriminate.
      intros Ek1.
      apply Hm in Em1.
      apply (proj1 (Hk _ Em1) _ _ _ Ek1).
    + destruct (snd m) as [[s  a'] | ] eqn:Em2; cbn; try discriminate.
      destruct (snd (k _)) as [[s' b'] | ] eqn:Ek2; cbn; try discriminate.
      intros HH; inv HH.
      apply Hm in Em2.
      apply (proj2 (Hk _ Em2) _ _ _ Ek2).
  - intros * Hm; split; intros *; cbn.
    + destruct (fst m) as [[a' s]|] eqn:Em1; cbn; try discriminate.
      intros HH; inv HH.
      eapply (proj1 Hm); eauto.
    + destruct (f u); cbn; try discriminate.
      destruct (snd m) as [[s b]|] eqn:Em2; cbn; try discriminate.
      intros HH; inv HH.
      eapply (proj2 Hm); eauto.
  - intros * HF []; split; eauto.
Qed.

#[global]
Instance Quasicompositional_weak_forward :
  Quasicompositional' biparser (@satisfies) (@weak_forward) := {
  ret_comp' := weak_forward_ret;
  bind_comp' := weak_forward_bind;
  comap_comp' := weak_forward_comap;
}.

Lemma weak_forward_empty_ U A : weak_forward (@empty (biparser U) _ _ A).
Proof. discriminate. Qed.

Lemma satisfies_empty U A : satisfies (fun _ => False) (@empty (biparser U) _ _ A).
Proof. split; discriminate. Qed.

Lemma weak_forward_empty U A :
  weak_forward' (fun _ => False) (@empty (biparser U) _ _ A).
Proof.
  split; [ apply satisfies_empty | apply weak_forward_empty_ ].
Qed.

Lemma weak_forward_token :
  weak_forward (fun _ => True) biparse_token.
Proof.
  intros b s s' H1. split; [auto | intros u s0 H2].
  destruct s; simpl in *.
  - discriminate.
  - inversion H1; inversion H2; subst.
    reflexivity.
Qed.

(**)

Lemma weak_forward_digit {b} : weak_forward (fun _ => True) (biparse_digit b).
Proof.
  unfold biparse_digit; intros.
  eapply bind_comap_comp'.
  { intros a; destruct lt_dec; cbn; reflexivity. }
  { apply weak_forward_token. }
  { intros a; destruct lt_dec.
    - eapply weaken_weak_forward, weak_forward_ret; constructor.
    - eapply weaken_weak_forward, weak_forward_empty; constructor. }
Qed.

Lemma weak_backward_digit {b} P : weak_backward P (biparse_digit b).
Proof.
  unfold biparse_digit.
  apply bind_comp.
  - apply comap_comp. apply weak_backward_token.
  - intros a.
    destruct (lt_dec a b).
    + apply weak_backward_ret.
    + apply weak_backward_empty.
Qed.

Lemma strengthen_weak_backward {U A} (P Q : _ -> Prop) (p : biparser U A)
  : (forall u, P u -> Q u) ->
    weak_backward Q p -> weak_backward P p.
Proof.
  unfold weak_backward. eauto.
Qed.

Lemma weak_backward_replicate {A} {n} {p : biparser A A} (P Q : _ -> Prop)
  : (forall xs, Q xs -> length xs = n /\ Forall P xs) ->
    weak_backward P p ->
    weak_backward Q (replicate n p).
Proof.
  intros F Hp.
  revert Q F; induction n; cbn [replicate]; intros.
  - apply weak_backward_ret.
  - apply bind_comp.
    { apply comap_comp.
      eapply strengthen_weak_backward; [ | apply Hp ].
      intros u [? [? ?]].
      destruct x; inv H.
      apply F in H0.
      apply (Forall_inv (proj2 H0)). }
    intros. apply bind_comp.
    { apply comap_comp.
      apply IHn.
      intros xs [? [? ?]]. destruct x; inv H.
      apply F in H0.
      destruct H0.
      inv H. inv H0. split; auto. }
    intros; apply weak_backward_ret.
Qed.

Lemma weak_forward_replicate {A} (P : A -> Prop) (Q : list A -> Prop)  {n} {p : biparser A A}
  : (forall xs, length xs = n /\ Forall P xs -> Q xs) ->
    weak_forward P p ->
    weak_forward Q (replicate n p).
Proof.
  intros F Hp.
  revert Q F; induction n; cbn [replicate]; intros.
  - apply (weaken_weak_forward (eq [])); [ | apply weak_forward_ret ].
    intros _ <-; apply (F []); auto.
  - eapply bind_comap_comp'; [ | eassumption | ].
    { intros; rewrite 2 bind_bind; reflexivity. }
    intros a.
    eapply bind_comap_comp'; [ | | ].
    { reflexivity. }
    { eapply IHn. intros xs [<- all].
Qed.

Lemma digit_unique {b} (d1 d2 : digit b) : proj1_sig d1 = proj1_sig d2 -> d1 = d2.
Proof.
  destruct d1, d2; cbn; intros <-.
  f_equal. apply le_unique.
Qed.

Lemma weak_forward_nat b k : weak_forward (biparse_nat b k).
Proof.
  induction k; cbn [biparse_nat].
  - apply ret_comp'.
  - apply bind_comap_comp'.
    { intros. rewrite 2 bind_bind. f_equal; apply functional_extensionality; intros ?.
      rewrite 2 ret_bind. f_equal. f_equal.
      symmetry. apply Nat.div_unique with (r := proj1_sig x); [ apply proj2_sig | reflexivity ]. }
    { auto. }
    intros; apply bind_comap_comp'.
    { intros; rewrite 2 ret_bind.
      f_equal. f_equal.
      apply digit_unique. cbn [proj1_sig modulo_d].
      symmetry; apply Nat.mod_unique with (q := a); [ apply proj2_sig | reflexivity ]. }
    { apply weak_forward_digit. }
    intros; apply weak_forward_ret.
Qed.

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

Lemma replicate_length {P} `{Biparser P} {PL : ProfmonadLaws P} (n : nat)
  : replicate (P := P) n biparse_token >>= (fun x : list t => ret (List.length x))
  = replicate n biparse_token >>= (fun _ : list t => ret n).
Proof.
  induction n; cbn.
  - rewrite 2 ret_bind. reflexivity.
  - rewrite !bind_bind. f_equal. apply functional_extensionality. intros x.
    rewrite !bind_bind.
    transitivity (comap (P := P) tail (replicate n biparse_token >>= fun x => ret (length x)) >>= fun n => ret (S n)).
    + rewrite natural_comap. rewrite !bind_bind. f_equal; apply functional_extensionality; intros xs.
      rewrite 2 ret_bind. reflexivity.
    + rewrite IHn. rewrite natural_comap, !bind_bind. f_equal; apply functional_extensionality; intros xs.
      rewrite 2 ret_bind. reflexivity.
Qed.

Lemma replicate_length_ {P} `{Biparser P} {PL : ProfmonadLaws P} (n : nat)
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

Lemma purify_bind {U A B} (p : biparser U A) (k : A -> biparser U B)
  : forall u, purify (bind p k) u = bind (purify p u) (fun a => purify (k a) u).
Proof.
  intros u.
  unfold purify; cbn.
  destruct (snd p u) as [[] | ]; cbn; [ | reflexivity ].
  destruct (snd (k a) u) as [[] | ]; cbn; reflexivity.
Qed.

Lemma purify_comap {U V A} (p : biparser V A) (f : U -> option V)
  : forall u, purify (comap f p) u = bind (f u) (purify p).
Proof.
  intros u; unfold purify; cbn.
  destruct (f u); cbn; [ | reflexivity ].
  destruct (snd p v) as [[] |]; cbn; reflexivity.
Qed.

Theorem aligned_string : aligned biparse_string.
Proof.
  intros s.
  unfold biparse_string.
  rewrite purify_bind.
  rewrite purify_comap.
  cbn [bind Monad_option bind_option].
