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
  List
  Setoid
  Morphisms.
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
  { Biparser_Profmonad :: Profmonad P;
    Biparser_Partial :: forall U, MonadFail (P U);
    biparse_token : P t t;
    biparse_many : forall U A, P (option U) (option A) -> P (list U) (list A)
  }.

Arguments biparse_token {P _}.
Arguments biparse_many {P _  U A}.

(** ** Example biparsers *)

Definition digit (b : nat) : Type := { n | n < b }.

Definition to_digit {b} (n : nat) (H : n < b) : digit b := exist _ n H.

Definition modulo_d (z : nat) (b : nat) : digit (S b).
Proof.
  apply (exist _ (Nat.modulo z (S b))).
  apply Nat.mod_upper_bound. discriminate.
Defined.

Definition digit_or_space (n : option nat) : t :=
  match n with
  | Some n => n
  | None => 10
  end.

(** Get a single [nat] token less than b. *)
Definition biparse_digit `{Biparser P} : P (option nat) (option nat) :=
  x <-( digit_or_space ) biparse_token  ;;
  match lt_dec x 10 with
  | left Hlt => ret (Some x)
  | right _ =>
    match Nat.eq_dec x 10 with
    | left Heq => ret None
    | right _ => fail tt
    end
  end.

Definition show_nat (n : nat) : list t.
Admitted.

(* You can allow leading zeroes at the cost of breaking forwards roundtripping (read_show_nat) *)
Definition read_nat (xs : list t) : option nat.
Admitted.

Lemma show_read_nat (n : nat)
  : read_nat (show_nat n) = Some n.
Admitted.

Lemma read_show_nat (xs : list t) (n : nat)
  : read_nat xs = Some n -> show_nat n = xs.
Admitted.

(** Parse a k-digit number in base b *)
Definition biparse_nat `{Biparser P} : P nat nat :=
  ds <-( show_nat ) biparse_many biparse_digit ;;
  match read_nat ds with
  | None => fail tt
  | Some n => ret n
  end.

(** Parse a length n followed by a list of nat-tokens ("string"). *)
Definition biparse_string `{Biparser P} : P (list nat) (list nat) :=
  n <-( @length _ ) biparse_nat;;
  replicate n biparse_token.

(** ** Instances *)

(** *** Products *)

#[global]
Instance Biparser_product P1 P2 `{Biparser P1, Biparser P2} :
  Biparser (Product P1 P2) :=
  { biparse_token := (biparse_token, biparse_token)
  ; biparse_many := fun U A p => (biparse_many (fst p), biparse_many (snd p))
  }.

(** *** Parser promonad ***)


(** Input streams *)
Definition stream := list t.

Module Delay.

CoInductive m (A : Type) : Type := Wait { step : m A + A }.

Arguments Wait {A}.
Arguments step {A}.

Definition flip_bind {A B} (k : A -> m B) : m A -> m B := cofix bind_ u :=
  Wait match step u with
  | inl more => inl (bind_ more)
  | inr x => step (k x)
  end.

#[global] Instance Monad_delay : Monad m :=
  {| ret := fun _ x => Wait (inr x)
  ;  bind := fun _ _ u k => flip_bind k u
  |}.

Inductive returns {A} (x : A) (u : m A) : Prop :=
| returns_now : step u = inr x -> returns x u
| returns_later {u'} : step u = inl u' -> returns x u' -> returns x u
.

Record equiv_delay {A} (u v : m A) : Prop :=
  { apply_equiv_delay : forall x, returns x u <-> returns x v }.

#[global]
Instance Equivalence_equiv_delay {A} : Equivalence (equiv_delay (A := A)).
  constructor.
  - constructor; reflexivity.
  - intros ? ? []; constructor; symmetry; auto.
  - intros ? ? ? [] []; constructor; etransitivity; eauto.
Qed.

#[global] Instance Setoid_delay {A} : Setoid (m A) :=
  {| equiv := equiv_delay |}.

Lemma returns_bind {A B} (u : m A) (k : A -> m B) x y
  : returns x u -> returns y (k x) -> returns y (bind u k).
Proof.
  induction 1.
  - intros Hk. destruct Hk.
    + constructor 1; cbn. rewrite H. auto.
    + econstructor 2; cbn; [rewrite H; eauto | auto].
  - intros Hk. econstructor 2; cbn.
    + rewrite H; eauto.
    + auto.
Qed.

Lemma returns_bind_inv {A B} (u : m A) (k : A -> m B) y
  : returns y (bind u k) -> exists x, returns x u /\ returns y (k x).
Proof.
  remember (bind u k) as b eqn:Eb.
  intros H; revert u Eb.
  induction H; cbn.
  - intros b' ->. cbn in H. destruct (step b') eqn:Eb'; [ discriminate | ].
    exists a; split.
    + constructor 1; auto.
    + constructor 1; auto.
  - intros b' ->. cbn in H. destruct (step b') as [ | a ] eqn:Eb'.
    + injection H; clear H; intros <-.
      destruct (IHreturns _ eq_refl) as [ a [] ].
      exists a; split.
      * econstructor 2; eauto.
      * auto.
    + exists a; split.
      * constructor 1; auto.
      * econstructor 2; eauto.
Qed.

#[global] Instance MonadLaws_delay : MonadLaws m.
Proof.
  constructor.
  - intros A u. cbn. constructor; split.
    + intros H; apply returns_bind_inv in H.
      destruct H as [a [Hu Hret]].
      destruct Hret; [ | discriminate ].
      injection H. intros <-; auto.
    + intros H; eapply returns_bind; eauto.
      constructor 1; auto.
  - intros A B u k. constructor; split.
    + intros []; [ constructor 1 | econstructor 2 ]; eauto.
    + intros []; [ constructor 1 | econstructor 2 ]; eauto.
  - intros A B C u k h. constructor; split.
    + intros H; apply returns_bind_inv in H.
      destruct H as [b [Huk Hh]].
      apply returns_bind_inv in Huk.
      destruct Huk as [a [Hu Hk]].
      eapply returns_bind; [ eauto | ].
      eapply returns_bind; eauto.
    + intros H; apply returns_bind_inv in H.
      destruct H as [a [Hu Hkh]].
      apply returns_bind_inv in Hkh.
      destruct Hkh as [b [Hk Hh]].
      eapply returns_bind; [ | eauto ].
      eapply returns_bind; eauto.
  - unfold Proper, pointwise_relation, respectful; cbn.
    intros A B.
    enough (forall x y : m A, equiv_delay x y ->
      forall x0 y0 : A -> m B, (forall a : A, equiv_delay (x0 a) (y0 a)) ->
      forall x1 : B, returns x1 (flip_bind x0 x) -> returns x1 (flip_bind y0 y)).
    { constructor; split; intros.
      { eapply H; eauto. }
      { eapply H. { symmetry; eauto. } { symmetry; eauto. } auto. } }
    intros x y Hxy k h Hkh b Hb.
    apply returns_bind_inv in Hb.
    destruct Hb as [ a [ Hx Ha ]].
    eapply returns_bind.
    + apply Hxy; eauto.
    + apply Hkh; eauto.
Qed.

Lemma returns_injective {A} (u : m A) (x y : A) : returns x u -> returns y u -> x = y.
Proof.
  induction 1; intros []; try congruence.
  assert (u' = u'0) by congruence.
  subst; auto.
Qed.

Definition bind_inv {A B} (u : m A) (k : A -> m B) b
  : bind u k == ret b -> exists a, (u == ret a) /\ (k a == ret b).
Proof.
  cbn.
  intros H.
  assert (Huk : returns b (bind u k)).
  { apply H. constructor; auto. }
  apply returns_bind_inv in Huk.
  destruct Huk as [ a [ Hu Hk ]].
  exists a; split.
  - constructor; split.
    + intros Ru.
      rewrite (returns_injective _ _ _ Hu Ru).
      constructor; auto.
    + intros Ra. destruct Ra; [ | discriminate ].
      injection H0; intros <-. auto.
  - constructor; split.
    + intros Rk.
      rewrite (returns_injective _ _ _ Rk Hk).
      constructor; auto.
    + intros Rk. destruct Rk; [ | discriminate ].
      injection H0; intros <-; auto.
Qed.

Definition ret_inv {A} (x : A) y
  : ret x == ret y -> x = y.
Proof.
  cbn. intros H.
  assert (R : returns x (ret x)).
  { constructor. auto. }
  apply H in R.
  destruct R; [ | discriminate].
  injection H0. auto.
Qed.

Definition bind_iter {A B} (f : A -> m (A + B)) : m (A + B) -> m B :=
  cofix bind_iter_ u :=
    Wait match step u with
      | inl u => inl (bind_iter_ u)
      | inr (inl x) => inl (bind_iter_ (f x))
      | inr (inr y) => inr y
      end.

Definition iter {A B} (f : A -> m (A + B)) (x : A) : m B :=
  bind_iter f (f x).

Inductive iter_returns_ {A B} (x : B) (f : A -> m (A + B)) : A + B -> Prop :=
| iter_returns_stop : iter_returns_ x f (inr x)
| iter_returns_continue {a y}
  : returns y (f a) ->
    iter_returns_ x f y ->
    iter_returns_ x f (inl a).

Definition iter_returns {A B} (x : B) (f : A -> m (A + B)) (a : A) : Prop :=
  iter_returns_ x f (inl a).

Lemma returns_bind_iter_inv {A B} (f : A -> m (A + B)) (u : m (A + B)) (x : B)
  : returns x (bind_iter f u) -> exists a, returns a u /\ iter_returns_ x f a.
Proof.
  remember (bind_iter f u) as b eqn:Eb.
  intros H; revert u Eb.
  induction H; cbn.
  - intros b' ->. cbn in H.
    destruct (step b') as [ | [ | ] ] eqn:Eb'; [ discriminate | discriminate | ].
    injection H; clear H; intros <-.
    exists (inr b); split.
    + constructor 1. auto.
    + constructor; auto.
  - intros u2 ->. cbn in H.
    destruct (step u2) as [ | [ | ] ] eqn:Eu2; [ | | discriminate ].
    + injection H; clear H; intros <-.
      specialize (IHreturns _ eq_refl).
      destruct IHreturns as [ a [ Hu Hf ]].
      exists a; split.
      * econstructor 2; eauto.
      * auto.
    + injection H; clear H; intros <-.
      specialize (IHreturns _ eq_refl).
      destruct IHreturns as [ z [ Hu Hf ]].
      exists (inl a); split.
      * constructor; auto.
      * econstructor; eauto.
Qed.

Lemma returns_bind_iter_returns {A B} (f : A -> m (A + B)) (x : B) (a : A + B)
  : iter_returns_ x f a -> match a with
    | inl a => returns x (bind_iter f (f a))
    | inr y => x = y
    end.
Proof.
  induction 1; [reflexivity | ].
  revert H; generalize (f a); intros u H; induction H.
  - destruct y.
    + econstructor 2; cbn.
      * rewrite H. reflexivity.
      * auto.
    + constructor; cbn. rewrite H. f_equal; auto.
  - econstructor 2; cbn.
    + rewrite H. reflexivity.
    + auto.
Qed.

Lemma returns_bind_iter {A B} (f : A -> m (A + B)) (u : m (A + B)) (x : B) (a : A + B)
  : returns a u -> iter_returns_ x f a -> returns x (bind_iter f u).
Proof.
  intros Hu Hf; induction Hu.
  - destruct a.
    + econstructor 2; cbn. { rewrite H; reflexivity. }
      apply returns_bind_iter_returns in Hf. auto.
    + remember (inr b) eqn:Eb; destruct Hf; [ | discriminate ].
      injection Eb; clear Eb; intros <-.
      constructor; cbn. rewrite H. reflexivity.
  - econstructor 2; cbn; [ rewrite H; reflexivity | auto ].
Qed.

Lemma returns_iter_inv {A B} (f : A -> m (A + B)) (x : B) (a : A)
  : returns x (iter f a) -> iter_returns x f a.
Proof.
  intros H; apply returns_bind_iter_inv in H.
  destruct H as [ a' [ Hu Hf ]].
  econstructor; eauto.
Qed.

Lemma returns_bind_iter_inv' {A B} (f : A -> m (A + B)) (u : m (A + B)) (y : B)
  : returns y (bind_iter f u) -> exists x, returns x u /\
      match x with
      | inl x' => returns y (bind_iter f (f x'))
      | inr y' => y = y'
      end.
Proof.
  intros H; apply returns_bind_iter_inv in H.
  destruct H as [ a [ Hu Hf ]].
  exists a; split; auto.
  destruct Hf; auto.
  eapply returns_bind_iter; eauto.
Qed.

Lemma returns_bind_iter' {A B} (f : A -> m (A + B)) (u : m (A + B)) (x : A + B) (y : B)
  : returns x u ->
    match x with
    | inl x' => returns y (bind_iter f (f x'))
    | inr y' => y = y'
    end -> returns y (bind_iter f u).
Proof.
  intros Hu Hf. eapply returns_bind_iter; eauto.
  destruct x.
  - eapply returns_bind_iter_inv in Hf.
    destruct Hf as [ a' [ Hu' Hf' ]].
    econstructor; eauto.
  - destruct Hf; constructor.
Qed.

Lemma unfold_iter {A B} (f : A -> m (A + B)) (x : A)
  : iter f x == (xy <- f x ;; match xy with
    | inl x => iter f x
    | inr y => ret y
    end).
Proof.
  constructor; intros y. split.
  - intros H; apply returns_bind_iter_inv' in H.
    destruct H as [ x' [ Hf Hiter ]].
    eapply returns_bind; [ eauto | ].
    destruct x'.
    + apply Hiter.
    + constructor; cbn; f_equal; auto.
  - intros H; apply returns_bind_inv in H.
    destruct H as [ xy [ Hf Hiter ]].
    eapply returns_bind_iter'.
    + eauto.
    + destruct xy; eauto.
      destruct Hiter; [ | discriminate ].
      injection H; auto.
Qed.

#[global]
Instance Proper_returns {A}
  : Proper (eq ==> equiv ==> iff) (@returns A).
Proof.
  unfold Proper, respectful.
  intros ? _ <- ? ? E. apply E.
Qed.

End Delay.

Arguments Delay.Monad_delay : simpl never.
Arguments Delay.Setoid_delay : simpl never.

Notation delay := Delay.m.

(** **** Parser monad *)

Definition parser (A : Type) : Type := stream -> delay (option (A * stream)).

#[global]
Instance Monad_parser : Monad parser :=
  { ret A x := fun s => ret (Some (x, s));
    bind A B m k := fun s =>
      bind (m s) (fun xs => match xs with
      | None => ret None
      | Some (a, s') => k a s'
      end)
  }.

#[global]
Instance Setoid_parser : Eq1 parser := fun A =>
  {| equiv := pointwise_relation stream equiv |}.

#[global]
Instance MonadLaws_parser : MonadLaws parser.
Proof.
  constructor.
  - cbn. red. intros. etransitivity; [ | eapply bind_ret ].
    apply Proper_bind; [ reflexivity | ].
    intros [ [] | ]; reflexivity.
  - cbn. red. intros. rewrite ret_bind. reflexivity.
  - cbn. red. intros. rewrite bind_bind. apply Proper_bind; [ reflexivity | ].
    red. intros [ [] | ].
    + apply Proper_bind; [ reflexivity | ].
      red. intros [ [] |]; reflexivity.
    + rewrite ret_bind; reflexivity.
  - unfold Proper, respectful, pointwise_relation.
    intros.
    cbn. intros s. apply Proper_bind.
    + auto.
    + intros [ []| ]; [ apply H0 | reflexivity ].
Qed.

#[global]
Instance MonadFail_parser : MonadFail parser :=
  { fail s := fun _ _ => ret None }.

#[global]
Instance MonadFailLaws_parser : MonadFailLaws parser.
Proof.
  constructor; try typeclasses eauto; cbn; auto.
  red. cbn. intros. rewrite ret_bind. reflexivity.
Qed.

(** **** Parser promonad *)

Definition parser2 := Fwd parser.

Definition Profmonad_parser2 := Profmonad_Fwd parser.

Definition parse_many_ {A} (u : parser (option A))
  : list A * stream -> Delay.m (option (list A * stream)) :=
  Delay.iter (fun '(acc, s) =>
    bind (M := Delay.m) (u s) (fun x =>
    ret match x with
    | None => inr None
    | Some (None, s) => inr (Some (List.rev acc, s))
    | Some (Some a, s) => inl (a :: acc, s)
    end)).

Definition parse_many {A} (u : parser (option A)) : parser (list A) :=
  fun s => parse_many_ u ([], s).

Lemma shift_parse_many_ {A} (u : parser (option A)) acc acc' s
  : parse_many_ u (acc ++ acc', s) ==
      (o <- parse_many_ u (acc, s) ;;
       match o with
       | None => ret None
       | Some (xs, s') => ret (Some (List.rev acc' ++ xs, s'))
       end).
Proof.
  constructor.
  intros xs. split.
  - intros H.
    unfold parse_many_ in H.
    apply Delay.returns_iter_inv in H.
    red in H.
    remember (inl _) eqn:El in H.
    revert s acc El.
    induction H as [ | ? ? H HH IH]; [ discriminate | ].
    intros ? ?; injection 1; intros ->. clear El.
    apply Delay.returns_bind_inv in H.
    destruct H as [ [[ [ | ] ? ] | ] [Hx Hy] ].
    + destruct Hy; [ | discriminate ].
      injection H; clear H; intros <-.
      specialize (IH _ (_ :: _) eq_refl).
      unfold parse_many_.
      rewrite Delay.unfold_iter.
      rewrite 2 bind_bind.
      apply Delay.returns_bind with (1 := Hx).
      rewrite ret_bind. fold (parse_many_ u).
      auto.
    + destruct Hy; [ | discriminate ].
      injection H; clear H; intros <-.
      unfold parse_many_.
      rewrite Delay.unfold_iter.
      rewrite 2 bind_bind.
      apply Delay.returns_bind with (1 := Hx).
      rewrite 2 ret_bind.
      inversion HH.
      constructor.
      rewrite List.rev_app_distr. auto.
    + destruct Hy; [ | discriminate ].
      injection H; clear H; intros <-.
      unfold parse_many_.
      rewrite Delay.unfold_iter.
      rewrite 2 bind_bind.
      apply Delay.returns_bind with (1 := Hx).
      rewrite 2 ret_bind.
      inversion HH. constructor; auto.
  - intros H.
    apply Delay.returns_bind_inv in H.
    destruct H as [ x [Hx Hxs] ].
    unfold parse_many_ in Hx.
    apply Delay.returns_iter_inv in Hx. red in Hx.
    remember (inl (acc, s)) eqn:El.
    revert acc s El.
    induction Hx as [ | ? ? H HH IH]; [ discriminate | ].
    intros ? ? El; injection El; clear El; intros ->.
    apply Delay.returns_bind_inv in H.
    destruct H as [ z [Hx Hy]].
    destruct Hy; [ | discriminate ].
    injection H; clear H; intros <-.
    destruct z as [[ [ | ] ? ] | ].
    + specialize (IH _ _ eq_refl).
      unfold parse_many_.
      rewrite Delay.unfold_iter.
      rewrite bind_bind.
      apply Delay.returns_bind with (1 := Hx).
      rewrite ret_bind.
      auto.
    + inversion HH. subst x.
      unfold parse_many_. rewrite Delay.unfold_iter.
      rewrite bind_bind.
      apply Delay.returns_bind with (1 := Hx).
      rewrite ret_bind.
      rewrite List.rev_app_distr. auto.
    + inversion HH. subst x.
      unfold parse_many_. rewrite Delay.unfold_iter.
      rewrite bind_bind.
      apply Delay.returns_bind with (1 := Hx).
      rewrite ret_bind.
      auto.
Qed.

Lemma unfold_parse_many {A} (u : parser (option A))
  : parse_many u == (
    x <- u ;;
    match x with
    | None => ret []
    | Some a => xs <- parse_many u ;;
                ret (a :: xs)
    end).
Proof.
  cbn. intros s.
  unfold parse_many.
  unfold parse_many_.
  rewrite Delay.unfold_iter.
  rewrite bind_bind.
  apply Proper_bind; [ reflexivity | ].
  intros [ [ [ | ] ? ] | ]; rewrite ret_bind.
  - fold (parse_many_ u).
    apply shift_parse_many_ with (acc := []) (acc' := [a]).
  - reflexivity.
  - reflexivity.
Qed.

#[global]
Instance Biparser_parser2 : Biparser parser2 :=
  { biparse_token s :=
      match s with
      | [] => ret None
      | n :: s' => ret (Some (n, s'))
      end
  ; biparse_many := fun U A => parse_many
  }.


(** *** Printer promonad ***)

(** **** Printer monad *)

Definition printer (A : Type) := option (stream * A).

#[global]
Instance Setoid_printer : Eq1 printer := Eq1_default _.

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
    destruct m as [[]|]; [simpl; rewrite app_nil_r|]; reflexivity.

  - intros.
    simpl.
    destruct (k a) as [[]|]; simpl; auto.

  - intros. simpl.
    destruct m as [[]|]; simpl; auto.
    destruct (k a) as [[]|]; simpl; auto.
    destruct (h b) as [[]|]; simpl; auto.
    rewrite app_assoc.
    auto.
  - cbv; intros. subst y; destruct x as [[] |]; [ rewrite <- H0 | reflexivity].
    destruct x0 as [[] | ]; reflexivity.
Qed.

#[global]
Instance MonadFail_printer : MonadFail printer :=
  { fail A s := None }.

#[global]
Instance MonadFailLaws_printer : MonadFailLaws printer.
Proof.
  constructor; try typeclasses eauto; cbn; auto.
Qed.

(** **** Printer promonad *)

Definition printer2 := Bwd printer.

Definition print_many {U A} (p : printer2 (option U) (option A)) : printer2 (list U) (list A) :=
  fix print_many_ xs :=
    match xs with
    | nil =>
      match p None with
      | Some (s, None) => Some (s, nil)
      | _ => None
      end
    | x :: xs =>
      match p (Some x) with
      | Some (s, Some y) => option_map (fun '(ss, ys) => (s ++ ss, y :: ys)) (print_many_ xs)
      | _ => None
      end
    end.

#[global]
Instance Biparser_printer2 : Biparser printer2 :=
  { biparse_token := (fun n => Some ([n], n))
  ; biparse_many := (fun _ _ => print_many)
  }.

Definition pure_many {U A} (p : pfunction (option U) (option A)) : pfunction (list U) (list A) :=
  fix pure_many_ xs :=
    match xs with
    | nil => match p None with Some None => Some nil | _ => None end
    | x :: xs => match p (Some x) with Some (Some y) => option_map (fun ys => y :: ys) (pure_many_ xs) | _ => None end
    end.

#[global]
Instance Biparser_pure : Biparser pfunction :=
  {|
    biparse_token := (fun n => Some n) : pfunction nat nat;
    biparse_many := fun _ _ => pure_many
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
  forall a s, P a ->
    (exists a', pr a = Some (s, a')) ->
    pa s == ret (Some (a, [])).

(* We have proved [biparse_string_left_round_trip] *)

Definition right_round_trip A (pa : parser2 A A) (pr : printer2 A A)
  : Prop :=
  forall a s,
    pa s == ret (Some (a, [])) ->
    exists a', pr a = Some (s, a').

Definition backward {A} (p : biparser A A) : Prop :=
  forall (a : A) (s s' : list t),
    (exists a', snd p a = Some (s, a')) ->
    fst p (s ++ s') == ret (Some (a, s')) .

Definition forward {A} (p : biparser A A) : Prop :=
  forall (a : A) (s01 s1 s0 : list t),
    fst p s01 == ret (Some (a, s1)) ->
    (exists a', snd p a = Some (s0, a')) ->
    s01 = s0 ++ s1.

(** *** Weak but compositional roundtrip properties *)

Definition weak_backward_on {U A} (p : biparser U A) (u : U) : Prop :=
  forall (a : A) (s s' : list t),
    snd p u = Some (s, a) ->
    fst p (s ++ s') == ret (Some (a, s')).

Definition weak_backward {U A} (p : biparser U A) : Prop :=
  forall u, weak_backward_on p u.

Definition weak_forward_on {U A} (p : biparser U A) (a : A) : Prop :=
  forall (u : U) (s01 s0 s1 : list t),
    fst p s01 == ret (Some (a, s1)) ->
    snd p u = Some (s0, a) ->
    s01 = s0 ++ s1.

Definition weak_forward {U A} (p : biparser U A) : Prop :=
  forall a, weak_forward_on p a.

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

Definition onlyNil {U} (xs : list U) : option (list U) :=
  match xs with
  | nil => Some nil
  | _ => None
  end.

Lemma unfold_biparse_many {U A} (p : biparser (option U) (option A))
  : biparse_many p ==
    (ox <- comap (fun x => Some (head x)) p ;;
    match ox with
    | None => comap onlyNil (ret nil)
    | Some x => xs <- comap tail (biparse_many p) ;;
                ret (x :: xs)
    end).
Proof.
  constructor.
  - change (fst (biparse_many p)) with (parse_many (fst p)).
    rewrite unfold_parse_many.
    apply Proper_bind.
    + apply (symmetry (unfold_comap_Fwd parser (U := list U) (V := U) head (fst p))).
    + intros []; [ | ].
      apply Proper_bind.
      { symmetry; apply (unfold_comap_Fwd parser tail). }
      { intros ?. reflexivity. }
      symmetry; apply (unfold_comap_Fwd parser onlyNil).
  - intros u; induction u; cbn.
    + destruct (snd p None) as [[s [x |]] |] eqn:E2; cbn; try reflexivity.
      rewrite 2 app_nil_r. reflexivity.
    + destruct (snd p (Some _)) as [[s [x |]] |] eqn:E2; cbn; try reflexivity.
      { destruct print_many as [[]|] eqn:E2'; cbn; [ | reflexivity ].
        rewrite 3 app_nil_r. reflexivity. }
Qed.

Lemma weak_backward_on_bind {U A B} (p : biparser U A) (k : A -> biparser U B) u
  : weak_backward_on p u -> (forall a, weak_backward_on (k a) u) -> weak_backward_on (bind p k) u.
Proof.
  intros WBp WBk b s s'. cbn.
  destruct (snd p u) as [ [s1 a] | ] eqn:ep; cbn; try discriminate.
  destruct (snd (k a) u) as [ [s2 b'] | ] eqn:ek; cbn; try discriminate.
  intros Hpk. inv Hpk.
  eapply WBp in ep.
  eapply WBk in ek.
  rewrite <- app_assoc.
  rewrite ep, ret_bind.
  eassumption.
Qed.

#[global]
Instance Proper_fst {U A} : Proper (equiv ==> eq ==> equiv) (@fst (parser2 U A) (printer2 U A)).
Proof.
  unfold Proper, respectful; intros * H.
  intros ? _ <-.
  apply H.
Qed.

#[global]
Instance Proper_snd {U A} : Proper (equiv ==> eq ==> equiv) (@snd (parser2 U A) (printer2 U A)).
Proof.
  unfold Proper, respectful; intros * H.
  intros ? _ <-.
  apply H.
Qed.

Definition iff_forall {A : Type} {P Q : A -> Prop} : (forall a, P a <-> Q a) -> (forall a, P a) <-> (forall a, Q a).
Proof. firstorder. Qed.

Definition iff_impl {A B C D : Prop} : (A <-> C) -> (B <-> D) -> (A -> B) <-> (C -> D).
Proof. firstorder. Qed.

#[global]
Instance Proper_weak_backward_on {U A} : Proper (equiv ==> eq ==> iff) (@weak_backward_on U A).
Proof.
  unfold Proper, respectful, weak_backward_on. intros ? ? Ep ? ? Eu.
  apply iff_forall; intros a.
  apply iff_forall; intros s.
  apply iff_forall; intros s'.
  rewrite Ep, Eu; reflexivity.
Qed.

#[global]
Instance Proper_weak_forward_on {U A} : Proper (equiv ==> eq ==> iff) (@weak_forward_on U A).
Proof.
  unfold Proper, respectful, weak_backward_on. intros ? ? Ep ? ? Eu.
  apply iff_forall; intros u.
  apply iff_forall; intros s01.
  apply iff_forall; intros s0.
  apply iff_forall; intros s1.
  rewrite Ep, Eu; reflexivity.
Qed.

(** ** Compositionality of weak roundtrip properties *)

Lemma weak_backward_on_comap {U V A} (f : U -> option V) (p : biparser V A) (u : U)
  : (forall v, f u = Some v -> weak_backward_on p v) -> weak_backward_on (comap f p) u.
Proof.
  unfold weak_backward_on.
  intros H a s s' Ha.
  transitivity (fst p (s ++ s')).
  { assert (W : fst (comap f p) == fst p).
    { change (fst (comap f p)) with (comap f (fst p)).
      apply (unfold_comap_Fwd _); auto. }
    apply W.
  }
  cbn in Ha.
  destruct (f u) as [v | ].
  - apply (H v); auto.
    rewrite <- Ha.
    rewrite <- bind_ret at 1.
    reflexivity.
  - discriminate.
Qed.

Lemma list_length_strong_ind {A} (P : list A -> Prop)
  : (forall x, (forall y, length y < length x -> P y) -> P x) ->
    forall x, P x.
Proof.
  intros IH.
  assert (forall n x, length x = n -> P x).
  { induction n using lt_wf_ind.
    intros ? <-.
    apply IH. intros; eapply H; eauto.
  }
  intros x.
  apply (H _ _ eq_refl).
Qed.

Definition run_parser {A} (p : parser A) (s : stream) : delay (option (A * stream)) :=
  p s.

#[global]
Instance Proper_run_parser {A} : Proper (equiv ==> eq ==> equiv) (@run_parser A).
Proof.
  unfold Proper, respectful, run_parser.
  intros ? ? Hp ? _ <-. apply Hp.
Qed.

Lemma run_parser_bind {A B} (p : parser A) (k : A -> parser B)
    (s s' : stream) (a : A)
    (H : run_parser p s == ret (Some (a, s')))
  : run_parser (bind p k) s == run_parser (k a) s'.
Proof.
  cbn.
  unfold run_parser in H.
  rewrite H.
  rewrite ret_bind.
  reflexivity.
Qed.

Lemma weak_backward_many U A (p : biparser (option U) (option A))
  (WB : weak_backward p) : weak_backward (biparse_many p).
Proof.
  unfold weak_backward.
  intros us; induction us as [ | u us IH ].
  - unfold weak_backward_on.
    intros a s s'. cbn.
    unfold weak_backward, weak_backward_on in WB.
    destruct (snd p None) as [ [s0 [ | ]] | ] eqn:EpNone; [ discriminate | | discriminate ].
    injection 1. intros <- <-.
    specialize (WB _ _ _ s' EpNone).
    change (run_parser (parse_many (fst p)) (s0 ++ s') == ret (Some ([], s'))).
    rewrite unfold_parse_many.
    rewrite (run_parser_bind _ _ _ _ _ WB).
    reflexivity.
  - unfold weak_backward_on.
    intros a s s'. cbn.
    destruct (snd p (Some u)) as [ [ s0 [ y | ] ] | ] eqn:EpSome; [ | discriminate .. ].
    unfold weak_backward_on in IH; cbn in IH.
    destruct print_many as [ [s1 a'] | ] eqn:Eprint_many; [ cbn | discriminate ].
    injection 1. intros <- <-.
    rewrite <- app_assoc.
    change (run_parser (parse_many (fst p)) (s0 ++ s1 ++ s') == ret (Some (y :: a', s'))).
    rewrite unfold_parse_many.
    specialize (WB _ _ _ (s1 ++ s') EpSome).
    rewrite (run_parser_bind _ _ _ _ _ WB).
    specialize (IH _ _ s' eq_refl).
    rewrite (run_parser_bind _ _ _ _ _ IH).
    reflexivity.
Qed.

Lemma fst_bind {U A B} (p : biparser U A) (k : A -> biparser U B) s
  : fst (bind p k) s = bind (fst p s) (fun a =>
      match a with
      | None => ret None
      | Some (x, s) => fst (k x) s
      end).
Proof. reflexivity. Qed.

Lemma snd_bind {U A B} (p : biparser U A) (k : A -> biparser U B) u
  : snd (bind p k) u = bind (snd p u) (fun x => snd (k x) u).
Proof. reflexivity. Qed.

Lemma fst_comap {U V A} (f : U -> option V) (p : biparser V A) s
  : fst (comap f p) s == fst p s.
Proof.
  cbn.
  etransitivity; [ | apply bind_ret ].
  apply Proper_bind; [ reflexivity | ].
  intros [ [] | ]; reflexivity.
Qed.

Lemma snd_comap {U V A} (f : U -> option V) (p : biparser V A) u
  : snd (comap f p) u == bind (f u) (snd p).
Proof.
  cbn.
  destruct (f u); [ cbn | reflexivity ].
  destruct snd as [ [] | ]; [ cbn | reflexivity ].
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma weak_forward_on_bind {U A B} (p : biparser U A) (k : A -> biparser U B) (f : B -> option A)
    (Hf : forall a, (x <- k a;; ret (f x)) == (x <- k a;; ret (Some a)))
  : forall b,
    (forall a, f b = Some a -> weak_forward_on p a) -> (forall a, weak_forward_on (k a) b) -> weak_forward_on (bind p k) b.
Proof.
  intros b Hp Hk u s01 s1 s0 Hparse Hprint.
  apply Delay.bind_inv in Hparse.
  destruct Hparse as (oa & Hp1 & Hk1).
  destruct oa as [ [a1 sp1] |].
  2:{ apply Delay.ret_inv in Hk1. discriminate. }
  simpl in Hprint.
  destruct snd as [ [s__m2 a2] | ] eqn:ep2 in Hprint; try discriminate;
    simpl in Hprint;
    destruct snd as [ [s__mk2 b2] | ] eqn:ek2 in Hprint; try discriminate;
    inversion Hprint; clear Hprint; subst.
  assert (ea : f b = Some a1 /\ a2 = a1); [ | destruct ea as [Hfb ->] ].
  { pose proof (Hf a1) as Hf1.
    apply Proper_fst in Hf1.
    specialize (Hf1 sp1 _ eq_refl).
    rewrite 2 fst_bind, Hk1, 2 ret_bind in Hf1. apply Delay.ret_inv in Hf1.
    pose proof (Hf a2) as Hf2.
    apply Proper_snd in Hf2.
    specialize (Hf2 u _ eq_refl).
    rewrite 2 snd_bind, ek2 in Hf2; cbn in Hf2.
    inv Hf1. inv Hf2. rewrite H0 in H1. inv H1; auto.
  }
  specialize (Hp _ Hfb _ _ _ _ Hp1 ep2).
  specialize (Hk _ _ _ _ _ Hk1 ek2).
  subst s01 sp1. rewrite app_assoc; auto.
Qed.

Lemma weak_forward_on_comap {U V A} (p : biparser U A) (f : V -> option U) a
  : weak_forward_on p a -> weak_forward_on (comap f p) a.
Proof.
  unfold weak_forward_on.
  intros H v s01 s0 s1 H1 H2.
  cbn in H2.
  destruct (f v) as [ | ] eqn:Efv; [ | discriminate ].
  destruct (snd p u) as [ [] | ] eqn:E2; cbn in H2; [ | discriminate ].
  rewrite app_nil_r in H2. inv H2.
  rewrite fst_comap in H1.
  eapply H; try eassumption.
Qed.

Lemma weak_forward_ret U A (a : A) : @weak_forward U A (ret a).
Proof.
  intros u b s s' s'' e e'.
  apply Delay.ret_inv in e. inv e. inv e'. reflexivity.
Qed.

Lemma weak_forward_on_many U A (p : biparser (option U) (option A))
  (WF : weak_forward p) : forall xs, (forall y ys, xs = y :: ys -> weak_forward_on (biparse_many p) ys) -> weak_forward_on (biparse_many p) xs.
Proof.
  intros xs IH.
  rewrite unfold_biparse_many.
  apply weak_forward_on_bind with (f := fun x => Some (head x)).
  + intros [].
    * rewrite 2 bind_bind. apply Proper_bind; [ reflexivity | intros ? ].
      rewrite 2 ret_bind. reflexivity.
    * rewrite <- 2 natural_comap. apply Proper_comap; [ reflexivity | ].
      rewrite 2 ret_bind; reflexivity.
  + intros ? H; inv H.
    apply weak_forward_on_comap.
    apply WF.
  + intros [].
    * apply weak_forward_on_bind with (f := tail).
      { intros a0; rewrite 2 ret_bind; reflexivity. }
      { intros ys Hys. destruct xs; [ discriminate | inv Hys].
        apply weak_forward_on_comap.
        apply (IH _ _ eq_refl). }
      { intros; apply weak_forward_ret. }
    * apply weak_forward_on_comap. apply weak_forward_ret.
Qed.

Lemma weak_forward_many U A (p : biparser (option U) (option A))
  (WF : weak_forward p) : weak_forward (biparse_many p).
Proof.
  unfold weak_forward.
  intros xs; induction xs; apply weak_forward_on_many; auto.
  - intros; discriminate.
  - intros ? ? H; inv H; auto.
Qed.

Lemma weak_backward_ret U A (a : A) : @weak_backward U A (ret a).
Proof.
  intros u b s s' e. inversion_clear e; reflexivity.
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
    rewrite E, ret_bind. reflexivity.
  - discriminate.
Qed.

Lemma weak_backward_bind U A B
      (m : biparser U A) (k : A -> biparser U B)
      (Hm : weak_backward m)
      (Hk : forall a, weak_backward (k a)) :
  weak_backward (bind m k).
Proof.
  unfold weak_backward. intros u.
  apply weak_backward_on_bind.
  - apply Hm.
  - intros a; apply Hk.
Qed.

Instance Compositional_weak_backward :
  Compositional (@weak_backward) := {
  ret_comp := weak_backward_ret;
  bind_comp := weak_backward_bind;
  comap_comp := weak_backward_comap;
}.

Lemma weak_backward_fail U A (s : String):
  weak_backward (@fail (biparser U) _ _ A s).
Proof.
  discriminate.
Qed.

Lemma weak_backward_token :
  weak_backward biparse_token.
Proof.
  intros u b s s' H; inversion H; subst; reflexivity.
Qed.

Lemma weak_forward_comap U U' A (f : U -> option U')
      (m : biparser U' A)
      (Hm : weak_forward m) :
  weak_forward (comap f m).
Proof.
  intros u; apply weak_forward_on_comap. apply Hm.
Qed.

Lemma weak_forward_bind U A B
      (m : biparser U A) (k : A -> biparser U B) (f : B -> option A)
      (Hf : forall a, (x <- k a;; ret (f x)) == (x <- k a;; ret (Some a)))
      (Hm : weak_forward m)
      (Hk : forall a, weak_forward (k a)) :
  weak_forward (bind m k).
Proof.
  intros u. eapply weak_forward_on_bind with (f := f).
  - assumption.
  - intros; apply Hm.
  - intros; apply Hk.
Qed.

#[global]
Instance Quasicompositional_weak_forward :
  Quasicompositional (@weak_forward) := {
  ret_comp' := weak_forward_ret;
  bind_comp' := weak_forward_bind;
  comap_comp' := weak_forward_comap;
}.

Lemma weak_forward_fail U A (s : String):
  weak_forward (@fail (biparser U) _ _ A s).
Proof.
  discriminate.
Qed.

Lemma weak_forward_token :
  weak_forward biparse_token.
Proof.
  intros u b s s' s'' H1 H2.
  destruct s; simpl in *.
  - apply Delay.ret_inv in H1. discriminate.
  - apply Delay.ret_inv in H1. inversion H1; inversion H2; subst.
    reflexivity.
Qed.

(**)

Lemma digit_or_space_digit n : n < 10 -> digit_or_space (Some n) = n.
Proof. reflexivity. Qed.

Lemma digit_or_space_space : digit_or_space None = 10.
Proof. reflexivity. Qed.

Lemma weak_forward_digit : weak_forward biparse_digit.
Proof.
  unfold biparse_digit; intros.
  apply bind_comap_comp'.
  { intros a; destruct lt_dec.
    - rewrite 2 ret_bind. rewrite digit_or_space_digit; [ | auto ]. reflexivity.
    - destruct Nat.eq_dec.
      + rewrite 2 ret_bind. unfold t. rewrite digit_or_space_space.
        subst; reflexivity.
      + rewrite 2 partial_left_zero; reflexivity.
  }
  { apply weak_forward_token. }
  { intros a; destruct lt_dec.
    - apply weak_forward_ret.
    - destruct Nat.eq_dec.
      + apply weak_forward_ret.
      + apply weak_forward_fail. }
Qed.

Lemma weak_backward_digit : weak_backward biparse_digit.
Proof.
  unfold biparse_digit.
  apply bind_comp.
  - apply comap_comp. apply weak_backward_token.
  - intros a.
    destruct (lt_dec a _).
    + apply weak_backward_ret.
    + destruct (Nat.eq_dec a _).
      * apply weak_backward_ret.
      * apply weak_backward_fail.
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

Lemma digit_unique {b} (d1 d2 : digit b) : proj1_sig d1 = proj1_sig d2 -> d1 = d2.
Proof.
  destruct d1, d2; cbn; intros <-.
  f_equal. apply le_unique.
Qed.

Lemma weak_forward_nat : weak_forward biparse_nat.
Proof.
  unfold biparse_nat.
  apply bind_comap_comp'.
  { intros. destruct read_nat eqn:Eread.
    + rewrite 2 ret_bind. rewrite (read_show_nat _ _ Eread). reflexivity.
    + rewrite 2 partial_left_zero. reflexivity. }
  { apply weak_forward_many. apply weak_forward_digit. }
  { intros. destruct read_nat eqn:Eread.
    + apply weak_forward_ret.
    + apply weak_forward_fail. }
Qed.

Lemma fmap_fmap_ {M} `{MonadLaws M} A B C (u : M A) (f : A -> B) (g : B -> C)
  : (u >>= fun x => ret (g (f x))) == ((u >>= fun x => ret (f x)) >>= fun y => ret (g y)).
Proof.
  rewrite bind_bind.
  apply Proper_bind; [ reflexivity | intros x ].
  rewrite ret_bind. reflexivity.
Qed.

Lemma replicate_length {P} `{Biparser P} `{Eq2 P} `{!forall a, MonadLaws (P a)} `{PL : !ProfmonadLaws P} (n : nat)
  :  replicate (P := P) n biparse_token >>= (fun x : list t => ret (List.length x))
  == replicate n biparse_token >>= (fun _ : list t => ret n).
Proof.
  induction n; cbn.
  - rewrite 2 ret_bind. reflexivity.
  - rewrite !bind_bind. apply Proper_bind; [ reflexivity | intros x ].
    rewrite !bind_bind.
    transitivity (comap (P := P) tail (replicate n biparse_token >>= fun x => ret (length x)) >>= fun n => ret (S n)).
    + rewrite natural_comap. rewrite !bind_bind. apply Proper_bind; [ reflexivity | intros xs ].
      rewrite 2 ret_bind. reflexivity.
    + rewrite IHn. rewrite natural_comap, !bind_bind. apply Proper_bind; [ reflexivity | intros xs ].
      rewrite 2 ret_bind. reflexivity.
Qed.

Lemma replicate_length_ {P} `{Biparser P} `{Eq2 P} `{!forall a, MonadLaws (P a)} `{PL : !ProfmonadLaws P} (n : nat)
  :  replicate (P := P) n biparse_token >>= (fun x : list t => ret (Some (List.length x)))
  == replicate n biparse_token >>= (fun _ : list t => ret (Some n)).
Proof.
  rewrite fmap_fmap_.
  rewrite fmap_fmap_ with (f := fun _ => n).
  apply Proper_bind; [ | reflexivity ].
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

Lemma weak_backward_nat : weak_backward biparse_nat.
Proof.
  unfold biparse_nat.
  apply bind_comp.
  - apply comap_comp.
    apply weak_backward_many.
    apply weak_backward_digit.
  - intros a. destruct read_nat.
    + apply ret_comp.
    + apply weak_backward_fail.
Qed.

Theorem weak_backward_string : weak_backward biparse_string.
Proof.
  unfold biparse_string.
  apply bind_comp.
  - apply comap_comp.
    apply weak_backward_nat.
  - intros n. apply weak_backward_replicate.
    apply weak_backward_token.
Qed.
