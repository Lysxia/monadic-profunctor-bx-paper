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
  { Biparser_Profmonad :> Profmonad P;
    Biparser_Partial :> forall U, MonadPartial (P U);
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

#[global] Instance Setoid_delay {A} : Setoid (m A).
Proof.
Admitted.

Definition terminates_with {A : Type} (P : A -> Prop) : m A -> Prop.
Admitted.

Definition may_terminate_with {A : Type} (P : A -> Prop) : m A -> Prop :=
  fun p => forall u, terminates_with (eq u) p -> P u.

#[global]
Notation terminates_with' p P := (terminates_with P p) (only parsing).

#[global]
Notation may_terminate_with' p P := (may_terminate_with P p) (only parsing).

Lemma may_terminate_with_bind {A B} (u : m A) (k : A -> m B) (P : B -> Prop)
  : may_terminate_with (fun a => may_terminate_with P (k a)) u -> may_terminate_with P (bind u k).
Proof.
Admitted.

End Delay.

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
Instance Setoid_parser : Eq1 parser.
Admitted.

#[global]
Instance MonadLaws_parser : MonadLaws parser.
Proof.
Admitted. (*
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
*)

#[global]
Instance MonadPartial_parser : MonadPartial parser :=
  { empty := fun _ _ => ret None }.

(** **** Parser promonad *)

Definition parser2 := Fwd parser.

Definition Profmonad_parser2 := Profmonad_Fwd parser.

Definition parse_many {A} (u : parser (option A)) : parser (list A).
Admitted.

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
Instance MonadPartial_printer : MonadPartial printer :=
  { empty A := None }.

#[global]
Instance MonadPartialLaws_printer : MonadPartialLaws printer.
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
  forall a, P a ->
    match pr a with
    | None => True
    | Some (s, _) => Delay.terminates_with (fun out => out = Some (a, [])) (pa s)
    end.

(* We have proved [biparse_string_left_round_trip] *)

Definition right_round_trip A (pa : parser2 A A) (pr : printer2 A A)
  : Prop :=
  forall s,
    Delay.may_terminate_with (fun out =>
    match out with
    | None => True
    | Some (a, []) =>
      match pr a with
      | None => False
      | Some (s', _) => s = s'
      end
    | Some _ => True
    end) (pa s).

Definition backward {A} (p : biparser A A) : Prop :=
  forall (a : A) (s s' : list t),
    (exists a', snd p a = Some (s, a')) ->
    Delay.terminates_with (fun out => out = Some (a, s')) (fst p (s ++ s')).

Definition forward {A} (p : biparser A A) : Prop :=
  forall (a : A) (s01 s1 s0 : list t),
    Delay.may_terminate_with (fun out =>
    out = Some (a, s1) ->
    (exists a', snd p a = Some (s0, a')) ->
    s01 = s0 ++ s1) (fst p s01).

(** *** Weak but compositional roundtrip properties *)

Definition weak_backward {U A} (p : biparser U A) : Prop :=
  forall (u : U) (a : A) (s s' : list t),
    snd p u = Some (s, a) ->
    Delay.terminates_with' (fst p (s ++ s')) (fun out => out = Some (a, s')).

Definition weak_forward {U A} (p : biparser U A) : Prop :=
  forall (a : A) (s01 : list t),
    Delay.may_terminate_with' (fst p s01) (fun out =>
    forall u s0 s1,
    out = Some (a, s1) ->
    snd p u = Some (s0, a) ->
    s01 = s0 ++ s1).

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
Admitted. (*
  intros ALIGNED WBWD a s s' [a' Ea].
  destruct (ALIGNED a).
  rewrite Ea in H.
  injection H; intros [] [].
  apply (WBWD _ _ _ _ Ea).
Qed. *)

Theorem forward_aligned {A} (p : biparser A A) :
  aligned p ->
  weak_forward p ->
  forward p.
Proof.
Admitted. (*
  intros ALIGNED WFWD a s01 s1 s0 E01 [a' E0].
  destruct (ALIGNED a).
  rewrite E0 in H.
  injection H. intros; subst.
  eapply WFWD; eauto.
Qed. *)

(** ** Compositionality of weak roundtrip properties *)

Lemma weak_backward_many U A (p : biparser (option U) (option A))
  (WB : weak_backward p) : weak_backward (biparse_many p).
Proof.
  unfold weak_backward.
  intros u; induction u; cbn; intros.
  - destruct (snd p None) as [ [ s0 [ | ] ] | ] eqn:E2; inv H.
    apply (WB _ _ _ s') in E2.
    admit.
  - destruct (snd p (Some a)) as [ [ s0 [ | ] ] | ] eqn:E2; try discriminate.
    destruct (print_many (snd p) u) as [ [] | ] eqn:E2'; inv H.
    eapply (WB _ _ _ (s1 ++ s')) in E2.
    admit.
Admitted.

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
  - admit.
  - intros u; induction u; cbn.
    + destruct (snd p None) as [[s [x |]] |] eqn:E2; cbn; try reflexivity.
      rewrite 2 app_nil_r. reflexivity.
    + destruct (snd p (Some _)) as [[s [x |]] |] eqn:E2; cbn; try reflexivity.
      { destruct print_many as [[]|] eqn:E2'; cbn; [ | reflexivity ].
        rewrite 3 app_nil_r. reflexivity. }
Admitted.

#[global]
Instance Proper_fst {U A} : Proper (equiv ==> eq ==> equiv) (@fst (parser2 U A) (printer2 U A)).
Proof.
  unfold Proper, respectful; intros * H.
Admitted.

#[global]
Instance Proper_may_terminate_with' {A} : Proper (pointwise_relation A iff ==> equiv ==> iff) Delay.may_terminate_with.
Proof.
Admitted.

Lemma fst_bind {U A B} (p : biparser U A) (k : A -> biparser U B) s
  : fst (bind p k) s = bind (fst p s) (fun a => 
      match a with
      | None => ret None
      | Some (x, s) => fst (k x) s
      end).
Proof.
Admitted.

Lemma fst_comap {U V A} (f : U -> option V) (p : biparser V A) s
  : fst (comap f p) s = fst p s.
Proof. Admitted.

Lemma weak_forward_many U A (p : biparser (option U) (option A))
  (WF : weak_forward p) : weak_forward (biparse_many p).
Proof.
  unfold weak_forward.
  intros xs; induction xs; intros.
  - rewrite unfold_biparse_many.
    rewrite fst_bind, fst_comap.
    apply Delay.may_terminate_with_bind.
    unfold weak_forward in WF.
    red. intros out1 Hout1.
    intros out2 Hout2.
    intros.
    destruct out1 as [[oa sa] |].
    + assert (Eoa : oa = None); [ | subst oa ].
      { admit. }
      specialize (WF None _ _ Hout1); cbn in WF.
      assert (Ep2 : snd p (head u) = Some (s0, None)).
      { admit. }
      specialize (WF (head u) _ _ eq_refl Ep2).
      admit.
    + admit.
  - rewrite unfold_biparse_many.
    rewrite fst_bind, fst_comap.
    apply Delay.may_terminate_with_bind.
    unfold weak_forward in WF.
    red. intros out1 Hout1.
    intros out2 Hout2.
    intros.
    destruct out1 as [[oa sa] |].
    + assert (Eoa : oa = Some a); [| subst oa ].
      { admit. }
      specialize (WF (Some a) _ _ Hout1); cbn in WF.
      assert (Ep2 : snd p (head u) = Some (s0, Some a)).
      { admit. }
      specialize (WF _ _ _ eq_refl Ep2).
Admitted.

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
  unfold biparse_digit; intros.
  apply bind_comap_comp'.
  { intros a; destruct lt_dec; cbn; reflexivity. }
  { apply weak_forward_token. }
  { intros a; destruct lt_dec.
    - apply weak_forward_ret.
    - apply weak_forward_empty. }
Qed.

Lemma weak_backward_digit {b} : weak_backward (biparse_digit b).
Proof.
  unfold biparse_digit.
  apply bind_comp.
  - apply comap_comp. apply weak_backward_token.
  - intros a.
    destruct (lt_dec a b).
    + apply weak_backward_ret.
    + apply weak_backward_empty.
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
