From Coq Require Import
  Morphisms
  FunctionalExtensionality
  Arith
  List
  Lia.
Import ListNotations.
From Profmonad Require Import
  Utils
  Profmonad.

Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

Definition gen (A : Type) : Type := list A.

Instance Monad_gen : Monad gen :=
  {| ret := fun A x => x :: nil
  ;  bind := fun A B xs k => List.flat_map k xs
  |}.

Instance MonadLaws_gen : MonadLaws gen.
Proof.
  constructor; cbn; intros.
  - induction m; cbn; f_equal; auto.
  - apply app_nil_r.
  - induction m; cbn; f_equal; auto.
    rewrite flat_map_app; f_equal; auto.
  - unfold Proper, respectful, pointwise_relation.
    intros x _ <- f f' Hf.
    f_equal. apply functional_extensionality; auto.
Qed.

Definition pred (A : Type) : Type := A -> bool.

Definition bigen : Type -> Type -> Type :=
  Product (Fwd gen) (Bwd option).

Instance ProfmonadLaws_bigen : ProfmonadLaws bigen.
Proof.
  apply LawfulProfmonad_Product.
  - apply ProfmonadLaws_Fwd.
    apply MonadLaws_gen.
  - exact (ProfmonadLaws_Bwd option).
Qed.

Definition run_gen {A B : Type} (g : bigen A B) : gen B :=
  fst g.

Definition member {A} (a : A) (g : gen A) : Prop :=
  List.In a g.

Definition is_Some {A : Type} (o : option A) : bool :=
  match o with
  | Some _ => true
  | None => false
  end.

Definition run_predP {A B : Type} (g : bigen A B) : A -> option B :=
  snd g.

Definition run_pred {A B : Type} (g : bigen A B) : A -> bool :=
  fun x => is_Some (snd g x).

Definition filter_ {A B} (f : A -> bool) : bigen unit B -> bigen A B :=
  comap (fun x => if f x then Some tt else None).

Definition bigen_bool : bigen bool bool :=
  ( [true; false]
  , Some
  ).

Definition bigen_range (min max : nat) : bigen nat nat :=
  ( seq min (max + 1 - min)
  , fun x => if (min <=? x) && (x <=? max) then Some x else None
  )%bool.

(** * Generating binary search trees *)

Inductive tree (A : Type) : Type :=
| Leaf
| Node : tree A -> A -> tree A -> tree A
.

Definition is_Leaf {A} (t : tree A) : bool :=
  match t with
  | Leaf => true
  | Node _ _ _ => false
  end.

Definition Node_value {A} (t : tree A) : option A :=
  match t with
  | Node _ v _ => Some v
  | _ => None
  end.

Definition Node_left {A} (t : tree A) : option (tree A) :=
  match t with
  | Node l _ _ => Some l
  | _ => None
  end.

Definition Node_right {A} (t : tree A) : option (tree A) :=
  match t with
  | Node _ _ r => Some r
  | _ => None
  end.

Definition bigen_leaf : bigen (tree nat) (tree nat) :=
  filter_ is_Leaf (ret Leaf).

Fixpoint bigen_bst (d : nat) (min max : nat) : bigen (tree nat) (tree nat) :=
  match d, Nat.ltb max min with
  | S d, false =>
    isL <-( is_Leaf ) bigen_bool ;;
    if isL then ret Leaf
    else (
      n <-( Node_value ?) (bigen_range min max) ;;
      l <-( Node_left ?) (bigen_bst d min (n-1)) ;;
      r <-( Node_right ?) (bigen_bst d (n+1) max) ;;
      ret (Node l n r)
    )
  | _, _ => bigen_leaf
  end.

Definition gen_bst (d : nat) (min max : nat) : gen (tree nat) :=
  run_gen (bigen_bst d min max).

Definition check_bst (d : nat) (min max : nat) : tree nat -> bool :=
  run_pred (bigen_bst d min max).

(** * Generator soundness and completeness *)

Definition sound {A : Type} (g : bigen A A) : Prop :=
  forall x, member x (run_gen g) -> run_pred g x = true.

Definition complete {A : Type} (g : bigen A A) : Prop :=
  forall x, run_pred g x = true -> member x (run_gen g).

(*
Definition weak_sound {A B : Type} (g : bigen A B) : Prop :=
  forall x, member x (run_gen g) -> _.
*)

Definition weak_complete {A B : Type} (g : bigen A B) : Prop :=
  forall x y, run_predP g x = Some y -> member y (run_gen g).

Definition aligned {A : Type} (g : bigen A A) : Prop :=
  forall x y, run_predP g x = Some y -> x = y.

Lemma run_pred_true {A B} (x : A) (g : bigen A B)
  : run_pred g x = true -> exists y, run_predP g x = Some y.
Proof.
  unfold run_pred, run_predP.
  destruct (snd g x); discriminate + eauto.
Qed.

Theorem aligned_weak_complete {A} (g : bigen A A)
  : aligned g -> weak_complete g -> complete g.
Proof.
  intros ALIGNED WCOMPLETE x TRUE.
  destruct (run_pred_true _ _ TRUE) as [y SOME].
  rewrite (ALIGNED x y SOME).
  eapply WCOMPLETE; eauto.
Qed.

Lemma member_ret {A} (a : A) : member a (ret a).
Proof.
  constructor. reflexivity.
Qed.

Instance Compositional_weak_complete : Compositional (@weak_complete).
Proof.
  unfold weak_complete.
  constructor.
  - intros. cbv in H. injection H. intros []. apply member_ret.
  - cbn; intros.
    destruct (Utils.option_bind_inv_Some _ _ _ H1) as [x' Ex'].
    rewrite Ex' in H1. cbn in H1.
    specialize H with (1 := Ex').
    apply in_flat_map.
    exists x'.
    split; auto.
    eapply H0, H1.
  - cbn; intros.
    apply in_flat_map.
    unfold Profunctor_pfunction in H0.
    destruct (Utils.option_map_inv_Some _ _ _ H0) as [x' Ex'].
    rewrite Ex' in H0; cbn in H0.
    destruct (Utils.option_bind_inv_Some _ _ _ Ex') as [r Er].
    rewrite Er in Ex'; cbn in Ex'.
    injection H0; intros [].
    exists x'.
    split.
    + eapply H, Ex'.
    + do 2 constructor.
Qed.

Lemma weak_complete_range min max : weak_complete (bigen_range min max).
Proof.
  red; cbn.
  intros x y.
  destruct (Nat.leb_spec min x); cbn; [ | discriminate].
  destruct (Nat.leb_spec x max); cbn; [ | discriminate].
  - injection 1; intros [].
    apply in_seq. lia.
Qed.

Lemma weak_complete_bool : weak_complete bigen_bool.
Proof.
  intros x []; cbn; eauto.
Qed.

Lemma weak_complete_leaf : weak_complete bigen_leaf.
Proof.
  intros [] y; cbn; try discriminate.
  injection 1; eauto.
Qed.

Theorem weak_complete_bst d min max
  : weak_complete (bigen_bst d min max).
Proof.
  revert min max; induction d; cbn [bigen_bst]; intros.
  - apply weak_complete_leaf.
  - destruct (Nat.ltb_spec max min).
    + apply weak_complete_leaf.
    + apply bind_comp.
      { apply comap_comp. apply @weak_complete_bool. }
      { intros [].
        { apply ret_comp. }
        { repeat (apply bind_comp; [ | intros ]).
          4: apply ret_comp.
          all: apply comap_comp; auto.
          apply weak_complete_range.
        }
      }
Qed.

Lemma aligned_leaf : aligned bigen_leaf.
Proof.
  unfold bigen_leaf.
  intros x y.
  destruct x; cbn.
  - injection 1. auto.
  - discriminate.
Qed.

Lemma run_predP_bind_comap {U V A B} (f : U -> V) u (k : A -> bigen U B) x
  : run_predP (b <-( f ) u ;; k b) x = Utils.bind_option (run_predP u (f x)) (fun b => run_predP (k b) x).
Proof.
  cbn. unfold Profunctor_pfunction. cbn.
  f_equal.
  unfold run_predP.
  destruct snd; reflexivity.
Qed.

Lemma aligned_bigen_bool : aligned bigen_bool.
Proof.
  cbv; congruence.
Qed.

Lemma valigned_bigen_bool b : run_predP bigen_bool b = Some b.
Proof.
  reflexivity.
Qed.

Lemma run_predP_bind {U A B} (u : bigen U A) (k : A -> bigen U B) x
  : run_predP (bind u k) x = Utils.bind_option (run_predP u x) (fun y => run_predP (k y) x).
Proof.
  reflexivity.
Qed.

Lemma run_predP_comap {U V A} (f : V -> option U) (u : bigen U A) x
  : run_predP (comap f u) x = Utils.bind_option (f x) (run_predP u).
Proof.
  cbn; unfold Profunctor_pfunction. destruct (f x); cbn.
  - unfold run_predP. destruct snd; reflexivity.
  - reflexivity.
Qed.

Lemma aligned_bigen_range min max : aligned (bigen_range min max).
Proof.
  red; cbn. intros x y.
  destruct (Nat.leb_spec min x).
  - destruct (Nat.leb_spec x max); cbn.
    + injection 1; auto.
    + discriminate.
  - discriminate.
Qed.

Theorem aligned_bst d min max : aligned (bigen_bst d min max).
Proof.
  revert min max; induction d; intros; cbn [bigen_bst].
  - exact @aligned_leaf.
  - destruct (Nat.ltb_spec max min).
    + exact @aligned_leaf.
    + unfold aligned.
      intros x y.
      rewrite run_predP_bind_comap.
      rewrite valigned_bigen_bool; cbn [Utils.bind_option].
      destruct x; cbn [is_Leaf].
      * injection 1; auto.
      * rewrite run_predP_bind, run_predP_comap. cbn [Utils.bind_option Node_value].
        destruct run_predP eqn:Erange; cbn [Utils.bind_option]; [ | discriminate].
        apply aligned_bigen_range in Erange; subst.
        rewrite run_predP_bind, run_predP_comap. cbn [Utils.bind_option Node_left].
        destruct run_predP eqn:Eleft; cbn [Utils.bind_option]; [ | discriminate].
        apply IHd in Eleft; subst.
        rewrite run_predP_bind, run_predP_comap. cbn [Utils.bind_option Node_right].
        destruct run_predP eqn:Eright; cbn [Utils.bind_option]; [ | discriminate].
        apply IHd in Eright; subst.
        injection 1. auto.
Qed.

Theorem complete_bst d min max : complete (bigen_bst d min max).
Proof.
  apply aligned_weak_complete.
  - apply aligned_bst.
  - apply weak_complete_bst.
Qed.

Lemma In_singleton_inv {A} (x y : A) : In x [y] -> x = y.
Proof.
  intros H; inversion H; subst; auto. inversion H0.
Qed.

Definition strongly_sound {A : Type} (g : bigen A A) : Prop :=
  forall x, member x (run_gen g) -> snd g x == Some x.

Lemma strongly_sound_sound {A} (g : bigen A A) : strongly_sound g -> sound g.
Proof.
  intros F x H. unfold run_pred. rewrite (F _ H). reflexivity.
Qed.

#[global]
Instance Idiomcompositional_strongly_sound : Idiomcompositional (@strongly_sound).
Proof.
  constructor.
  - unfold strongly_sound. intros * H; apply In_singleton_inv in H; subst; reflexivity.
  - unfold strongly_sound; cbn; intros * Hf Hm Hk b Hb.
    apply in_flat_map in Hb. destruct Hb as (a & Ha1 & Hb).
    apply in_flat_map in Ha1; destruct Ha1 as (a2 & Ha2 & Ha1).
    apply In_singleton_inv in Ha1; subst a2.
    apply Hm in Ha2. apply Hk in Hb.
    rewrite option_map_id.
    assert (Hf' : f b = Some a).
    { specialize (Hf a).
      destruct Hf as [Hf1 Hf2].
      cbn in Hf1. cbn in Hf2. unfold pointwise_relation in Hf2.
      specialize (Hf2 b).
      rewrite Hb in Hf2. injection Hf2. auto. }
    rewrite Hf'; cbn. rewrite Ha2; cbn. auto.
Qed.

Lemma strongly_sound_leaf : strongly_sound bigen_leaf.
Proof.
  red; cbn. intros ? [<- | []]. cbn. reflexivity.
Qed.

Lemma strongly_sound_bool : strongly_sound bigen_bool.
Proof.
  red. reflexivity.
Qed.

Lemma strongly_sound_range min max : strongly_sound (bigen_range min max).
Proof.
  red; cbn.
  intros x Hx; apply in_seq in Hx. destruct Hx as (Hmin & Hmax).
  rewrite (proj1 (Bool.reflect_iff _ _ (Nat.leb_spec0 min x)) Hmin).
  rewrite (proj1 (Bool.reflect_iff _ _ (Nat.leb_spec0 _ _))); [ | lia ].
  reflexivity.
Qed.

Theorem strongly_sound_bst d min max : strongly_sound (bigen_bst d min max).
Proof.
  revert min max; induction d; intros; cbn [bigen_bst].
  - exact @strongly_sound_leaf.
  - destruct (Nat.ltb_spec max min).
    + apply @strongly_sound_leaf.
    + apply bind_idiomcomp.
      { intros [].
        - reflexivity.
        - rewrite 2 bind_bind.
          apply Proper_bind; [ reflexivity | intros ? ].
          rewrite 2 bind_bind.
          apply Proper_bind; [ reflexivity | intros ? ].
          rewrite 2 bind_bind.
          apply Proper_bind; [ reflexivity | intros ? ].
          rewrite 2 ret_bind.
          reflexivity. }
      { apply @strongly_sound_bool. }
      { intros [].
        { apply ret_idiomcomp. }
        { repeat (apply bind_idiomcomp; [ | auto using strongly_sound_range | intros ]); [ .. | apply ret_idiomcomp ].
          - intros ?.
            rewrite 2 bind_bind.
            apply Proper_bind; [ reflexivity | intros ? ].
            rewrite 2 bind_bind.
            apply Proper_bind; [ reflexivity | intros ? ].
            rewrite 2 ret_bind; reflexivity.
          - intros ?.
            rewrite 2 bind_bind.
            apply Proper_bind; [ reflexivity | intros ? ].
            rewrite 2 ret_bind; reflexivity.
          - intros ?. rewrite 2 ret_bind; reflexivity.
        }
      }
Qed.

Theorem sound_bst d min max : sound (bigen_bst d min max).
Proof.
  apply strongly_sound_sound, strongly_sound_bst.
Qed.

Print Assumptions complete_bst.
