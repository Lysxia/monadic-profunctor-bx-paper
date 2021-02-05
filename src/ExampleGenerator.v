From Coq Require Import
  Arith
  List
  Lia.
Import ListNotations.
From Promonad Require Import
  Promonad.

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
Qed.

Definition pred (A : Type) : Type := A -> bool.

Definition bigen : Type -> Type -> Type :=
  Product (Fwd gen) (Bwd option).

Instance PromonadLaws_bigen : PromonadLaws bigen.
Proof.
  apply LawfulPromonad_Product.
  - apply PromonadLaws_Fwd.
    apply MonadLaws_gen.
  - exact (PromonadLaws_Bwd option).
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
  - typeclasses eauto.
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

Print Assumptions weak_complete_bst.
