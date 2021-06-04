(* The main results formalized here are
   [weak_backward_bind]:
     weak backward round tripping is preserved by [bind].
   [weak_forward_bind]:
     weak forward round tripping is preserved by [bind]
     when the continuation is an injective arrow.
 *)

From Coq Require Import
  FunctionalExtensionality
  PeanoNat
  List.
Import ListNotations.

From Promonad Require Import
  Utils
  Promonad.

Record Lens (S U A : Type) : Type := {
  get : S -> option A;
  put : U -> S -> option (A * S * (S -> bool));
}.

Arguments get {S U A}.
Arguments put {S U A}.

Definition bind {S U A B : Type}
           (m : Lens S U A) (k : A -> Lens S U B) : Lens S U B := {|
  get s := a <- get m s;; get (k a) s;
  put u s :=
    abc <- put m u s;;
    let '(a, s, p) := abc in
    def <- put (k a) u s;;
    let '(b, s, q) := def in
    ret (b, s, fun x => (p x && q x)%bool)
|}.

Definition ret {S U A : Type} (a : A) : Lens S U A := {|
  get _ := Some a;
  put _ s := Some (a, s, fun _ => true);
|}.

Instance Monad_Lens S U : Monad (Lens S U) := {|
  Promonad.bind _ _ := bind;
  Promonad.ret _ := ret;
|}.

Definition map1_triple {a a' b c} (f : a -> a') (x : a * b * c) : a' * b * c :=
  (f (fst (fst x)), snd (fst x), snd x).

Instance Profunctor_Lens S : Profunctor (Lens S) :=
  fun _ _ _ _ f g l =>
    {| get s := option_map g (get l s)
    ;  put x s := option_map (map1_triple g) (put l (f x) s)
    |}.

Instance PartialProfunctor_Lens S : PartialProfunctor (Lens S) := {|
  toFailureP A B (l : Lens S A B) :=
    {| get s := get l s
    ;  put ox s := bind_option ox (fun x => put l x s)
    |}
|}.

Definition weak_backward {S U A} (m : Lens S U A) : Prop :=
  forall u a s s_ s' p,
    put m u s = Some (a, s_, p) ->
    p s' = true ->
    get m s' = Some a.

Lemma weak_backward_bind {S U A B} (m : Lens S U A)
      (k : A -> Lens S U B)
      (Hm : weak_backward m)
      (Hk : forall a, weak_backward (k a)) :
  weak_backward (bind m k).
Proof.
  intros u a s s_ s' p Hu Hp.
  simpl in *.
  destruct (put m u) as [[[]] | ] eqn:eputm; try discriminate; simpl in *.
  destruct (put (k a0) u) as [[[]] | ] eqn:eputk; try discriminate; simpl in *.
  inversion Hu; subst; clear Hu.
  destruct (andb_prop _ _ Hp).
  replace (get m s') with (Some a0).
  { simpl. eapply Hk; eauto. }
  { symmetry. eapply Hm; eauto. }
Qed.

Definition weak_forward {S U A} (m : Lens S U A) : Prop :=
  forall u a s s' p,
    get m s = Some a ->
    put m u s = Some (a, s', p) ->
    s = s'.

Lemma weak_forward_bind {S U A B} (m : Lens S U A)
      (k : A -> Lens S U B) (i : B -> option A)
      (Hi : forall a,
          (x <- k a;; ret (i x)) = (x <- k a;; ret (Some a)))
      (Hm : weak_forward m)
      (Hk : forall a, weak_forward (k a)) :
  weak_forward (bind m k).
Proof.
  intros u b s s' p Hget Hput.
  simpl in *.
  destruct (get m s) eqn:egetm; try discriminate; simpl in *.
  destruct (put m u) as [[[]] | ] eqn:eputm;
    try discriminate; simpl in *.
  destruct (put (k a0) u) as [[[]] | ] eqn:eputk;
    try discriminate; simpl in *.
  inversion Hput; subst; clear Hput.
  assert (Hia := Hi a).
  assert (Hia0 := Hi a0).
  apply (f_equal (fun l => get l s)) in Hia.
  apply (f_equal (fun l => put l u s0)) in Hia0.
  cbn in *.
  rewrite Hget in Hia; cbn in Hia.
  rewrite eputk in Hia0; cbn in Hia0.
  inversion Hia0; clear Hia0.
  inversion Hia; clear Hia.
  rewrite H1 in H0; inversion H0; subst; clear H0.
  assert (s = s0); [ | subst ].
  { revert egetm eputm. apply Hm. }
  revert Hget eputk. red in Hk. apply Hk.
Qed.

Definition cat {S T U} (l1 : Lens S T T) (l2 : Lens T U U) : Lens S U U :=
  {| get := fun s => bind_option (get l1 s) (get l2)
  ;  put := fun x s =>
      match get l1 s with
      | None => None
      | Some t =>
        bind_option (put l2 x t) (fun '(y, xt, q') =>
        bind_option (put l1 xt s) (fun '(_, s', p') =>
        if q' xt then
          Some (y, s', p')
        else
          None))
      end |}.

Inductive Tree : Type :=
| Leaf
| Node : Tree -> nat -> Tree -> Tree
.

Definition getRoot (t : Tree) : option nat :=
  match t with
  | Leaf => None
  | Node _ n _ => Some n
  end.

Definition eqb_option {A} (eq : A -> A -> bool) (x y : option A) : bool :=
  match x, y with
  | None, None => true
  | Some x, Some y => eq x y
  | _, _ => false
  end.

Definition rootL : Lens Tree (option nat) (option nat) :=
  {| get t := Some (getRoot t)
  ;  put n' t :=
      let t' := match n', t with
                | None, _ => Leaf
                | Some n, Leaf => Node Leaf n Leaf
                | Some n, Node l _ r => Node l n r
                end in
      let p t'' := eqb_option Nat.eqb n' (getRoot t'') in
      Some (n', t', p)
  |}.

Definition getRight (t : Tree) : option Tree :=
  match t with
  | Leaf => None
  | Node _ _ r => Some r
  end.

Fixpoint eqb_Tree (t1 t2 : Tree) : bool :=
  match t1, t2 with
  | Leaf, Leaf => true
  | Node l1 n1 r1, Node l2 n2 r2 => eqb_Tree l1 l2 && Nat.eqb n1 n2 && eqb_Tree r1 r2
  | _, _ => false
  end.

Definition rightL : Lens Tree Tree Tree :=
  {| get t := getRight t
  ;  put r t :=
      match t with
      | Leaf => None
      | Node l n _ => Some (r, Node l n r, fun t' => eqb_option eqb_Tree (Some r) (getRight t'))
      end
  |}.

Fixpoint spineL (n : nat) : Lens Tree (list nat) (list nat) :=
  match n with
  | O => bind (comap (fun _ => Some None) rootL) (fun _ => ret nil)
  | S n =>
    bind (comap (fun xs => Some (head xs)) rootL) (fun hd =>
    match hd with
    | None => ret nil
    | Some h => bind (comap tail (cat rightL (spineL n))) (fun tl =>
                ret (h :: tl))
    end)
  end.
