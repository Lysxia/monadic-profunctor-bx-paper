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

From Profmonad Require Import
  Utils
  Profmonad.

Record Lens (S U A : Type) : Type := {
  get : S -> option A;
  put : U -> S -> option (A * S * (S -> bool));
}.

Arguments get {S U A}.
Arguments put {S U A}.

Definition bind_Lens {S U A B : Type}
           (m : Lens S U A) (k : A -> Lens S U B) : Lens S U B := {|
  get s := a <- get m s;; get (k a) s;
  put u s :=
    abc <- put m u s;;
    let '(a, s, p) := abc in
    def <- put (k a) u s;;
    let '(b, s, q) := def in
    ret (b, s, fun x => (p x && q x)%bool)
|}.

Definition ret_Lens {S U A : Type} (a : A) : Lens S U A := {|
  get _ := Some a;
  put _ s := Some (a, s, fun _ => true);
|}.

Definition Monad_Lens S U : Monad (Lens S U) := {|
  Profmonad.bind _ _ := bind_Lens;
  Profmonad.ret _ := ret_Lens;
|}.

Definition map1_triple {a a' b c} (f : a -> a') (x : a * b * c) : a' * b * c :=
  (f (fst (fst x)), snd (fst x), snd x).

Definition Profunctor_Lens S : Profunctor (Lens S) :=
  fun _ _ _ _ f g l =>
    {| get s := option_map g (get l s)
    ;  put x s := option_map (map1_triple g) (put l (f x) s)
    |}.

Definition PartialProfunctor_Lens S : PartialProfunctor (Lens S) := {|
  asProfunctor := Profunctor_Lens S
; toFailureP A B (l : Lens S A B) :=
    {| get s := get l s
    ;  put ox s := bind_option ox (fun x => put l x s)
    |}
|}.

Instance Profmonad_Lens S : Profmonad (Lens S).
Proof.
  constructor; eauto using Monad_Lens, PartialProfunctor_Lens.
Defined.

Definition anyb_option {A} (p : A -> bool) (ox : option A) : bool :=
  match ox with
  | None => false
  | Some x => p x
  end.

Definition cat {S T U} (l1 : Lens S T T) (l2 : Lens T U U) : Lens S U U :=
  {| get := fun s => bind_option (get l1 s) (get l2)
  ;  put := fun x s =>
        bind_option (get l1 s) (fun t =>
        bind_option (put l2 x t) (fun '(y, xt, q') =>
        bind_option (put l1 xt s) (fun '(_, s', p') =>
        Some (y, s', fun s_ => (p' s_ && anyb_option q' (get l1 s_))%bool))))
  |}.

Definition Key := nat.
Definition Val := nat.
Definition Map := (Key -> Val).

Definition insert (k : Key) (x : Val) (f : Map) : Map :=
  fun k' => if Nat.eqb k k' then x else f k'.

Definition atKey (k : Key) : Lens Map Val Val :=
  {| get f := Some (f k)
  ;  put x f := Some (x, insert k x f, fun f' => Nat.eqb (f' k) x)
  |}.

Fixpoint atKeys (ks : list Key) : Lens Map (list Val) (list Val) :=
  match ks with
  | nil => ret nil
  | k :: ks =>
    bind (comap head (atKey k)) (fun x =>
    bind (comap tail (atKeys ks)) (fun xs =>
    ret (x :: xs)))
  end.

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

(** Lists of bounded length *)
Fixpoint blist (n : nat) (A : Type) : Type :=
  match n with
  | O => unit
  | S n => option (A * blist n A)
  end.

Definition bnil {n : nat} {A : Type} : blist n A :=
  match n with
  | O => tt
  | S _ => None
  end.

Definition bcons {n : nat} {A : Type} (x : A) (xs : blist n A) : blist (S n) A :=
  Some (x, xs).

Delimit Scope blist_scope with blist.
Notation "[ x ; .. ; y ]" := (bcons x .. (bcons y bnil) ..) : blist_scope.

Definition bhead {n A} (xs : blist (S n) A) : option A :=
  match xs with
  | None => None
  | Some ys => Some (fst ys)
  end.

Definition btail {n A} (xs : blist (S n) A) : option (blist n A) :=
  match xs with
  | None => None
  | Some ys => Some (snd ys)
  end.

Fixpoint spineL (n : nat) : Lens Tree (blist n nat) (blist n nat) :=
  match n with
  | O => ret tt
  | S n =>
    bind (comap (fun xs => Some (bhead xs)) rootL) (fun hd =>
    match hd with
    | None => ret None
    | Some h => bind (comap btail (cat rightL (spineL n))) (fun tl =>
                ret (Some (h, tl)))
    end)
  end.

Definition t0 : Tree := Node (Node Leaf 0 Leaf) 1 (Node Leaf 2 Leaf).

Lemma example_0
 : map fst (put (spineL 3) [3; 4; 5]%blist t0)
 = Some ([3; 4; 5]%blist, Node (Node Leaf 0 Leaf) 3 (Node Leaf 4 (Node Leaf 5 Leaf))).
Proof. reflexivity. Qed.

(**)

Instance MonadLaws_Lens {S U} : MonadLaws (Lens S U).
Proof.
  constructor; cbn.
  - intros ? []; unfold bind_Lens; cbn.
    f_equal.
    + apply functional_extensionality; intros. exact (bind_ret (M := option) _ _).
    + do 2 (apply functional_extensionality; intros).
      destruct (put0 x x0) as [ [[] ?] | ]; cbn; f_equal.
      f_equal. apply functional_extensionality; intros ?. rewrite Bool.andb_true_r. reflexivity.
  - intros ? ? ? ?; unfold bind_Lens; cbn.
    destruct (k a); cbn; f_equal.
    do 2 (apply functional_extensionality; intros).
    destruct (put0 x x0) as [ [[] ?] | ]; cbn; f_equal.
  - intros; unfold bind_Lens; cbn. f_equal.
    + apply functional_extensionality; intros; exact (bind_bind (M := option) _ _ _ _ _ _).
    + do 2 (apply functional_extensionality; intros).
      destruct (put m x x0) as [ [[] ?] | ]; cbn; [ | reflexivity ].
      destruct (put (k a) x s) as [ [[] ?] | ]; cbn; [ | reflexivity ].
      destruct (put (h b0) x s0) as [ [[] ?] | ]; cbn; f_equal. f_equal.
      apply functional_extensionality; intros; rewrite Bool.andb_assoc. reflexivity.
Qed.

Instance ProfunctorLaws_Lens {S} : ProfunctorLaws (Lens S).
Proof.
  constructor; cbn.
  - intros; apply functional_extensionality; intros []; unfold dimap, Profunctor_Lens, id; cbn.
    f_equal.
    + apply functional_extensionality. intros; destruct (get0 _); reflexivity.
    + do 2 (apply functional_extensionality; intros).
      destruct (put0 _ _) as [ [[] ? ] | ]; reflexivity.
  - intros; apply functional_extensionality; intros []; unfold dimap, Profunctor_Lens, compose; cbn.
    f_equal.
    + apply functional_extensionality. intros; destruct (get0 _); reflexivity.
    + do 2 (apply functional_extensionality; intros).
      destruct (put0 _ _) as [ [[] ? ] | ]; reflexivity.
Qed.

Instance PartialProfunctorLaws_Lens {S} : PartialProfunctorLaws (Lens S).
Proof.
  constructor; cbn.
  - typeclasses eauto.
  - intros; unfold Profunctor_Lens; cbn.
    f_equal. do 2 (apply functional_extensionality; intros).
    destruct x; cbn; reflexivity.
Qed.

Instance comap_morphism_Lens {S U V : Type} (f : U -> V)
  : MonadMorphism  (M := Lens S V) (N := Lens S U)
      (fun A : Type => comap (fun u : U => Some (f u))).
Proof.
  constructor; cbn; unfold Profunctor_Lens; cbn.
  - intros; unfold ret_Lens; cbn. f_equal.
  - intros; unfold bind_Lens; cbn. f_equal.
    + apply functional_extensionality; intros.
      destruct get; cbn; reflexivity.
    + do 2 (apply functional_extensionality; intros).
      destruct put as [ [[] ? ] | ]; cbn; [ | reflexivity ].
      destruct put as [ [[] ? ] | ]; cbn; reflexivity.
Qed.

Lemma map_dimap_Lens {S U A B} (f : A -> B) (u : Lens S U A)
  : map f u = dimap id f u.
Proof.
  cbn. unfold bind_Lens, Profunctor_Lens. f_equal; apply functional_extensionality; intros ?.
  apply functional_extensionality; intros ?.
  cbn. destruct put as [ [ [] ] | ]; cbn; auto.
  unfold map1_triple; cbn. f_equal. f_equal.
  apply functional_extensionality; intros ?.
  apply Bool.andb_true_r.
Qed.

Instance ProfmonadLaws_Lens {S} : ProfmonadLaws (Lens S).
Proof.
  constructor; typeclasses eauto + apply @map_dimap_Lens.
Qed.

Definition backward {S A} (l : Lens S A A) : Prop :=
  forall a a' s s_ s' p,
    put l a s = Some (a', s_, p) ->
    p s' = true ->
    get l s' = Some a.

Definition weak_backward {S U A} (m : Lens S U A) : Prop :=
  forall u a s s_ s' p,
    put m u s = Some (a, s_, p) ->
    p s' = true ->
    get m s' = Some a.

Definition backward_on {S A} (P : A -> Prop) (l : Lens S A A) : Prop :=
  forall a a' s s_ s' p,
    P a ->
    put l a s = Some (a', s_, p) ->
    p s' = true ->
    get l s' = Some a.

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

Instance Compositional_weak_backward {S} : Compositional (@weak_backward S).
Proof.
  constructor; cbn.
  - typeclasses eauto.
  - red; cbn; intros. inversion H; auto.
  - apply @weak_backward_bind.
  - unfold weak_backward, Profunctor_Lens; cbn; intros.
    destruct (f u) eqn:Ef; cbn in H0; [ | discriminate ].
    destruct put as [ [[] ?] | ] eqn:Eput; unfold map1_triple in H0; cbn in H0; [ | discriminate].
    inversion H0; subst; clear H0.
    erewrite H; eauto; reflexivity.
Qed.

Definition forward {S A} (m : Lens S A A) : Prop :=
  forall a a' s s' p,
    get m s = Some a ->
    put m a s = Some (a', s', p) ->
    s = s'.

Definition forward_on {S A} (P : A -> Prop) (m : Lens S A A) : Prop :=
  forall a a' s s' p,
    P a ->
    get m s = Some a ->
    put m a s = Some (a', s', p) ->
    s = s'.

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

Instance Quasicompositional_weak_forward {S} : Quasicompositional (@weak_forward S).
Proof.
  constructor; cbn.
  - red; cbn; intros. inversion H0; auto.
  - exact (@weak_forward_bind S).
  - unfold weak_forward, Profunctor_Lens; cbn; intros.
    destruct (get m s) eqn:Hget; cbn in H0; inversion H0; subst; clear H0.
    destruct (f u) eqn:Hf; cbn in H1; [ | discriminate ].
    destruct put as [ [[] ?] | ] eqn:Hput; unfold map1_triple in H1; cbn in H1; [ | discriminate ].
    inversion H1; subst; clear H1.
    revert Hget Hput; apply H.
Qed.

Definition all_option {A} (P : A -> Prop) (ox : option A) : Prop :=
  match ox with
  | None => True
  | Some x => P x
  end.

Definition aligned_at {S A B} (l : Lens S A B) (a : A) (b : B) : Prop :=
  forall s,
    all_option (fun '(b', _, _) => b = b') (put l a s).

Lemma aligned_at_bind {S U A B} (m : Lens S U A) (k : A -> Lens S U B) (x : U) (b : B)
  : forall a, aligned_at m x a ->
    aligned_at (k a) x b -> aligned_at (bind m k) x b.
Proof.
  intros. unfold aligned_at; cbn; unfold bind_Lens; cbn.
  intros s; specialize (H s). subst.
  destruct (put m x s) as [ [[] ?] | ]; cbn in *; auto.
  { red in H0. specialize (H0 s0). subst.
    destruct put as [ [[] ?] | ]; cbn in H0 |- *; subst; auto.
  }
Qed.

Lemma aligned_at_ret {S A B} (a : A) (b : B)
  : aligned_at (S := S) (ret b) a b.
Proof.
  cbn; unfold aligned_at, ret_Lens; cbn. auto.
Qed.

Lemma aligned_at_comap {S U V A} (l : Lens S V A) (f : U -> option V) (u : U) (v : V) (a : A)
  : aligned_at l v a -> f u = Some v -> aligned_at (comap f l) u a.
Proof.
  unfold aligned_at. intros Hl Hf s. specialize (Hl s).
  cbn; rewrite Hf; cbn. destruct put as [ [[] ?] | ]; cbn in Hl |- *; auto.
Qed.

Lemma aligned_at_cat {S T U} (lt : Lens S T T) (lu : Lens T U U) (u : U)
  : aligned_at lu u u -> aligned_at (cat lt lu) u u.
Proof.
  unfold aligned_at; cbn.
  intros Hlu s.
  destruct get; cbn; [ | auto].
  specialize (Hlu t).
  destruct put as [ [[] ?] | ]; cbn; [ | auto].
  cbn in Hlu; subst.
  destruct put as [ [[] ?] | ]; cbn; [ | auto].
  auto.
Qed.

Definition aligned {S A} (l : Lens S A A) : Prop :=
  forall a s, exists s' p,
  put l a s = Some (a, s', p).

Lemma aligned_forward {S A} (l : Lens S A A)
  : aligned l -> weak_forward l -> forward l.
Proof.
  intros Hal Hwf; red; intros * Hget Hput.
  specialize (Hal a s).
  destruct Hal as [ ? [? ?] ].
  rewrite H in Hput; inversion Hput; subst; clear Hput.
  red in Hwf. specialize Hwf with (1 := Hget) (2 := H). auto.
Qed.

Definition weak_aligned {S A} (l : Lens S A A) : Prop :=
  forall a, aligned_at l a a.

Lemma weak_aligned_forward {S A} (l : Lens S A A)
  : weak_aligned l -> weak_forward l -> forward l.
Proof.
  intros Hal Hwf; red; intros * Hget Hput.
  specialize (Hal a s). rewrite Hput in Hal; cbn in Hal; subst.
  red in Hwf. specialize Hwf with (1 := Hget) (2 := Hput). auto.
Qed.

Lemma weak_aligned_backward {S A} (l : Lens S A A)
  : weak_aligned l -> weak_backward l -> backward l.
Proof.
  intros Hal Hwb; red; intros * Hput Hp.
  specialize (Hal a s). rewrite Hput in Hal; cbn in Hal; subst.
  red in Hwb. specialize Hwb with (1 := Hput) (2 := Hp). auto.
Qed.

Lemma weak_aligned_forward_on {S A} (P : A -> Prop) (l : Lens S A A)
  : (forall a, P a -> aligned_at l a a) -> weak_forward l -> forward_on P l.
Proof.
  intros Hal Hwf; red; intros * HP Hget Hput.
  specialize (Hal a HP s). rewrite Hput in Hal; cbn in Hal; subst.
  red in Hwf. specialize Hwf with (1 := Hget) (2 := Hput). auto.
Qed.

Lemma weak_aligned_backward_on {S A} (P : A -> Prop) (l : Lens S A A)
  : (forall a, P a -> aligned_at l a a) -> weak_backward l -> backward_on P l.
Proof.
  intros Hal Hwb; red; intros * HP Hput Hp.
  specialize (Hal a HP s). rewrite Hput in Hal; cbn in Hal; subst.
  red in Hwb. specialize Hwb with (1 := Hput) (2 := Hp). auto.
Qed.

(** [atKeys] *)

Lemma weak_backward_atKey k : weak_backward (atKey k).
Proof.
  unfold weak_backward; cbn; intros.
  inversion H; subst; clear H.
  f_equal.
  apply Nat.eqb_eq. auto.
Qed.

Lemma weak_backward_atKeys ks : weak_backward (atKeys ks).
Proof.
  induction ks; cbn [atKeys].
  - apply ret_comp.
  - apply bind_comp. { apply comap_comp, weak_backward_atKey. }
    intros; apply bind_comp. { apply comap_comp; auto. }
    intros; apply ret_comp.
Qed.

Lemma weak_forward_atKey k : weak_forward (atKey k).
Proof.
  unfold weak_forward; cbn; intros.
  inversion H; subst; clear H.
  inversion H0; subst; clear H0.
  apply functional_extensionality.
  intros x; unfold insert. destruct (Nat.eqb_spec k x); subst; auto.
Qed.

Lemma weak_forward_atKeys ks : weak_forward (atKeys ks).
Proof.
  induction ks; cbn [atKeys].
  - apply ret_comp'.
  - apply bind_comp' with (f := head).
    { intros; rewrite 2 bind_bind. apply bind_cong; [ reflexivity | ].
      intros; rewrite 2 ret_bind. reflexivity. }
    { apply comap_comp', weak_forward_atKey. }
    intros.  apply bind_comp' with (f := tail).
    { intros; rewrite 2 ret_bind; reflexivity. }
    { apply comap_comp', IHks. }
    intros; apply ret_comp'.
Qed.

Lemma weak_aligned_atKey k : weak_aligned (atKey k).
Proof.
  unfold weak_aligned, aligned_at, atKey; cbn; auto.
Qed.

Lemma aligned_at_atKeys ks xs : length ks = length xs -> aligned_at (atKeys ks) xs xs.
Proof.
  revert xs; induction ks; destruct xs; cbn [length atKeys]; intros Hlen; inversion Hlen.
  - apply aligned_at_ret.
  - eapply aligned_at_bind.
    { eapply aligned_at_comap; [ | reflexivity ]. apply weak_aligned_atKey. }
    eapply aligned_at_bind.
    { eapply aligned_at_comap; [ | reflexivity ]. eauto. }
    apply aligned_at_ret.
Qed.

Lemma forward_on_atKeys ks : forward_on (fun xs => length ks = length xs) (atKeys ks).
Proof.
  apply weak_aligned_forward_on.
  - apply aligned_at_atKeys.
  - apply weak_forward_atKeys.
Qed.

Lemma backward_on_atKeys ks : backward_on (fun xs => length ks = length xs) (atKeys ks).
Proof.
  apply weak_aligned_backward_on.
  - apply aligned_at_atKeys.
  - apply weak_backward_atKeys.
Qed.

Lemma eqb_option_true x y : eqb_option Nat.eqb x y = true -> x = y.
Proof.
  destruct x, y; cbn; discriminate + reflexivity + idtac.
  intros H; apply Nat.eqb_eq in H; subst; reflexivity.
Qed.

Lemma weak_backward_rootL : weak_backward rootL.
Proof.
  unfold weak_backward; cbn [put get rootL].
  intros * H H0; inversion H; subst; clear H.
  apply eqb_option_true in H0; subst; auto.
Qed.

Lemma eqb_Tree_eq t t' : eqb_Tree t t' = true -> t = t'.
Proof.
  revert t'; induction t; destruct t'; cbn; try discriminate; auto.
  intros H; apply andb_prop in H. destruct H as [H H'].
  apply andb_prop in H; destruct H as [H0 H1].
  apply Nat.eqb_eq in H1.
  f_equal; auto.
Qed.

Lemma weak_backward_rightL : weak_backward rightL.
Proof.
  unfold weak_backward; cbn [put get rightL]; intros *.
  destruct s; [discriminate | ].
  intros H; inversion H; clear H; subst.
  destruct getRight; [ | discriminate ].
  intros H; apply eqb_Tree_eq in H; f_equal; auto.
Qed.

Lemma weak_backward_cat {S T U} (u : Lens S T T) (v : Lens T U U)
  : weak_backward u -> weak_backward v -> weak_backward (cat u v).
Proof.
  intros Hu Hv; unfold weak_backward; cbn [cat put get]. intros * H1 H2.
  destruct get eqn:Hget in H1; [ | discriminate]; cbn in H1.
  destruct put as [ [ [] ? ] | ] eqn:Hput in H1; cbn in H1; [ | discriminate].
  destruct put as [ [ [] ? ] | ] eqn:Hput2 in H1; cbn in H1; [ | discriminate ].
  inversion H1; subst; clear H1.
  apply andb_prop in H2. destruct H2 as [H21 H22].
  red in Hu; specialize Hu with (1 := Hput2) (2 := H21). rewrite Hu in H22 |- *. cbn in H22 |- *.
  red in Hv; specialize Hv with (1 := Hput) (2 := H22).
  assumption.
Qed.

Lemma weak_forward_rootL : weak_forward rootL.
Proof.
  unfold weak_forward; cbn [put get rootL]. intros * H1 H2.
  inversion H1; inversion H2; subst; clear H1 H2.
  destruct s; reflexivity.
Qed.

Lemma weak_aligned_rootL : weak_aligned rootL.
Proof.
  red; intros ? []; cbn; auto.
Qed.

Lemma weak_forward_rightL : weak_forward rightL.
Proof.
  unfold weak_forward; cbn [put get rightL]. intros * H1 H2.
  destruct s; [ discriminate | ].
  cbn in H1, H2; inversion H1; inversion H2; subst; auto.
Qed.

Lemma weak_aligned_rightL : weak_aligned rightL.
Proof.
  red; intros ? []; cbn; auto.
Qed.

Lemma forward_rightL : forward rightL.
Proof.
  apply weak_aligned_forward.
  - apply weak_aligned_rightL.
  - apply weak_forward_rightL.
Qed.

Lemma weak_forward_cat {S T U} (u : Lens S T T) (v : Lens T U U)
  : forward u -> weak_forward v -> weak_forward (cat u v).
Proof.
  intros Hu Hv; unfold weak_forward; cbn [cat put get]. intros * H1 H2.
  destruct (get u s) eqn:Hget in H1, H2; [ | discriminate ]; cbn in H1, H2.
  destruct put as [ [ [] ? ] | ] eqn:Hput in H2; [ | discriminate]; cbn in H2.
  destruct put as [ [ [] ? ] | ] eqn:Hput2 in H2; [ | discriminate]; cbn in H2.
  inversion H2; subst; clear H2.
  red in Hv; specialize Hv with (1 := H1) (2 := Hput); subst.
  red in Hu; specialize Hu with (1 := Hget) (2 := Hput2). auto.
Qed.

Lemma weak_backward_spineL n : weak_backward (spineL n).
Proof.
  induction n; cbn [spineL].
  - red; cbn; congruence.
  - apply bind_comp.
    { apply comap_comp, weak_backward_rootL. }
    { intros [].
      + apply bind_comp.
        { apply comap_comp, weak_backward_cat.
          * apply weak_backward_rightL.
          * apply IHn. }
        { intros; apply ret_comp. }
      + apply ret_comp. }
Qed.

Lemma weak_forward_spineL n : weak_forward (spineL n).
Proof.
  induction n; cbn [spineL].
  - red; cbn. congruence.
  - apply bind_comap_comp'.
    { intros []; cbn delta.
      rewrite 2 bind_bind.
      f_equal.
      rewrite 2 ret_bind; reflexivity. }
    { apply weak_forward_rootL. }
    { intros [].
      + apply bind_comap_comp'.
        { intros; rewrite 2 ret_bind; reflexivity. }
        { apply weak_forward_cat.
          * apply forward_rightL.
          * apply IHn. }
        { intros; apply ret_comp'. }
      + apply ret_comp'. }
Qed.

Lemma weak_aligned_spineL n : weak_aligned (spineL n).
Proof.
  red; induction n; cbn [spineL]; intros xs.
  - destruct xs. apply aligned_at_ret.
  - apply aligned_at_bind with (a := bhead xs).
    { eapply aligned_at_comap; [ | reflexivity ]. apply weak_aligned_rootL. }
    destruct xs as [ [x xs'] | ] eqn:Hxs; cbn [bhead].
    + eapply aligned_at_bind.
      { eapply aligned_at_comap; [ | reflexivity ].
        apply aligned_at_cat. auto. }
      apply aligned_at_ret.
    + apply aligned_at_ret.
Qed.

Theorem forward_spineL n : forward (spineL n).
Proof.
  apply weak_aligned_forward.
  - apply weak_aligned_spineL.
  - apply weak_forward_spineL.
Qed.

Lemma backward_spineL n : backward (spineL n).
Proof.
  apply weak_aligned_backward.
  - apply weak_aligned_spineL.
  - apply weak_backward_spineL.
Qed.
