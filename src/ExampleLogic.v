From Coq Require Import Arith List Lia.
From Profmonad Require Import Utils Profmonad.
Import ListNotations.
Set Implicit Arguments.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

Definition GG m := Product (Fwd m) (Bwd option).

Definition mkGG {m u v} (fwd : m v) (bwd : u -> option v) : GG m u v := (fwd, bwd).
Definition generate {m u v} (p : GG m u v) : m v := fst p.
Definition check {m u v} (p : GG m u v) : u -> option v := snd p.
Definition toPredicate {m u v} (p : GG m u v) : u -> bool := fun x => isSome (check p x).
Definition mkAlignedGG {m v} (fwd : m v) (bwd : v -> bool) : GG m v v :=
  (fwd, fun x => if bwd x then Some x else None).

Class MonadPlus (m : Type -> Type) : Type :=
  { Monad_MonadPlus : Monad m
  ; mzero : forall {a}, m a
  ; mplus : forall {a}, m a -> m a -> m a
  }.
#[global] Existing Instance Monad_MonadPlus.

#[global] Instance MonadPlus_Bwd {m} `{MonadPlus m} {a} : MonadPlus (Bwd m a) :=
  { mzero := fun _ _ => mzero
  ; mplus := fun _ l r x => mplus (l x) (r x) }.

#[global]
Instance MonadPlus_list : MonadPlus list :=
  {| mzero := fun _ => nil
  ;  mplus := List.app
  |}.

Definition trueOrFalse {m} `{MonadPlus m} : GG m bool bool :=
  mkGG (mplus (ret true) (ret false)) (fun _ => Some true). (* TODO: shouldn't this be (fun x => Some x) *)

Definition from_singleton {a} (xs : list a) : option a :=
  match xs with
  | x :: nil => Some x
  | _ => None
  end.

Definition oneBool {m} `{MonadPlus m} : GG m (list bool) (list bool) :=
  b <-( from_singleton ?) trueOrFalse ;;
  ret (b :: nil).

Definition reject {m} `{MonadPlus m} {a} : GG m a a :=
  mkAlignedGG mzero (fun _ => false). (* TODO: in the paper this is MonadFail *)

Definition Pos : Type := (nat * nat).

Definition validPos : list Pos := list_prod (seq 0 8) (seq 0 8).

(* adiff n m = abs (n - m) *)
Fixpoint adiff (n m : nat) : nat :=
  match n, m with
  | O, m | m, O => m
  | S n, S m => adiff n m
  end.

Definition conflict (p q : Pos) : bool :=
  let '(x1, y1) := p in
  let '(x2, y2) := q in
  (x1 =? x2) || (y1 =? y2) || (adiff x1 x2 =? adiff y1 y2).

Definition choose {m} `{MonadPlus m} {a} (xs : list a) : m a :=
  List.fold_right (fun x y => mplus (ret x) y) mzero xs.

Definition isValidPos (x : Pos) : bool :=
  (fst x <? 8) && (snd x <? 8).

Definition safePlacing {m} `{MonadPlus m} (xs : list Pos) : GG m Pos Pos :=
  let noconflicts p := List.forallb (fun q => negb (conflict p q)) xs in
  mkAlignedGG (choose (filter noconflicts validPos)) (fun x => noconflicts x && isValidPos x)%bool.
(* TODO: update paper
   The isValidPos condition was added in the checker direction to satisfy completeness. *)

Fixpoint nQueens {m} `{MonadPlus m} (n : nat) : GG m (list Pos) (list Pos) :=
  if (8 <? n) then reject else
  match n with
  | O => ret nil
  | S n =>
    xs <-( tail ?) (nQueens n) ;;
    x  <-( head ?) (safePlacing xs) ;;
    ret (x :: xs)
  end.

Definition checkNQueens : list Pos -> bool := toPredicate (nQueens 8).
Definition generateNQueens : list (list Pos) := generate (nQueens 8).

(* Eval lazy in (head generateNQueens). *)
(*
= Some
         ((7, 3)
          :: (6, 1)
             :: (5, 6)
                :: (4, 2) :: (3, 5) :: (2, 7) :: (1, 4) :: (0, 0) :: nil)
     : option (list Pos)

----------
|x       |
|      x |
|    x   |
|       x|
| x      |
|   x    |
|     x  |
|  x     |
----------
*)

Definition checkOneSolution : option (list Pos) :=
  check (nQueens 8) [(2,7); (3,2); (6,1); (7,4); (4,6); (5,3); (1,5); (0,0)].
Eval lazy in checkOneSolution.

Definition State s a : Type := (s -> (s * a)).
Definition OptionT m a : Type := m (option a).

#[global]
Instance Monad_State {s} : Monad (State s) :=
  {| ret := fun _ x s => (s, x)
  ;  bind := fun _ _ u k s => let '(s, y) := u s in k y s
  |}.

#[global]
Instance Monad_OptionT {m} `{Monad m} : Monad (OptionT m) :=
  {| ret := fun _ x => ret (Some x)
  ;  bind := fun _ _ u k => bind (M := m) u (fun ox => match ox with Some x => k x | None => ret None end)
  |}.

Section RMonad.

Context (C : Type -> Type).

Class K a := k : C a.

Class RMonad (m : Type -> Type) : Type :=
  { rret : forall {a} {Ca : K a}, a -> m a
  ; rbind : forall {a b} {Ca : K a} {Cb : K b}, m a -> (a -> m b) -> m b
  }.

Class RProfunctor (p : Type -> Type -> Type) : Type :=
  { rdimap : forall {a a' b b'} {Cb : K b} {Cb' : K b'}, (a' -> a) -> (b -> b') -> p a b -> p a' b'
  }.

Class RPartialProfunctor (p : Type -> Type -> Type) : Type :=
  { asRProfunctor : RProfunctor p
  ; rtoFailureP : forall {a b} {Cb : K b}, p a b -> p (option a) b
  }.
#[global] Existing Instance asRProfunctor.

Class RProfmonad (p : Type -> Type -> Type) : Type :=
  { asRMonad : forall {a}, RMonad (p a)
  ; asRPartialProfunctor : RPartialProfunctor p
  }.
#[global] Existing Instance asRMonad.
#[global] Existing Instance asRPartialProfunctor.

Definition comap {P} `{!RPartialProfunctor P} {U V A : Type} {Ca : C A}
  (f : U -> option V) (u : P V A) : P U A :=
  rdimap (Cb := Ca) (Cb' := Ca) f (fun x => x) (rtoFailureP (Cb := Ca) u).

Class RMonadPlus (m : Type -> Type) : Type :=
  { RMonadPlusAsRMonad : RMonad m
  ; rmzero : forall {a}, m a
  }.
#[global] Existing Instance RMonadPlusAsRMonad.

End RMonad.

Declare Scope rmonad_scope.
Delimit Scope rmonad_scope with rmonad.

Notation "x <- m ;; k" := (rbind m (fun x => k))
(at level 90, right associativity) : rmonad_scope.
Infix ">>=" := rbind (at level 61, left associativity).

Notation "x <-( f ?) m ;; m2" := (x <- comap f m ;; m2)%rmonad
(at level 90, right associativity) : rmonad_scope.

Notation "x <- m 'upon' f ;; m2" := (x <- comap f m ;; m2)%rmonad
(at level 90, right associativity) : rmonad_scope.

Notation "x <-( f ) m ;; m2" :=
  (x <- comap (fun z => Some (f z)) m ;; m2)%rmonad
(at level 90, right associativity) : rmonad_scope.

Class CompareLaws {a} (compare : a -> a -> comparison) : Prop :=
  { CLreflexivity : forall x, compare x x = Eq
  ; CLstrictness : forall x y, compare x y = Eq -> x = y
  ; CLantisymmetry : forall x y, compare x y = CompOpp (compare y x)
  ; CLtransitivity : forall x y z, compare x y = Lt -> compare y z = Lt -> compare x z = Lt
  }.

Class Ord (a : Type) : Type :=
  { compare : a -> a -> comparison
  ; compareLaws : CompareLaws compare
  }.
#[global] Existing Instance compareLaws.

#[global] Instance K_Ord {a} {Ord_a : Ord a} : K Ord a := Ord_a.

Definition app_comparison (m n : comparison) : comparison :=
  match m with
  | Eq => n
  | Gt | Lt => m
  end.

Fixpoint compare_list {a} (compare : a -> a -> comparison) (xs ys : list a) : comparison :=
  match xs, ys with
  | [], _ :: _ => Lt
  | _ :: _, [] => Gt
  | [], [] => Eq
  | x :: xs, y :: ys => app_comparison (compare x y) (compare_list compare xs ys)
  end.

Lemma CompOpp_app_comparison {m n} : CompOpp (app_comparison m n) = app_comparison (CompOpp m) (CompOpp n).
Proof. destruct m; reflexivity. Qed.

Lemma app_comparison_Lt_r {m n p} : (n = Lt -> p = Lt) -> app_comparison m n = Lt -> app_comparison m p = Lt.
Proof. destruct m; auto. Qed.

#[local]
Instance CompareLaws_list {a} (compare : a -> a -> comparison) `{!CompareLaws compare}
  : CompareLaws (compare_list compare).
Proof.
  constructor.
  - intros xs; induction xs as [ | x xs IH]; [ reflexivity | cbn ].
    rewrite CLreflexivity, IH; reflexivity.
  - intros xs; induction xs as [ | x xs IH]; intros [ | y ys]; cbn; try reflexivity + discriminate.
    destruct (compare x y) eqn:Exy; cbn; try discriminate.
    apply CLstrictness in Exy. intros Exys; apply IH in Exys. f_equal; assumption.
  - intros xs; induction xs as [ | x xs IH]; intros [ | y ys]; cbn; try reflexivity + discriminate.
    rewrite CompOpp_app_comparison; f_equal; [ apply CLantisymmetry | apply IH ].
  - intros xs; induction xs as [ | x xs IH]; intros [ | y ys]; cbn; try discriminate;
    intros [ | z zs]; cbn; try reflexivity + discriminate.
    destruct (compare x y) eqn:Exy; cbn; try discriminate.
    + apply CLstrictness in Exy; subst. intros Exys; apply app_comparison_Lt_r, IH, Exys.
    + intros _. destruct (compare y z) eqn:Eyz; cbn; try discriminate.
      { apply CLstrictness in Eyz; subst. rewrite Exy; reflexivity. }
      { rewrite (CLtransitivity _ _ _ Exy Eyz). reflexivity. }
Qed.

#[global]
Instance Ord_list {a} `{Ord a} : Ord (list a) := { compare := compare_list compare }.

Record set (a : Type) : Type := MkSet { set_to_list : list a }.

Definition empty_set {a} : set a := MkSet [].

Definition is_empty {a} (s : set a) : bool :=
  match set_to_list s with [] => true | _ :: _ => false end.

Definition size {a} (s : set a) : nat := length (set_to_list s).

Fixpoint init {a} (xs : list a) : list a :=
  match xs with
  | [] => []
  | _ :: [] => []
  | x :: xs => x :: init xs
  end.

Fixpoint last {a} (xs : list a) : option a :=
  match xs with
  | [] => None
  | x :: [] => Some x
  | _ :: xs => last xs
  end.

Definition headS {a} (s : set a) : option a := last (set_to_list s).

Definition tailS {a} (s : set a) : option (set a) := Some (MkSet (init (set_to_list s))).

Fixpoint insert_ {a} `{Ord a} (y : a) (xxs : list a) : list a :=
  match xxs with
  | x :: xs =>
    match compare x y with
    | Eq => xxs
    | Lt => x :: insert_ y xs
    | Gt => y :: xxs
    end
  | nil => y :: nil
  end.

Definition insert {a} `{Ord a} (y : a) (s : set a) : set a := MkSet (insert_ y (set_to_list s)).

Fixpoint remove_ {a} `{Ord a} (y : a) (xxs : list a) : list a :=
  match xxs with
  | x :: xs =>
    match compare x y with
    | Eq => xs
    | Lt => x :: remove_ y xs
    | Gt => xxs
    end
  | nil => nil
  end.

Definition remove {a} `{Ord a} (y : a) (s : set a) : set a := MkSet (remove_ y (set_to_list s)).

Definition eqb_comparison (m n : comparison) : bool :=
  match m, n with
  | Eq, Eq | Lt, Lt | Gt, Gt => true
  | _, _ => false
  end.

Definition ceqb {a} `{Ord a} (x y : a) : bool :=
  eqb_comparison Eq (compare x y).

Definition elem {a} `{Ord a} (x : a) (s : set a) : bool :=
  List.existsb (ceqb x) (set_to_list s).

Definition set_filter {a} (f : a -> bool) (s : set a) : set a :=
  MkSet (List.filter f (set_to_list s)).

Definition set_forallb {a} (f : a -> bool) (s : set a) : bool :=
  List.forallb f (set_to_list s).

Fixpoint merge {b} `{Ord b} (xs : list b) : list b -> list b :=
  fix merge_xs ys :=
    match xs, ys with
    | [], _ => ys
    | _, [] => xs
    | x :: xs', y :: ys' =>
      match compare x y with
      | Eq => x :: merge xs' ys'
      | Lt => x :: merge xs' ys
      | Gt => y :: merge_xs ys'
      end
    end.

Definition union {a} `{Ord a} (s s' : set a) : set a := MkSet (merge (set_to_list s) (set_to_list s')).

Fixpoint bind_set {a b} `{Ord b} (m : list a) (k : a -> list b) : list b :=
  match m with
  | [] => []
  | x :: xs => merge (k x) (bind_set xs k)
  end.

#[global]
Instance RMonad_set : RMonad Ord set :=
  { rret := fun _ _ x => MkSet (x :: [])
  ; rbind := fun _ _ _ (_ : Ord _) m k => MkSet (bind_set (set_to_list m) (fun x => set_to_list (k x)))
  }.

#[global]
Instance RMonadPlus_set : RMonadPlus Ord set :=
  { rmzero := fun _ => MkSet []
  }.

Definition compare_set {a} `{Ord a} (x y : set a) : comparison :=
  compare (set_to_list x) (set_to_list y).

#[local] Instance CompareLaws_set {a} `{Ord a} : CompareLaws compare_set.
Proof.
  constructor; repeat match goal with [ |- forall (H : set _), _ ] => intros [] end; cbn.
  - apply CLreflexivity.
  - intros HH; f_equal; apply (CLstrictness HH).
  - apply CLantisymmetry.
  - apply CLtransitivity.
Qed.

#[global] Instance Ord_set {a} `{Ord a} : Ord (set a) := { compare := compare_set }.

Module GGR.

Definition GGR m := Product (Fwd m) (Bwd (OptionT (State bool))).

#[global] Instance RMonad_Fwd {C} {m} `{RMonad C m} {a} : RMonad C (Fwd m a) := _.
#[global] Instance RMonad_Monad {C} {m} `{Monad m} : RMonad C m :=
  { rret := fun _ _ => ret
  ; rbind := fun _ _ _ _ => bind
  }.
#[global] Instance RMonad_Product {C} {p q} {a} {RMonad_p : RMonad C (p a)} {RMonad_q : RMonad C (q a)} : RMonad C (Product p q a) :=
  { rret := fun _ Ca x => (rret (Ca := Ca) x, rret (Ca := Ca) x)
  ; rbind := fun _ _ Ca Cb m k =>
     ( rbind (Ca := Ca) (Cb := Cb) (fst m) (fun x => fst (k x))
     , rbind (Ca := Ca) (Cb := Cb) (snd m) (fun x => snd (k x)) ) }.

#[global] Instance MonadPlus_OptionT {m} `{Monad m} : MonadPlus (OptionT m) :=
  { mzero := fun _ => ret None
  ; mplus := fun _ l r => bind (M := m) l (fun x =>
      match x with None => r | Some x => ret x end)
  }.

#[global] Instance RMonadPlus_Fwd {C} {m} `{RMonadPlus C m} {a} : RMonadPlus C (Fwd m a) :=
  { rmzero := fun _ => rmzero }.
#[global] Instance RMonadPlus_MonadPlus {C} {m} `{MonadPlus m} : RMonadPlus C m :=
  { rmzero := fun _ => mzero }.
#[global] Instance RMonad_Bwd {C} {m} `{RMonad C m} {a} : RMonad C (Bwd m a) :=
  { rret := fun _ _ x _ => rret x
  ; rbind := fun _ _ _ _ m k y => rbind (m y) (fun x => k x y) }.
#[global] Instance RMonadPlus_Bwd {C} {m} `{RMonadPlus C m} {a} : RMonadPlus C (Bwd m a) :=
  { rmzero := fun _ _ => rmzero }.
#[global] Instance RMonadPlus_Product {C} {p q} {a}
  {RMonadPlus_p : RMonadPlus C (p a)} {RMonadPlus_q : RMonadPlus C (q a)} : RMonadPlus C (Product p q a) :=
  { rmzero := fun _ => (rmzero, rmzero) }.

#[global] Instance RMonadPlus_GGR {C} {m} `{RMonadPlus C m} {a} : RMonadPlus C (GGR m a) := _.

#[global] Instance RProfunctor_Product {C} {p q}
  {RProfunctor1 : RProfunctor C p} {RProfunctor2 : RProfunctor C q} : RProfunctor C (Product p q) :=
  { rdimap := fun _ _ _ _ _ _ f g x => (rdimap f g (fst x), rdimap f g (snd x)) } .

#[global] Instance RPartialProfunctor_Product {C} {p q}
  {RPartialProfunctor1 : RPartialProfunctor C p} {RPartialProfunctor2 : RPartialProfunctor C q} : RPartialProfunctor C (Product p q) :=
  { rtoFailureP := fun _ _ _ x => (rtoFailureP (fst x), rtoFailureP (snd x)) }.

#[global] Instance RProfunctor_Fwd {C} {m} `{RMonad C m} : RProfunctor C (Fwd m) :=
  { rdimap := fun _ _ _ _ _ _ f g x => rbind x (fun x => rret (g x)) }.

#[global] Instance RPartialProfunctor_Fwd {C} {m} `{RMonadPlus C m} : RPartialProfunctor C (Fwd m) :=
  { rtoFailureP := fun _ _ _ x => x }.

#[global] Instance RProfmonad_Fwd {C} {m} `{RMonadPlus C m} : RProfmonad C (Fwd m) := {}.

#[global] Instance RProfunctor_Bwd {C} {m} `{RMonad C m} : RProfunctor C (Bwd m) :=
  { rdimap := fun _ _ _ _ _ _ f g x y => rbind (x (f y)) (fun x => rret (g x)) }.

#[global] Instance RPartialProfunctor_Bwd {C} {m} `{RMonadPlus C m} : RPartialProfunctor C (Bwd m) :=
  { rtoFailureP := fun _ _ _ m x => match x with None => rmzero | Some x => m x end }.

#[global] Instance RProfmonad_Bwd {C} {m} `{RMonadPlus C m} : RProfmonad C (Bwd m) := {}.

#[global] Instance RProfmonad_Product {C} {p q}
  {RProfmonad1 : RProfmonad C p} {RProfmonad2 : RProfmonad C q} : RProfmonad C (Product p q) := {}.

#[global] Instance RProfmonad_GGR {C} {m} `{RMonadPlus C m} : RProfmonad C (GGR m) := _.

Definition mkIrrecoverable {m} {v} (gen : m v) (chk : v -> bool) : GGR m v v :=
  (gen, fun y => if chk y then ret (M := OptionT (State bool)) y else fun s => (s, None)).

Definition mkRecoverable {m} {v} (gen : m v) (chk : v -> bool) : GGR m v v :=
  (gen, fun y => if chk y then fun _ => (true, Some y) else fun _ => (false, Some y)).

Definition reject {C} {m} `{RMonadPlus C m} {a} : GGR m a a :=
  mkIrrecoverable (rmzero (C := C)) (fun _ => false). (* TODO: in the paper this is MonadFail *)

Variant Actor : Type := Human | Fox | Chicken | Grain.
Variant Side : Type := L | R.

Definition Actor_eqb (x y : Actor) : bool :=
  match x, y with
  | Human, Human | Fox, Fox | Chicken, Chicken | Grain, Grain => true
  | _, _ => false
  end.

Definition compatible (x y : Actor) : bool :=
  match x, y with
  | Fox, Chicken
  | Chicken, Fox
  | Chicken, Grain
  | Grain, Chicken => false
  | _, _ => true
  end.

Definition row (x : Side) : Side := match x with L => R | R => L end.

Definition chars : set Actor := MkSet [Human; Fox; Chicken; Grain].

Definition compare_Actor (x y : Actor) : comparison :=
  match x, y with
  | Human, Human | Fox, Fox | Chicken, Chicken | Grain, Grain => Eq
  | Human, _ | Fox, (Chicken | Grain) | Chicken, Grain => Lt
  | Fox, Human | Chicken, (Human | Fox) | Grain, (Human | Fox | Chicken) => Gt
  end.

#[local]
Instance CompareLaws_Actor : CompareLaws compare_Actor.
Proof.
  constructor; repeat intros [ | | | ]; discriminate + reflexivity.
Qed.

#[global]
Instance Ord_Actor : Ord Actor := { compare := compare_Actor }.

Definition compat (xs : set Actor) : GGR set Actor Actor :=
  mkRecoverable (m := set)
    (if elem Human xs then set_filter (fun c => negb (elem c xs)) chars
     else set_filter (fun c => negb (elem c xs) && set_forallb (compatible c) xs)%bool chars)
    (fun c => (set_forallb (compatible c) xs || elem Human xs) && negb (elem c xs))%bool.

Definition Actor_leb (x y : Actor) : bool :=
  match x, y with
  | Human, _ => true
  | _, Grain => true
  | Fox, Human => false
  | Fox, (Fox | Chicken) => true
  | Grain, (Human | Fox | Chicken) => false
  | Chicken, (Human | Fox) => false
  | Chicken, Chicken => true
  end.

#[global]
Instance MonadPartial_OptionT {m} `{Monad m} : MonadPartial (OptionT m) :=
  {| empty := fun _ => ret None |}.

Fixpoint safeSide (n : nat) : GGR set (set Actor) (set Actor) :=
  if 4 <? n then reject (C := Ord) else
  match n with
  | O => rret empty_set
  | S n =>
    (* invariant: decreasing sorted list *)
    xs <-( tailS ?) (safeSide n) ;;
    x  <-( headS ?) (compat xs) ;;
    rret (insert x xs)
  end%rmonad.

Record PuzzleState : Type := MkPuzzleState
  { leftBank : set Actor
  ; boat : set Actor
  ; rightBank : set Actor
  ; boatLocation : Side
  }.

Infix "<>" := app_comparison.

Definition compare_Side (p q : Side) : comparison :=
  match p, q with
  | L, L | R, R => Eq | L, R => Lt | R, L => Gt
  end.

#[local] Instance CompareLaws_Side : CompareLaws compare_Side.
Proof.
  constructor; repeat intros [ | ]; discriminate + reflexivity.
Qed.

#[global] Instance Ord_Side : Ord Side := { compare := compare_Side }.

Definition compare_PuzzleState (p q : PuzzleState) : comparison :=
  compare (leftBank p) (leftBank q) <> (compare (boat p) (boat q) <> (compare (rightBank p) (rightBank q) <> compare (boatLocation p) (boatLocation q))).

Lemma app_comparison_reflexivity {x y} : x = Eq -> y = Eq -> (x <> y) = Eq.
Proof.
  intros -> ->; reflexivity.
Qed.

Lemma app_comparison_strictness {x y} : (x <> y) = Eq -> x = Eq /\ y = Eq.
Proof. destruct x; discriminate + constructor; reflexivity + assumption. Qed.

Lemma app_comparison_transitivity {A} {compare : A -> A -> comparison}
    `{!CompareLaws compare} {x y z n m p}
  : (m = Lt -> n = Lt -> p = Lt) ->
    (compare x y <> m) = Lt -> (compare y z <> n) = Lt -> (compare x z <> p) = Lt.
Proof.
  destruct compare eqn:Exy; [ apply CLstrictness in Exy; subst | | discriminate ].
  - destruct compare; [ | | discriminate]; cbn; auto.
  - destruct (compare y z) eqn:Eyz; [ apply CLstrictness in Eyz; subst | | discriminate ].
    + rewrite Exy; auto.
    + rewrite (CLtransitivity _ _ _ Exy Eyz). reflexivity.
Qed.

#[local] Instance CompareLaws_PuzzleState : CompareLaws compare_PuzzleState.
Proof.
  constructor; unfold compare_PuzzleState.
  - intros []; cbn. repeat apply app_comparison_reflexivity; apply CLreflexivity.
  - intros [] []; cbn. intros H.
    do 3 (apply app_comparison_strictness in H; destruct H as [? H]).
    f_equal; apply CLstrictness; assumption.
  - intros [] []; cbn. rewrite !CompOpp_app_comparison; repeat f_equal; apply CLantisymmetry.
  - intros [] [] []; cbn.
    repeat apply app_comparison_transitivity; apply CLtransitivity.
Qed.

#[global] Instance Ord_PuzzleState : Ord PuzzleState := {}.

Definition fromSet {a} `{Ord a} (s : set a) : GGR set a a :=
  mkIrrecoverable s (fun x => elem x s).

Definition validState (s : PuzzleState) : bool :=
  (size (leftBank s) + size (rightBank s) + size (boat s) =? 4) &&
  (size (union (leftBank s) (union (rightBank s) (boat s))) =? 4) &&
  (size (boat s) <=? 2) &&
  (is_empty (boat s) || elem Human (boat s)).

Notation "f '$' x" := (f x)
  (right associativity, at level 100, only parsing).

Definition modify_boatLocation (f : Side -> Side) (p : PuzzleState) :=
  match p with
  | MkPuzzleState l b r s => MkPuzzleState l b r (f s)
  end.

Definition set_boat (b : set _) (p : PuzzleState) :=
  match p with
  | MkPuzzleState l _ r s => MkPuzzleState l b r s
  end.

Definition set_leftBank (l : set _) (p : PuzzleState) :=
  match p with
  | MkPuzzleState _ b r s => MkPuzzleState l b r s
  end.

Definition set_rightBank (r : set _) (p : PuzzleState) :=
  match p with
  | MkPuzzleState l b _ s => MkPuzzleState l b r s
  end.

Definition singleton {a} `{Ord a} (x : a) : set a := insert x empty_set.

#[local] Open Scope bool_scope.

Definition reachableStates (p : PuzzleState) : set PuzzleState :=
  let insertValid (b : bool) x s := if (b && validState x)%bool then insert x s else s in
  let human_on_boat := negb (is_empty (boat p)) in
  (* row *)
  insertValid human_on_boat (modify_boatLocation row p) $
  (* unload *)
  insertValid (ceqb L (boatLocation p) && human_on_boat)
    (set_boat empty_set $ set_leftBank (union (boat p) (leftBank p)) p) $
  insertValid (ceqb R (boatLocation p) && human_on_boat)
    (set_boat empty_set $ set_rightBank (union (boat p) (rightBank p)) p) $
  (* move cargo on boat *)
  let loadL s x := insertValid (ceqb L (boatLocation p) && elem Human (leftBank p))
    (set_boat (insert Human (insert x empty_set)) $ set_leftBank (remove Human (remove x (leftBank p))) p) s in
  fold_left loadL (set_to_list (leftBank p)) $
  let loadR s x :=  insertValid (ceqb R (boatLocation p) && elem Human (rightBank p))
    (set_boat (insert Human (insert x empty_set)) $ set_rightBank (remove Human (remove x (rightBank p))) p) s in
  fold_left loadR (set_to_list (rightBank p)) $
  empty_set.

Definition startState : PuzzleState := MkPuzzleState chars empty_set empty_set L.
Definition endState : PuzzleState := MkPuzzleState empty_set empty_set chars R.
Definition complete := ceqb endState.

(* Compute (reachableStates startState). *)
(* Compute (rbind (rbind (reachableStates startState) reachableStates) reachableStates). *)
Lemma ttt : size (rbind (rbind (reachableStates startState) reachableStates) reachableStates) = 8.
Proof. reflexivity. Qed.

Definition ultimateSuccess {a} (xs : GGR set a a) (x : a) : bool :=
  let (ok, res) := snd xs x true in ok && isSome res.

Definition isSafeSide (xs : set Actor) : bool :=
  ultimateSuccess (safeSide (size xs)) xs.

Definition safeState (current : PuzzleState) : GGR set PuzzleState PuzzleState :=
  let is_safe s := isSafeSide (leftBank s) && isSafeSide (rightBank s) in
  fromSet (set_filter is_safe (reachableStates current)).

Definition genSafeState s := fst (safeState s).

(* Compute genSafeState startState >>= genSafeState >>= genSafeState. *)

Fixpoint riverCrossing' (n : nat) (visited : set PuzzleState) (s : PuzzleState)
  : GGR set (list PuzzleState) (list PuzzleState) :=
  match n with
  | O => rmzero
  | S n =>
    x <-( head ?) (safeState s) ;;
    if complete x then rret [x]
    else if elem x visited then rmzero
    else xs <-( tail ?) riverCrossing' n (insert x visited) x ;; rret (x :: xs)
  end%rmonad.

Definition riverCrossing : GGR set (list PuzzleState) (list PuzzleState) :=
  riverCrossing' 30 (insert startState empty_set) startState.

(* Compute fst riverCrossing. *)

End GGR.


(** * Proofs *)

#[global] Instance MonadLaws_option : MonadLaws option.
Proof.
  constructor.
  - intros ? []; reflexivity.
  - reflexivity.
  - intros ? ? ? [] ? ?; reflexivity.
Qed.

#[global] Instance MonadPartialLaws_option : MonadPartialLaws (M := option) _.
Proof.
  constructor.
  - typeclasses eauto.
  - reflexivity.
Qed.

(** ** n-Queens *)

(** Completeness: if it is accepted by the predicate, it may be generated *)
Definition complete : forall A B, GG list A B -> Prop :=
  fun _ _ gg =>
    forall a b, check gg a = Some b -> List.In b (generate gg).

#[global] Instance ProfmonadLaws_GG : ProfmonadLaws (GG list).
Proof. typeclasses eauto. Qed.

#[global] Instance Compositional_complete : Compositional (P := GG list) (@complete).
Proof.
  constructor.
  - typeclasses eauto.
  - intros. red. intros *; cbn. injection 1. left; auto.
  - unfold complete; cbn; intros.
    destruct (option_bind_inv_Some _ _ _ H1) as [a' H'].
    rewrite H' in H1; cbn in H1.
    apply H in H'. apply H0 in H1.
    apply in_flat_map.
    eexists; split; eauto.
  - unfold complete; cbn; intros. unfold Profunctor_pfunction in H0.
    destruct (option_map_inv_Some _ _ _ H0) as [a' H'].
    rewrite H' in H0; cbn in H0; injection H0; clear H0; intros <-.
    destruct (option_bind_inv_Some _ _ _ H') as [a'' H''].
    rewrite H'' in H'; cbn in H'.
    apply H in H'.
    apply in_flat_map.
    eexists; split; eauto. constructor; reflexivity.
Qed.

(* Soundness: if it can be generated, the predicate must accept it *)
Definition sound : forall A, GG list A A -> Prop :=
  fun _ gg =>
    forall a, List.In a (generate gg) -> check gg a = Some a.

#[global] Instance Idiomcompositional_sound : Idiomcompositional (P := GG list) (@sound).
Proof.
  constructor.
  - unfold sound; cbn. intros * [ <- | []]; constructor.
  - unfold sound; cbn. intros * H H1 H2 b H3.
    apply in_flat_map in H3; destruct H3 as [a [H3 H4]].
    apply in_flat_map in H3; destruct H3 as [a' [H3 H5]].
    destruct H5 as [ -> | []].
    apply H1 in H3. apply H2 in H4.
    unfold check in H3, H4.
    rewrite option_map_id.
    assert (Hf : f b = Some a).
    { specialize (H a). injection H; intros H5 _. apply (f_equal (fun f => f b)) in H5.
      rewrite H4 in H5; cbn in H5. injection H5; auto. }
    rewrite Hf; cbn. rewrite H3; cbn. auto.
Qed.

Lemma sound_reject : forall A, sound (reject (a := A)).
Proof. unfold sound; cbn. contradiction. Qed.

Lemma sound_mkAlignedGG {v} {p : list v} {q : v -> bool}
    (H : forall x, In x p -> q x = true)
  : sound (mkAlignedGG p q).
Proof.
  unfold sound; cbn. intros. rewrite H; auto.
Qed.

Lemma choose_id {A} (xs : list A) : choose xs = xs.
Proof.
  induction xs; cbn; [ reflexivity | ]. f_equal; auto.
Qed.

Lemma sound_validPos : forall x, In x validPos -> isValidPos x = true.
Proof.
  unfold validPos, isValidPos. intros [x y] H. cbn. apply in_prod_iff in H. destruct H as [H1 H2].
  apply in_seq in H1, H2.
  apply Bool.andb_true_iff. split; apply Nat.leb_le; lia.
Qed.

Lemma sound_safePlacing xs : sound (safePlacing xs).
Proof.
  apply sound_mkAlignedGG.
  intros x H; rewrite choose_id in H.
  apply filter_In in H. destruct H. apply Bool.andb_true_iff; split; auto using sound_validPos.
Qed.

Lemma sound_nQueens' : forall n, sound (nQueens n).
Proof.
  induction n as [ | n IH ].
  - unfold sound; cbn. intros _ [ <- | []]; reflexivity.
  - unfold nQueens; fold nQueens. destruct (Nat.ltb_spec0 8 (S n)) as [ Hltb | Hltb ].
    + apply @sound_reject.
    + apply bind_idiomcomp.
      { intros. rewrite 2 bind_bind. reflexivity. }
      { apply IH. }
      intros. apply bind_idiomcomp.
      { intros; cbn; reflexivity. }
      { apply sound_safePlacing. }
      intros. apply ret_idiomcomp.
Qed.

Lemma sound_sound : forall A (m : GG list A A), sound m -> forall x, List.In x (generate m) -> toPredicate m x = true.
Proof. intros * Hsound x Hx; apply Hsound in Hx. unfold toPredicate. rewrite Hx. reflexivity. Qed.

(** TODO: setting n := 8 makes Qed very slow. *)
Theorem sound_nQueens : forall n x, List.In x (generate (nQueens n)) -> toPredicate (nQueens n) x = true.
Proof.
  intros n; apply @sound_sound, sound_nQueens'.
Qed.

Definition aligned {m A} (P : A -> Prop) (m : GG m A A) : Prop :=
  forall x, P x -> forall y, check m x = Some y -> x = y.

Lemma aligned_reject : forall a (P : a -> Prop), aligned P (reject (a := a)).
Proof. red; discriminate. Qed.

Lemma aligned_bind : forall a b (P Q : _ -> Prop) (u : GG list a a) (k : a -> GG list b b) (f : b -> option a),
  (forall y, Q y -> exists x, f y = Some x /\ P x) ->
  aligned P u -> (forall x, P x -> aligned (fun y => f y = Some x /\ Q y) (k x)) -> aligned Q (bind (Profmonad.comap f u) k).
Proof.
  intros * Hf Hu Hk. red. cbn; intros y Hy y' Ey.
  specialize (Hf _ Hy). destruct Hf as [ x [ Ex Hx ] ]. rewrite Ex in Ey; cbn in Ey.
  destruct (snd u) eqn:Eu in Ey; [ cbn in Ey | discriminate ].
  apply Hu in Eu; auto; subst.
  apply Hk in Ey; auto; subst.
Qed.

Lemma aligned_mkAlignedGG {v} {P : v -> Prop} {p : list v} {q}
  : aligned P (mkAlignedGG p q).
Proof.
  unfold aligned; cbn. intros ? ? ? H; destruct q; [ injection H; auto | discriminate ].
Qed.

Lemma aligned_safePlacing : forall xs (P : _ -> Prop), aligned P (safePlacing xs).
Proof.
  intros. apply @aligned_mkAlignedGG.
Qed.

Lemma aligned_nQueens : forall n, aligned (fun xs => List.length xs = n) (nQueens n).
Proof.
  induction n as [ | n IH ].
  - red; cbn. intros []; [ | discriminate ].
    intros _ ?; injection 1; auto.
  - cbn [nQueens]. destruct (Nat.ltb_spec0 8 (S n)) as [ Hltb | Hltb ].
    + apply @aligned_reject.
    + eapply @aligned_bind; [ | apply IH | ].
      { intros [ | ? tl ]; [ discriminate | injection 1; intros ]. exists tl. split; auto. }
      intros. eapply @aligned_bind; [ | apply (@aligned_safePlacing _ (fun _ => True)) | ].
      { intros [ | ? tl ]; cbn; intros [HH1 HH2]; [discriminate | ].
        injection HH1; injection HH2; clear HH1 HH2; intros; subst.
        exists p; eauto. }
      intros. red; cbn. intros [] [? [? ?]]; [ discriminate | ].
      injection H1; injection H2; intros [] []. intros ?; injection 1; auto.
Qed.

Lemma complete_reject {A} : complete (reject (a := A)).
Proof.
  unfold complete; cbn. discriminate.
Qed.

Lemma complete_mkAlignedGG {v} {p : list v} {q : v -> bool}
  : (forall x, q x = true -> In x p) -> complete (mkAlignedGG p q).
Proof.
  intros H; unfold complete; cbn; intros.
  destruct (q a) eqn:Eq; [ | discriminate ].
  injection H0; intros []. auto.
Qed.

Lemma complete_validPos : forall x, isValidPos x = true -> In x validPos.
Proof.
  unfold isValidPos; intros [x y] H. cbn in H.
  apply Bool.andb_true_iff in H; destruct H as [H1 H2].
  apply Nat.leb_le in H1, H2.
  unfold validPos.
  apply in_prod; apply in_seq; cbn; lia.
Qed.

Lemma complete_safePlacing xs : complete (safePlacing xs).
Proof.
  apply complete_mkAlignedGG; intros x H.
  rewrite choose_id.
  apply filter_In.
  apply Bool.andb_true_iff in H; destruct H as [H1 H2].
  split; auto using complete_validPos.
Qed.

Lemma complete_nQueens' : forall n, complete (nQueens n).
Proof.
  induction n as [ | n IH ].
  - unfold complete; cbn. intros _ ?; cbn; injection 1; auto.
  - cbn [nQueens]. destruct (Nat.ltb_spec0 8 (S n)) as [ Hltb | Hltb ].
    + apply @complete_reject.
    + apply bind_comp.
      { apply comap_comp, IH. }
      intros. apply bind_comp. 
      { apply comap_comp, complete_safePlacing. }
      intros; apply ret_comp.
Qed.

Lemma complete_complete : forall A (P : A -> Prop) (m : GG list A A), aligned P m -> complete m -> forall x, P x -> toPredicate m x = true -> List.In x (generate m).
Proof.
  intros * Haligned Hcomplete x HPx Hx. unfold toPredicate in Hx.
  destruct check eqn:Echeck in Hx; [ | discriminate ].
  destruct (Haligned _ HPx _ Echeck).
  revert Echeck; apply Hcomplete.
Qed.

Theorem complete_nQueens : forall n xs, length xs = n -> toPredicate (nQueens n) xs = true -> List.In xs (generate (nQueens n)).
Proof.
  intros n; apply complete_complete.
  - apply @aligned_nQueens.
  - apply complete_nQueens'.
Qed.
