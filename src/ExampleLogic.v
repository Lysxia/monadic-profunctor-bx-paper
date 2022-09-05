From Coq Require Import Arith List.
From Profmonad Require Import Utils Profmonad.
Import ListNotations.
Set Implicit Arguments.
Set Contextual Implicit.

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

#[global]
Instance MonadPlus_list : MonadPlus list :=
  {| mzero := fun _ => nil
  ;  mplus := List.app
  |}.

Definition trueOrFalse {m} `{MonadPlus m} : GG m bool bool :=
  mkGG (mplus (ret true) (ret false)) (fun _ => Some true). (* TODO: shouldn't this be (fun x => Some x) *)

Definition singleton {a} (xs : list a) : option a :=
  match xs with
  | x :: nil => Some x
  | _ => None
  end.

Definition oneBool {m} `{MonadPlus m} : GG m (list bool) (list bool) :=
  b <-( singleton ?) trueOrFalse ;;
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

Definition safePlacing {m} `{MonadPlus m} (xs : list Pos) : GG m Pos Pos :=
  let noconflicts p := List.forallb (fun q => negb (conflict p q)) xs in
  mkAlignedGG (choose (filter noconflicts validPos)) noconflicts.

Fixpoint nQueens {m} `{MonadPlus m} (n : nat) : GG m (list Pos) (list Pos) :=
  if (8 <? n) then reject else
  match n with
  | O => ret nil
  | S n =>
    xs <-( tail ?) (nQueens n) ;;
    x  <-( head ?) (safePlacing xs) ;;
    ret (x :: xs)
  end.

Definition allSolutions : list (list Pos) := generate (nQueens 8).

(* Eval lazy in (head allSolutions). *)
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

Class RMonad (m : Type -> Type) : Type :=
  { rret : forall {a} {Ca : C a}, a -> m a
  ; rbind : forall {a b} {Ca : C a} {Cb : C b}, m a -> (a -> m b) -> m b
  }.

Class RProfunctor (p : Type -> Type -> Type) : Type :=
  { rdimap : forall {a a' b b'} {Cb : C b} {Cb' : C b'}, (a' -> a) -> (b -> b') -> p a b -> p a' b'
  }.

Class RPartialProfunctor (p : Type -> Type -> Type) : Type :=
  { asRProfunctor : RProfunctor p
  ; rtoFailureP : forall {a b} {Cb : C b}, p a b -> p (option a) b
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

Record set (a : Type) : Type := MkSet { unset : list a }.

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

Fixpoint bind_set {a b} `{Ord b} (m : list a) (k : a -> list b) : list b :=
  match m with
  | [] => []
  | x :: xs => merge (k x) (bind_set xs k)
  end.

#[global]
Instance RMonad_set : RMonad Ord set :=
  { rret := fun _ _ x => MkSet (x :: [])
  ; rbind := fun _ _ _ _ m k => MkSet (bind_set (unset m) (fun x => unset (k x)))
  }.

#[global]
Instance RMonadPlus_set : RMonadPlus Ord set :=
  { rmzero := fun _ => MkSet []
  }.

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

#[global] Instance RMonadPlus_GGR {C} {m} `{RMonadPlus C m} {a} : RMonadPlus C (GGR m a).
Admitted.

#[global] Instance RProfmonad_GGR {C} {m} `{RMonadPlus C m} : RProfmonad C (GGR m).
Admitted.

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

Definition chars : set Actor := MkSet [Human; Chicken; Fox; Grain].

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

Definition Actor_elem (x : Actor) (xs : list Actor) : bool :=
  List.existsb (Actor_eqb x) xs.

Definition filter_set {a} (f : a -> bool) (xs : set a) : set a :=
  MkSet (List.filter f (unset xs)).

Definition compat (xs : list Actor) : GGR set Actor Actor :=
  mkRecoverable (m := set)
    (if Actor_elem Human xs then filter_set (fun c => negb (Actor_elem c xs)) chars
     else filter_set (fun c => negb (Actor_elem c xs) && List.forallb (compatible c) xs)%bool chars)
    (fun c => (List.forallb (compatible c) xs || Actor_elem Human xs) && negb (Actor_elem c xs))%bool.

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

Fixpoint insert (y : Actor) (xxs : list Actor) : list Actor := 
  match xxs with
  | x :: xs => if Actor_eqb x y then xxs else if Actor_leb x y then x :: insert y xs else y :: xxs
  | nil => y :: nil
  end.

#[global]
Instance MonadPartial_OptionT {m} `{Monad m} : MonadPartial (OptionT m) :=
  {| empty := fun _ => ret None |}.

Fixpoint safeSide (n : nat) : GGR set (list Actor) (list Actor) :=
  if 4 <? n then reject (C := Ord) else
  match n with
  | O => rret nil
  | S n =>
    (* invariant: decreasing sorted list *)
    xs <-( tail ?) (safeSide n) ;;
    x  <-( head ?) (compat xs) ;;
    rret (insert x xs)
  end%rmonad.

End GGR.
