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

Module GGR.

Definition GGR m := Product (Fwd m) (Bwd (OptionT (State bool))).

Definition mkIrrecoverable {m} `{Monad m} {v} (gen : m v) (chk : v -> bool) : GGR m v v :=
  (gen, fun y => if chk y then ret (M := OptionT (State bool)) y else fun s => (s, None)).

Definition mkRecoverable {m} `{Monad m} {v} (gen : m v) (chk : v -> bool) : GGR m v v :=
  (gen, fun y => if chk y then fun _ => (true, Some y) else fun _ => (false, Some y)).

Definition reject {m} `{MonadPlus m} {a} : GGR m a a :=
  mkIrrecoverable mzero (fun _ => false). (* TODO: in the paper this is MonadFail *)

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

Definition chars : list Actor := [Human; Chicken; Fox; Grain].

Definition Actor_elem (x : Actor) (xs : list Actor) : bool :=
  List.existsb (Actor_eqb x) xs.

Definition compat (xs : list Actor) : GGR list Actor Actor :=
  mkRecoverable
    (if Actor_elem Human xs then filter (fun c => negb (Actor_elem c xs)) chars
     else filter (fun c => negb (Actor_elem c xs) && List.forallb (compatible c) xs)%bool chars)
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

Fixpoint safeSide (n : nat) : GGR list (list Actor) (list Actor) :=
  if 4 <? n then reject else
  match n with
  | O => ret nil
  | S n =>
    (* invariant: decreasing sorted list *)
    xs <-( tail ?) (safeSide n) ;;
    x  <-( head ?) (compat xs) ;;
    ret (insert x xs)
  end.


