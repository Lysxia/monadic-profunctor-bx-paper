From Coq Require Import List.
Import ListNotations.

(*** Common functions ***)

Definition compose {A B C : Type} (f : B -> C) (g : A -> B) : A -> C := fun x => f (g x).
Notation "f ∘ g" := (compose f g) (at level 20, right associativity).

Definition head A (xs : list A) : option A :=
  match xs with
  | [] => None
  | x :: _ => Some x
  end.

Definition tail A (xs : list A) : option (list A) :=
  match xs with
  | [] => None
  | _ :: xs' => Some xs'
  end.

Arguments head {A}.
Arguments tail {A}.

(** * The option monad *)

Definition bind_option {A B} (m : option A) (k : A -> option B) :=
  match m with
  | None => None
  | Some x => k x
  end.

Delimit Scope opt_scope with opt.
Bind Scope opt_scope with option.

Notation "x <- m ;; k" := (bind_option m (fun x => k))
(at level 90, right associativity) : opt_scope.

Lemma option_bind_inv_Some {A B} (u : option A) (k : A -> option B) (b : B)
  : bind_option u k = Some b -> exists a, u = Some a.
Proof.
  destruct u; discriminate + eauto.
Qed.

Lemma option_map_inv_Some {A B} (f : A -> B) (u : option A) (b : B)
  : option_map f u = Some b -> exists a, u = Some a.
Proof.
  destruct u; discriminate + eauto.
Qed.

(** Extend a total function to a partial one. *)
Definition total {A B} (f : A -> B) : A -> option B :=
  fun a => Some (f a).
