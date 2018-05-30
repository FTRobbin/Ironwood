(* Temporal logic, monotonicity and witness theorems *)

Require Import Program.

Class State {A : Type} (leq : A -> A -> Prop) (nxt : A -> A) :=
{
  reflex : forall s, leq s s;
  succ : forall s, leq s (nxt s);
  transit : forall s s' s'', leq s s' -> leq s' s'' -> leq s s''
}.

Definition Next {A : Type} `{State A} (p : A -> Prop) : A -> Prop :=
  fun s => p (nxt s).

Definition Until {A : Type} `{State A} (p : A -> Prop) (q : A -> Prop) : A -> Prop :=
  fun s => exists s'', (leq s s'' /\ q s'') /\ (forall s', leq s s' -> leq s' s'' -> p s').

Definition Always {A : Type} `{State A} (p : A -> Prop) : A -> Prop :=
  fun s => forall s', leq s s' -> p s'.

Definition Eventually {A : Type} `{State A} (p : A -> Prop) : A -> Prop :=
  fun s => exists s', leq s s' /\ p s'.