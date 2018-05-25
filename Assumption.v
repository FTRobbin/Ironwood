(* Axioms and assumptions *)

Axiom fun_eqiv : forall {A: Type} {B: Type} (f : A -> B) (g : A -> B), (forall (x : A), f x = g x) -> f = g.
