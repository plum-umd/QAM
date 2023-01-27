Require Import Coq.Lists.ListSet.

(* *Syntax* *)
Definition var := nat.
Definition prob := nat.
Definition message := nat.
Definition channel := nat.
Definition repeater := nat.

Inductive action : Type :=
| Tnil : action
| TSend : prob -> channel -> message -> action
| TRecv : channel -> message -> action.
                                

Inductive process : Type :=
| TNil : process
| TAct : action -> process -> process
| TParal : process -> process -> process.

Definition relation :=  list (repeater * repeater * prob).
Definition relation_update := nat -> relation. 

Inductive config : Type :=
| Config : list (process * repeater * nat) -> relation -> relation_update -> config.
.


