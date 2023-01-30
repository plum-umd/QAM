Require Import Coq.Lists.ListSet.

(* *Syntax* *)
Definition var := nat.
Definition prob := nat.
Definition message := nat.
Definition channel := nat.
Definition repeater := nat.
Definition tau := nat. (* time *)

Inductive action : Type :=
| TSend (p: prob) (c: channel) (m: message)
| TRecv (c: channel) (x: var).
                                
Inductive process : Type :=
| TNil
| TAct (a: action) (p: process)
| TParal (p1: process) (p2: process).

Definition relation :=  list (repeater * repeater * prob).
Definition relation_update := tau -> relation -> relation.  

Inductive PCell : Type :=
|SingleP (p: process) (n: nat) (c: channel)
|MultiP (p: process) (n: nat) (c: channel) (plst: PCell).  

Inductive config : Type :=
| PRConfig : PCell -> relation -> config
| Config : PCell -> relation -> relation_update -> config.

Notation "p1 | p2" := (TParal p1 p2) (at level 50).



