Require Import PeanoNat Permut Setoid.
Require Import List.
Import ListNotations.
(**** Untilities ****)

(* This file defines the syntax of Quantum Abstract Machine.
Var               x,y
Message Name      e
Quantum Channel   c,d
Classical Channel h_c, h_d
Channel           delta := c | h_c
Quantum Message   q := unit | e | c.miu | dagger_q
Classical Message iota := h_q 
Message           miu := q | iota
Contexts          phi := list (c)d.miu      
Action            A := c_down | c_up | h_c!iota_send | delta?(x)_recv 
                      | c encode miu | c!(x)_decode | q!miu(x)_encode | q!(x)_decode
                      | c?(x)_trans 
Process           R,T := 0 | AR | R+T | !R
Raw Membrane      M,N := {|bar_R|}
Membrane          P,Q := {|Bar_R|}phi | R{|Bar_T|}phi | P[(c)d.miu]Q
*)
(*********************************************)
(***      Syntax     ***)

Definition var := nat.

Definition mess_n : Type := nat. (* message name *)
Definition chan_n : Type := nat. (* channel name *)

Definition qchan : Type := chan_n.
Definition cchan : Type := chan_n.
(* Inductive channel:= QC (q : qchan) | CC (c : cchan). *)
Inductive qmess := Unit | Mess (m: mess_n) | ChanM (c: chan_m) | PartM (q: qmess)
with      chan_m := ChM (c: qchan) (mu: mess)
with      cmess := MeasureQ (q : qmess)
with      mess   := QtM (q: qmess) | CcM (i: cmess).

Inductive shareC := ShareC (c: chan_n) (m: chan_m).

Definition contexts  := list shareC.

Inductive action := CreatC (c: qchan) | QSwap (c: qchan) | CSend (cc: cchan) (cm: cmess)
               | CcRecv (cc: cchan) (x: var) | CqRecv (qc: qchan) (x: var)
               | LEncode (q: qmess) (mu: mess) (x: var) | LDecode (q: qmess) (x: var)
               | GEncode (c: qchan) (x: mess) | GDecode (c: qchan) (x: var)
               | Trans (c: qchan) (x: var).

Inductive process := Nil | AR (a: action) (r: process) | Choice (p: process) (r: process) | Rept (r: process).

Definition rmemb := list process.

Inductive memb := CtxM (r: rmemb) (phi: contexts) | ALock (r: process) (t: memb) | ActM (p: memb) (c: shareC) (Q: memb).

Definition config := list memb.



(***      Semantics   ***)
(** Free Channel **)
Fixpoint FC_con (cx: contexts) :=
  match cx with
  | [] => []
  | ((ShareC c (ChM d m)) :: t) => c :: d :: (FC_con t)
  end.

Fixpoint FC_qmess (q: qmess) :=
  match q with
  | Unit | Mess _ => []
  | ChanM (ChM c mu) => c :: (FC_mess mu)
  | PartM q => FC_qmess q
  end
with FC_mess (mu: mess) :=
  match mu with
  | CcM _ => []
  | QtM q => FC_qmess q
  end.

Definition FC_action (a: action) :=
       match a with
       | CreatC c | QSwap c | CqRecv c _ | GEncode c _ | GDecode c _ | Trans c _ => [c]
       | CSend _ _ | CcRecv _ _ => []
       | LEncode q m _ => (FC_qmess q) ++ (FC_mess m)
       | LDecode q _ => FC_qmess q
 
end.

Fixpoint FC_process (r: process) :=
  match r with
  | Nil => []
  | AR a p =>  (FC_process p) ++ (FC_action a)
  | Choice p q => (FC_process p) ++ (FC_process q)
  | Rept p => FC_process p
  end.

Definition FC_rmemb (rm: rmemb) := concat (map FC_process rm).

Fixpoint FC_memb (m: memb) :=
  match m with
  | CtxM r phi => (FC_rmemb r) ++ (FC_con phi)
  | ALock p t => (FC_process p) ++ (FC_memb t)
  | ActM p c q => (FC_memb p) ++ (FC_con [c]) ++ (FC_memb q)
  end.

(** Message Algebra **)
Fixpoint eq_qmess (q1: qmess) (q2: qmess) :=
  match q1, q2 with
  | Unit, Unit => true
  | Mess n1, Mess n2 => Nat.eqb n1 n2
  | ChanM (ChM c1 m1), ChanM (ChM c2 m2) => if Nat.eqb c1 c2 then eq_mess m1 m2 else false
  | PartM q1, PartM q2 => eq_qmess q1 q2
  | _ , _  => false
  end
with eq_cmess (c1: cmess) (c2: cmess) :=
       match c1, c2 with
       | MeasureQ q1, MeasureQ q2 => eq_qmess q1 q2
       end
with eq_mess (m1: mess) (m2: mess) :=
       match m1, m2 with
       | QtM q1, QtM q2 => eq_qmess q1 q2
       | CcM c1, CcM c2 => eq_cmess c1 c2
       | _, _ => false
      end.
                                                                      
Definition recover_mess m1 m2 :=
  match m1, m2 with
  | QtM q, QtM Unit => QtM q
  | QtM Unit, QtM q => QtM q
  | CcM (MeasureQ q1), QtM q2 => if eq_qmess q1 q2 then QtM q1 else QtM Unit 
  | QtM q1, CcM (MeasureQ q2) => if eq_qmess q1 q2 then QtM q1 else QtM Unit
  | _, _ => QtM Unit
  end.

(** Op Sem **)
Fixpoint replace_mess (p: process) (x: var) (m: mess) : process := p. (*TODO*)

Inductive process_sem : process -> rmemb -> Prop :=
| choose_l : forall p1 p2,  process_sem (Choice p1 p2) [p1]
| choose_r : forall p1 p2, process_sem (Choice p1 p2) [p2]
| mt : forall p1,  process_sem (Rept p1) [p1; p1]
| nt : forall p1,  process_sem (Rept p1) [Nil].

(*
Print action.
Print qmess.
Print memb.
 *)

Definition fresh (c: nat) := c. (*TODO*)

Inductive disjoint_union : list qchan -> list qchan -> Prop :=
| nil_case : disjoint_union nil nil
| cons_case : forall x l ls, ~ (In x ls) -> disjoint_union l ls -> disjoint_union (x :: l) ls.

Inductive qam_sem : config -> config -> (option mess) -> Prop :=
| mem_split : forall (p1: process) (p2: rmemb) (cf: config),
    qam_sem ((CtxM (p1 :: p2) [])::cf) ((CtxM [p1] []):: (CtxM p2 []) :: cf) None
| cohere : forall (d: qchan) (c : chan_n) (phi1: contexts) (phi2: contexts) (p: process) (q: process) (r1: rmemb) (r2: rmemb) (cf: config),
    not (In d ((FC_con phi1)++(FC_con phi2))) ->
    qam_sem ((CtxM ((AR (CreatC d) p)::r1) phi1)::(CtxM ((AR (CreatC d) q)::r2) phi2)::cf) ((CtxM (p::r1) ((ShareC (fresh c) (ChM d (QtM Unit)))::phi1))::(CtxM (q::r2) ((ShareC (fresh c) (ChM d (QtM Unit)))::phi2))::cf) None
| decohere : forall mb1 mb2 s cf,
    qam_sem ((ActM mb1 s mb2)::cf) (mb1::mb2::cf) None
| encode : forall mu mu' c d phi p r1 cf,
    disjoint_union (FC_mess mu) (FC_con phi ++ [c;d]) ->
    qam_sem ((CtxM ((AR (GEncode d mu) p)::r1) ((ShareC c (ChM d mu'))::phi)) :: cf) ((CtxM (p::r1) ((ShareC c (ChM d (recover_mess mu mu')))::phi)) :: cf) None 
| decode : forall c d qm x y p q mb1 mb2 cf,
    qam_sem ((ActM (ALock (AR (GDecode d x) p) mb1) (ShareC c (ChM d (QtM qm))) (ALock (AR (CqRecv d y) q) mb2))::cf) ((ALock (replace_mess p x (CcM (MeasureQ qm))) mb1)::(ALock (replace_mess q y (QtM (PartM qm))) mb2)::cf) (Some (QtM (ChanM (ChM d (QtM qm)))))
| assemble : forall (q: qmess) (mu: mess) (p: process) x mb cf,
    qam_sem ((ALock (AR (LEncode q mu x) p) mb)::cf) ((ALock (replace_mess p x (recover_mess (QtM q) mu)) mb)::cf) None
| extract : forall (c: qchan) (i: cmess) (x: var) (p: process) mb (cf: config),
    qam_sem ((ALock (AR (LDecode (ChanM (ChM c (CcM i))) x) p) mb)::cf) ((ALock (replace_mess p x (CcM i)) mb)::cf) (Some (QtM (ChanM (ChM c (CcM i)))))  
| transfer : forall (m: mess) (c: chan_n) (d: chan_n) (x: var) (p: process) (cf: config) mb1 mb2,
    qam_sem ((ActM (ALock (AR (Trans d x) p) mb1) (ShareC c (ChM d m)) mb2)::cf)  ((ALock (replace_mess p x m) mb1) :: mb2 :: cf) None 
| commu : forall (c: cchan) (i: cmess) x p q mb1 mb2 cf,
    qam_sem ((ALock (AR (CSend c i) p) mb1)::(ALock (AR (CcRecv c x) q) mb2)::cf) ((ALock p mb1)::(ALock (replace_mess q x (CcM i)) mb2)::cf) (Some (CcM i))  
| swap : forall (d: qchan) (c1 c2: chan_n) p q mb1 mb2 mb1' mb2' cf,
    not (In c1 (FC_memb mb2')) ->
    qam_sem ((ActM (ALock (AR (QSwap d) p) mb1) (ShareC c1 (ChM d (QtM Unit))) mb2)::(ActM (ALock (AR (QSwap d) q) mb1') (ShareC c2 (ChM d (QtM Unit))) mb2')::cf) ((ActM mb2 (ShareC c1 (ChM d (QtM Unit))) mb2')::(ALock p mb1)::(ALock q mb1')::cf) None.  
