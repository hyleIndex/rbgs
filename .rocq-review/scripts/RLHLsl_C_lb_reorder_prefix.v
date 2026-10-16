From Stdlib Require Import List Bool Arith.PeanoNat PArith.PArith. Import ListNotations.
Require Import models.EffectSignatures models.RelaxedSignature models.LinCCAL.
Require Import models.simlin.RelaxedLTS models.simlin.RelaxedLang models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedHoareSpec models.simlin.RelaxedHoareCompLin models.simlin.RelaxedHoareCompLinSpec.
Require Import models.simlin.RelaxedHoareBase models.simlin.RelaxedHoareRun.
Require Import examples.Relaxed.WindowTable models.view.PrefixView.
Import LinCCALBase RelaxedSig RelaxedLTSSpec RelaxedLang RelaxedSemantics RelaxedHoareRun RelaxedHoareBase RelaxedTraceLin RelaxedHoareCompLinSpec.
Module WT := WindowTable.

Inductive SLoc := Sq (i : nat) | Sx (i : nat) | Sy (i : nat).
Definition SLoc_eq_dec (a b : SLoc) : {a = b} + {a <> b}. Proof. decide equality; apply Nat.eq_dec. Defined.
Inductive GLoc := GD (l : SLoc) | GBw | GBr.
Inductive SOp := sRd (l : SLoc) | sWr (l : SLoc) (v : nat) | sInc (l : SLoc) | sWmb | sRmb.
Definition sar (o : SOp) : Type := match o with sRd _ => nat | _ => unit end.
Definition SSig : Sig.t := {| Sig.op := SOp; Sig.ar := sar |}.
Definition ogl (o : SOp) : GLoc := match o with sRd l | sWr l _ | sInc l => GD l | sWmb => GBw | sRmb => GBr end.
Definition ocat (o : SOp) : WT.DCat := match o with sRd _ => WT.DR | sWr _ _ | sInc _ => WT.DW | sWmb => WT.Wmb | sRmb => WT.Rmb end.
Definition sl_beq (a b : SLoc) : bool := match a, b with Sq i, Sq j | Sx i, Sx j | Sy i, Sy j => Nat.eqb i j | _, _ => false end.
Definition gl_beq (a b : GLoc) : bool := match a, b with GD l, GD l' => sl_beq l l' | GBw, GBw | GBr, GBr => true | _, _ => false end.
Definition sindep (rc : bool) (o o' : SOp) : Prop := (gl_beq (ogl o) (ogl o') || WT.dto rc (ocat o) (ocat o')) = false.
Definition E_S (rc : bool) : RelaxedSig.t := {| effect := SSig; handle := nat; semi_independent := sindep rc; mode := fun _ => Local |}.
Definition Regs := SLoc -> nat.
Definition upd (m : Regs) l v : Regs := fun l' => if SLoc_eq_dec l l' then v else m l'.
Definition δS (m : Regs) (o : SOp) : sar o -> Regs -> Prop :=
  match o as o0 return sar o0 -> Regs -> Prop with
  | sRd l => fun r m' => r = m l /\ m' = m | sWr l v => fun _ m' => m' = upd m l v
  | sInc l => fun _ m' => m' = upd m l (S (m l)) | sWmb | sRmb => fun _ m' => m' = m end.
Inductive FOp := fW (i vx vy : nat) | fR (i : nat).
Definition far (o : FOp) : Type := match o with fR _ => (nat * nat)%type | _ => unit end.
Definition FSig : Sig.t := {| Sig.op := FOp; Sig.ar := far |}.
Definition slsi (o o' : FOp) : Prop := match o, o' with fR i, fW j _ _ | fW i _ _, fR j => i <> j | _, _ => False end.
Definition F2 (si : FOp -> FOp -> Prop) : RelaxedSig.t := {| effect := FSig; handle := nat; semi_independent := si; mode := fun _ => Local |}.
Definition AS := nat -> (nat * nat)%type.
Definition δF (A : AS) (o : FOp) : far o -> AS -> Prop :=
  match o as o0 return far o0 -> AS -> Prop with
  | fW i vx vy => fun _ A' => A' = (fun j => if Nat.eqb i j then (vx, vy) else A j)
  | fR i => fun r A' => r = A i /\ A' = A end.
Inductive WSt := W0 | W1 | W2 | W3 | W4 | W5 | WD.
Definition wnext (i vx vy : nat) (st : WSt) : SStep SSig WSt unit :=
  match st with
  | W0 => SCall (sInc (Sq i)) [] (fun _ => W1) | W1 => SCall sWmb [] (fun _ => W2)
  | W2 => SCall (sWr (Sx i) vx) [] (fun _ => W3) | W3 => SCall (sWr (Sy i) vy) [] (fun _ => W4)
  | W4 => SCall sWmb [] (fun _ => W5) | W5 => SCall (sInc (Sq i)) [] (fun _ => WD) | WD => SDone tt end.
Inductive RSt := RG | RA (s : nat) | RX (s : nat) | RY (s a : nat) | RB (s a c : nat) | RT (s a c : nat) | RD (a c : nat).
Definition rnext (i : nat) (st : RSt) : SStep SSig RSt (nat * nat) :=
  match st with
  | RG => SCall (sRd (Sq i)) [] (fun s => RA s) | RA s => SCall sRmb [] (fun _ => RX s)
  | RX s => SCall (sRd (Sx i)) [] (fun a => RY s a) | RY s a => SCall (sRd (Sy i)) [] (fun c => RB s a c)
  | RB s a c => SCall sRmb [] (fun _ => RT s a c)
  | RT s a c => SCall (sRd (Sq i)) [] (fun s' => if Nat.even s && Nat.eqb s s' then RD a c else RG)
  | RD a c => SDone (a, c) end.
CoFixpoint div {E : RelaxedSig.t} {R : Type} : Prog E R := Tau div.
Definition M2w (rc : bool) (si : FOp -> FOp -> Prop) (tw : nat -> tid) : RelaxedModuleImpl (E_S rc) (F2 si) :=
  fun op t => match op as o return Prog (E_S rc) (far o) with
  | fW i vx vy => if Pos.eqb t (tw i) then run (G := E_S rc) (wnext i vx vy) [] W0 else div
  | fR i => run (G := E_S rc) (rnext i) [] RG end.
Definition regs0 : Regs := fun _ => 0.  Definition A0 : AS := fun _ => (0, 0).
Definition sl2_target := forall rc si tw, (forall o o', slsi o o' -> si o o') ->
  exists I R G, RLHL2Hyps (VE := EIhl (E := E_S rc) δS) (VF := RelaxedHoareSpec.EI (F := F2 si) δF) I R G (M2w rc si tw) ((regs0, []), []) (A0, []).
Definition sl2_relin_target := forall rc si tw s, (forall o o', slsi o o' -> si o o') ->
  RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI (F := E_S rc) δS) (M2w rc si tw) (regs0, []) s ->
  PrefixView.complete s -> rel_lin (@PrefixView.sel (F2 si)) s si (RelaxedHoareSpec.seq_legal (F := F2 si) δF A0).

Lemma lb_cross rc i j : i <> j -> forall c w, In c [sRd (Sq i); sRmb; sRd (Sx i); sRd (Sy i)] ->
  In w [sInc (Sq j); sWmb; sWr (Sx j) 1; sWr (Sy j) 1] -> sindep rc c w.
Proof. intros Hij c w Hc Hw. unfold sindep. apply Nat.eqb_neq in Hij.
  destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn; rewrite ?Hij; destruct rc; reflexivity. Qed.
Lemma rmb_blocks_rd rc l : ~ sindep rc sRmb (sRd l).
Proof. unfold sindep. destruct rc; cbn; discriminate. Qed.
Ltac ex_wait v := match goal with
  | |- program_execution_tagged ?t (Build_ProgramConfig (@Wait ?E ?R _ (@MkFutureRef _ ?o ?h) ?k) ?H) _ _ =>
      eapply tagged_execution_emit; [ eapply (@tagged_wait_pending E R t o h v k H); apply resolve_here | cbn beta ] end.
Ltac ex_step hh v := rewrite run_unfold; cbn -[run]; eapply tagged_execution_emit;
  [ apply tagged_futureD with (h := hh); unfold handle_fresh; cbn; intuition discriminate | cbn beta ]; ex_wait v.
Ltac ex_done := rewrite run_unfold; cbn -[run]; apply tagged_execution_refl.
Lemma rd_retry_prod rc si tw t : exists tr, program_produces_tagged t (M2w rc si tw (fR 2) t) tr (1, 1) /\ length tr = 24.
Proof. eexists. split; [eexists; split |].
  - unfold initial_program. cbn [M2w]. ex_step 0 1. ex_step 1 tt. ex_step 2 0. ex_step 3 1. ex_step 4 tt. ex_step 5 2.
    ex_step 6 2. ex_step 7 tt. ex_step 8 1. ex_step 9 1. ex_step 10 tt. ex_step 11 2. ex_done.
  - constructor. repeat constructor.
  - reflexivity. Qed.
Lemma wr_guard_prod rc si tw t : tw 1 = t -> exists tr, program_produces_tagged t (M2w rc si tw (fW 1 1 1) t) tr tt /\ length tr = 12.
Proof. intros Ht. eexists. split; [eexists; split |].
  - unfold initial_program. cbn [M2w]. rewrite Ht, Pos.eqb_refl.
    ex_step 10 tt. ex_step 11 tt. ex_step 12 tt. ex_step 13 tt. ex_step 14 tt. ex_step 15 tt. ex_done.
  - constructor. repeat constructor.
  - reflexivity. Qed.

Definition kk si (t : tid) (h : nat) : CallKey (F2 si) := (t, h).
Definition M2 (rc : bool) (si : FOp -> FOp -> Prop) : RelaxedModuleImpl (E_S rc) (F2 si) :=
  fun op t => match op as o return Prog (E_S rc) (far o) with
  | fW i vx vy => run (G := E_S rc) (wnext i vx vy) [] W0 | fR i => run (G := E_S rc) (rnext i) [] RG end.
Ltac untag_rw := repeat match goal with H : untag ?m = _ |- context [untag ?m] => rewrite H end.
Ltac sindep_ok := let Hn := fresh "Hn" in intros Hn; apply Hn; cbn; unfold sindep; cbn; reflexivity.
Ltac cross_ok := first
  [ left; cbn [RelaxedModuleSemantics.ts_event]; untag_rw; cbn; first [discriminate | assumption | congruence]
  | right; split; [cbn [RelaxedModuleSemantics.ts_event]; untag_rw; reflexivity |];
    unfold RelaxedModuleSemantics.must_precede; cbn [RelaxedModuleSemantics.ts_event]; untag_rw; cbn;
    first [ solve [discriminate] | solve [let H := fresh in intros H; exact H] | solve [sindep_ok]
          | solve [match goal with Hd : forall q, ~ tev_deps ?m q |- ~ tev_deps ?m _ => apply Hd end] ] ].
Ltac m_next := apply RelaxedModuleSemantics.tagged_select_next; [cross_ok |].
Ltac m_here := apply RelaxedModuleSemantics.tagged_select_here.
Ltac ei_inv := cbn; untag_rw; cbn; exists tt; eexists; split; [reflexivity | reflexivity].

Lemma rd_prod si t : exists tr, program_produces_tagged t (M2 false si (fR 2) t) tr (1, 1) /\
  map untag tr = [Build_ThreadEvent t (@InvEv (E_S false) 0 (sRd (Sq 2))); Build_ThreadEvent t (@ResEv (E_S false) 0 (sRd (Sq 2)) 2);
    Build_ThreadEvent t (@InvEv (E_S false) 1 sRmb); Build_ThreadEvent t (@ResEv (E_S false) 1 sRmb tt);
    Build_ThreadEvent t (@InvEv (E_S false) 2 (sRd (Sx 2))); Build_ThreadEvent t (@ResEv (E_S false) 2 (sRd (Sx 2)) 1);
    Build_ThreadEvent t (@InvEv (E_S false) 3 (sRd (Sy 2))); Build_ThreadEvent t (@ResEv (E_S false) 3 (sRd (Sy 2)) 1);
    Build_ThreadEvent t (@InvEv (E_S false) 4 sRmb); Build_ThreadEvent t (@ResEv (E_S false) 4 sRmb tt);
    Build_ThreadEvent t (@InvEv (E_S false) 5 (sRd (Sq 2))); Build_ThreadEvent t (@ResEv (E_S false) 5 (sRd (Sq 2)) 2)].
Proof. eexists. split; [eexists; split |].
  - unfold initial_program. cbn [M2]. ex_step 0 2. ex_step 1 tt. ex_step 2 1. ex_step 3 1. ex_step 4 tt. ex_step 5 2. ex_done.
  - constructor. repeat constructor.
  - reflexivity. Qed.
Lemma wr_prod si t : exists tr, program_produces_tagged t (M2 false si (fW 1 1 1) t) tr tt /\
  map untag tr = [Build_ThreadEvent t (@InvEv (E_S false) 10 (sInc (Sq 1))); Build_ThreadEvent t (@ResEv (E_S false) 10 (sInc (Sq 1)) tt);
    Build_ThreadEvent t (@InvEv (E_S false) 11 sWmb); Build_ThreadEvent t (@ResEv (E_S false) 11 sWmb tt);
    Build_ThreadEvent t (@InvEv (E_S false) 12 (sWr (Sx 1) 1)); Build_ThreadEvent t (@ResEv (E_S false) 12 (sWr (Sx 1) 1) tt);
    Build_ThreadEvent t (@InvEv (E_S false) 13 (sWr (Sy 1) 1)); Build_ThreadEvent t (@ResEv (E_S false) 13 (sWr (Sy 1) 1) tt);
    Build_ThreadEvent t (@InvEv (E_S false) 14 sWmb); Build_ThreadEvent t (@ResEv (E_S false) 14 sWmb tt);
    Build_ThreadEvent t (@InvEv (E_S false) 15 (sInc (Sq 1))); Build_ThreadEvent t (@ResEv (E_S false) 15 (sInc (Sq 1)) tt)] /\
  exists w0 rest, tr = w0 :: rest /\ forall q, ~ tev_deps w0 q.
Proof. eexists. split; [eexists; split |].
  - unfold initial_program. cbn [M2]. ex_step 10 tt. ex_step 11 tt. ex_step 12 tt. ex_step 13 tt. ex_step 14 tt. ex_step 15 tt. ex_done.
  - constructor. repeat constructor.
  - split; [reflexivity |]. do 2 eexists. split; [reflexivity |]. intros q [(i & [] & _) _]. Qed.
Example lb_reorder_prefix si (t : tid) : exists c,
  RelaxedModuleSemantics.module_execution_tagged (RelaxedHoareSpec.EI (F := E_S false) δS) (M2 false si)
    (RelaxedModuleSemantics.initial_tagged_module (RelaxedHoareSpec.EI (F := E_S false) δS) (regs0, []))
    [RelaxedModuleSemantics.OverlayEvent (Build_ThreadEvent t (@InvEv (F2 si) 0 (fR 2)));
     RelaxedModuleSemantics.OverlayEvent (Build_ThreadEvent t (@InvEv (F2 si) 1 (fW 1 1 1)));
     RelaxedModuleSemantics.UnderlayEvent (Build_ThreadEvent t (@InvEv (E_S false) 10 (sInc (Sq 1))))] c.
Proof.
  destruct (rd_prod si t) as (trr & Hpr & Hmr). destruct (wr_prod si t) as (trw & Hpw & Hmw & w0 & rest & Hw & Hd). subst trw.
  destruct trr as [|r0 [|r1 [|r2 [|r3 [|r4 [|r5 [|r6 [|r7 [|r8 [|r9 [|r10 [|r11 [|r12 trr]]]]]]]]]]]]]; try discriminate Hmr.
  pose proof Hmr as Hm'. injection Hm' as E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11.
  pose proof Hmw as Hw'. cbn [map] in Hw'. injection Hw' as F0 _. rewrite <- F0. eexists.
  eapply RelaxedModuleSemantics.tagged_module_execution_cons.
  { eapply RelaxedModuleSemantics.tagged_invoke; [intros [] | exact Hpr |].
    rewrite Hmr. split; [cbn; repeat constructor; cbn; intuition discriminate | intros key _ []]. }
  eapply RelaxedModuleSemantics.tagged_module_execution_cons.
  { eapply RelaxedModuleSemantics.tagged_invoke; [cbn; intros [H|[]]; discriminate H | exact Hpw |].
    rewrite Hmw. split; [cbn; repeat constructor; cbn; intuition discriminate |].
    intros key Hk Hu. rewrite Hmr in Hu. cbn in Hk, Hu.
    repeat (destruct Hk as [<- | Hk]; [repeat (destruct Hu as [Hu | Hu]; [discriminate Hu |]); exact Hu |]); exact Hk. }
  cbn [app RelaxedModuleSemantics.schedule_trace_tagged map].
  eapply RelaxedModuleSemantics.tagged_module_execution_cons;
  [ apply RelaxedModuleSemantics.tagged_underlay with
      (candidate := @RelaxedModuleSemantics.Build_TaggedScheduledEvent (E_S false) (F2 si) (kk si t 1) w0);
    [ cbn; do 12 m_next; m_here | ei_inv ] | ].
  apply RelaxedModuleSemantics.tagged_module_execution_refl.
Qed.

Print Assumptions rd_prod.
Print Assumptions wr_prod.
Print Assumptions lb_reorder_prefix.
