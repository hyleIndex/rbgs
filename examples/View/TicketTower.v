(** * The ticket-lock tower over TSO, composed

    [VL MemHW  --M_TL-->  VL TLC  --M_SL-->  VL RecP]

    Each of the two proofs presents its underlay with a ghost:

    | proof                | underlay presentation | ghost                      |
    |----------------------|-----------------------|----------------------------|
    | [M_TL_ghost] (lock)  | [MemHWg]              | owner of each ticket       |
    | [M_SL_ghost] (SeqLock) | [TLCm]              | data of the last release   |

    So the ticket lock has two presentations: [TLC] as the overlay of
    its own proof, [TLCm] as the underlay of the SeqLock's.
    [ViewLiftGhost.cal_ghost_to_plain] removes each ghost
    ([M_TL_plain], [M_SL_plain]).  The two proofs then meet at the same
    lifted state [Idle (vinit TLC tl_init)], and compose.  The memory
    ghost does work in the lock's proof; the lock's ghost is redundant in
    the SeqLock's proof (see [TicketTowerSeqLock]).

    - [presentations]: the lock's correctness against [TLC], the SeqLock's
      correctness against [TLCm], and the bridge from [TLCm] to [TLC].
    - [tower_CompLin]: compositional linearizability of [M_TL ▶ₘ M_SL]
      from the TSO memory to the record ([CompLinSound.cal_to_CompLin],
      [CompLinVComp.VComp.CompLin_vcomp]).
    - [rec_stale_read], [rec_sc_no_stale_read]: the record is not SC.
      After a write has responded, another thread can still read the
      initial value.

    The result is relative to the timeline model of TSO ([MemHW]), which
    is not complete for x86-TSO: it has no store forwarding
    ([ViewLiftOMCA.n6_mp_inseparable]), and writes enter the timeline in
    the order of their responses ([ViewLiftMultiWriter.no_issue_order_run]). *)

Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Lists.List.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import TPSimulation.
Require Import TPSimulationSet.
Require Import CompLin.
Require Import CompLinSound.
Require Import CompLinVComp.
Require Import models.simlin.AtomicLTS.
Require Import models.view.ViewLift.
Require Import models.view.ViewLiftGhost.
Require Import examples.View.TicketTowerSpecs.
Require Import examples.View.TicketTowerLock.
Require Import examples.View.TicketTowerSeqLock.
Import ListNotations.

Module TicketTower.
  Import Reg LinCCALBase LTSSpec AtomicLTS ViewLift TicketTowerSpecs.

  (** ** Two presentations of the ticket lock *)

  Theorem presentations :
    (* the ticket lock on TSO memory, against [TLC] *)
    TPSimulation.TPSimulation.cal (VE := VL MemHW) (VF := VL TLC) TicketTowerLock.M_TL
      (Idle (vinit MemHW hw_init)) (Idle (vinit TLC tl_init)) /\
    (* the SeqLock over the lock, against [TLCm] *)
    TPSimulation.TPSimulation.cal (VE := VL TLCm) (VF := VL RecP) TicketTowerSeqLock.M_SL
      (Idle (vinit TLCm (tl_init, rel_init))) (Idle (vinit RecP rec_init)) /\
    (* any proof over [TLCm] is one over [TLC] *)
    (forall (F : Op.t) (VF : @LTS F) (M : ModuleImpl ETL F) ρ0,
       TPSimulation.TPSimulation.cal (VE := VL TLCm) (VF := VF) M (Idle (vinit TLCm (tl_init, rel_init))) ρ0 ->
       TPSimulation.TPSimulation.cal (VE := VL TLC) (VF := VF) M (Idle (vinit TLC tl_init)) ρ0).
  Proof.
    split; [exact TicketTowerLock.M_TL_plain|].
    split; [exact TicketTowerSeqLock.M_SL_ghost|].
    intros F VF M ρ0 Hc. exact (ViewLiftGhost.cal_ghost_to_plain TLC rel_up VF M tl_init rel_init ρ0 Hc).
  Qed.

  (** ** Composition *)

  Lemma cal_set {E F} (VE : @LTS E) (VF : @LTS F) (M : ModuleImpl E F) σ0 ρ0 :
    TPSimulation.TPSimulation.cal (VE := VE) (VF := VF) M σ0 ρ0 -> TPSimulationSet.TPSimulation.cal M σ0 ρ0.
  Proof.
    intros Hc. unfold TPSimulationSet.TPSimulation.cal, TPSimulationSet.TPSimulation.ac_init.
    apply TPSimulation.TPSimulation.TPSimulation_singleton. exact Hc.
  Qed.

  Theorem tower_CompLin :
    @CompLin.CompLin.CompLin EHW ERec (VL MemHW) (VL RecP)
      (CompLinVComp.CompLinVComp.implVComp TicketTowerLock.M_TL TicketTowerSeqLock.M_SL)
      (Idle (vinit MemHW hw_init)) (Idle (vinit RecP rec_init)).
  Proof.
    apply (@CompLinVComp.CompLinVComp.VComp.CompLin_vcomp EHW ETL ERec (VL MemHW) (VL TLC) (VL RecP)
             TicketTowerLock.M_TL TicketTowerSeqLock.M_SL _ (Idle (vinit TLC tl_init)) _).
    - apply CompLinSound.CompLinSound.cal_to_CompLin.
      apply cal_set. exact TicketTowerLock.M_TL_plain.
    - apply CompLinSound.CompLinSound.cal_to_CompLin.
      apply cal_set. exact TicketTowerSeqLock.M_SL_plain.
  Qed.

  (** ** The record is weak *)

  (** Thread 1 writes [(1, 1)] at timestamp 3; then thread 2 reads at
      timestamp 2 and gets the initial record. *)
  Lemma rec_stale_read :
    exists x1 x2 x3 x4,
      Step (VL RecP) (Build_ThreadEvent 1%positive (InvEv (rwrite 1 1)))
        (Idle (vinit RecP rec_init)) x1 /\
      Step (VL RecP) (Build_ThreadEvent 1%positive (ResEv (rwrite 1 1) tt)) x1 x2 /\
      Step (VL RecP) (Build_ThreadEvent 2%positive (InvEv rread)) x2 x3 /\
      Step (VL RecP) (Build_ThreadEvent 2%positive (ResEv rread (O, O))) x3 x4.
  Proof.
    set (r1 := upd_app RecP (vinit RecP rec_init) 1%positive (rwrite 1 1) 3%positive (1, 1)).
    exists (Pending (vinit RecP rec_init) 1%positive (rwrite 1 1)), (Idle r1),
      (Pending r1 2%positive rread), (Idle (upd_retro RecP r1 2%positive rread 2%positive)).
    split; [|split; [|split]].
    - apply (step_inv (VStep RecP)). eapply vstep_inv. reflexivity.
    - apply (step_res (VStep RecP)).
      refine (vstep_app RecP 1%positive (rwrite 1 1) tt 3%positive (1, 1) _ _ _ eq_refl eq_refl _ _ _ eq_refl).
      + reflexivity.
      + intros o h [].
      + reflexivity.
    - apply (step_inv (VStep RecP)). eapply vstep_inv. reflexivity.
    - apply (step_res (VStep RecP)).
      refine (vstep_retro RecP 2%positive rread (O, O) 2%positive r1 _ _ eq_refl eq_refl _ _ _ eq_refl).
      + reflexivity.
      + intros o h Hin. simpl in Hin. contradiction.
      + simpl. split; reflexivity.
  Qed.

  Lemma astep_cases {E : Op.t} {S : Type} (St : @ThreadEvent E -> S -> S -> Prop) ev x x' :
    AStep St ev x x' ->
    match te_ev ev with
    | InvEv op => exists s1 s2, x = Idle s1 /\ x' = Pending s2 (te_tid ev) op /\ St ev s1 s2
    | ResEv op r => exists s1 s2, x = Pending s1 (te_tid ev) op /\ x' = Idle s2 /\ St ev s1 s2
    end.
  Proof. intros H. destruct H; simpl; eauto 6. Qed.

  (** In the SC record, a read after the write has responded returns the
      written value. *)
  Lemma rec_sc_no_stale_read x1 x2 x3 x4 :
    Step (SC RecP) (Build_ThreadEvent 1%positive (InvEv (rwrite 1 1))) (Idle rec_init) x1 ->
    Step (SC RecP) (Build_ThreadEvent 1%positive (ResEv (rwrite 1 1) tt)) x1 x2 ->
    Step (SC RecP) (Build_ThreadEvent 2%positive (InvEv rread)) x2 x3 ->
    ~ Step (SC RecP) (Build_ThreadEvent 2%positive (ResEv rread (O, O))) x3 x4.
  Proof.
    intros H1 H2 H3 H4.
    apply astep_cases in H1 as (a1 & b1 & Ha1 & -> & Hs1). injection Ha1 as <-.
    apply (scstep_inv_inv RecP) in Hs1. subst b1.
    apply astep_cases in H2 as (a2 & b2 & Ha2 & -> & Hs2). injection Ha2 as <-.
    apply (scstep_res_spec RecP) in Hs2. simpl in Hs2. subst b2.
    apply astep_cases in H3 as (a3 & b3 & Ha3 & -> & Hs3). injection Ha3 as <-.
    apply (scstep_inv_inv RecP) in Hs3. subst b3.
    apply astep_cases in H4 as (a4 & b4 & Ha4 & -> & Hs4). injection Ha4 as <-.
    apply (scstep_res_spec RecP) in Hs4. simpl in Hs4. destruct Hs4 as (Heq & _). discriminate.
  Qed.
End TicketTower.
