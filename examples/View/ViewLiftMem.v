(** * The owned TSO memory of [TryStackTSO.v] is observationally SC

    [OwnedMemTSOSpec.VMemTSO] has no timeline: [om_heap] is the current
    heap, and every response must be timestamped above the views of all
    threads.  So its timestamps never influence a result, and it behaves
    like the atomic SC memory.

    [MemP] gives the same memory as [ViewLift] parameters: [mread] is
    retroactive and does not synchronize, [malloc] and [mwrite] are
    appended and synchronize, and every pair of operations is dependent.
    Since every appended operation synchronizes, the collapse theorem of
    [ViewLift] applies.

    - [sc_sim_by_tso]: the SC memory is simulated by [VMemTSO].  The
      relation is the identity on heaps, plus a bound on all views.
      [VMemTSO] answers each step with a timestamp above that bound.
    - [mem_tso_to_sc], [mem_tso_to_vl]: [cal] proofs against [VMemTSO]
      transfer to the SC memory and to [VL MemP].

    Only this direction holds as stated.  [VMemTSO] also has an error
    ([error_mwrite_racy]) raised while another thread's write to the same
    location is pending, and the atomic LTS has no counterpart for it. *)

Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import TPSimulation.
Require Import examples.Common.AtomicLTS.
Require Import examples.View.TryStackTSO.
Require Import models.view.UnderlayRefinement.
Require Import models.view.ViewLift.

Module ViewLiftMem.
  Import Reg LinCCALBase LTSSpec AtomicLTS HeapSpec OwnedMemTSOSpec ViewLift.

  Section Mem.
    Context {A : Type}.

    Definition mstate : Type := (Heap A * Heap LocStat)%type.

    Definition mem_spec (s : mstate) (t : tid) (m : EMem_op A) : EMem_ar m -> mstate -> Prop :=
      match m as m0 return EMem_ar m0 -> mstate -> Prop with
      | malloc => fun ret s' =>
          exists init, fst s ret = None /\
            s' = (heap_update ret init (fst s), heap_update ret (LAlloc t) (snd s))
      | mread l => fun v s' => fst s l = Some v /\ snd s l = Some LWritten /\ s' = s
      | mwrite l v => fun _ s' =>
          snd s l = Some (LAlloc t) /\
            s' = (heap_update l v (fst s), heap_update l LWritten (snd s))
      end.

    Definition mem_err (t : tid) (m : EMem_op A) (s : mstate) : Prop :=
      match m with
      | malloc => False
      | mread l => snd s l <> Some LWritten
      | mwrite l _ => snd s l <> Some (LAlloc t)
      end.

    Definition MemP : @Params (EMem A) := {|
      vl_state := mstate;
      vl_spec := mem_spec;
      vl_err := mem_err;
      vl_retro := fun m => match m with mread _ => true | _ => false end;
      vl_dep := fun _ _ => true;
      vl_sync := fun m => match m with mread _ => false | _ => true end;
    |}.

    Lemma MemP_sync : forall m, vl_retro MemP m = false -> vl_sync MemP m = true.
    Proof. intros [| l | l v]; simpl; congruence. Qed.

    Lemma MemP_pres : forall s t m r s',
      vl_retro MemP m = true -> vl_spec MemP s t m r s' -> s' = s.
    Proof. intros s t [| l | l v] r s' Hr Hs; try discriminate. exact (proj2 (proj2 Hs)). Qed.

    Definition mem_init : mstate := (empty_heap, empty_heap).

    (** ** The SC memory is simulated by [VMemTSO] *)

    Definition bounded (c : OwnedMemState A) : Prop :=
      exists B, forall t, Pos.le (om_view c t) B.

    Definition MK (st : mstate) (c : OwnedMemState A) : Prop :=
      st = (om_heap c, om_loc c) /\ bounded c.

    Definition MR (x : @AState (EMem A) mstate) (y : @AState (EMem A) (OwnedMemState A)) : Prop :=
      match x, y with
      | Idle st, Idle c => MK st c
      | Pending st t m, Pending c t' m' => MK st c /\ t = t' /\ m = m'
      | _, _ => False
      end.

    Lemma MK_init : MK mem_init initOwnedMem.
    Proof. split; [reflexivity|]. exists xH. intros t. apply Pos.le_refl. Qed.

    Lemma sc_sim_by_tso : UnderlayRefinement.UnderlaySim VMemTSO (SC MemP) MR.
    Proof.
      constructor.
      - intros ev x x' y HR Hs. destruct Hs as [t op s1 s2 Hs | t op r s1 s2 Hs].
        + apply (scstep_inv_inv MemP) in Hs. subst s2.
          destruct y as [c | c t' op']; [|contradiction].
          exists (Pending c t op). split; [|simpl; auto].
          constructor. destruct op; constructor.
        + apply (scstep_res_spec MemP) in Hs.
          destruct y as [c | c t' op']; [contradiction|].
          destruct HR as ((-> & B & HB) & <- & <-).
          set (h := Pos.succ B).
          assert (Hfresh : forall t0, Pos.lt (om_view c t0) h).
          { intros t0. specialize (HB t0). unfold h. lia. }
          destruct op as [| l | l v]; simpl in Hs.
          * destruct Hs as (init & Hnone & ->).
            exists (Idle (mkOwnedMemTSO (heap_update r init (om_heap c))
                                        (heap_update r (LAlloc t) (om_loc c))
                                        (view_advance_all h))).
            split.
            -- constructor. eapply step_malloc_res; [exact Hfresh | exact Hnone | reflexivity ..].
            -- split; [reflexivity|]. exists h. intros t0. apply Pos.le_refl.
          * destruct Hs as (Hv & Hl & ->).
            exists (Idle (mkOwnedMemTSO (om_heap c) (om_loc c) (upd_tid_time (om_view c) t h))).
            split.
            -- constructor. eapply step_mread_res; [exact Hfresh | exact Hv | exact Hl | reflexivity ..].
            -- split; [reflexivity|]. exists h. intros t0. unfold upd_tid_time. simpl.
               destruct (Pos.eqb t t0); [apply Pos.le_refl|]. specialize (HB t0). unfold h. lia.
          * destruct r. destruct Hs as (Hl & ->).
            exists (Idle (mkOwnedMemTSO (heap_update l v (om_heap c))
                                        (heap_update l LWritten (om_loc c))
                                        (view_advance_all h))).
            split.
            -- constructor. eapply step_mwrite_res; [exact Hfresh | exact Hl | reflexivity ..].
            -- split; [reflexivity|]. exists h. intros t0. apply Pos.le_refl.
      - intros ev x y HR He. destruct He as [ev st Herr].
        destruct y as [c | c t' op']; [|contradiction].
        destruct HR as (-> & _).
        destruct ev as [t [op | op r]]; unfold err_at in Herr; simpl in Herr; [|contradiction].
        destruct op as [| l | l v]; simpl in Herr; [contradiction | |].
        + constructor. exact Herr.
        + constructor. exact Herr.
    Qed.

    (** [VL MemP] is simulated by [VMemTSO], through the SC memory. *)
    Lemma vl_sim_by_tso :
      UnderlayRefinement.UnderlaySim VMemTSO (VL MemP)
        (fun x z => exists y, SCRel MemP x y /\ MR y z).
    Proof.
      apply UnderlayRefinement.us_trans with (V2 := SC MemP).
      - exact sc_sim_by_tso.
      - exact (vl_sim_by_sc MemP MemP_sync).
    Qed.

    Lemma vl_tso_init :
      exists y, SCRel MemP (Idle (vinit MemP mem_init)) y /\ MR y (Idle initOwnedMem).
    Proof. exists (Idle mem_init). split; [apply SCRel_init | exact MK_init]. Qed.

    Section Transfer.
      Context {F : Op.t} (VF : @LTS F) (M : Lang.ModuleImpl (EMem A) F).

      Theorem mem_tso_to_sc ρ0 :
        TPSimulation.cal (VE := VMemTSO) (VF := VF) M (Idle initOwnedMem) ρ0 ->
        TPSimulation.cal (VE := SC MemP) (VF := VF) M (Idle mem_init) ρ0.
      Proof.
        intros Hc. exact (UnderlayRefinement.cal_refine VMemTSO (SC MemP) VF MR sc_sim_by_tso M
                            (Idle mem_init) (Idle initOwnedMem) ρ0 MK_init Hc).
      Qed.

      Theorem mem_tso_to_vl ρ0 :
        TPSimulation.cal (VE := VMemTSO) (VF := VF) M (Idle initOwnedMem) ρ0 ->
        TPSimulation.cal (VE := VL MemP) (VF := VF) M (Idle (vinit MemP mem_init)) ρ0.
      Proof.
        intros Hc. exact (UnderlayRefinement.cal_refine VMemTSO (VL MemP) VF _ vl_sim_by_tso M
                            (Idle (vinit MemP mem_init)) (Idle initOwnedMem) ρ0 vl_tso_init Hc).
      Qed.
    End Transfer.
  End Mem.
End ViewLiftMem.
