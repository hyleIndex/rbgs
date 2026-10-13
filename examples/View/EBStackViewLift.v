(** * The EB stack components over the atomic SC product (collapse)

    [EBStackTSO.v] runs the component layer of the elimination-backoff
    stack on a derived shared-clock underlay: [Pall = (Ptop ⊗ Pmem) ⊗ Pex],
    lifted with [ViewLift] and one clock for the three objects
    ([EShared], [components_correct]).  The transfer from the tensor of the
    per-object view specifications is a composition of generic simulations
    (T1 twice, the per-object simulations, [us_tens], [us_trans],
    [cal_refine]), about 50 lines.

    Before that, the bottom was CSL-Lin's hand-written global view
    [VComboTSO], and the transfer was a hand-written bridge of about 980
    lines.  The derived bottom differs from [VComboTSO] in two ways:
    [VL Pall] has one atomic phase for all three objects, while
    [VComboTSO] let calls on different objects overlap; and [VMemTSO]'s
    error in a pending state has no counterpart in [VL].

    Here: every appended operation of [Pall] synchronizes, so the collapse
    theorem gives the same proof against the atomic SC product
    ([components_correct_sc]). *)

Require Import Stdlib.PArith.PArith.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import TPSimulation.
Require Import examples.Common.AtomicLTS.
Require Import examples.View.ViewSpecs.
Require Import examples.View.TryStackTSO.
Require Import examples.View.ExchangerTSO.
Require Import examples.View.EBStackTSO.
Require Import models.view.UnderlayRefinement.
Require Import models.view.ViewLift.
Require Import models.view.ViewLiftTensor.
Require Import examples.View.ViewLiftCAS.
Require Import examples.View.ViewLiftMem.

Module EBStackViewLift.
  Import Reg LinCCALBase LTSSpec AtomicLTS TPSimulation UnderlayRefinement ViewLift ViewLiftTensor.
  Import CASRegTSOSpec OwnedMemTSOSpec HeapSpec EBStackTSOImpl.

  (** ** Collapse: the same proof against the atomic SC product *)

  Lemma Pall_sync : forall m, vl_retro Pall m = false -> vl_sync Pall m = true.
  Proof.
    apply PT_sync; [apply PT_sync|].
    - apply ViewLiftCAS.CASP_sync.
    - apply ViewLiftMem.MemP_sync.
    - apply ViewLiftCAS.CASP_sync.
  Qed.

  Lemma Pall_pres : forall s t m r s', vl_retro Pall m = true -> vl_spec Pall s t m r s' -> s' = s.
  Proof.
    apply PT_pres; [apply PT_pres|].
    - apply ViewLiftCAS.CASP_pres.
    - apply ViewLiftMem.MemP_pres.
    - apply ViewLiftCAS.CASP_pres.
  Qed.

  Theorem components_correct_sc :
    cal (VE := SC Pall) (VF := li_lts Fmid) components_impl (Idle s0) (li_init Fmid).
  Proof.
    apply (cal_view_to_sc Pall Pall_sync Pall_pres (li_lts Fmid) components_impl).
    exact components_correct.
  Qed.
End EBStackViewLift.
