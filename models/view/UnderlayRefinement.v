(** * Moving a [cal] proof to a refined underlay

    If every step of an underlay LTS [VE'] can be matched by a step of
    [VE] (a forward simulation on underlay states), and every error of
    [VE'] is an error of [VE], then a thread-pool simulation of an
    implementation over [VE] is also one over [VE'].  The overlay side
    is untouched.

    [EBStackTSOImpl.components_correct] (examples/View/EBStackTSO.v)
    uses it, together with T1 ([ViewLiftTensor]).  This replaced a
    hand-written bridge of about 980 lines to CSL-Lin's global view.

    Simulations compose: [us_refl], [us_trans], and [us_tens] for the
    tensor of underlays.  [us_reach] transfers finite executions. *)

Require Import Stdlib.FSets.FMapPositive.
Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import TPSimulation.

Module UnderlayRefinement.
  Import Reg LinCCALBase LTSSpec Lang Semantics TPSimulation.

  Section Refine.
    Context {E F : Op.t}.
    Context (VE VE' : @LTS E) (VF : @LTS F).
    Context (Rel : State VE' -> State VE -> Prop).

    (** [VE'] is simulated by [VE]. *)
    Record UnderlaySim : Prop := {
      us_step : forall ev σ' σ'' τ,
        Rel σ' τ -> Step VE' ev σ' σ'' ->
        exists τ', Step VE ev τ τ' /\ Rel σ'' τ';
      us_error : forall ev σ' τ,
        Rel σ' τ -> Error VE' ev σ' -> Error VE ev τ;
    }.

    Context (Hsim : UnderlaySim).
    Context (M : ModuleImpl E F).

    Lemma ts_step_refine f ev σ' ts1 σ'' ts2 τ :
      Rel σ' τ ->
      @ts_step E F VE' f ev σ' ts1 σ'' ts2 ->
      exists τ', @ts_step E F VE f ev τ ts1 τ' ts2 /\ Rel σ'' τ'.
    Proof.
      intros HR Hs. destruct Hs as [t op k s1 s2 Hstep | t op ret k s1 s2 Hstep].
      - destruct (us_step Hsim _ _ _ _ HR Hstep) as (τ' & Hτ & HR1).
        exists τ'. split; [constructor; exact Hτ | exact HR1].
      - destruct (us_step Hsim _ _ _ _ HR Hstep) as (τ' & Hτ & HR1).
        exists τ'. split; [constructor; exact Hτ | exact HR1].
    Qed.

    Lemma ustep_refine ev σ' c σ'' c' τ :
      Rel σ' τ ->
      @ustep E F VE' ev σ' c σ'' c' ->
      exists τ', @ustep E F VE ev τ c τ' c' /\ Rel σ'' τ'.
    Proof.
      intros HR Hs. destruct Hs as [f ts1 ts2 Hfind Hstep Hupd].
      destruct (ts_step_refine _ _ _ _ _ _ _ HR Hstep) as (τ' & Hτ & HR1).
      exists τ'. split; [econstructor; eauto | exact HR1].
    Qed.

    Lemma uerror_refine ev σ' c τ :
      Rel σ' τ ->
      @uerror E F VE' ev σ' c -> @uerror E F VE ev τ c.
    Proof.
      intros HR He. destruct He as [f ts Hfind Herr].
      econstructor; [exact Hfind|].
      destruct Herr as [t op s k Herror]. constructor.
      exact (us_error Hsim _ _ _ HR Herror).
    Qed.

    Theorem tpsim_refine σ' τ c ρ π :
      Rel σ' τ ->
      @TPSimulation E F VE VF M τ c ρ π ->
      @TPSimulation E F VE' VF M σ' c ρ π.
    Proof.
      revert σ' τ c ρ π. cofix IH.
      intros σ' τ c ρ π HR Hs.
      destruct Hs as [Herror | Hinv Hret Hustep Hlin Htau Hnoerr].
      - constructor. exact Herror.
      - constructor 2.
        + intros t f c' Hstep. exact (IH _ _ _ _ _ HR (Hinv t f c' Hstep)).
        + intros t f ret c' Hstep.
          destruct (Hret t f ret c' Hstep) as [Hpi Hsim1].
          split; [exact Hpi | exact (IH _ _ _ _ _ HR Hsim1) ].
        + intros ev σ'' c' Hstep.
          destruct (ustep_refine _ _ _ _ _ _ HR Hstep) as (τ' & Hτ & HR1).
          destruct (Hustep ev τ' c' Hτ) as (rho1 & pi1 & Hsteps & Hsim1).
          exists rho1, pi1. split; [exact Hsteps | exact (IH _ _ _ _ _ HR1 Hsim1) ].
        + destruct Hlin as (rho1 & pi1 & Hsteps & Hsim1).
          exists rho1, pi1. split; [exact Hsteps | exact (IH _ _ _ _ _ HR Hsim1) ].
        + intros t c' Hstep. exact (IH _ _ _ _ _ HR (Htau t c' Hstep)).
        + intros ev Herr. apply (Hnoerr ev). exact (uerror_refine _ _ _ _ HR Herr).
    Qed.

    Corollary cal_refine σ0' τ0 ρ0 :
      Rel σ0' τ0 ->
      @cal E F VE VF M τ0 ρ0 -> @cal E F VE' VF M σ0' ρ0.
    Proof. unfold cal. intros HR Hc. exact (tpsim_refine _ _ _ _ _ HR Hc). Qed.
  End Refine.


  (** ** Composing underlay simulations *)

  Section Compose.
    Lemma us_refl {E : Op.t} (V : @LTS E) : UnderlaySim V V eq.
    Proof.
      constructor.
      - intros ev x x' y <- Hs. exists x'. split; [exact Hs | reflexivity].
      - intros ev x y <- He. exact He.
    Qed.

    (** [V3] is simulated by [V2], which is simulated by [V1]. *)
    Lemma us_trans {E : Op.t} (V1 V2 V3 : @LTS E) R21 R32 :
      UnderlaySim V1 V2 R21 -> UnderlaySim V2 V3 R32 ->
      UnderlaySim V1 V3 (fun x z => exists y, R32 x y /\ R21 y z).
    Proof.
      intros H21 H32. constructor.
      - intros ev x x' z (y & Hxy & Hyz) Hs.
        destruct (us_step _ _ _ H32 _ _ _ _ Hxy Hs) as (y' & Hy & Hxy').
        destruct (us_step _ _ _ H21 _ _ _ _ Hyz Hy) as (z' & Hz & Hyz').
        exists z'. split; [exact Hz|]. exists y'. auto.
      - intros ev x z (y & Hxy & Hyz) He.
        exact (us_error _ _ _ H21 _ _ _ Hyz (us_error _ _ _ H32 _ _ _ Hxy He)).
    Qed.

    (** Simulation is a congruence for the tensor of underlays. *)
    Lemma us_tens {E1 E2 : Op.t} (V1 V1' : @LTS E1) (V2 V2' : @LTS E2) R1 R2 :
      UnderlaySim V1 V1' R1 -> UnderlaySim V2 V2' R2 ->
      UnderlaySim (tens_lts V1 V2) (tens_lts V1' V2')
        (fun x y => R1 (fst x) (fst y) /\ R2 (snd x) (snd y)).
    Proof.
      intros H1 H2. constructor.
      - intros [t [[op | op] | [op | op] r]] [a1 b1] [a2 b2] [a b] [HR1 HR2] Hs;
          simpl in HR1, HR2, Hs |- *; destruct Hs as [Hs <-].
        + destruct (us_step _ _ _ H1 _ _ _ _ HR1 Hs) as (a3 & Ha & HR1').
          exists (pair a3 b). simpl. auto.
        + destruct (us_step _ _ _ H2 _ _ _ _ HR2 Hs) as (b3 & Hb & HR2').
          exists (pair a b3). simpl. auto.
        + destruct (us_step _ _ _ H1 _ _ _ _ HR1 Hs) as (a3 & Ha & HR1').
          exists (pair a3 b). simpl. auto.
        + destruct (us_step _ _ _ H2 _ _ _ _ HR2 Hs) as (b3 & Hb & HR2').
          exists (pair a b3). simpl. auto.
      - intros [t [[op | op] | [op | op] r]] [a1 b1] [a b] [HR1 HR2] He;
          simpl in HR1, HR2, He |- *.
        + exact (us_error _ _ _ H1 _ _ _ HR1 He).
        + exact (us_error _ _ _ H2 _ _ _ HR2 He).
        + exact (us_error _ _ _ H1 _ _ _ HR1 He).
        + exact (us_error _ _ _ H2 _ _ _ HR2 He).
    Qed.
  End Compose.

  (** ** Finite executions are transferred along a simulation *)

  Inductive Reach {E : Op.t} (V : @LTS E) : State V -> list (@ThreadEvent E) -> State V -> Prop :=
  | reach_nil s : Reach V s nil s
  | reach_cons s ev s' evs s'' :
      Step V ev s s' -> Reach V s' evs s'' -> Reach V s (cons ev evs) s''.

  Lemma us_reach {E : Op.t} (V V' : @LTS E) R :
    UnderlaySim V V' R ->
    forall x y evs x', R x y -> Reach V' x evs x' -> exists y', Reach V y evs y' /\ R x' y'.
  Proof.
    intros Hsim x y evs x' HR Hr. revert y HR.
    induction Hr as [s | s ev s' evs s'' Hs Hr IH]; intros y HR.
    - exists y. split; [constructor | exact HR].
    - destruct (us_step _ _ _ Hsim _ _ _ _ HR Hs) as (y1 & Hy & HR1).
      destruct (IH y1 HR1) as (y' & Hy' & HR').
      exists y'. split; [econstructor; eauto | exact HR'].
  Qed.

End UnderlayRefinement.
