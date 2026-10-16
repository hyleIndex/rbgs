From Stdlib Require Import List Bool Arith.PeanoNat PArith.PArith micromega.Lia Relations.Relation_Operators.
Require Import models.EffectSignatures models.RelaxedSignature models.LinCCAL.
Require Import models.simlin.RelaxedLTS models.simlin.RelaxedModuleSemantics models.simlin.RelaxedPossibility models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedHoareBase models.simlin.RelaxedHoareDag models.simlin.RelaxedHoareSpec models.simlin.RelaxedHoareCompLinSpec models.simlin.RelaxedHoareRun models.simlin.RelaxedHoareReady.
Require Import examples.Relaxed.RelaxedHoareSL2Prog examples.Relaxed.RelaxedHoareSL2Inv.
Import ListNotations LinCCALBase RelaxedSig RelaxedLTSSpec RelaxedModuleSemantics RelaxedPossibility RelaxedHoareCompLinSpec RelaxedHoareBase RelaxedHoareDag RelaxedHoareRun RelaxedHoareReady RelaxedHoareSL2Prog RelaxedHoareSL2Inv.

Section Merge.
  Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.
  Context (I : Assn VE VF) (R G : CallKey F -> PRel VE VF) (k : CallKey F) (Pinit : Assn VE VF).
  Lemma fam_merge Γ fin fin0 Q tr l1 l2 Z :
    BarrierWith I R k Pinit Γ fin fin0 Q ->
    Fam I Γ fin fin0 tr l1 Z -> Fam I Γ fin fin0 tr l2 Z ->
    (forall d, d < length Γ -> ~ rem Γ l1 d \/ ~ rem Γ l2 d) -> Q Z.
  Proof.
    intros Hbw H1 H2 Hcov. apply (bw_sum _ _ _ _ _ _ _ _ Hbw Z (fa_I _ _ _ _ _ _ _ H1) (fa_fin0 _ _ _ _ _ _ _ H1)).
    intros d sd Hd _. assert (Hlt : d < length Γ) by (apply nth_error_Some; congruence).
    destruct (Hcov d Hlt) as [Hn | Hn].
    - exact (fa_fin _ _ _ _ _ _ _ H1 d Hlt Hn).
    - exact (fa_fin _ _ _ _ _ _ _ H2 d Hlt Hn).
  Qed.
End Merge.

Module M24Scratch.
  Definition rc := true.
  Definition si : FOp -> FOp -> Prop := fun _ _ => False.
  Definition tw : nat -> tid := fun _ => 2%positive.
  Definition t : tid := 1%positive.
  Definition k : CallKey (F2 si) := (t, 0).
  Definition kG : CallKey (E_S rc) := (t, 10).
  Definition kA : CallKey (E_S rc) := (t, 11).
  Definition kX : CallKey (E_S rc) := (t, 12).
  Definition m : Regs := fun l => match l with Sq 0 => 2 | Sx 0 => 1 | Sy 0 => 1 | _ => 0 end.
  Definition A : AS := fun i => if Nat.eqb i 0 then (1, 1) else (0, 0).
  Definition recx : RelaxedTraceLin.Op (E_S rc) := RelaxedTraceLin.Build_Op kX (sRd (Sx 0)) 1.
  Definition VE := EIhl (E := E_S rc) δS.
  Definition VF := RelaxedHoareSpec.EI (F := F2 si) δF.
  Definition σ : State VE := ((m, [recx]), [kX; kA; kG]).
  Definition σ' : State VE := ((m, []), [kX; kA; kG]).
  Definition P : LinPool (F2 si) := [make_lin_entry k (@ls_inv (F2 si) (fR 0))].
  Definition γ : Ghost (E_S rc) (F2 si) := [Build_ScheduledEvent k (IE rc t 14 sRmb)].
  Definition p : Poss VF := @PossOk (F2 si) VF (A, []) P.
  Definition s : PState VE VF := (σ, p, γ).
  Definition s' : PState VE VF := (σ', p, γ).

  Lemma doom_vacuous_after_consumption key l w st :
    eihl_rec_used (E := E_S rc) δS (ps_mem st) -> eihl_done_res (E := E_S rc) δS key (ps_mem st) ->
    KDoomRd rc si key l w st /\ KMine rc si key (RelaxedTraceLin.Build_Op key (sRd l) w) st.
  Proof.
    intros Hru Hd. split.
    - exists (S w). split; [lia | exact (eihl_done_res_mine _ key _ _ Hru Hd)].
    - exact (eihl_done_res_mine _ key _ _ Hru Hd).
  Qed.

  Definition M24 (st : PState VE VF) : Prop :=
    exists (r0 ax : nat),
      KMine rc si kG (RelaxedTraceLin.Build_Op kG (sRd (Sq 0)) r0) st /\
      (eihl_done_res (E := E_S rc) δS kG (ps_mem st) -> r0 = 2) /\
      r0 <= regs rc si st (Sq 0) /\
      KMine rc si kX (RelaxedTraceLin.Build_Op kX (sRd (Sx 0)) ax) st /\
      (eihl_done_res (E := E_S rc) δS kX (ps_mem st) -> ax = 0) /\
      (forall A0 Pf0 P0, ps_poss st = @PossOk (F2 si) VF (A0, Pf0) P0 ->
         r0 = 2 -> regs rc si st (Sq 0) = 2 -> Nat.even 2 = true -> ax = fst (A0 0)).

  Lemma kX_kG : kX <> kG. Proof. unfold kX, kG. intros H. injection H. lia. Qed.

  Lemma m24_pre : M24 s.
  Proof.
    exists 2, 1. unfold KMine, eihl_mine, eihl_rec_used, eihl_done_res, regs, s, σ, ps_mem, ps_poss, p. cbn.
    split; [split; [intros x [<- | []]; left; reflexivity | split; [auto 10 | intros x [<- | []] Hk; exfalso; exact (kX_kG Hk)]] |].
    split; [reflexivity |]. split; [lia |].
    split; [split; [intros x [<- | []]; left; reflexivity | split; [left; reflexivity | intros x [<- | []] _; reflexivity]] |].
    split; [intros [_ Hn]; exfalso; exact (Hn recx (or_introl eq_refl) eq_refl) |].
    intros A0 Pf0 P0 Hp _ _ _. injection Hp as <- _ _. reflexivity.
  Qed.

  Lemma m24_post_false : ~ M24 s'.
  Proof.
    unfold M24, eihl_done_res, regs, s', σ', ps_mem, ps_poss, p. cbn.
    intros (r0 & ax & _ & HG & _ & _ & HX & Hv).
    specialize (HG (conj (or_intror (or_intror (or_introl eq_refl))) (fun x (H : In x []) => match H with end))).
    specialize (HX (conj (or_introl eq_refl) (fun x (H : In x []) => match H with end))).
    subst r0 ax. specialize (Hv A [] P eq_refl eq_refl eq_refl eq_refl). cbn in Hv. discriminate.
  Qed.

  Lemma rsl_step : Rsl rc si k s s'.
  Proof.
    unfold Rsl, s, s', ps_mem, ps_poss, ps_ghost, p, regs. cbn. split.
    - apply rt_step. exists (Build_ThreadEvent t (@ResEv (E_S rc) 12 (sRd (Sx 0)) 1)).
      cbn. split; [| reflexivity]. exists [], []. split; reflexivity.
    - exists A, [], P, A, [], P. split; [reflexivity |]. split; [reflexivity |].
      split; [auto |]. split; [auto |]. split; [tauto |]. split; [apply oldersub_refl |].
      split.
      + intros i _. unfold InstFrozen. auto.
      + intros i. split; [lia |]. intros _. split; [reflexivity | auto].
  Qed.

  Lemma islc_ok : IslC rc si tw m A [] P γ.
  Proof.
    constructor.
    - unfold lin_pool_well_formed, lin_domain. cbn. constructor; [intros [] | constructor].
    - split.
      + intros e [<- | []]. cbn. left. reflexivity.
      + intros i j e1 e2 H1 H2 Ho. exfalso.
        destruct i as [| i]; [| destruct i; discriminate]. cbn in H1. injection H1 as <-.
        destruct j as [| j]; [| destruct j; discriminate]. cbn in H2. injection H2 as <-.
        cbn in Ho. unfold key_older in Ho. inversion Ho; subst;
          repeat match goal with H : subseq _ [] |- _ => inversion H; clear H end.
    - constructor; [| constructor]. cbn. split; [reflexivity | exact I].
    - intros o [].
    - constructor.
    - intros e [<- | []]. cbn. split; [intros _ | reflexivity].
      exists (Build_ScheduledEvent k (IE rc t 14 sRmb)). split; [left; reflexivity |]. split; reflexivity.
    - intros e i vx vy [<- | []] H. discriminate.
    - intros i k1 k2 (vx & vy & ls & Hl & Hop). exfalso.
      destruct Hl as [Hl | []]. unfold make_lin_entry in Hl. injection Hl as _ _ Hls. subst ls. discriminate.
    - intros [| i] He; reflexivity.
    - intros [| i] He; discriminate.
    - constructor; [intros [] | constructor].
  Qed.

  Lemma isl_pre : Isl rc si tw s.
  Proof. exists A, [], P. split; [reflexivity |]. split; [intros x [<- | []]; left; reflexivity | exact islc_ok]. Qed.
  Lemma isl_post : Isl rc si tw s'.
  Proof. exists A, [], P. split; [reflexivity |]. split; [intros x [] | exact islc_ok]. Qed.

  Theorem m24_not_stable :
    Isl rc si tw s /\ M24 s /\ Rsl rc si k s s' /\ Isl rc si tw s' /\ ~ M24 s'.
  Proof. exact (conj isl_pre (conj m24_pre (conj rsl_step (conj isl_post m24_post_false)))). Qed.
End M24Scratch.
Print Assumptions fam_merge.
Print Assumptions M24Scratch.doom_vacuous_after_consumption.
Print Assumptions M24Scratch.m24_not_stable.
