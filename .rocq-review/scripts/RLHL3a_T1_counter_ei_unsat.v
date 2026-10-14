Require Import Stdlib.Lists.List Stdlib.PArith.PArith Stdlib.Arith.PeanoNat Stdlib.micromega.Lia Stdlib.Relations.Relation_Operators.
Require Import models.EffectSignatures models.RelaxedSignature models.LinCCAL models.simlin.RelaxedLTS models.simlin.RelaxedLang models.simlin.RelaxedSemantics models.simlin.RelaxedModuleSemantics models.simlin.RelaxedPossibility models.simlin.RelaxedHoareBase models.simlin.RelaxedHoareDag models.simlin.RelaxedHoare models.simlin.RelaxedHoareSound models.simlin.RelaxedTraceLin models.simlin.RelaxedHoareSpec.
Require Import examples.Relaxed.RelaxedHoareChecks.
Import ListNotations.
Module T1.
  Import LinCCALBase RelaxedSig RelaxedLTSSpec RelaxedLang RelaxedSemantics RelaxedModuleSemantics RelaxedPossibility RelaxedHoareBase RelaxedHoareDag RelaxedHoare RelaxedHoareSound.
  Import RelaxedHoareChecks.Counter RelaxedHoareChecks.CounterHL.
  Definition EVE : LTS USig := RelaxedHoareSpec.EI RelaxedHoareChecks.CounterRelLin.uδ.
  Theorem EVE_not_handle_linear used : ~ HandleLinear EVE used.
  Proof.
    intros Hhl.
    assert (H1 : Step EVE (Build_ThreadEvent t0 (@InvEv USig 0 FAA)) (0, []) (1, [@RelaxedTraceLin.Build_Op USig (t0, 0) FAA 0])).
    { cbn. exists 0, 1. split; [split; reflexivity | reflexivity]. }
    assert (H2 : Step EVE (Build_ThreadEvent t0 (@InvEv USig 0 FAA)) (1, [@RelaxedTraceLin.Build_Op USig (t0, 0) FAA 0]) (2, [@RelaxedTraceLin.Build_Op USig (t0, 0) FAA 1; @RelaxedTraceLin.Build_Op USig (t0, 0) FAA 0])).
    { cbn. exists 1, 2. split; [split; reflexivity | reflexivity]. }
    exact (hl_fresh _ _ Hhl t0 0 FAA _ _ H2 (hl_inv_used _ _ Hhl t0 0 FAA _ _ H1)).
  Qed.
  Theorem counter_ei_unsat (I : Assn EVE CVFe) (R G : CallKey OSig -> PRel EVE CVFe) (q0 : State EVE) (m0 : nat) :
    ~ RLHL2Hyps I R G Mc q0 (m0, []).
  Proof.
    intros HH. destruct q0 as [n0 l0].
    pose proof (h_sem _ _ _ _ _ _ HH) as Hsem.
    set (q1 := (S n0, @RelaxedTraceLin.Build_Op USig (t0, 0) FAA n0 :: l0) : State EVE).
    assert (Hfirst : forall r : nat, exists A0 m2 p1,
      CallTriple I R G key0 Inc r A0 /\ untag m2 = Build_ThreadEvent t0 (@ResEv USig 0 FAA r) /\
      A0 [m2] (q1, p1, []) /\ I (q1, p1, []) /\ Good m0 p1 /\
      exists v pool, p1 = @PossOk OSig CVFe v pool /\ lin_domain pool = [key0]).
    { intros r. destruct (inc_trace_gen t0 0 r) as (tr & Hprod & Htr).
      destruct (Hsem t0 Inc 0 tr r Hprod) as (A0 & Htri & Hinit0).
      set (p0 := @PossOk OSig CVFe (m0, []) [make_lin_entry key0 (@ls_inv OSig Inc)]).
      assert (Hpi : poss_invoke CVFe t0 0 Inc (@PossOk OSig CVFe (m0, []) []) p0) by (constructor; constructor; intros []).
      destruct (Hinit0 (n0, l0) _ [] p0 (h_init _ _ _ _ _ _ HH) Hpi) as [HI0 HA0].
      destruct tr as [| m1 [| m2 [| m3 tr]]]; try discriminate. cbn in Htr. injection Htr as H1 H2.
      unfold ghost_new in HI0, HA0. cbn [app map] in HI0, HA0. rewrite H1, H2 in HI0, HA0.
      cbn [inv_events te_ev map] in HI0, HA0.
      pose proof Htri as [Hemit _ _].
      destruct (Hemit [] m1 [m2] ltac:(constructor) (n0, l0) p0 _ [] ltac:(rewrite H1; cbn; exists [], []; split; [reflexivity | split; [reflexivity | constructor]]) HA0 HI0 q1 ltac:(rewrite H1; cbn; exists n0, (S n0); split; [split; reflexivity | reflexivity]))
        as (p1 & Hps & HA1 & HI1 & _).
      exists A0, m2, p1. split; [exact Htri |]. split; [exact H2 |]. split; [exact HA1 |]. split; [exact HI1 |].
      split.
      - eapply good_steps; [exact Hps |]. exists m0, [], [], (@ls_inv OSig Inc).
        split; [reflexivity |]. split; [left; reflexivity |]. split; [reflexivity |].
        split; [intros o [] | exact Logic.I].
      - destruct (h_ok _ _ _ _ _ _ HH _ HI1) as (v & pool & Hp1 & _). cbn in Hp1. subst p1.
        exists v, pool. split; [reflexivity |].
        rewrite <- (poss_steps_ok_domain CVFe _ _ _ _ Hps). reflexivity. }
    assert (HA : n0 = m0).
    { destruct (Hfirst n0) as (A0 & m2 & p1 & [Hemit _ Hret] & Hm2 & HA1 & HI1 & HG1 & _).
      destruct (Hemit [] m2 [] ltac:(constructor) q1 p1 [] [] ltac:(rewrite Hm2; reflexivity) HA1 HI1 (S n0, l0)
                  ltac:(rewrite Hm2; cbn; exists [], l0; split; reflexivity))
        as (p2 & Hps2 & HA2 & HI2 & _).
      destruct (Hret _ HA2 HI2 ltac:(intros e [])) as (p3 & Hps3 & (v & pool & -> & Hl) & _).
      exact (good_linr m0 v pool n0 (good_steps _ _ _ (rt_trans _ _ _ _ _ Hps2 Hps3) HG1) Hl). }
    assert (HB : S n0 = m0).
    { destruct (Hfirst (S n0)) as (A0 & m2 & p1 & [Hemit0 Hstab0 Hret0] & Hm2 & HA1 & HI1 & HG1 & v & pool & -> & Hdom).
      destruct (inc_trace_gen t0 0 0) as (tr1 & Hprod1 & Htr1).
      destruct (Hsem t0 Inc 1 tr1 0 Hprod1) as (A1 & [Hemit1 _ _] & Hinit1).
      set (p1' := @PossOk OSig CVFe v (make_lin_entry key1 (@ls_inv OSig Inc) :: pool)).
      assert (Hpi : poss_invoke CVFe t0 1 Inc (@PossOk OSig CVFe v pool) p1').
      { constructor. constructor. unfold lin_fresh. rewrite Hdom. intros [H | []]. discriminate H. }
      destruct (Hinit1 q1 _ [] p1' HI1 Hpi) as [HI1' HA1'].
      pose proof (h_invoke_rely _ _ _ _ _ _ HH key1 key0 Inc tr1 0 (q1, @PossOk OSig CVFe v pool, []) p1'
                    ltac:(discriminate) Hprod1 HI1 Hpi) as HR.
      pose proof (Hstab0 [m2] _ _ HA1 HR HI1') as HA0'. cbn [ps_mem ps_ghost snd fst] in HA0'.
      destruct tr1 as [| n1 [| n2 [| n3 tr1]]]; try discriminate. cbn in Htr1. injection Htr1 as H1 H2.
      cbn [ps_mem ps_ghost snd fst] in HA0', HI1', HA1'.
      unfold ghost_new in HI1', HA1', HA0'. cbn [app map] in HI1', HA1', HA0'. rewrite H1, H2 in HI1', HA1', HA0'.
      cbn [inv_events te_ev map] in HI1', HA1', HA0'.
      set (q2 := (S (S n0), @RelaxedTraceLin.Build_Op USig (t0, 0) FAA (S n0) :: @RelaxedTraceLin.Build_Op USig (t0, 0) FAA n0 :: l0) : State EVE).
      destruct (Hemit1 [] n1 [n2] ltac:(constructor) q1 p1' _ [] ltac:(rewrite H1; cbn; exists [], []; split; [reflexivity | split; [reflexivity | constructor]]) HA1' HI1' q2 ltac:(rewrite H1; cbn; exists (S n0), (S (S n0)); split; [split; reflexivity | reflexivity]))
        as (p2 & Hps2 & _ & HI2 & HG2).
      pose proof (h_guar_rely _ _ _ _ _ _ HH key1 key0 _ _ ltac:(discriminate) HG2) as HR2.
      pose proof (Hstab0 [m2] _ _ HA0' HR2 HI2) as HA2.
      destruct (Hemit0 [] m2 [] ltac:(constructor) q2 p2 [] [] ltac:(rewrite Hm2; reflexivity) HA2 HI2 (S (S n0), @RelaxedTraceLin.Build_Op USig (t0, 0) FAA n0 :: l0)
                  ltac:(rewrite Hm2; cbn; exists [], (@RelaxedTraceLin.Build_Op USig (t0, 0) FAA n0 :: l0); split; reflexivity))
        as (p3 & Hps3 & HA3 & HI3 & _).
      destruct (Hret0 _ HA3 HI3 ltac:(intros e [])) as (p4 & Hps4 & (v4 & pool4 & -> & Hl) & _).
      assert (HG2' : Good m0 p2) by exact (good_steps _ _ _ Hps2 (good_invoke1 _ _ _ HG1 Hpi)).
      exact (good_linr m0 v4 pool4 (S n0) (good_steps _ _ _ (rt_trans _ _ _ _ _ Hps3 Hps4) HG2') Hl). }
    lia.
  Qed.
End T1.
Print Assumptions T1.EVE_not_handle_linear.
Print Assumptions T1.counter_ei_unsat.
