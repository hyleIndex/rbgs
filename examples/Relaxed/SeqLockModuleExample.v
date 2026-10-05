(** * SeqLockModuleExample: non-vacuity of [SeqLockModule.seqlock_module_rel_lin]

    A concrete module execution of the SeqLock module [M false SL.plainTL]
    with one overlay call [write(1,1)] by thread 1.  The underlay trace is
    the six calls of the write path
      [acq; wmb; x.wrt 1; y.wrt 1; wmb; rel]
    with their future-store tags exactly as produced by [RelaxedLang].

    We exhibit
    - the program run ([write_produces]) and the module execution
      ([w_execution]), complete (empty queue, all calls dead);
    - an underlay witness [W_w] establishing [rel_lin] for the underlay
      ([w_underlay_rel_lin]);
    and then apply the module-level theorem to obtain overlay [rel_lin]
    ([seqlock_module_nonvacuous]).  This shows that the hypotheses of
    [seqlock_module_rel_lin] are jointly satisfiable and that the
    conclusion is about a non-empty overlay history. *)
From Stdlib Require Import List Arith.PeanoNat PArith micromega.Lia.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedTraceLin.
Require Import examples.Relaxed.BracketedLink.
Require Import examples.Relaxed.SeqLockCOH.
Require Import examples.Relaxed.SeqLockProg.
Require Import examples.Relaxed.SeqLockModule.
Import ListNotations.
Import LinCCALBase RelaxedSig RelaxedLTSSpec RelaxedLang RelaxedSemantics RelaxedModuleSemantics RelaxedTraceLin.
Import SeqLockProg.SeqLockProg.
Module BL := BracketedLink.BracketedLink.
Module SLM := SeqLockModule.SeqLockModule.

Abbreviation G := (E false SL.plainTL).
Abbreviation FF := (F false).

Definition VE0 : LTS G := {| State := unit; Step := fun _ _ _ => True; Error := fun _ _ => False |}.
Definition t1 : tid := 1%positive.

Definition S1 : FutureStore G := [Build_FutureEntry (E := G) 0 (Resolved (E := G) sAcq tt)].
Definition S2 : FutureStore G := Build_FutureEntry (E := G) 1 (Resolved (E := G) sWmb tt) :: S1.
Definition S3 : FutureStore G := Build_FutureEntry (E := G) 2 (Resolved (E := G) (sWrX 1) tt) :: S2.
Definition S4 : FutureStore G := Build_FutureEntry (E := G) 3 (Resolved (E := G) (sWrY 1) tt) :: S3.
Definition S5 : FutureStore G := Build_FutureEntry (E := G) 4 (Resolved (E := G) sWmb tt) :: S4.

Definition iv (h : nat) (o : SOp) (H : FutureStore G) : TaggedEvent G :=
  Build_TaggedEvent (Build_ThreadEvent t1 (@InvEv G h o)) (resolved_in H).
Definition rs (h : nat) (o : SOp) : TaggedEvent G :=
  Build_TaggedEvent (Build_ThreadEvent t1 (@ResEv G h o (dflt o))) no_deps.

Definition wtr : list (TaggedEvent G) :=
  [iv 0 sAcq []; rs 0 sAcq; iv 1 sWmb S1; rs 1 sWmb; iv 2 (sWrX 1) S2; rs 2 (sWrX 1);
   iv 3 (sWrY 1) S3; rs 3 (sWrY 1); iv 4 sWmb S4; rs 4 sWmb; iv 5 sRel S5; rs 5 sRel].

Lemma write_produces : program_produces_tagged t1 (M false SL.plainTL (fWrite 1 1) t1) wtr tt.
Proof.
  eexists. split.
  - cbn [M]. unfold write, initial_program, wtr.
    eapply tagged_execution_emit; [apply tagged_future; unfold handle_fresh; cbn; tauto |]. cbn beta.
    eapply tagged_execution_emit; [eapply tagged_wait_pending; apply resolve_here |]. cbn beta.
    eapply tagged_execution_emit; [apply tagged_future; unfold handle_fresh; cbn; intuition discriminate |]. cbn beta.
    eapply tagged_execution_emit; [eapply tagged_resolve; apply resolve_here |].
    eapply tagged_execution_emit; [apply tagged_future; unfold handle_fresh; cbn; intuition discriminate |]. cbn beta.
    eapply tagged_execution_emit; [eapply tagged_resolve; apply resolve_here |].
    eapply tagged_execution_emit; [apply tagged_future; unfold handle_fresh; cbn; intuition discriminate |]. cbn beta.
    eapply tagged_execution_emit; [eapply tagged_resolve; apply resolve_here |].
    eapply tagged_execution_emit; [apply tagged_future; unfold handle_fresh; cbn; intuition discriminate |]. cbn beta.
    eapply tagged_execution_emit; [eapply tagged_resolve; apply resolve_here |].
    eapply tagged_execution_emit; [apply tagged_future; unfold handle_fresh; cbn; intuition discriminate |]. cbn beta.
    eapply tagged_execution_emit; [eapply tagged_resolve; apply resolve_here |].
    do 5 (eapply tagged_execution_silent; [apply tagged_wait_resolved; cbn; tauto | cbn beta]).
    apply tagged_execution_refl.
  - constructor. repeat constructor.
Qed.

Definition T_w : list (ModuleEvent G FF) :=
  OverlayEvent (Build_ThreadEvent t1 (@InvEv FF 0 (fWrite 1 1))) ::
  map (fun m => UnderlayEvent (untag m)) wtr ++
  [OverlayEvent (Build_ThreadEvent t1 (@ResEv FF 0 (fWrite 1 1) tt))].

Ltac ustep ev :=
  eapply tagged_module_execution_cons;
  [ eapply tagged_underlay with (candidate := Build_TaggedScheduledEvent (F := FF) (t1, 0) ev) (q' := tt);
    [cbn; apply tagged_select_here | exact I] | ].

Lemma w_execution : exists c,
  module_execution_tagged VE0 (M false SL.plainTL) (initial_tagged_module VE0 tt) T_w c /\
  tm_queue c = [] /\ (forall e, In e (tm_calls c) -> ce_cell FF e = DeadCall).
Proof.
  eexists. split; [| split].
  - unfold T_w.
    eapply tagged_module_execution_cons.
    { apply tagged_invoke; [unfold call_fresh; cbn; tauto | exact write_produces |].
      split.
      - cbn. repeat constructor; cbn; intuition discriminate.
      - intros key _ []. }
    cbn [map app wtr].
    ustep (iv 0 sAcq []). ustep (rs 0 sAcq). ustep (iv 1 sWmb S1). ustep (rs 1 sWmb).
    ustep (iv 2 (sWrX 1) S2). ustep (rs 2 (sWrX 1)). ustep (iv 3 (sWrY 1) S3). ustep (rs 3 (sWrY 1)).
    ustep (iv 4 sWmb S4). ustep (rs 4 sWmb). ustep (iv 5 sRel S5). ustep (rs 5 sRel).
    eapply tagged_module_execution_cons.
    { eapply tagged_return; [apply finish_here | intros []]. }
    apply tagged_module_execution_refl.
  - reflexivity.
  - intros e [<- | []]. reflexivity.
Qed.

Definition W_w : list (Op G) :=
  [Build_Op (E := G) (t1, 0) sAcq tt; Build_Op (E := G) (t1, 1) sWmb tt;
   Build_Op (E := G) (t1, 2) (sWrX 1) tt; Build_Op (E := G) (t1, 3) (sWrY 1) tt;
   Build_Op (E := G) (t1, 4) sWmb tt; Build_Op (E := G) (t1, 5) sRel tt].

Lemma w_inv_pos i k op :
  inv_at BL.under_sel T_w i k op -> exists h, h < 6 /\ k = (t1, h) /\ i = 2 * h + 1.
Proof.
  intros (x & Hx & Hs).
  do 14 (destruct i as [|i]; [cbn in Hx; injection Hx as <-; cbn in Hs; try discriminate;
     injection Hs as Ht Hh _; destruct k as [tk hk]; cbn in Ht, Hh; subst tk hk;
     (eexists; split; [| split; reflexivity]); lia |]).
  cbn in Hx. destruct i; discriminate.
Qed.

Lemma w_res_pos i k op v :
  res_at BL.under_sel T_w i k op v -> exists h, h < 6 /\ k = (t1, h) /\ i = 2 * h + 2.
Proof.
  intros (x & Hx & Hs).
  do 14 (destruct i as [|i]; [cbn in Hx; injection Hx as <-; cbn in Hs; try discriminate;
     apply (f_equal (option_map (fun ev => (te_tid G ev, event_handle (te_ev G ev))))) in Hs;
     cbn in Hs; injection Hs as Ht Hh; destruct k as [tk hk]; cbn in Ht, Hh; subst tk hk;
     (eexists; split; [| split; reflexivity]); lia |]).
  cbn in Hx. destruct i; discriminate.
Qed.

Lemma w_underlay_rel_lin :
  rel_lin BL.under_sel T_w (semi_independent G)
    (BL.nuE_all (E := G) SL.comp_dec SLM.compE (SLM.nuEc false SL.plainTL)).
Proof.
  exists W_w. split; [| split; [| split; [| split]]].
  - intros [|]; cbn; repeat split.
  - cbn. repeat constructor; cbn; intuition congruence.
  - intros o Ho. destruct Ho as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; split;
      [exists 1 | exists 2 | exists 3 | exists 4 | exists 5 | exists 6 | exists 7 | exists 8
      | exists 9 | exists 10 | exists 11 | exists 12]; eexists; split; reflexivity.
  - intros i k op Hi. destruct (w_inv_pos i k op Hi) as (h & Hh & -> & _).
    exists (nth h W_w (Build_Op (E := G) (t1, 0) sAcq tt)). split; [|do 6 (destruct h as [|h]; [reflexivity|]); lia].
    apply nth_In. cbn. lia.
  - intros o o' Ho Ho' Hr.
    assert (Hlt : snd (op_key o) < snd (op_key o')).
    { destruct Hr as [(i & j & Hi & Hj & Hij) | (_ & i & j & Hi & Hj & Hij & _)].
      - destruct (w_res_pos _ _ _ _ Hi) as (h & _ & Hk & ->).
        destruct (w_inv_pos _ _ _ Hj) as (h' & _ & Hk' & ->).
        rewrite Hk, Hk'. cbn. lia.
      - destruct (w_inv_pos _ _ _ Hi) as (h & _ & Hk & ->).
        destruct (w_inv_pos _ _ _ Hj) as (h' & _ & Hk' & ->).
        rewrite Hk, Hk'. cbn. lia. }
    unfold W_w in Ho, Ho'.
    destruct Ho as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
      destruct Ho' as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
      cbn in Hlt; try lia; unfold before, W_w;
      first [ (eexists [], _; split; [reflexivity | cbn; tauto])
            | (eexists [_], _; split; [reflexivity | cbn; tauto])
            | (eexists [_; _], _; split; [reflexivity | cbn; tauto])
            | (eexists [_; _; _], _; split; [reflexivity | cbn; tauto])
            | (eexists [_; _; _; _], _; split; [reflexivity | cbn; tauto]) ].
Qed.

Theorem seqlock_module_nonvacuous : exists T c,
  module_execution_tagged VE0 (M false SL.plainTL) (initial_tagged_module VE0 tt) T c /\
  tm_queue c = [] /\ (forall e, In e (tm_calls c) -> ce_cell FF e = DeadCall) /\
  rel_lin BL.under_sel T (semi_independent G)
    (BL.nuE_all (E := G) SL.comp_dec SLM.compE (SLM.nuEc false SL.plainTL)) /\
  rel_lin BL.over_sel T (semi_independent FF) (BL.nuF_all (F := FF) SL.comp_dec fcomp (SLM.nuFc false)) /\
  inv_at BL.over_sel T 0 (t1, 0) (fWrite 1 1).
Proof.
  destruct w_execution as (c & Hx & Hq & Hd).
  exists T_w, c. split; [exact Hx|]. split; [exact Hq|]. split; [exact Hd|].
  split; [exact w_underlay_rel_lin|].
  split; [exact (SLM.seqlock_module_rel_lin false VE0 tt T_w c Hx Hq Hd w_underlay_rel_lin)|].
  eexists. split; reflexivity.
Qed.
