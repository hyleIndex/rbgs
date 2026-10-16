(** * RLHL, part 15: the history presentation [Log VE] and [EIhlv]
      (RLHL-seqlock task .L; option B of the reader evaluation)

    Plan: .rocq-review/tasks/RLHL-seqlock.md, Addendum 3 (author decision
    "option B"), task .L; design in
    .rocq-review/tasks/RLHL-seqlock-reader-eval.md §4 and
    RLHL-seqlock-reader-eval/eval1.md.  Parts 1-3 and the core of Part 4
    port the closed scratch .rocq-review/scripts/RLHLsl_readerB_loglift.v
    (statements unchanged); the m-59 variant, the side-field transfer and
    Parts 5-7 are new.  The program logic is unchanged: [PState],
    [ghost_emit], [CallTriple], [RProvable], [method_sound] and
    [rlhl_gsim] are generic in the underlay [VE] and are only
    instantiated here.

    ** Why a history presentation

    The decided underlay presentation [RelaxedHoareCompLinSpec.EIhl δ]
    (decisions M-16, M-20, m-20) is lossy.  An [EI] response deletes its
    record, and the used-key list of [EIhl] keeps only the key
    [(tid, handle)].  Once a record is consumed its value is gone from the
    proof state: [eihl_mine κ x0] then holds for every [x0]
    ([RelaxedHoareRun.eihl_done_res_mine]).  So the fact "record value =
    response value" is available only in the precondition of that
    response's own slot ([eihl_mine_res]); and a fact "the consumed record
    of κ had value v" is not stable under a rely that admits any [EIhl]
    step, because another call's step that consumes the record is the
    same [EIhl] transition (reader evaluation §1.2, scratch lemma
    [m24_not_stable]).  A method that validates after reading needs such
    facts at its return: the reader of [RelaxedHoareSL2Prog] combines four
    record values with the abstract value seen at its linearization
    point.  By the reader evaluation (§1-2; argued, not mechanized) it has
    no [MethodProvable] derivation over [EIhl] with the frozen invariant.

    [Log VE] adds the list of the underlay events taken so far.  Over
    [EIhlv δ := Log (EIhl δ)] the record history [recs] (the pending
    records, then the records consumed by the logged responses) keeps
    every record with its value for ever: [LogVal x] names a value
    permanently, [LogOK] gives one value per key ([logval_unique]), and
    [logval_step] makes [LogVal] stable under every step of every thread.
    This is the history half of the auxiliary-variable device (history
    variables, Owicki-Gries; Abadi-Lamport).  It restores the underlay
    projection of the paper's proof state [s]: Appendix/programlogic.tex
    :530 ([s] is the concrete trace of all events, including both overlay
    invocations and their underlay actions), :579 (rule EStep,
    [σ'.s = σ.s · t:e]) and :549 (the simulation quantifies over
    [(t, poss) ∈ I], [t] a trace).  The overlay invocations of [s] and
    the reachability clause [σ'.s ∈ ⟦M⟧] (cyan) of :579 are not
    represented.  [EIhl] is a lossy abstraction of that state and [Log]
    restores the missing underlay component, as [HL] restored
    handle-linearity; like [HL] it is justified by a closed trace
    equivalence ([loglift]).  (Line numbers as in async-ccal commit
    4a2db8e1, 42 higher than in 01484091 from :511 on; see the note before
    the table of [RelaxedHoare], review m-67.)

    No prophecy variable is added (latest-review m-36).  The ghost stores
    no response values, but its remaining invocations, committed at
    invocation, determine the outcome of the call's own future
    validation: the SeqLock read LP ([RelaxedHoareSL2Inv.isl_read_lp],
    at the read's last [rmb]) is such a future-dependent LP under a
    single possibility.  It is sound by run-to-completion (impl.tex:141,
    :172: the body trace is fixed when the call is invoked); cf.
    Appendix/relaxedlin.tex:520, :628, which say single possibilities
    are not generally sufficient for future-dependent LPs (review m-65).
    LPs that depend on the future behaviour of other calls, which no
    committed own invocation determines, are not covered by this device,
    and no such example is mechanized.  This file does not make RLHL
    complete: implex.tex:3 ("RLHL is complete with respect to relaxed
    linearizability") stays unsupported.

    ** Part 1: [Log VE] and the trace equivalence
    - [Log VE]: state [(σ, l)], step [Step VE ev σ σ' ∧ l' = ev :: l],
      [Error] of the base part.  [log_steps]: any number of [Log] steps;
      [LogMono X]: [X] is kept by every step; [log_steps_mono],
      [log_steps_step], [log_steps_refl], [log_steps_suffix] (the log only
      grows), [log_steps_base].  [log_handle_linear].
    - [loglift]: [MTraces VE M σ0 s <-> MTraces (Log VE) M (σ0, []) s],
      for every [VE], [M], [σ0] (no step is disabled, so unlike
      [RelaxedHoareCompLinSpec.hlift] no invariant is needed);
      [complin_log_under].

    ** Part 2: [EIhlv] and the value kit
    - [EIhlv δ := Log (EIhl δ)], state [((((s, U), used), log)];
      [EIhlv_handle_linear]; [loglift_ei] (traces over [EI δ], [EIhl δ]
      and [EIhlv δ] coincide).
    - [recs], [LogVal], [LogOK]; [logok_init], [logok_step]/[_mono]/
      [_steps]; [logval_step]/[_mono]/[_steps]; [logval_unique] (one value
      per key); [logval_val_dec] (the value itself, for signatures with
      decidable operations, by [Eqdep_dec]); [logval_res] (a response
      returns the logged value of its key); [logval_res_logged] (a
      response logs its own record); [logval_inv] (an invocation logs a
      record whose value [δ] chose); [logval_pending]; [logok_rec_used]
      ([LogOK] gives [eihl_rec_used] on the base part); [log_steps_eihl]
      (the base part of [log_steps] is [eihl_steps]).

    ** Part 3: the conclusion over the plain [EI δ]
    - [rlhl_complin_eihlv]: [RLHL2Hyps] over [EIhlv δ] from
      [((σ0, []), [])] give [RCompLin M (EI δ) σ0 (EI δF) (s0, [])]
      ([rlhl_complin_ei], then [complin_log_under] and
      [complin_hlift_under]).
    - [rlhl_eihlv_rel_lin]: then [complin_ei_rel_lin] ([cc_rel_lin]):
      every complete overlay trace over [EI δ] is relaxed-linearizable to
      [seq_legal δF s0].

    ** Part 4: lifting assertions and relations (generic in [VE], [VF])
    - [dropS] (the base part of a proof state), [liftA P], [liftG g]
      (base relation, log unconstrained), [liftGL g] := [liftG g] and the
      memory moves by [log_steps], [liftGLk] (the family), [logA X] (a fact
      about the lifted memory), [liftI J I] := [I] on the base part and
      [J] on the lifted memory, for an invariant [J] kept by every step
      ([LogOK] for [EIhlv]).
    - Stability: [stable_lift], [stable_liftL]; [stable_logA]: every
      [LogMono] fact is stable under every [liftGL r]; [Stable_ex].
    - Updates: [evupdate_lift] (the scratch version, guarantee [liftG g]);
      the m-59 variant [evupdate_liftL] (guarantee [liftGL g], which
      contains the event's own [Log] step), its general form
      [evupdate_liftL_gen] (arbitrary lifted pre and post, which may
      mention the log; [J] and the log move are discharged), and
      [evupdate_liftL_with] (base update plus log facts carried across the
      step); [evupdate_conseq], [evupdate_ex].
    - [postinvoke_lift], [retcond_lift] (for [mp_PI] and [mp_ret]).
    - Side fields of [RLHL2Hyps], each from its base version:
      [guar_rely_lift] ([h_guar_rely]), [invoke_rely_lift]
      ([h_invoke_rely]), [return_rely_lift] ([h_return_rely]), [ok_lift]
      ([h_ok]), [init_lift] ([h_init]; needs [J (σ0, [])]).
      [methodsem_lift] ([h_sem], semantically) and [rlhl2_lift] (the whole
      record).  [rlhl2_lift_of_provable]: derivations over [Log VE] plus
      the base side fields give [RLHL2Hyps] over [Log VE]; this is the
      shape the SeqLock needs, since its reader is derived over [EIhlv]
      directly.

    ** Part 5: lifting derivations
    - [liftSlot] (assertions by [liftA], guarantee by [liftGL], same
      event); [newslotok_lift], [barrierwith_lift], [close_lift],
      [rprovable_lift] (by [RProvable_coind]) and [methodprovable_lift]:
      every [MethodProvable] derivation over [VE] is one over [Log VE],
      with invariant [liftI J I], rely and guarantee [liftGLk], and
      postcondition [liftA Q].  An admissibility result about the
      existing rules, not a new rule.
    - [slot_post_and], [newslotok_post_and]: strengthen the post of a new
      slot by a fact its own event establishes (generic in the underlay).

    ** Part 6: the [EIhlv] assembly
    - [liftIV I := liftI LogOK I].  [rlhl2_eihlv_of_provable]: derivations
      over [EIhlv δ] for every thread and operation (the [∃ Ω Q] shape of
      [RelaxedHoareCompLin.rlhl_sound_complin]) and the five side fields
      over [EIhl δ] give [RLHL2Hyps] over [EIhlv δ] from
      [((((sE, []), []), [])].  [rlhl_sound_complin_eihlv],
      [rlhl_sound_rel_lin_eihlv]: the conclusions of Part 3.

    ** Part 7: smoke test ([RunCounterLog])
    - (a) [counter_run_provable_v]: the [EIhl] derivation
      [RelaxedHoareRun.ren_run_provable] of the SI = ∅ FAA→Inc counter
      [RelaxedHoareRun.RunCounter], transferred by
      [methodprovable_lift]; [counter_run_rlhl2_v]: with the side fields
      of [RunCounter.counter_run_rlhl2] transferred.
    - (b) [counter_log_provable]: a direct [run_method_provable] (hence
      [rp_run]) derivation over [EIhlv uδ] whose postcondition [QlogC]
      also says that the call's underlay record [FAA ↦ r] is in the
      history.  The response slot establishes it ([slot_post_and],
      [logval_res_logged]); the final edge keeps it under the lifted rely
      ([stable_logA]).  [counter_log_rlhl2_v], [counter_log_complin],
      [counter_log_rel_lin].

    ** K / S / P / R
    - K (Print Assumptions, Rocq 9.3.0): 71 of the 77
      [Lemma]/[Theorem]/[Corollary] results are closed.
      [rlhl_complin_eihlv], [rlhl_sound_complin_eihlv] and
      [RunCounterLog.counter_log_complin] use [Classical_Prop.classic],
      inherited from [RelaxedHoareCompLin.rlhl_complin_ei] (through
      [rinv_val]), exactly as [rlhl_complin_eihl].
      [rlhl_eihlv_rel_lin], [rlhl_sound_rel_lin_eihlv] and
      [RunCounterLog.counter_log_rel_lin] use [classic] and
      [Eqdep.Eq_rect_eq.eq_rect_eq], the latter inherited from
      [RelaxedGSim.gsim_rel_lin] through [cc_rel_lin].  No proof in this
      file uses an axiom directly.
    - S: Parts 1, 2, 4 and 5 hold for every underlay, overlay, module and
      invariant [J] kept by every step.  [rlhl_complin_eihlv] covers every
      trace over the plain [EI δ], complete or not; the rel_lin
      corollaries cover complete traces.  Part 6 starts from an [EI δ]
      state with no pending record ([(sE, [])]), as [LogOK] requires.
      The smoke test is the one-operation counter at SI = ∅ with
      one-call bodies: it shows that the transfer and the history kit
      work inside [rp_run] derivations, and nothing about the SeqLock.
    - P: Appendix/programlogic.tex:530, :579 and :549 (the proof state
      carries the trace; [Log] restores only its underlay projection, see
      above).  implex.tex:3 and relatedwork.tex:32 (completeness): not
      supported, see above.
    - R: infrastructure for popl2027-reviews.md:215 ("No example verified
      on the COH model") through the SeqLock tasks .4v-.7; it answers no
      reviewer concern by itself.

    ** Limitations, and what is not here
    - [sl_logval_rd] of the scratch (two logged values of one [sRd] key
      are equal) is not in this file, because the file is generic and is
      listed before [RelaxedHoareSL2Prog] in _CoqProject.  It is one line
      in the SeqLock lifting file (.4v):
      [rd_rec_inj key l v w (logval_unique (E := E_S rc) δS σ _ _ Hok Hv Hw eq_refl)]
      (now [RelaxedHoareSL2InvLog.sl_logval_rd]).  [logval_val_dec] is
      the generic form.
    - [liftSlot] and [methodprovable_lift] add no log fact; a derivation
      that uses the history adds it explicitly ([slot_post_and], or slots
      written over [EIhlv] directly, as the SeqLock reader must).
    - This file does not contain the SeqLock reader derivation over
      [EIhlv].  It is [RelaxedHoareSL2Read.read_provable_v] (the sketch
      of eval1.md §3, completed with the gaps G1-G6 recorded in
      [RelaxedHoareSL2InvLog]).
    - [Log]'s [Error] is the base [Error] on the base part ([EI]'s is
      [False]). *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Sorting.Permutation.
Require Import Stdlib.Relations.Relation_Operators.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Logic.Eqdep_dec.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedPossibility.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.view.PrefixView.
Require Import models.simlin.RelaxedHoareBase.
Require Import models.simlin.RelaxedHoareDag.
Require Import models.simlin.RelaxedHoare.
Require Import models.simlin.RelaxedHoareSound.
Require Import models.simlin.RelaxedHoareSpec.
Require Import models.simlin.RelaxedHoareGSim.
Require Import models.simlin.RelaxedHoareCompLin.
Require Import models.simlin.RelaxedHoareCompLinSpec.
Require Import models.simlin.RelaxedHoareInherit.
Require Import models.simlin.RelaxedHoareRun.

Import ListNotations.


Module RelaxedHoareLog.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedPossibility.
  Import RelaxedTraceLin.
  Import RelaxedHoareBase.
  Import RelaxedHoareDag.
  Import RelaxedHoare.
  Import RelaxedHoareCompLin.
  Import RelaxedHoareCompLinSpec.

  (** ** Part 1. The history presentation [Log VE] *)

  Section Log.
    Context {E : RelaxedSig.t} (VE : LTS E).

    (** A state of [Log VE] is a state of [VE] with the list of the
        underlay events taken so far, newest first.  A step is a step of
        [VE] that prepends its event. *)
    Definition logx_step (ev : ThreadEvent E) (σ σ' : State VE * list (ThreadEvent E)) : Prop :=
      Step VE ev (fst σ) (fst σ') /\ snd σ' = ev :: snd σ.

    Definition Log : LTS E :=
      {| State := (State VE * list (ThreadEvent E))%type; Step := logx_step;
         Error := fun ev σ => Error VE ev (fst σ) |}.

    (** Any number of [Log VE] steps, of any thread and operation. *)
    Definition log_steps : State Log -> State Log -> Prop :=
      clos_refl_trans _ (fun σ σ' => exists ev, Step Log ev σ σ').

    (** [X] is kept by every step. *)
    Definition LogMono (X : State Log -> Prop) : Prop :=
      forall ev σ σ', Step Log ev σ σ' -> X σ -> X σ'.

    Lemma log_steps_mono (X : State Log -> Prop) σ σ' : LogMono X -> log_steps σ σ' -> X σ -> X σ'.
    Proof.
      intros HX. induction 1 as [σ σ' (ev & Hs) | σ | σ σ1 σ' _ IH1 _ IH2]; auto.
      exact (HX ev σ σ' Hs).
    Qed.

    Lemma log_steps_step ev σ σ' : Step Log ev σ σ' -> log_steps σ σ'.
    Proof. intros Hs. apply rt_step. exists ev. exact Hs. Qed.

    Lemma log_steps_refl σ : log_steps σ σ.
    Proof. apply rt_refl. Qed.

    (** The log only grows. *)
    Lemma log_steps_suffix σ σ' : log_steps σ σ' -> exists l, snd σ' = l ++ snd σ.
    Proof.
      induction 1 as [σ σ' (ev & _ & Hl) | σ | σ σ1 σ' _ (l1 & H1) _ (l2 & H2)].
      - exists [ev]. exact Hl.
      - exists []. reflexivity.
      - exists (l2 ++ l1). rewrite H2, H1. apply app_assoc.
    Qed.

    (** The base parts move by base steps. *)
    Lemma log_steps_base σ σ' :
      log_steps σ σ' -> clos_refl_trans _ (fun a b => exists ev, Step VE ev a b) (fst σ) (fst σ').
    Proof.
      induction 1 as [σ σ' (ev & Hs & _) | σ | σ σ1 σ' _ IH1 _ IH2].
      - apply rt_step. exists ev. exact Hs.
      - apply rt_refl.
      - eapply rt_trans; eauto.
    Qed.

    (** [Log] keeps handle-linearity, with the same [used] read off the
        base state. *)
    Lemma log_handle_linear used : HandleLinear VE used -> HandleLinear Log (fun σ k => used (fst σ) k).
    Proof.
      intros [H1 H2 H3]. constructor.
      - intros t h op σ σ' [Hs _]. exact (H1 t h op _ _ Hs).
      - intros ev σ σ' k [Hs _]. exact (H2 ev _ _ k Hs).
      - intros t h op σ σ' [Hs _]. exact (H3 t h op _ _ Hs).
    Qed.

    Context {G : RelaxedSig.t} (M : RelaxedModuleImpl E G).

    Definition lift_cfgL (c : @TaggedModuleConfig E G VE) (l : list (ThreadEvent E)) : @TaggedModuleConfig E G Log :=
      @Build_TaggedModuleConfig E G Log (tm_lts_state c, l) (tm_calls c) (tm_queue c) (tm_used_underlay c).

    Definition drop_cfgL (c : @TaggedModuleConfig E G Log) : @TaggedModuleConfig E G VE :=
      @Build_TaggedModuleConfig E G VE (fst (tm_lts_state c)) (tm_calls c) (tm_queue c) (tm_used_underlay c).

    Lemma liftL_step ev c c' l :
      module_step_tagged VE M ev c c' -> exists l', module_step_tagged Log M ev (lift_cfgL c l) (lift_cfgL c' l').
    Proof.
      destruct 1 as [t h op q calls Q used trace ret Hcf Hprod Hft | cand q q' calls Q Q' used Hsel Hlts
                    | t h op ret q calls calls' Q used Hfin Hdone].
      - exists l. exact (tagged_invoke Log M t h op (q, l) calls Q used trace ret Hcf Hprod Hft).
      - exists (untag (ts_event cand) :: l).
        exact (tagged_underlay Log M cand (q, l) (q', untag (ts_event cand) :: l) calls Q Q' used Hsel (conj Hlts eq_refl)).
      - exists l. exact (tagged_return Log M t h op ret (q, l) calls calls' Q used Hfin Hdone).
    Qed.

    Lemma liftL_exec c evs c' :
      module_execution_tagged VE M c evs c' ->
      forall l, exists l', module_execution_tagged Log M (lift_cfgL c l) evs (lift_cfgL c' l').
    Proof.
      induction 1 as [c | c1 c2 c3 ev evs Hst Hex IH]; intros l.
      - exists l. constructor.
      - destruct (liftL_step ev c1 c2 l Hst) as (l2 & Hst'). destruct (IH l2) as (l3 & Hex').
        exists l3. econstructor; [exact Hst' | exact Hex'].
    Qed.

    Lemma dropL_step ev c c' :
      module_step_tagged Log M ev c c' -> module_step_tagged VE M ev (drop_cfgL c) (drop_cfgL c').
    Proof.
      destruct 1 as [t h op q calls Q used trace ret Hcf Hprod Hft | cand q q' calls Q Q' used Hsel Hlts
                    | t h op ret q calls calls' Q used Hfin Hdone]; cbn.
      - exact (tagged_invoke VE M t h op (fst q) calls Q used trace ret Hcf Hprod Hft).
      - exact (tagged_underlay VE M cand (fst q) (fst q') calls Q Q' used Hsel (proj1 Hlts)).
      - exact (tagged_return VE M t h op ret (fst q) calls calls' Q used Hfin Hdone).
    Qed.

    Lemma dropL_exec c evs c' :
      module_execution_tagged Log M c evs c' -> module_execution_tagged VE M (drop_cfgL c) evs (drop_cfgL c').
    Proof.
      induction 1 as [c | c1 c2 c3 ev evs Hst Hex IH]; [constructor |].
      econstructor; [exact (dropL_step _ _ _ Hst) | exact IH].
    Qed.

    (** The module has the same overlay traces over [VE] and over [Log VE]
        (from the empty log).  No step is disabled by the log, so no
        invariant is needed (unlike [RelaxedHoareCompLinSpec.hlift]). *)
    Theorem loglift (σ0 : State VE) (s : list (ThreadEvent G)) : MTraces VE M σ0 s <-> MTraces Log M (σ0, []) s.
    Proof.
      split.
      - intros (evs & c & Hex & Hov). destruct (liftL_exec _ _ _ Hex []) as (l & Hex').
        exists evs, (lift_cfgL c l). split; [exact Hex' | exact Hov].
      - intros (evs & c & Hex & Hov). exists evs, (drop_cfgL c). split; [exact (dropL_exec _ _ _ Hex) | exact Hov].
    Qed.
  End Log.

  (** Verifying [M] over [Log VE] or over [VE] gives the same copy-cat
      inclusion. *)
  Corollary complin_log_under {E F : RelaxedSig.t} (M : RelaxedModuleImpl E F) (VE : LTS E) (σ0 : State VE)
      (VF : LTS F) (v0 : State VF) :
    RCompLin M VE σ0 VF v0 <-> RCompLin M (Log VE) (σ0, []) VF v0.
  Proof. split; intros HC s Hs; apply HC; apply (loglift VE M σ0 s); exact Hs. Qed.

  (** ** Part 2. [EIhlv] and its value kit *)

  Section LogVal.
    Context {E : RelaxedSig.t} {St : Type}.
    Context (δ : St -> forall o : Sig.op (RelaxedSig.effect E), Sig.ar o -> St -> Prop).

    (** State [((((s, U), used), log)]. *)
    Definition EIhlv : LTS E := Log (EIhl δ).
    Local Abbreviation V := EIhlv.

    Theorem EIhlv_handle_linear :
      HandleLinear V (fun σ k => hl_used (RelaxedHoareSpec.EI δ) (fst σ) k).
    Proof. exact (log_handle_linear (EIhl δ) _ (EIhl_handle_linear δ)). Qed.

    (** The overlay traces over [EI δ], [EIhl δ] and [EIhlv δ] coincide. *)
    Corollary loglift_ei {F : RelaxedSig.t} (M : RelaxedModuleImpl E F) (σ0 : State (RelaxedHoareSpec.EI δ)) s :
      MTraces (RelaxedHoareSpec.EI δ) M σ0 s <-> MTraces V M ((σ0, []), []) s.
    Proof.
      rewrite (hlift_ei δ M σ0 s). exact (loglift (EIhl δ) M (σ0, []) s).
    Qed.

    (** The records consumed by a logged response. *)
    Definition res_ops (ev : ThreadEvent E) : list (Op E) :=
      match te_ev E ev with ResEv h o r => [Build_Op (te_tid E ev, h) o r] | InvEv _ _ => [] end.

    (** The record history: the pending records, then the records
        consumed by the logged responses (newest first).  Since [EI] fixes
        the value of a record at invocation, every record ever created
        stays visible here with its value. *)
    Definition recs (σ : State V) : list (Op E) := snd (fst (fst σ)) ++ flat_map res_ops (snd σ).

    (** [x] is (or was) the record of its key. *)
    Definition LogVal (x : Op E) (σ : State V) : Prop := In x (recs σ).

    (** Every record of the history has a used key, and the keys of the
        history are distinct. *)
    Definition LogOK (σ : State V) : Prop :=
      (forall x, In x (recs σ) -> In (op_key x) (snd (fst σ))) /\ NoDup (map (@op_key E) (recs σ)).

    Lemma logok_init (s : St) : LogOK (((s, []), []), []).
    Proof. split; [intros x [] | constructor]. Qed.

    Lemma logval_step ev (σ σ' : State V) x : Step V ev σ σ' -> LogVal x σ -> LogVal x σ'.
    Proof.
      destruct σ as [[[s P] u] l], σ' as [[[s' P'] u'] l']. intros [Hs Hl] Hx. cbn in Hs, Hl. subst l'.
      unfold LogVal, recs in *. cbn in *. destruct ev as [t [h o | h o r]]; cbn in Hs |- *.
      - destruct Hs as (_ & (r & st' & _ & Heq) & _). injection Heq as -> ->. right. exact Hx.
      - destruct Hs as ((P1 & P2 & HP & Heq) & _). injection Heq as -> ->. cbn in HP. subst P.
        repeat rewrite in_app_iff in *. cbn in *. tauto.
    Qed.

    Lemma logval_mono x : LogMono (EIhl δ) (LogVal x).
    Proof. intros ev σ σ' Hs Hx. exact (logval_step ev σ σ' x Hs Hx). Qed.

    Lemma logval_steps (σ σ' : State V) x : log_steps (EIhl δ) σ σ' -> LogVal x σ -> LogVal x σ'.
    Proof. apply log_steps_mono. apply logval_mono. Qed.

    Lemma logok_step ev (σ σ' : State V) : Step V ev σ σ' -> LogOK σ -> LogOK σ'.
    Proof.
      destruct σ as [[[s P] u] l], σ' as [[[s' P'] u'] l']. intros [Hs Hl] [Hu Hnd]. cbn in Hs, Hl. subst l'.
      unfold LogOK, recs in *. cbn [fst snd] in *.
      destruct ev as [t [h o | h o r]]; cbn in Hs; cbn [flat_map res_ops te_ev te_tid app].
      - destruct Hs as (Hnu & (r & st' & _ & Heq) & ->). injection Heq as -> ->. split.
        + intros x [<- | Hx]; [left; reflexivity | right; exact (Hu x Hx)].
        + constructor; [| exact Hnd]. intros Hin. apply in_map_iff in Hin as (x & Hk & Hx).
          cbn in Hk. apply Hnu. rewrite <- Hk. exact (Hu x Hx).
      - destruct Hs as ((P1 & P2 & HP & Heq) & ->). injection Heq as -> ->. cbn in HP. subst P.
        assert (Hp : Permutation ((P1 ++ Build_Op (t, h) o r :: P2) ++ flat_map res_ops l)
                                 ((P1 ++ P2) ++ Build_Op (t, h) o r :: flat_map res_ops l)).
        { rewrite <- !app_assoc. apply Permutation_app_head. cbn [app]. apply Permutation_middle. }
        split.
        + intros x Hx. apply Hu. exact (Permutation_in _ (Permutation_sym Hp) Hx).
        + exact (Permutation_NoDup (Permutation_map _ Hp) Hnd).
    Qed.

    Lemma logok_mono : LogMono (EIhl δ) LogOK.
    Proof. intros ev σ σ' Hs H. exact (logok_step ev σ σ' Hs H). Qed.

    Lemma logok_steps (σ σ' : State V) : log_steps (EIhl δ) σ σ' -> LogOK σ -> LogOK σ'.
    Proof. apply log_steps_mono. apply logok_mono. Qed.

    Lemma nodup_key_inj {A B : Type} (f : A -> B) (L : list A) x y :
      NoDup (map f L) -> In x L -> In y L -> f x = f y -> x = y.
    Proof.
      induction L as [| a L IH]; cbn; intros Hnd Hx Hy Hf; [destruct Hx |].
      inversion Hnd as [| ? ? Hnin Hnd']; subst. destruct Hx as [<- | Hx], Hy as [<- | Hy]; auto.
      - exfalso. apply Hnin. rewrite Hf. apply in_map. exact Hy.
      - exfalso. apply Hnin. rewrite <- Hf. apply in_map. exact Hx.
    Qed.

    (** One value per key, for ever. *)
    Lemma logval_unique (σ : State V) x y : LogOK σ -> LogVal x σ -> LogVal y σ -> op_key x = op_key y -> x = y.
    Proof. intros [_ Hnd] Hx Hy Hk. exact (nodup_key_inj _ _ x y Hnd Hx Hy Hk). Qed.

    (** The same, for the value: two logged results of one key and one
        operation are equal, when the operations have decidable equality
        ([Eqdep_dec], no axiom). *)
    Lemma logval_val_dec (Hdec : forall o1 o2 : Sig.op (RelaxedSig.effect E), {o1 = o2} + {o1 <> o2})
        (σ : State V) key o (v w : Sig.ar o) :
      LogOK σ -> LogVal (Build_Op key o v) σ -> LogVal (Build_Op key o w) σ -> v = w.
    Proof.
      intros Hok Hv Hw. pose proof (logval_unique σ _ _ Hok Hv Hw eq_refl) as Heq.
      apply (f_equal (fun x : Op E => existT (fun o0 => Sig.ar o0) (op_op x) (op_ret x))) in Heq. cbn in Heq.
      exact (inj_pair2_eq_dec _ Hdec _ _ _ _ Heq).
    Qed.

    (** A response returns the logged value of its key. *)
    Lemma logval_res t h o (r : Sig.ar o) x (σ σ' : State V) :
      LogOK σ -> LogVal x σ -> op_key x = (t, h) ->
      Step V (Build_ThreadEvent t (@ResEv E h o r)) σ σ' -> x = Build_Op (t, h) o r.
    Proof.
      intros Hok Hx Hk Hs. apply (logval_unique σ); [exact Hok | exact Hx | | exact Hk].
      destruct σ as [[[s P] u] l], σ' as [[[s' P'] u'] l']. destruct Hs as [Hs _]. cbn in Hs.
      destruct Hs as ((P1 & P2 & HP & _) & _). cbn in HP. unfold LogVal, recs. cbn [fst snd]. rewrite HP.
      apply in_or_app. left. apply in_or_app. right. left. reflexivity.
    Qed.

    (** A response logs its own record. *)
    Lemma logval_res_logged t h o (r : Sig.ar o) (σ σ' : State V) :
      Step V (Build_ThreadEvent t (@ResEv E h o r)) σ σ' -> LogVal (Build_Op (t, h) o r) σ'.
    Proof.
      destruct σ as [[[s P] u] l], σ' as [[[s' P'] u'] l']. intros [_ Hl]. cbn in Hl. subst l'.
      unfold LogVal, recs. cbn [fst snd flat_map res_ops te_ev te_tid]. apply in_or_app. right. left. reflexivity.
    Qed.

    (** An invocation creates a logged record whose value is chosen by [δ]. *)
    Lemma logval_inv t h o (σ σ' : State V) :
      Step V (Build_ThreadEvent t (@InvEv E h o)) σ σ' ->
      exists r st', δ (fst (fst (fst σ))) o r st' /\ fst (fst (fst σ')) = st' /\ LogVal (Build_Op (t, h) o r) σ'.
    Proof.
      destruct σ as [[[s P] u] l], σ' as [[[s' P'] u'] l']. intros [Hs _]. cbn in Hs.
      destruct Hs as (_ & (r & st' & Hd & Heq) & _). injection Heq as -> ->.
      exists r, st'. split; [exact Hd |]. split; [reflexivity |]. left. reflexivity.
    Qed.

    (** Pending records are logged; with [LogOK], the base state satisfies
        [RelaxedHoareCompLinSpec.eihl_rec_used]. *)
    Lemma logval_pending (σ : State V) x : In x (snd (fst (fst σ))) -> LogVal x σ.
    Proof. intros Hx. unfold LogVal, recs. apply in_or_app. left. exact Hx. Qed.

    Lemma logok_rec_used (σ : State V) : LogOK σ -> eihl_rec_used δ (fst σ).
    Proof. intros [Hu _] x Hx. exact (Hu x (logval_pending σ x Hx)). Qed.

    (** The base part of [log_steps] is [RelaxedHoareCompLinSpec.eihl_steps],
        the memory part of the existing frame-style relies ([Rren], [Rsl]). *)
    Lemma log_steps_eihl (σ σ' : State V) : log_steps (EIhl δ) σ σ' -> eihl_steps δ (fst σ) (fst σ').
    Proof. exact (log_steps_base (EIhl δ) σ σ'). Qed.
  End LogVal.

  (** ** Part 3. Copy-cat inclusion and relaxed linearizability from
      RLHL over [EIhlv] *)

  Section Transfer.
    Import RelaxedHoareBase.
    Context {E F : RelaxedSig.t} {St StF : Type}.
    Context (δ : St -> forall o : Sig.op (RelaxedSig.effect E), Sig.ar o -> St -> Prop).
    Context (δF : StF -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> StF -> Prop) (s0 : StF).
    Local Abbreviation V := (EIhlv δ).
    Local Abbreviation VF := (RelaxedHoareSpec.EI δF).

    (** RLHL hypotheses over [EIhlv δ] from [((σ0, []), [])] give copy-cat
        inclusion over the plain [EI δ] from [σ0].  Uses [classic],
        inherited from [RelaxedHoareCompLin.rlhl_complin_ei] (through
        [rinv_val]), as for [rlhl_complin_eihl]. *)
    Corollary rlhl_complin_eihlv (I : Assn V VF) (R G : CallKey F -> PRel V VF)
        (M : RelaxedModuleImpl E F) (σ0 : State (RelaxedHoareSpec.EI δ)) :
      RLHL2Hyps I R G M ((σ0, []), []) (s0, []) -> RCompLin M (RelaxedHoareSpec.EI δ) σ0 VF (s0, []).
    Proof.
      intros HH. apply (proj2 (complin_hlift_under M (RelaxedHoareSpec.EI δ) σ0 _ _)).
      apply (proj2 (complin_log_under M (EIhl δ) (σ0, []) _ _)).
      exact (rlhl_complin_ei δF s0 I R G M ((σ0, []), []) HH).
    Qed.

    (** [rlhl_complin_eihlv] followed by [RelaxedHoareCompLinSpec.cc_rel_lin]:
        every complete overlay trace over [EI δ] is relaxed-linearizable.
        Uses [classic] (above) and [eq_rect_eq], inherited from
        [RelaxedGSim.gsim_rel_lin] through [cc_rel_lin]. *)
    Corollary rlhl_eihlv_rel_lin (I : Assn V VF) (R G : CallKey F -> PRel V VF)
        (M : RelaxedModuleImpl E F) (σ0 : State (RelaxedHoareSpec.EI δ)) :
      RLHL2Hyps I R G M ((σ0, []), []) (s0, []) ->
      forall s, MTraces (RelaxedHoareSpec.EI δ) M σ0 s -> PrefixView.complete s ->
        RelaxedTraceLin.rel_lin (@PrefixView.sel F) s (semi_independent F) (RelaxedHoareSpec.seq_legal δF s0).
    Proof.
      intros HH. exact (complin_ei_rel_lin δF s0 M (RelaxedHoareSpec.EI δ) σ0 (rlhl_complin_eihlv I R G M σ0 HH)).
    Qed.
  End Transfer.

  (** ** Part 4. Lifting assertions, relations and the side fields from
      [VE] to [Log VE] *)

  Section Generic.
    Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.

    Lemma Stable_ex {A : Type} (I : Assn VE VF) (r : PRel VE VF) (P : A -> Assn VE VF) :
      (forall x, Stable I r (P x)) -> Stable I r (fun s => exists x, P x s).
    Proof. intros H s s' (x & Hx) Hr HI. exists x. exact (H x s s' Hx Hr HI). Qed.

    Lemma evupdate_conseq (I : Assn VE VF) g k ev (P P' Q Q' : Assn VE VF) :
      EvUpdate I g k ev P Q -> (forall s, P' s -> P s) -> (forall s, Q s -> Q' s) -> EvUpdate I g k ev P' Q'.
    Proof.
      intros H HP HQ σ p γ γ' Hp HI Hge σ' Hs.
      destruct (H σ p γ γ' (HP _ Hp) HI Hge σ' Hs) as (p' & Hps & Hq & HI' & Hg).
      exists p'. split; [exact Hps |]. split; [exact (HQ _ Hq) |]. split; [exact HI' | exact Hg].
    Qed.

    Lemma evupdate_ex {A : Type} (I : Assn VE VF) g k ev (P : A -> Assn VE VF) Q :
      (forall x, EvUpdate I g k ev (P x) Q) -> EvUpdate I g k ev (fun s => exists x, P x s) Q.
    Proof. intros H σ p γ γ' (x & Hx). exact (H x σ p γ γ' Hx). Qed.

    Lemma clos_refl_cases {A : Type} (r : A -> A -> Prop) x y : clos_refl _ r x y -> x = y \/ r x y.
    Proof. intros [y' Hr |]; [right; exact Hr | left; reflexivity]. Qed.
  End Generic.

  Section Lift.
    Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.

    (** The base part of a lifted proof state. *)
    Definition dropS (s : PState (Log VE) VF) : PState VE VF := (fst (ps_mem s), ps_poss s, ps_ghost s).

    (** A base assertion read on the base part. *)
    Definition liftA (P : Assn VE VF) : Assn (Log VE) VF := fun s => P (dropS s).

    (** A base relation read on the base parts; the log is unconstrained. *)
    Definition liftG (g : PRel VE VF) : PRel (Log VE) VF := fun s s' => g (dropS s) (dropS s').

    (** A base relation read on the base parts, and the memory moves by
        [Log VE] steps (latest-review m-59).  Used for both the rely and
        the guarantee: every fact kept by [Log VE] steps ([LogMono]) is then
        stable ([stable_logA]). *)
    Definition liftGL (g : PRel VE VF) : PRel (Log VE) VF := fun s s' => liftG g s s' /\ log_steps VE (ps_mem s) (ps_mem s').

    (** The family version, for [R] and [G]. *)
    Definition liftGLk (R : CallKey F -> PRel VE VF) : CallKey F -> PRel (Log VE) VF := fun k => liftGL (R k).

    (** A fact about the lifted memory (typically about the log). *)
    Definition logA (X : State (Log VE) -> Prop) : Assn (Log VE) VF := fun s => X (ps_mem s).

    (** [J]: an invariant of the lifted memory, kept by every step
        ([RelaxedHoareLog.LogOK] for [EIhlv]). *)
    Context (J : State (Log VE) -> Prop).

    (** The lifted invariant: the base invariant on the base part, and [J]. *)
    Definition liftI (I : Assn VE VF) : Assn (Log VE) VF := fun s => I (dropS s) /\ J (ps_mem s).

    Lemma stable_lift (I : Assn VE VF) (r : PRel VE VF) P : Stable I r P -> Stable (liftI I) (liftG r) (liftA P).
    Proof. intros H s s' Hp Hr [HI _]. exact (H _ _ Hp Hr HI). Qed.

    Lemma stable_liftL (I : Assn VE VF) (r : PRel VE VF) P : Stable I r P -> Stable (liftI I) (liftGL r) (liftA P).
    Proof. intros H s s' Hp [Hr _] [HI _]. exact (H _ _ Hp Hr HI). Qed.

    (** Facts kept by every [Log VE] step are stable under every lifted
        relation [liftGL r], whatever [r] and the invariant. *)
    Lemma stable_logA (I' : Assn (Log VE) VF) (r : PRel VE VF) X :
      LogMono VE X -> Stable I' (liftGL r) (logA X).
    Proof. intros HX s s' Hx [_ Hl] _. exact (log_steps_mono VE X _ _ HX Hl Hx). Qed.

    (** The lifted [PostInvoke] (the [Pinit] of a lifted derivation) gives
        the base one on the base part, and [J]. *)
    Lemma postinvoke_lift (I : Assn VE VF) k op Ω s :
      PostInvoke (liftI I) k op Ω s -> PostInvoke I k op Ω (dropS s) /\ J (ps_mem s).
    Proof.
      intros (p0 & γ0 & evs & [HI HJs] & Hinv & Hg & HΩ & Hf). split; [| exact HJs].
      exists p0, γ0, evs. split; [exact HI |]. split; [exact Hinv |]. split; [exact Hg |]. split; [exact HΩ | exact Hf].
    Qed.

    (** The return condition: no log move is needed (memory is unchanged). *)
    Lemma retcond_lift (I : Assn VE VF) (G : CallKey F -> PRel VE VF) k op r s :
      J (ps_mem s) -> RetCond I G k op r (dropS s) -> RetCond (liftI I) (liftGLk G) k op r s.
    Proof.
      intros HJs (p1 & Hps & Hlk & HI1 & Hcr & Hrm). exists p1.
      split; [exact Hps |]. split; [exact Hlk |]. split; [split; [exact HI1 | exact HJs] |]. split.
      - destruct (clos_refl_cases _ _ _ Hcr) as [Heq | Hg].
        + assert (Hp1 : p1 = ps_poss s).
          { destruct s as [[σ p] γ]. cbn in Heq |- *. injection Heq as Hq. symmetry. exact Hq. }
          rewrite Hp1. destruct s as [[σ p] γ]. apply r_refl.
        + apply r_step. split; [exact Hg | apply log_steps_refl].
      - intros p2 Hp2. split; [exact (Hrm p2 Hp2) | exact HJs].
    Qed.

    Context (HJ : LogMono VE J).

    (** The scratch's lifting: guarantee [liftG g] only. *)
    Lemma evupdate_lift (I : Assn VE VF) g k ev P Q :
      EvUpdate I g k ev P Q -> EvUpdate (liftI I) (liftG g) k ev (liftA P) (liftA Q).
    Proof.
      intros H σ p γ γ' HP [HI HJσ] Hge σ' Hs.
      destruct (H (fst σ) p γ γ' HP HI Hge (fst σ') (proj1 Hs)) as (p' & Hps & HQ & HI' & Hg).
      exists p'. split; [exact Hps |]. split; [exact HQ |]. split; [split; [exact HI' | exact (HJ _ _ _ Hs HJσ)] | exact Hg].
    Qed.

    (** m-59, general form: an update over [Log VE] whose guarantee is
        [liftGL g] (it includes the [Log] step of the event) reduces to a
        statement on the base parts; [J] is kept and the log move is
        supplied here.  [P] and [Q] are arbitrary lifted assertions (they
        may mention the log). *)
    Lemma evupdate_liftL_gen (I : Assn VE VF) (g : PRel VE VF) k ev (P Q : Assn (Log VE) VF) :
      (forall σ p γ γ' σ', P (σ, p, γ) -> I (fst σ, p, γ) -> J σ -> ghost_emit k ev γ γ' ->
         Step (Log VE) ev σ σ' ->
         exists p', poss_steps VF p p' /\ Q (σ', p', γ') /\ I (fst σ', p', γ') /\
                    g (fst σ, p, γ) (fst σ', p', γ')) ->
      EvUpdate (liftI I) (liftGL g) k ev P Q.
    Proof.
      intros H σ p γ γ' HP [HI HJσ] Hge σ' Hs.
      destruct (H σ p γ γ' σ' HP HI HJσ Hge Hs) as (p' & Hps & HQ & HI' & Hg).
      exists p'. split; [exact Hps |]. split; [exact HQ |].
      split; [split; [exact HI' | exact (HJ _ _ _ Hs HJσ)] |].
      split; [exact Hg | exact (log_steps_step VE ev σ σ' Hs)].
    Qed.

    (** m-59: a base update lifts with the guarantee [liftGL g]. *)
    Lemma evupdate_liftL (I : Assn VE VF) g k ev P Q :
      EvUpdate I g k ev P Q -> EvUpdate (liftI I) (liftGL g) k ev (liftA P) (liftA Q).
    Proof.
      intros H. apply evupdate_liftL_gen. intros σ p γ γ' σ' HP HI _ Hge Hs.
      exact (H (fst σ) p γ γ' HP HI Hge (fst σ') (proj1 Hs)).
    Qed.

    (** A base update with log facts carried across the step. *)
    Lemma evupdate_liftL_with (I : Assn VE VF) g k ev P Q (X Y : State (Log VE) -> Prop) :
      EvUpdate I g k ev P Q ->
      (forall σ σ', J σ -> X σ -> Step (Log VE) ev σ σ' -> Y σ') ->
      EvUpdate (liftI I) (liftGL g) k ev (fun s => liftA P s /\ logA X s) (fun s => liftA Q s /\ logA Y s).
    Proof.
      intros H HXY. apply evupdate_liftL_gen. intros σ p γ γ' σ' [HP HX] HI HJσ Hge Hs.
      destruct (H (fst σ) p γ γ' HP HI Hge (fst σ') (proj1 Hs)) as (p' & Hps & HQ & HI' & Hg).
      exists p'. split; [exact Hps |]. split; [split; [exact HQ | exact (HXY σ σ' HJσ HX Hs)] |].
      split; [exact HI' | exact Hg].
    Qed.

    (** *** Transfer of the side fields of [RLHL2Hyps] *)

    Section Sides.
      Context (I : Assn VE VF) (R G : CallKey F -> PRel VE VF) (M : RelaxedModuleImpl E F).

      (** [h_guar_rely]. *)
      Lemma guar_rely_lift :
        (forall k k' s s', k <> k' -> G k s s' -> R k' s s') ->
        forall k k' s s', k <> k' -> liftGLk G k s s' -> liftGLk R k' s s'.
      Proof. intros H k k' s s' Hne [Hg Hl]. split; [exact (H k k' _ _ Hne Hg) | exact Hl]. Qed.

      (** [h_invoke_rely]. *)
      Lemma invoke_rely_lift :
        (forall k k' op tr ret s p', k <> k' ->
           program_produces_tagged (fst k) (M op (fst k)) tr ret -> I s ->
           poss_invoke VF (fst k) (snd k) op (ps_poss s) p' ->
           R k' s (ps_mem s, p', ps_ghost s ++ ghost_new k tr)) ->
        forall k k' op tr ret s p', k <> k' ->
          program_produces_tagged (fst k) (M op (fst k)) tr ret -> liftI I s ->
          poss_invoke VF (fst k) (snd k) op (ps_poss s) p' ->
          liftGLk R k' s (ps_mem s, p', ps_ghost s ++ ghost_new k tr).
      Proof.
        intros H k k' op tr ret s p' Hne Hprod [HI _] Hinv.
        split; [exact (H k k' op tr ret (dropS s) p' Hne Hprod HI Hinv) | apply log_steps_refl].
      Qed.

      (** [h_return_rely]. *)
      Lemma return_rely_lift :
        (forall k k' op r s p2, k <> k' -> I s ->
           poss_return VF (fst k) (snd k) op r (ps_poss s) p2 -> NoOwn k (ps_ghost s) ->
           R k' s (ps_mem s, p2, ps_ghost s)) ->
        forall k k' op r s p2, k <> k' -> liftI I s ->
          poss_return VF (fst k) (snd k) op r (ps_poss s) p2 -> NoOwn k (ps_ghost s) ->
          liftGLk R k' s (ps_mem s, p2, ps_ghost s).
      Proof.
        intros H k k' op r s p2 Hne [HI _] Hret Hno.
        split; [exact (H k k' op r (dropS s) p2 Hne HI Hret Hno) | apply log_steps_refl].
      Qed.

      (** [h_ok]. *)
      Lemma ok_lift :
        (forall s, I s -> exists v pool, ps_poss s = PossOk v pool /\ lin_pool_well_formed pool) ->
        forall s, liftI I s -> exists v pool, ps_poss s = PossOk v pool /\ lin_pool_well_formed pool.
      Proof. intros H s [HI _]. exact (H (dropS s) HI). Qed.

      (** [h_init], from the empty log. *)
      Lemma init_lift σ0 v0 :
        I (σ0, PossOk v0 [], []) -> J (σ0, []) -> liftI I ((σ0, []), PossOk v0 [], []).
      Proof. intros HI HJ0. split; [exact HI | exact HJ0]. Qed.

      (** [h_sem], semantically: a base certificate lifts. *)
      Theorem methodsem_lift t op :
        MethodSem I R G M t op -> MethodSem (liftI I) (liftGLk R) (liftGLk G) M t op.
      Proof.
        intros Hsem h tr ret Hprod. destruct (Hsem h tr ret Hprod) as (A & [Hemit Hstab Hret] & Hinit).
        exists (fun l => liftA (A l)). split.
        - constructor.
          + intros pre m post Hfr σ p γ γ' Hge HA [HI HJσ] σ' Hs.
            destruct (Hemit pre m post Hfr (fst σ) p γ γ' Hge HA HI (fst σ') (proj1 Hs)) as (p' & Hps & HA' & HI' & Hg).
            exists p'. split; [exact Hps |]. split; [exact HA' |].
            split; [split; [exact HI' | exact (HJ _ _ _ Hs HJσ)] |].
            split; [exact Hg | exact (log_steps_step VE (untag m) σ σ' Hs)].
          + intros l. apply stable_liftL. apply Hstab.
          + intros s HA [HI HJs] Hno. apply (retcond_lift I G _ op ret s HJs). exact (Hret (dropS s) HA HI Hno).
        - intros σ p γ p' [HI HJσ] Hinv. destruct (Hinit (fst σ) p γ p' HI Hinv) as [HI' HA].
          split; [split; [exact HI' | exact HJσ] | exact HA].
      Qed.

      (** The whole record, when [h_sem] holds over the base. *)
      Theorem rlhl2_lift σ0 v0 :
        RLHL2Hyps I R G M σ0 v0 -> J (σ0, []) -> RLHL2Hyps (liftI I) (liftGLk R) (liftGLk G) M (σ0, []) v0.
      Proof.
        intros [Hsem Hgr Hir Hrr Hok Hinit] HJ0. constructor.
        - intros t op. exact (methodsem_lift t op (Hsem t op)).
        - exact (guar_rely_lift Hgr).
        - exact (invoke_rely_lift Hir).
        - exact (return_rely_lift Hrr).
        - exact (ok_lift Hok).
        - exact (init_lift σ0 v0 Hinit HJ0).
      Qed.

      (** The assembly used when the methods are derived over [Log VE]
          directly (the SeqLock reader): derivations over [Log VE], the
          base side fields, and [J] initially.  This is
          [RelaxedHoareGSim.rlhl2_of_provable] over [Log VE] with the side
          fields transferred. *)
      Theorem rlhl2_lift_of_provable σ0 v0
          (Hprov : forall t op, exists Ω Q, MethodProvable (liftI I) (liftGLk R) (liftGLk G) M t op Ω Q)
          (Hgr : forall k k' s s', k <> k' -> G k s s' -> R k' s s')
          (Hir : forall k k' op tr ret s p', k <> k' ->
             program_produces_tagged (fst k) (M op (fst k)) tr ret -> I s ->
             poss_invoke VF (fst k) (snd k) op (ps_poss s) p' ->
             R k' s (ps_mem s, p', ps_ghost s ++ ghost_new k tr))
          (Hrr : forall k k' op r s p2, k <> k' -> I s ->
             poss_return VF (fst k) (snd k) op r (ps_poss s) p2 -> NoOwn k (ps_ghost s) ->
             R k' s (ps_mem s, p2, ps_ghost s))
          (Hok : forall s, I s -> exists v pool, ps_poss s = PossOk v pool /\ lin_pool_well_formed pool)
          (Hinit : I (σ0, PossOk v0 [], [])) (HJ0 : J (σ0, [])) :
        RLHL2Hyps (liftI I) (liftGLk R) (liftGLk G) M (σ0, []) v0.
      Proof.
        exact (RelaxedHoareGSim.rlhl2_of_provable (liftI I) (liftGLk R) (liftGLk G) M (σ0, []) v0 Hprov
                 (guar_rely_lift Hgr) (invoke_rely_lift Hir) (return_rely_lift Hrr) (ok_lift Hok)
                 (init_lift σ0 v0 Hinit HJ0)).
      Qed.
    End Sides.
  End Lift.

  (** ** Part 5. Lifting derivations *)

  Section LiftDerivation.
    Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.

    (** A slot with every assertion read on the base part and the
        guarantee [liftGL]; the event is unchanged. *)
    Definition liftSlot (sl : Slot VE VF) : Slot (Log VE) VF :=
      mkSlot (sl_ev sl) (liftA (sl_start sl)) (fun d => liftA (sl_in sl d)) (liftA (sl_post sl)) (liftGL (sl_guar sl)).

    Lemma evs_liftS (Γ : list (Slot VE VF)) : evs (map liftSlot Γ) = evs Γ.
    Proof. unfold evs. rewrite map_map. reflexivity. Qed.

    Lemma own_invs_liftS (Γ : list (Slot VE VF)) : own_invs (map liftSlot Γ) = own_invs Γ.
    Proof. unfold own_invs. rewrite evs_liftS. reflexivity. Qed.

    Lemma nth_error_liftS (Γ : list (Slot VE VF)) n sl' :
      nth_error (map liftSlot Γ) n = Some sl' -> exists sl, nth_error Γ n = Some sl /\ sl' = liftSlot sl.
    Proof.
      rewrite nth_error_map. destruct (nth_error Γ n) as [sl |]; cbn; intros H; [| discriminate].
      injection H as <-. exists sl. split; reflexivity.
    Qed.

    Lemma nth_error_liftS' (Γ : list (Slot VE VF)) n sl :
      nth_error Γ n = Some sl -> nth_error (map liftSlot Γ) n = Some (liftSlot sl).
    Proof. intros H. rewrite nth_error_map, H. reflexivity. Qed.

    Lemma map_liftS_snoc (Γ : list (Slot VE VF)) sl : map liftSlot Γ ++ [liftSlot sl] = map liftSlot (Γ ++ [sl]).
    Proof. rewrite map_app. reflexivity. Qed.

    Context (J : State (Log VE) -> Prop) (HJ : LogMono VE J).
    Context (I : Assn VE VF) (R G : CallKey F -> PRel VE VF).
    Local Abbreviation IL := (liftI J I).
    Local Abbreviation RL := (liftGLk R).
    Local Abbreviation GL := (liftGLk G).

    Section Call.
      Context (k : CallKey F) (Pinit : Assn VE VF) (Pinit' : Assn (Log VE) VF).
      Context (HP : forall s, IL s -> Pinit' s -> liftA Pinit s).

      Lemma newslotok_lift (Γ : list (Slot VE VF)) sl :
        NewSlotOK I R G k Pinit Γ sl -> NewSlotOK IL RL GL k Pinit' (map liftSlot Γ) (liftSlot sl).
      Proof.
        intros [Hg Hu Hes Hei HRs HRi Hins Hini Hios Hioi].
        assert (He : evs (map liftSlot Γ ++ [liftSlot sl]) = evs (Γ ++ [sl]))
          by (rewrite map_liftS_snoc; apply evs_liftS).
        assert (Hl : length (map liftSlot Γ) = length Γ) by apply length_map.
        constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar liftSlot].
        - intros s s' [Hs Hl']. split; [exact (Hg _ _ Hs) | exact Hl'].
        - apply (evupdate_conseq _ _ _ _ (liftA (pre_of (Γ ++ [sl]) (length Γ) sl)) _ (liftA (sl_post sl)));
            [exact (evupdate_liftL J HJ I _ k _ _ _ Hu) | | intros s Hs; exact Hs].
          intros s [Hst Hin]. split; [exact Hst |]. intros d Hd. apply Hin. rewrite He, Hl. exact Hd.
        - intros s HI Hp. exact (Hes _ (proj1 HI) (HP s HI Hp)).
        - intros d sd' Hd Hsd' s HI Hp. rewrite He, Hl in Hd.
          destruct (nth_error_liftS _ _ _ Hsd') as (sd & Hsd & ->).
          exact (Hei d sd Hd Hsd _ (proj1 HI) Hp).
        - exact (stable_liftL J I (R k) _ HRs).
        - intros d Hd. rewrite He, Hl in Hd. exact (stable_liftL J I (R k) _ (HRi d Hd)).
        - intros g sg' Hsg'. destruct (nth_error_liftS _ _ _ Hsg') as (sg & Hsg & ->).
          exact (stable_liftL J I _ _ (Hins g sg Hsg)).
        - intros d g sg' Hd Hsg' Hnb. rewrite He, Hl in Hd. rewrite evs_liftS in Hnb.
          destruct (nth_error_liftS _ _ _ Hsg') as (sg & Hsg & ->).
          exact (stable_liftL J I _ _ (Hini d g sg Hd Hsg Hnb)).
        - intros y sy' Hsy' Hnb. rewrite He, Hl in Hnb.
          destruct (nth_error_liftS _ _ _ Hsy') as (sy & Hsy & ->).
          exact (stable_liftL J I _ _ (Hios y sy Hsy Hnb)).
        - intros y sy' d Hsy' Hnb Hd. rewrite He, Hl in Hnb. rewrite evs_liftS in Hd.
          destruct (nth_error_liftS _ _ _ Hsy') as (sy & Hsy & ->).
          exact (stable_liftL J I _ _ (Hioi y sy d Hsy Hnb Hd)).
      Qed.

      Lemma barrierwith_lift (Γ : list (Slot VE VF)) fin fin0 P :
        BarrierWith I R k Pinit Γ fin fin0 P ->
        BarrierWith IL RL k Pinit' (map liftSlot Γ) (fun d => liftA (fin d)) (liftA fin0) (liftA P).
      Proof.
        intros [Hest Hest0 Hif Hif0 HR HR0 Hsum]. constructor.
        - intros d sd' Hsd' s HI Hp. destruct (nth_error_liftS _ _ _ Hsd') as (sd & Hsd & ->).
          exact (Hest d sd Hsd _ (proj1 HI) Hp).
        - intros s HI Hp. exact (Hest0 _ (proj1 HI) (HP s HI Hp)).
        - intros d g sg' Hd Hsg' Hnb. rewrite length_map in Hd. rewrite evs_liftS in Hnb.
          destruct (nth_error_liftS _ _ _ Hsg') as (sg & Hsg & ->).
          exact (stable_liftL J I _ _ (Hif d g sg Hd Hsg Hnb)).
        - intros g sg' Hsg'. destruct (nth_error_liftS _ _ _ Hsg') as (sg & Hsg & ->).
          exact (stable_liftL J I _ _ (Hif0 g sg Hsg)).
        - intros d. exact (stable_liftL J I _ _ (HR d)).
        - exact (stable_liftL J I _ _ HR0).
        - intros s HI H0 Hfin. apply (Hsum (dropS s) (proj1 HI) H0).
          intros d sd Hsd Hres. exact (Hfin d (liftSlot sd) (nth_error_liftS' _ _ _ Hsd) Hres).
      Qed.

      Lemma close_lift {A : Type} (Q : A -> Assn VE VF) a (Γ : list (Slot VE VF)) H :
        Close I R G k Pinit Q a Γ H -> Close IL RL GL k Pinit' (fun a => liftA (Q a)) a (map liftSlot Γ) H.
      Proof.
        induction 1 as [Γ H fin fin0 Hall Hbw | Γ H h op sl Hpend Hev Hnew Hrest IH].
        - apply (close_done IL RL GL k Pinit' (fun a => liftA (Q a)) a (map liftSlot Γ) H
                   (fun d => liftA (fin d)) (liftA fin0) Hall).
          exact (barrierwith_lift Γ fin fin0 (Q a) Hbw).
        - apply (close_resolve IL RL GL k Pinit' (fun a => liftA (Q a)) a (map liftSlot Γ) H h op
                   (fun r => liftSlot (sl r)) Hpend).
          + intros r. exact (Hev r).
          + intros r. exact (newslotok_lift Γ (sl r) (Hnew r)).
          + intros r H' Hres. rewrite map_liftS_snoc. exact (IH r H' Hres).
      Qed.

      Lemma rprovable_lift {A : Type} (K : A -> list (Slot VE VF) -> FutureStore E -> Prop)
          (K' : A -> list (Slot (Log VE) VF) -> FutureStore E -> Prop) :
        (forall a Γ H, K a Γ H -> K' a (map liftSlot Γ) H) ->
        forall Γ H p, RProvable I R G k Pinit K Γ H p -> RProvable IL RL GL k Pinit' K' (map liftSlot Γ) H p.
      Proof.
        intros HK Γ0 H0 p0 D0.
        apply (RProvable_coind IL RL GL k Pinit' K'
                 (fun Γ' H p => exists Γ, Γ' = map liftSlot Γ /\ RProvable I R G k Pinit K Γ H p));
          [| exists Γ0; split; [reflexivity | exact D0]].
        clear Γ0 H0 p0 D0. intros Γ' H p (Γ & -> & D).
        apply rp_unfold in D.
        destruct p as [op c | op deps c | B f c | r | p']; cbn in D |- *.
        - destruct D as (sl & H1 & H2 & H3). exists (fun h => liftSlot (sl h)).
          split; [exact H1 |]. split; [intros h Hf; exact (newslotok_lift Γ (sl h) (H2 h Hf)) |].
          intros h Hf. exists (Γ ++ [sl h]). split; [apply map_liftS_snoc | exact (H3 h Hf)].
        - destruct D as (sl & H1 & H2 & H3). exists (fun h => liftSlot (sl h)).
          split; [exact H1 |]. split; [intros h Hf; exact (newslotok_lift Γ (sl h) (H2 h Hf)) |].
          intros h Hf. exists (Γ ++ [sl h]). split; [apply map_liftS_snoc | exact (H3 h Hf)].
        - revert c D. destruct f as [op h]. intros c D. cbn in D |- *.
          destruct D as [[H1 H2] | (sl & H1 & H2 & H3 & H4)].
          + left. split; [exact H1 |]. intros r Hr. exists Γ. split; [reflexivity | exact (H2 r Hr)].
          + right. exists (fun r => liftSlot (sl r)). split; [exact H1 |]. split; [exact H2 |].
            split; [intros r; exact (newslotok_lift Γ (sl r) (H3 r)) |].
            intros r H' Hres. exists (Γ ++ [sl r]). split; [apply map_liftS_snoc | exact (H4 r H' Hres)].
        - exact (HK r Γ H D).
        - exists Γ. split; [reflexivity | exact D].
      Qed.
    End Call.

    (** Every derivation over [VE] is a derivation over [Log VE], with the
        lifted invariant, rely, guarantee and postcondition. *)
    Theorem methodprovable_lift (M : RelaxedModuleImpl E F) t op Ω Q :
      MethodProvable I R G M t op Ω Q ->
      MethodProvable IL RL GL M t op Ω (fun h r => liftA (Q h r)).
    Proof.
      intros [HPI Hret Htr]. constructor.
      - intros h s Hs. destruct (postinvoke_lift J I (t, h) op (Ω h) s Hs) as [Hs' HJs].
        split; [exact (HPI h _ Hs') | exact HJs].
      - intros h r s HQ [HI HJs] Hno. apply (retcond_lift J I G (t, h) op r s HJs).
        exact (Hret h r (dropS s) HQ HI Hno).
      - intros h. set (Pi := PostInvoke I (t, h) op (Ω h)). set (Pi' := PostInvoke IL (t, h) op (Ω h)).
        assert (HPi : forall s, IL s -> Pi' s -> liftA Pi s)
          by (intros s _ Hs; exact (proj1 (postinvoke_lift J I (t, h) op (Ω h) s Hs))).
        refine (rprovable_lift (t, h) Pi Pi' HPi
                  (fun a Γ H => Close I R G (t, h) Pi (Q h) a Γ H /\ Ω h (own_invs Γ))
                  (fun a Γ' H => Close IL RL GL (t, h) Pi' (fun r => liftA (Q h r)) a Γ' H /\ Ω h (own_invs Γ'))
                  _ [] empty_store (M op t) (Htr h)).
        intros a Γ H [Hc HΩ]. split; [exact (close_lift (t, h) Pi Pi' HPi (Q h) a Γ H Hc) |].
        rewrite own_invs_liftS. exact HΩ.
    Qed.
  End LiftDerivation.

  (** Strengthening the postcondition of a new slot by a fact about the
      memory reached by its own event (for instance a [LogVal] fact that
      the event logs, [logval_res_logged]).  Only [ns_update] changes; the
      event, the edges and the guarantee are those of [sl].  Generic in
      the underlay. *)
  Section SlotPostAnd.
    Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.
    Context (I : Assn VE VF) (R G : CallKey F -> PRel VE VF) (k : CallKey F) (Pinit : Assn VE VF).

    Definition slot_post_and (sl : Slot VE VF) (Y : State VE -> Prop) : Slot VE VF :=
      mkSlot (sl_ev sl) (sl_start sl) (sl_in sl) (fun s => sl_post sl s /\ Y (ps_mem s)) (sl_guar sl).

    Lemma newslotok_post_and (Γ : list (Slot VE VF)) sl (Y : State VE -> Prop) :
      NewSlotOK I R G k Pinit Γ sl ->
      (forall σ p γ σ', pre_of (Γ ++ [sl]) (length Γ) sl (σ, p, γ) -> I (σ, p, γ) ->
         Step VE (untag (sl_ev sl)) σ σ' -> Y σ') ->
      NewSlotOK I R G k Pinit Γ (slot_post_and sl Y).
    Proof.
      intros [Hg Hu Hes Hei HRs HRi Hins Hini Hios Hioi] HY.
      assert (He : evs (Γ ++ [slot_post_and sl Y]) = evs (Γ ++ [sl])) by (unfold evs; rewrite !map_app; reflexivity).
      constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar slot_post_and].
      - exact Hg.
      - intros σ p γ γ' [Hst Hin] HI Hge σ' Hs.
        assert (Hpre : pre_of (Γ ++ [sl]) (length Γ) sl (σ, p, γ)).
        { split; [exact Hst |]. intros d Hd. apply Hin. rewrite He. exact Hd. }
        destruct (Hu σ p γ γ' Hpre HI Hge σ' Hs) as (p' & Hps & Hq & HI' & Hg').
        exists p'. split; [exact Hps |]. split; [split; [exact Hq | exact (HY σ p γ σ' Hpre HI Hs)] |].
        split; [exact HI' | exact Hg'].
      - exact Hes.
      - intros d sd Hd. rewrite He in Hd. exact (Hei d sd Hd).
      - exact HRs.
      - intros d Hd. rewrite He in Hd. exact (HRi d Hd).
      - exact Hins.
      - intros d g sg Hd. rewrite He in Hd. exact (Hini d g sg Hd).
      - intros y sy Hsy Hnb. rewrite He in Hnb. exact (Hios y sy Hsy Hnb).
      - intros y sy d Hsy Hnb. rewrite He in Hnb. exact (Hioi y sy d Hsy Hnb).
    Qed.
  End SlotPostAnd.

  (** ** Part 6. The [EIhlv] instance of the lifting *)

  Section EIhlvLift.
    Import RelaxedHoareBase.
    Context {E F : RelaxedSig.t} {St StF : Type}.
    Context (δ : St -> forall o : Sig.op (RelaxedSig.effect E), Sig.ar o -> St -> Prop).
    Context (δF : StF -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> StF -> Prop) (s0 : StF).
    Local Abbreviation VB := (EIhl δ).
    Local Abbreviation V := (EIhlv δ).
    Local Abbreviation VF := (RelaxedHoareSpec.EI δF).

    (** The lifted invariant over [EIhlv]: [J := LogOK]. *)
    Definition liftIV (I : Assn VB VF) : Assn V VF := liftI (LogOK δ) I.

    (** RLHL hypotheses over [EIhlv δ] from derivations over [EIhlv δ] and
        the side fields over [EIhl δ]. *)
    Theorem rlhl2_eihlv_of_provable (I : Assn VB VF) (R G : CallKey F -> PRel VB VF)
        (M : RelaxedModuleImpl E F) (sE : St)
        (Hprov : forall t op, exists Ω Q, MethodProvable (liftIV I) (liftGLk R) (liftGLk G) M t op Ω Q)
        (Hgr : forall k k' s s', k <> k' -> G k s s' -> R k' s s')
        (Hir : forall k k' op tr ret s p', k <> k' ->
           program_produces_tagged (fst k) (M op (fst k)) tr ret -> I s ->
           poss_invoke VF (fst k) (snd k) op (ps_poss s) p' ->
           R k' s (ps_mem s, p', ps_ghost s ++ ghost_new k tr))
        (Hrr : forall k k' op r s p2, k <> k' -> I s ->
           poss_return VF (fst k) (snd k) op r (ps_poss s) p2 -> NoOwn k (ps_ghost s) ->
           R k' s (ps_mem s, p2, ps_ghost s))
        (Hok : forall s, I s -> exists v pool, ps_poss s = PossOk v pool /\ lin_pool_well_formed pool)
        (Hinit : I (((sE, []), []), @PossOk F VF (s0, []) [], [])) :
      RLHL2Hyps (liftIV I) (liftGLk R) (liftGLk G) M ((((sE, []), []), [])) (s0, []).
    Proof.
      exact (rlhl2_lift_of_provable (VE := VB) (VF := VF) (LogOK δ) I R G M ((sE, []), []) (s0, []) Hprov Hgr Hir Hrr Hok Hinit
               (logok_init δ sE)).
    Qed.

    (** The paper-facing form over [EIhlv]: derivations over [EIhlv δ],
        side fields over [EIhl δ], conclusion over the plain [EI δ].
        Uses [classic], inherited through [rlhl_complin_eihlv]. *)
    Corollary rlhl_sound_complin_eihlv (I : Assn VB VF) (R G : CallKey F -> PRel VB VF)
        (M : RelaxedModuleImpl E F) (sE : St)
        (Hprov : forall t op, exists Ω Q, MethodProvable (liftIV I) (liftGLk R) (liftGLk G) M t op Ω Q)
        (Hgr : forall k k' s s', k <> k' -> G k s s' -> R k' s s')
        (Hir : forall k k' op tr ret s p', k <> k' ->
           program_produces_tagged (fst k) (M op (fst k)) tr ret -> I s ->
           poss_invoke VF (fst k) (snd k) op (ps_poss s) p' ->
           R k' s (ps_mem s, p', ps_ghost s ++ ghost_new k tr))
        (Hrr : forall k k' op r s p2, k <> k' -> I s ->
           poss_return VF (fst k) (snd k) op r (ps_poss s) p2 -> NoOwn k (ps_ghost s) ->
           R k' s (ps_mem s, p2, ps_ghost s))
        (Hok : forall s, I s -> exists v pool, ps_poss s = PossOk v pool /\ lin_pool_well_formed pool)
        (Hinit : I (((sE, []), []), @PossOk F VF (s0, []) [], [])) :
      RCompLin M (RelaxedHoareSpec.EI δ) (sE, []) VF (s0, []).
    Proof.
      exact (rlhl_complin_eihlv δ δF s0 _ _ _ M (sE, [])
               (rlhl2_eihlv_of_provable I R G M sE Hprov Hgr Hir Hrr Hok Hinit)).
    Qed.

    (** The same, followed by [RelaxedHoareCompLinSpec.cc_rel_lin]: every
        complete overlay trace over the plain [EI δ] is
        relaxed-linearizable.  Uses [classic] and [eq_rect_eq],
        inherited through [rlhl_eihlv_rel_lin]. *)
    Corollary rlhl_sound_rel_lin_eihlv (I : Assn VB VF) (R G : CallKey F -> PRel VB VF)
        (M : RelaxedModuleImpl E F) (sE : St)
        (Hprov : forall t op, exists Ω Q, MethodProvable (liftIV I) (liftGLk R) (liftGLk G) M t op Ω Q)
        (Hgr : forall k k' s s', k <> k' -> G k s s' -> R k' s s')
        (Hir : forall k k' op tr ret s p', k <> k' ->
           program_produces_tagged (fst k) (M op (fst k)) tr ret -> I s ->
           poss_invoke VF (fst k) (snd k) op (ps_poss s) p' ->
           R k' s (ps_mem s, p', ps_ghost s ++ ghost_new k tr))
        (Hrr : forall k k' op r s p2, k <> k' -> I s ->
           poss_return VF (fst k) (snd k) op r (ps_poss s) p2 -> NoOwn k (ps_ghost s) ->
           R k' s (ps_mem s, p2, ps_ghost s))
        (Hok : forall s, I s -> exists v pool, ps_poss s = PossOk v pool /\ lin_pool_well_formed pool)
        (Hinit : I (((sE, []), []), @PossOk F VF (s0, []) [], [])) :
      forall s, MTraces (RelaxedHoareSpec.EI δ) M (sE, []) s -> PrefixView.complete s ->
        RelaxedTraceLin.rel_lin (@PrefixView.sel F) s (semi_independent F) (RelaxedHoareSpec.seq_legal δF s0).
    Proof.
      exact (rlhl_eihlv_rel_lin δ δF s0 _ _ _ M (sE, [])
               (rlhl2_eihlv_of_provable I R G M sE Hprov Hgr Hir Hrr Hok Hinit)).
    Qed.
  End EIhlvLift.

  (** ** Part 7. Smoke test: the [RunCounter] instance over [EIhlv]

      [RelaxedHoareRun.RunCounter] (the SI = ∅ FAA→Inc counter, body run
      by the one-call machine [one_next]) over [EIhlv uδ], twice:
      - (a) its [EIhl] derivation [RelaxedHoareRun.ren_run_provable],
        transferred by [methodprovable_lift] ([counter_run_provable_v]),
        with the side fields of [RelaxedHoareRun.RunCounter.counter_run_rlhl2]
        transferred by [rlhl2_eihlv_of_provable] ([counter_run_rlhl2_v]);
      - (b) a direct [rp_run] derivation over [EIhlv uδ]
        ([counter_log_provable]) whose postcondition also says that the
        underlay record [FAA ↦ r] of the call is in the history; the
        response slot carries it ([slot_post_and], [logval_res_logged]),
        the final edge keeps it under the lifted rely ([stable_logA]).
      Both give copy-cat inclusion over the plain [EI uδ] and relaxed
      linearizability of its complete traces. *)

  Module RunCounterLog.
    Import RelaxedHoareBase RelaxedHoareInherit RelaxedHoareRun RelaxedHoareRun.RunCounter.
    Local Abbreviation Ic := (Iren uδ cδ (fun n : nat => n) ρc (fun _ => true)).
    Local Abbreviation Rc := (Rren uδ cδ).
    Local Abbreviation Gc := (Gren uδ cδ).
    Local Abbreviation V := (EIhlv uδ).
    Local Abbreviation VF := (RelaxedHoareSpec.EI cδ).

    Definition IcV : Assn V VF := liftIV uδ cδ Ic.
    Definition RcV : CallKey OSig -> PRel V VF := liftGLk Rc.
    Definition GcV : CallKey OSig -> PRel V VF := liftGLk Gc.

    (** (a) The [EIhl] derivation, transferred. *)
    Theorem counter_run_provable_v t o :
      MethodProvable IcV RcV GcV Mc t o (fun _ => Ωren ρc t o) (fun h r => liftA (KLinr uδ cδ (t, h) o r)).
    Proof.
      exact (methodprovable_lift (LogOK uδ) (logok_mono uδ) Ic Rc Gc Mc t o _ _
               (ren_run_provable uδ cδ (fun n => n) ρc (fun _ => true) backc c_δ c_si (fun _ => eq_refl) c_inj t o)).
    Qed.

    Theorem counter_run_rlhl2_v : RLHL2Hyps IcV RcV GcV Mc ((((0, []), []), [])) (0, []).
    Proof.
      pose proof counter_run_rlhl2 as HH.
      exact (rlhl2_eihlv_of_provable uδ cδ 0 Ic Rc Gc Mc 0
               (fun t o => ex_intro _ _ (ex_intro _ _ (counter_run_provable_v t o)))
               (h_guar_rely _ _ _ _ _ _ HH) (h_invoke_rely _ _ _ _ _ _ HH) (h_return_rely _ _ _ _ _ _ HH)
               (h_ok _ _ _ _ _ _ HH) (h_init _ _ _ _ _ _ HH)).
    Qed.

    (** (b) A direct derivation over [EIhlv] whose postcondition uses the
        history. *)
    Section Direct.
      Context (t : tid).

      (** Linearized with [r], and the underlay record [FAA ↦ r] of the
          call is (or was) a record of the history. *)
      Definition QlogC (h : handle OSig) (r : nat) : Assn V VF := fun s =>
        liftA (KLinr uδ cδ (t, h) Inc r) s /\ exists hu, LogVal uδ (@Build_Op USig (t, hu) FAA r) (ps_mem s).

      Definition PiV (h : handle OSig) : Assn V VF := PostInvoke IcV (t, h) Inc (Ωren ρc t Inc).

      Definition slI (h hu : nat) : Slot V VF := liftSlot (sl_invD uδ cδ ρc backc t h Inc hu).

      Definition slR (h hu r : nat) : Slot V VF :=
        slot_post_and (liftSlot (sl_res uδ cδ ρc backc t h Inc hu r)) (LogVal uδ (@Build_Op USig (t, hu) FAA r)).

      Definition log_inv (h : handle OSig) (st : option nat) (cs : list (RCall USig)) (Γ : list (Slot V VF))
          (H : FutureStore USig) : Prop :=
        match st with
        | None => cs = [] /\ Γ = [] /\ H = empty_store
        | Some b => exists hu r, b = r /\ Γ = [slI h hu; slR h hu r]
        end.

      Lemma pi_drop h s : IcV s -> PiV h s -> liftA (PostInvoke Ic (t, h) Inc (Ωren ρc t Inc)) s.
      Proof. intros _ Hs. exact (proj1 (postinvoke_lift (LogOK uδ) Ic (t, h) Inc _ s Hs)). Qed.

      Lemma slI_new h hu : NewSlotOK IcV RcV GcV (t, h) (PiV h) [] (slI h hu).
      Proof.
        exact (newslotok_lift (LogOK uδ) (logok_mono uδ) Ic Rc Gc (t, h) _ (PiV h) (pi_drop h) [] _
                 (ren_run_newinv uδ cδ (fun n => n) ρc (fun _ => true) backc c_δ c_si (fun _ => eq_refl) t h Inc hu)).
      Qed.

      Lemma slR_new h hu r : NewSlotOK IcV RcV GcV (t, h) (PiV h) [slI h hu] (slR h hu r).
      Proof.
        apply newslotok_post_and.
        - exact (newslotok_lift (LogOK uδ) (logok_mono uδ) Ic Rc Gc (t, h) _ (PiV h) (pi_drop h) [_] _
                   (ren_run_newres uδ cδ (fun n => n) ρc (fun _ => true) backc c_inj t h Inc hu r)).
        - intros σ p γ σ' _ _ Hs. exact (logval_res_logged uδ t hu FAA r σ σ' Hs).
      Qed.

      Lemma log_close h hu r H :
        all_resolved H -> Close IcV RcV GcV (t, h) (PiV h) (QlogC h) r [slI h hu; slR h hu r] H.
      Proof.
        intros Hall. pose proof (ren_run_dprec uδ cδ ρc backc t h Inc hu r 0) as Hd01.
        apply close_done with
          (fin := fun d => match d with
                           | 1 => fun s => liftA (KLinr uδ cδ (t, h) Inc r) s /\
                                           LogVal uδ (@Build_Op USig (t, hu) FAA r) (ps_mem s)
                           | _ => fun _ => True end)
          (fin0 := fun _ => True); [exact Hall |].
        constructor.
        - intros d sd Hd. destruct d as [| [| d]]; cbn in Hd; try (destruct d; discriminate).
          + intros s _ _. exact Logic.I.
          + injection Hd as <-. intros s _ Hs. exact Hs.
        - intros s _ _. exact Logic.I.
        - intros d g sg Hd Hg Hnb. destruct d as [| [| d]]; [apply Stable_true | | cbn in Hd; lia].
          exfalso. apply Hnb. destruct g as [| [| g]]; [| apply before_refl | destruct g; discriminate].
          apply before_dprec. apply Hd01. reflexivity.
        - intros g sg _. apply Stable_true.
        - intros [| [| d]]; [apply Stable_true | | apply Stable_true].
          apply Stable_and.
          + apply stable_liftL. apply KLinr_stable.
          + exact (stable_logA IcV (Rc (t, h)) _ (logval_mono uδ _)).
        - apply Stable_true.
        - intros s _ _ Hfin. destruct (Hfin 1 (slR h hu r) eq_refl Logic.I) as [Hk Hl].
          split; [exact Hk | exists hu; exact Hl].
      Qed.

      (** The derivation, through [run_method_provable] (hence [rp_run]),
          over [EIhlv uδ]. *)
      Theorem counter_log_provable :
        MethodProvable IcV RcV GcV Mc t Inc (fun _ => Ωren ρc t Inc) QlogC.
      Proof.
        apply (run_method_provable IcV RcV GcV Mc t Inc _ _ (one_next (S := UEff) FAA (fun r : nat => r)) None log_inv).
        - reflexivity.
        - intros h s Hs. destruct (postinvoke_lift (LogOK uδ) Ic (t, h) Inc _ s Hs) as [Hs' HJs].
          split; [exact (ren_PI uδ cδ (fun n => n) ρc (fun _ => true) (fun _ => eq_refl) t h Inc _ Hs') | exact HJs].
        - intros h r s [HQ _] [HI HJs] Hno. apply (retcond_lift (LogOK uδ) Ic Gc (t, h) Inc r s HJs).
          exact (ren_ret uδ cδ (fun n => n) ρc (fun _ => true) t h Inc r (dropS s) HQ HI Hno).
        - intros h. cbn. auto.
        - intros h st cs Γ H Hc Hi. destruct st as [b |]; cbn in Hi |- *.
          + destruct Hi as (hu & r & -> & ->). split.
            * apply log_close. exact (proj1 (proj2 (runctx_store _ _ _ _ Hc))).
            * exists hu. reflexivity.
          + destruct Hi as (-> & -> & ->).
            exists (slI h), (slR h).
            split; [intros hu; reflexivity |]. split; [intros hu _; apply slI_new |].
            split; [intros hu v; reflexivity |]. split; [intros hu v _; apply slR_new |].
            intros hu v H' _ _ _. exists hu, v. split; reflexivity.
      Qed.
    End Direct.

    Theorem counter_log_rlhl2_v : RLHL2Hyps IcV RcV GcV Mc ((((0, []), []), [])) (0, []).
    Proof.
      pose proof counter_run_rlhl2 as HH.
      apply (rlhl2_eihlv_of_provable uδ cδ 0 Ic Rc Gc Mc 0).
      - intros t []. exists (fun _ => Ωren ρc t Inc), (QlogC t). exact (counter_log_provable t).
      - exact (h_guar_rely _ _ _ _ _ _ HH).
      - exact (h_invoke_rely _ _ _ _ _ _ HH).
      - exact (h_return_rely _ _ _ _ _ _ HH).
      - exact (h_ok _ _ _ _ _ _ HH).
      - exact (h_init _ _ _ _ _ _ HH).
    Qed.

    (** Copy-cat inclusion over the plain [EI uδ] ([classic], through
        [rlhl_complin_eihlv]), and relaxed linearizability of its complete
        traces ([classic], [eq_rect_eq], through [cc_rel_lin]). *)
    Corollary counter_log_complin :
      RCompLin Mc (RelaxedHoareSpec.EI uδ) (0, []) VF (0, []).
    Proof. exact (rlhl_complin_eihlv uδ cδ 0 _ _ _ Mc (0, []) counter_log_rlhl2_v). Qed.

    Corollary counter_log_rel_lin s :
      MTraces (RelaxedHoareSpec.EI uδ) Mc (0, []) s -> PrefixView.complete s ->
      RelaxedTraceLin.rel_lin (@PrefixView.sel OSig) s (semi_independent OSig) (RelaxedHoareSpec.seq_legal cδ 0).
    Proof. exact (rlhl_eihlv_rel_lin uδ cδ 0 _ _ _ Mc (0, []) counter_log_rlhl2_v s). Qed.
  End RunCounterLog.

End RelaxedHoareLog.
