(** * RLHL errors: trace-level error clause with an implementation-side
      obligation (task RLHL-latch L.10, plan §2.1; latest-review m-8)

    Purpose.  The author decided (research-intent §8, 2026-10-13 "Add TErr
    like CompLin", and 2026-10-15 "m-8 / D5 (i): accepted") that the
    relaxed copy-cat comparison gets a CompLin-style undefined-behaviour
    clause, *and* that the implementation bears the error obligation: a
    module that misuses its underlay produces an error trace, which its own
    specification must license.  This file gives the trace-level
    definitions of that clause, beside the old error-free ones of
    [RelaxedHoareCompLin] (nothing old is changed), and the lemmas that
    connect the two.  It contains no RLHL rule and no simulation with
    errors (plan items A2/A3, [GSimRelErr], [RLHL2HypsE], are deferred).

    ** Definitions

    - [TItem F]: a trace item, an overlay event [TEv e] or the error marker
      [TErr k op], tagged with the overlay key [k] and the overlay
      operation [op] of the call that erred (D5 (iv), RD-9).
    - [module_error_tagged VE k op c]: the tagged error rule.  Some
      frontier candidate of [c] ([select_frontier_tagged], so it could be
      emitted now) is an [Error] of [VE] at the current underlay state,
      and its owner [k] is an active call of operation [op].  It is the
      tagged-frontier analogue of [RelaxedModuleSemantics.module_error_at]
      and of CompLin's [TraceStepError] (CompLin.v:122-125).
    - [MTracesE VE M σ0 s]: [s] is [map TEv] of the overlay trace of an
      execution of [M] over [VE] (any length, pending calls allowed), or
      that followed by one [TErr k op] for an error enabled at the final
      configuration.  The analogue of [CompLin.ImplTraces].  Differences:
      the marker can only be the last item (CompLin's trace may continue
      after [TErr]; the closure below licenses every continuation of an
      error prefix, so restricting the implementation side to traces that
      end at the first marker loses nothing: a longer CompLin trace has a
      prefix ending in its first marker, and a licence of that prefix
      licenses the longer trace).
    - [RTracesClosed VF v s]: [MTracesE VF idF v s], or [s] extends a
      prefix [p] such that [p ++ [TErr k op]] is an error trace of the
      copy-cat over [VF].  The analogue of [CompLin.ImplTracesClosed]
      (CompLin.v:150-153).
    - [RCompLinErr M VE σ0 VF v0]: every [MTracesE VE M σ0] trace is in
      [RTracesClosed VF v0].  The analogue of [CompLin.CompLin]
      (Def. 4.1), now with both the spec-side licence and the
      implementation-side obligation: an implementation error
      ([TErr] produced by [M] over [VE]) must itself be in
      [RTracesClosed], i.e. licensed by a copy-cat error over [VF] at the
      same or an earlier point.
    - [Licensed VF v s]: some prefix of [map TEv s] followed by a copy-cat
      error marker is an [MTracesE VF idF v] trace (undefined behaviour of
      the specification before or at the end of [s]).
    - [EIe δ bad]: the sequential specification LTS [RelaxedHoareSpec.EI
      δ] with an explicit precondition.  Its steps are exactly those of
      [EI δ] ([ei_step δ]); its [Error] holds at an invocation of [o] by
      thread [t] in EI state [σ] when [bad σ t o] (D5 (ii), RD-9: [bad]
      receives the thread id and the whole EI state, including the
      pending records).  Steps at bad invocations are not removed: under
      the closure this makes no difference, and the error-free part of
      [EIe] is literally [EI δ] ([mtraces_eie_ei]).

    ** Results

    - [mtraces_in_mtracesE], [mtracesE_noerr], [mtracesE_map_TEv]: the
      error-free part of [MTracesE] is [MTraces].
    - [rtraces_closed_of_rtraces], [rtraces_closed_split] (a closed trace
      of the form [map TEv s] is a copy-cat trace or [Licensed]),
      [rtraces_closed_of_licensed], [licensed_app] (a licence extends to
      every continuation), [licensed_noerr], [rtraces_closed_noerr].
    - [rcomplin_err_of_rcomplin] (no [Error] in [VE]: old ⇒ new) and
      [rcomplin_of_err] (no [Error] in [VF]: new ⇒ old).
    - [hliftE]: [MTracesE VE M σ0 s <-> MTracesE (HL VE) M (σ0, []) s];
      [HL] lifts [Error] pointwise, [Error (HL V) ev σ = Error V ev (fst
      σ)], and the key list never matters for [MTracesE].  Corollaries
      [complinE_hlift_under], [rtraces_closed_hlift].
    - [mtraces_eie_ei]: [MTraces (EIe δ bad) M σ s <-> MTraces (EI δ) M σ
      s]; [rtraces_eie_ei] is the copy-cat instance.  [TaggedModuleConfig (EIe δ bad)] and [TaggedModuleConfig (EI
      δ)] are different types (the record is indexed by the LTS), so this
      is a configuration transport ([cfg_ie], [cfg_ei]), not a
      conversion.
    - [complin_err_rel_lin]: from [RCompLinErr M VE σ0 (EIe δ bad) (s0,
      [])], every complete, unlicensed overlay trace of [M] over [VE] is
      relaxed-linearizable to [seq_legal δ s0] (via
      [RelaxedHoareCompLinSpec.cc_rel_lin]).
    - [pool_keys_trace]: in every reachable configuration the keys of the
      call pool are exactly the overlay keys invoked so far, newest first:
      [map call_key (tm_calls c) = rev (invocation_keys (overlay_events
      evs))] (returned calls stay as [DeadCall]).  With
      [ov_inv_keys_nodup] (overlay keys are never reused) and
      [res_key_in_pool] (a responded key is in the pool).
    - Copy-cat facts over any [V]: [cc_used_threads] (one underlay key per
      copy-cat call, on the call's thread), [cc_pending] (a queued
      underlay invocation belongs to a call that is invoked and not
      returned in the overlay trace, with the same operation),
      [cc_fresh_handle_cl] (an unused underlay handle of a thread exists
      while the thread has a fresh overlay key; [classic]).
    - [cc_license_cfg], [cc_license_gen], [cc_license_gen_cl]: if [p] is a
      copy-cat trace over [V], [(t, h)] is not invoked in [p], every
      invocation of [op] by [t] is an [Error] of [V] in every state, and
      every call of [t] pending in [p] has an operation semi-independent
      of [op], then [Licensed V v (p ++ [inv t h op])].
      [cc_license_indep], [cc_license_indep_cl]: the instance [V := EIe δ
      bad] from [RTraces (EI δ) (s0, []) p] (plan §2.1).

    ** K / S / P / R

    - K: Rocq 9.3.0.  Every result is closed under the global context
      except: [complin_err_rel_lin] uses [Eqdep.Eq_rect_eq.eq_rect_eq] and
      [Classical_Prop.classic], both inherited from
      [RelaxedHoareCompLinSpec.cc_rel_lin] (through
      [RelaxedGSim.gsim_rel_lin] and [RelaxedHoareCompLin.rinv_val]);
      [cc_fresh_handle_cl], [cc_license_gen_cl] and [cc_license_indep_cl]
      use [Classical_Prop.classic] (in [cc_fresh_handle_cl], through
      [NNPP]), to pick an unused underlay handle (below).  No dependent equality on [ResEv] / [ActiveCall] is
      inverted.
    - S: all statements are generic in the LTSs, modules and signatures,
      cover every execution (complete or not), and change no existing
      definition.  [complin_err_rel_lin] is for complete traces only and
      excludes licensed traces (a licensed trace is undefined behaviour of
      the specification: no claim).  [cc_license_*] need an inhabitant
      [r0 : Sig.ar op] (the copy-cat commits its result at the overlay
      invocation; a module that can invoke [op] at all supplies one) and,
      for the closed versions, an inexhaustible handle type
      ([forall l, exists h', ~ In h' l]; [nat_inexhaustible] discharges it
      for [handle := nat]).  The [_cl] versions drop the latter: by
      [cc_used_threads] the copy-cat has used exactly one underlay key of
      thread [t] per overlay call of [t] in [p], all distinct, while [h]
      and the handles of those calls are one more distinct handle of [t],
      so by pigeonhole ([NoDup_incl_length]) not every handle of [t] is
      used; extracting the unused one from this double negation is where
      [classic] enters (handles have no decidable equality).
    - P: the paper has no error or undefined-behaviour clause; its
      soundness proposition (Appendix/relaxedlin.tex:665-667, ν_E;cc_E;M ⊆
      ν_F;cc_F) is error-free.  The clause here is CompLin's (CompLin.v
      Def. 4.1, [ImplTracesClosed]), as decided by the author (m-8,
      research-intent §8).  Nothing in the paper can cite this file yet.
    - R: latest-review m-8 (MAJOR after RLHL-3a iteration 2): a spec-side
      licence alone is unsound for layering; the implementation must also
      be obliged.  [RCompLinErr] carries that obligation;
      [examples/Relaxed/RelaxedHoareLockErr.v] (negative half of [m8_gap])
      shows that it rejects a module that misuses a lower lock with a
      precondition.  For LatchSet's underlay [EIhl δcoh] the obligation is
      vacuous ([Error := False]), so [cc_license_indep] is the piece the
      LatchSet error form ([latch_complin_err], task L.11) needs.

    ** Provisional decisions relied on (research-intent §7, not yet put to
       the author)

    - RD-9 / D5 (ii): [EIe] with an explicit [bad] taking the EI state and
      the thread id.  D5 (iv): [TErr] tagged with (key, op).  D5 (vi)
      ([PossError] absorbs) concerns the deferred [GSimRelErr]; nothing
      here depends on it.  D5 (iii) (licensed [cte_noerr]) and (v)
      (error-aware layering) are deferred (RD-9).
    - RD-1: LatchSet's error form is derived from an error-free RLHL proof
      plus [cc_license_indep], not from [GSimRelErr] / [RLHL2HypsE].
    - RD-10: the negative half of [m8_gap] is in the first deliverable
      ([RelaxedHoareLockErr]).

    ** Known limitations

    - No error-aware simulation or logic: [GSimRelErr], [gsim_complin_err],
      [CallTripleE], [RLHL2HypsE], [method_soundE] (plan A2/A3) are not
      here.  So no RLHL-verified module is yet shown to satisfy
      [RCompLinErr] over an erroring underlay.
    - Licensing is existential over copy-cat runs, as in CompLin: a trace
      is licensed if *some* copy-cat run of a prefix errs.  For a
      state-dependent [bad] this is angelic towards errors (design A §12
      item 1).  [cc_license_*] avoid the issue by requiring a
      state-independent [bad].
    - Thread-unaware [δ] (m-37): [bad] sees the thread id, [δ] does not.
    - [hliftE]'s [Error (HL V)] also holds at already-used keys, where
      [Step (HL V)] is disabled; this matters only for the deferred
      RLHL-side obligation (design A §7). *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.PArith.PArith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Logic.Classical_Prop.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedGSim.
Require Import models.view.PrefixView.
Require Import models.simlin.RelaxedHoareSpec.
Require Import models.simlin.RelaxedHoareCompLin.
Require Import models.simlin.RelaxedHoareCompLinSpec.

Import ListNotations.


Module RelaxedHoareErrSpec.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedTraceLin.
  Import RelaxedGSim.
  Import RelaxedHoareCompLin.

  (** ** Part 1: definitions *)

  Variant TItem (F : RelaxedSig.t) : Type :=
  | TEv (e : ThreadEvent F)
  | TErr (k : CallKey F) (op : Sig.op (RelaxedSig.effect F)).

  Arguments TItem _ : clear implicits.
  Arguments TEv {F} _.
  Arguments TErr {F} _ _.

  (** The tagged error rule: a frontier candidate whose event is an
      [Error] of [VE] in the current underlay state, owned by an active
      call [k] of operation [op]. *)
  Inductive module_error_tagged {E F : RelaxedSig.t} (VE : LTS E) :
      CallKey F -> Sig.op (RelaxedSig.effect F) -> @TaggedModuleConfig E F VE -> Prop :=
  | tagged_error (cand : TaggedScheduledEvent E F) (op : Sig.op (RelaxedSig.effect F)) (ret : Sig.ar op)
      q pool queue queue' used
      (Hsel : select_frontier_tagged cand queue queue')
      (Hact : In (Build_CallEntry (fst (ts_owner cand)) (snd (ts_owner cand)) (ActiveCall op ret)) pool)
      (Herr : Error VE (untag (ts_event cand)) q) :
      module_error_tagged VE (ts_owner cand) op (Build_TaggedModuleConfig q pool queue used).

  (** The traces of [M] over [VE], with a final error marker when an
      error is enabled: the analogue of [CompLin.ImplTraces]. *)
  Definition MTracesE {E F : RelaxedSig.t} (VE : LTS E) (M : RelaxedModuleImpl E F) (σ0 : State VE)
      (s : list (TItem F)) : Prop :=
    exists evs c, module_execution_tagged VE M (initial_tagged_module VE σ0) evs c /\
      (s = map TEv (overlay_events evs) \/
       exists k op, module_error_tagged VE k op c /\ s = map TEv (overlay_events evs) ++ [TErr k op]).

  (** The copy-cat's traces over [VF], closed under undefined behaviour:
      the analogue of [CompLin.ImplTracesClosed]. *)
  Definition RTracesClosed {F : RelaxedSig.t} (VF : LTS F) (v : State VF) (s : list (TItem F)) : Prop :=
    MTracesE VF idF v s \/ exists p k op tl, MTracesE VF idF v (p ++ [TErr k op]) /\ s = p ++ tl.

  (** The analogue of [CompLin.CompLin] (Def. 4.1) with the error clause
      on both sides. *)
  Definition RCompLinErr {E F : RelaxedSig.t} (M : RelaxedModuleImpl E F) (VE : LTS E) (σ0 : State VE)
      (VF : LTS F) (v0 : State VF) : Prop :=
    forall s, MTracesE VE M σ0 s -> RTracesClosed VF v0 s.

  (** Undefined behaviour of the specification at or before the end of
      [s]. *)
  Definition Licensed {F : RelaxedSig.t} (VF : LTS F) (v : State VF) (s : list (ThreadEvent F)) : Prop :=
    exists p k op tl, MTracesE VF idF v (p ++ [TErr k op]) /\ map TEv s = p ++ tl.

  (** [EI δ] with an explicit precondition: an invocation of [o] by [t]
      in EI state [σ] is an error when [bad σ t o]. *)
  Section EIe.
    Context {F : RelaxedSig.t} {St : Type}.
    Context (δ : St -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> St -> Prop).
    Context (bad : St * list (Op F) -> tid -> Sig.op (RelaxedSig.effect F) -> Prop).

    Definition eie_error (ev : ThreadEvent F) (s : St * list (Op F)) : Prop :=
      match te_ev F ev with InvEv _ o => bad s (te_tid F ev) o | ResEv _ _ _ => False end.

    Definition EIe : LTS F :=
      {| State := (St * list (Op F))%type; Step := RelaxedHoareSpec.ei_step δ; Error := eie_error |}.
  End EIe.

  (** ** Part 2: [TItem] lists and the error-free part *)

  Section Items.
    Context {F : RelaxedSig.t}.

    Lemma TEv_inj (e e' : ThreadEvent F) : TEv e = TEv e' -> e = e'.
    Proof. intros H. injection H as H. exact H. Qed.

    Lemma map_TEv_inj (s s' : list (ThreadEvent F)) : map TEv s = map TEv s' -> s = s'.
    Proof.
      revert s'. induction s as [| e s IH]; intros [| e' s'] H; cbn in H; try discriminate H; [reflexivity |].
      injection H as He Hs. f_equal; [exact He | exact (IH s' Hs)].
    Qed.

    Lemma TErr_notin_map (s : list (ThreadEvent F)) k op : ~ In (TErr k op) (map TEv s).
    Proof. intros Hin. apply in_map_iff in Hin as (e & He & _). discriminate He. Qed.

    Lemma map_TEv_ne_err (s : list (ThreadEvent F)) p k op : map TEv s <> p ++ [TErr k op].
    Proof.
      intros H. apply (TErr_notin_map s k op). rewrite H. apply in_or_app. right. left. reflexivity.
    Qed.
  End Items.

  Lemma module_error_tagged_noerr {E F : RelaxedSig.t} (VE : LTS E) (k : CallKey F) op c :
    (forall ev q, ~ Error VE ev q) -> ~ module_error_tagged VE k op c.
  Proof. intros Hne Herr. destruct Herr as [cand op ret q pool queue queue' used Hsel Hact Herr]. exact (Hne _ _ Herr). Qed.

  Lemma mtraces_in_mtracesE {E F : RelaxedSig.t} (VE : LTS E) (M : RelaxedModuleImpl E F) (σ0 : State VE) s :
    MTraces VE M σ0 s -> MTracesE VE M σ0 (map TEv s).
  Proof. intros (evs & c & Hex & <-). exists evs, c. split; [exact Hex | left; reflexivity]. Qed.

  Lemma mtracesE_noerr {E F : RelaxedSig.t} (VE : LTS E) (M : RelaxedModuleImpl E F) (σ0 : State VE) s :
    (forall ev q, ~ Error VE ev q) -> MTracesE VE M σ0 s -> exists s', s = map TEv s' /\ MTraces VE M σ0 s'.
  Proof.
    intros Hne (evs & c & Hex & [-> | (k & op & Herr & ->)]).
    - exists (overlay_events evs). split; [reflexivity |]. exists evs, c. auto.
    - exfalso. exact (module_error_tagged_noerr VE k op c Hne Herr).
  Qed.

  Lemma mtracesE_map_TEv {E F : RelaxedSig.t} (VE : LTS E) (M : RelaxedModuleImpl E F) (σ0 : State VE) s :
    MTracesE VE M σ0 (map TEv s) -> MTraces VE M σ0 s.
  Proof.
    intros (evs & c & Hex & [Heq | (k & op & _ & Heq)]).
    - exists evs, c. split; [exact Hex |]. symmetry. exact (map_TEv_inj _ _ Heq).
    - exfalso. exact (map_TEv_ne_err _ _ _ _ Heq).
  Qed.

  Lemma rtraces_closed_of_rtraces {F : RelaxedSig.t} (VF : LTS F) (v : State VF) s :
    RTraces VF v s -> RTracesClosed VF v (map TEv s).
  Proof. intros H. left. exact (mtraces_in_mtracesE VF idF v s H). Qed.

  Lemma rtraces_closed_of_licensed {F : RelaxedSig.t} (VF : LTS F) (v : State VF) s :
    Licensed VF v s -> RTracesClosed VF v (map TEv s).
  Proof. intros (p & k & op & tl & H & Heq). right. exists p, k, op, tl. auto. Qed.

  (** A closed trace without error marker is a copy-cat trace or is
      licensed. *)
  Lemma rtraces_closed_split {F : RelaxedSig.t} (VF : LTS F) (v : State VF) s :
    RTracesClosed VF v (map TEv s) -> RTraces VF v s \/ Licensed VF v s.
  Proof.
    intros [H | (p & k & op & tl & H & Heq)].
    - left. exact (mtracesE_map_TEv VF idF v s H).
    - right. exists p, k, op, tl. auto.
  Qed.

  (** A licence extends to every continuation. *)
  Lemma licensed_app {F : RelaxedSig.t} (VF : LTS F) (v : State VF) s s' :
    Licensed VF v s -> Licensed VF v (s ++ s').
  Proof.
    intros (p & k & op & tl & H & Heq). exists p, k, op, (tl ++ map TEv s'). split; [exact H |].
    rewrite map_app, Heq, app_assoc. reflexivity.
  Qed.

  Lemma licensed_noerr {F : RelaxedSig.t} (VF : LTS F) (v : State VF) s :
    (forall ev q, ~ Error VF ev q) -> ~ Licensed VF v s.
  Proof.
    intros Hne (p & k & op & tl & H & _). destruct (mtracesE_noerr VF idF v _ Hne H) as (s' & Hs' & _).
    exact (map_TEv_ne_err s' p k op (eq_sym Hs')).
  Qed.

  (** Over an error-free [VF] the closure adds nothing. *)
  Lemma rtraces_closed_noerr {F : RelaxedSig.t} (VF : LTS F) (v : State VF) s :
    (forall ev q, ~ Error VF ev q) -> RTracesClosed VF v s -> exists s', s = map TEv s' /\ RTraces VF v s'.
  Proof.
    intros Hne [H | (p & k & op & tl & H & _)].
    - exact (mtracesE_noerr VF idF v s Hne H).
    - exfalso. destruct (mtracesE_noerr VF idF v _ Hne H) as (s' & Hs' & _).
      exact (map_TEv_ne_err s' p k op (eq_sym Hs')).
  Qed.

  (** Old ⇒ new when the underlay has no error. *)
  Lemma rcomplin_err_of_rcomplin {E F : RelaxedSig.t} (M : RelaxedModuleImpl E F) (VE : LTS E) (σ0 : State VE)
      (VF : LTS F) (v0 : State VF) :
    (forall ev q, ~ Error VE ev q) -> RCompLin M VE σ0 VF v0 -> RCompLinErr M VE σ0 VF v0.
  Proof.
    intros Hne HC s Hs. destruct (mtracesE_noerr VE M σ0 s Hne Hs) as (s' & -> & Hs').
    apply rtraces_closed_of_rtraces. exact (HC s' Hs').
  Qed.

  (** New ⇒ old when the overlay has no error: a copy-cat [TErr] needs
      [Error VF]. *)
  Lemma rcomplin_of_err {E F : RelaxedSig.t} (M : RelaxedModuleImpl E F) (VE : LTS E) (σ0 : State VE)
      (VF : LTS F) (v0 : State VF) :
    (forall ev q, ~ Error VF ev q) -> RCompLinErr M VE σ0 VF v0 -> RCompLin M VE σ0 VF v0.
  Proof.
    intros Hne HC s Hs.
    destruct (rtraces_closed_split VF v0 s (HC _ (mtraces_in_mtracesE VE M σ0 s Hs))) as [H | H]; [exact H |].
    exfalso. exact (licensed_noerr VF v0 s Hne H).
  Qed.

  (** ** Part 3: [HL] lifts [Error] correctly *)

  Section HLE.
    Context {E G : RelaxedSig.t} (VE : LTS E) (M : RelaxedModuleImpl E G).

    Lemma error_lift (k : CallKey G) op c u :
      module_error_tagged VE k op c -> module_error_tagged (RelaxedHoareCompLinSpec.HL VE) k op
                                         (RelaxedHoareCompLinSpec.lift_cfg VE c u).
    Proof.
      destruct 1 as [cand op ret q pool queue queue' used Hsel Hact Herr]. unfold RelaxedHoareCompLinSpec.lift_cfg. cbn.
      exact (tagged_error (RelaxedHoareCompLinSpec.HL VE) cand op ret (q, u) pool queue queue' used Hsel Hact Herr).
    Qed.

    Lemma error_drop (k : CallKey G) op c :
      module_error_tagged (RelaxedHoareCompLinSpec.HL VE) k op c ->
      module_error_tagged VE k op (RelaxedHoareCompLinSpec.drop_cfg VE c).
    Proof.
      destruct 1 as [cand op ret q pool queue queue' used Hsel Hact Herr].
      exact (tagged_error VE cand op ret (fst q) pool queue queue' used Hsel Hact Herr).
    Qed.

    (** [HLift] with errors: the error traces of [M] over [VE] and over
        [HL VE] (from the empty key list) coincide. *)
    Theorem hliftE (σ0 : State VE) (s : list (TItem G)) :
      MTracesE VE M σ0 s <-> MTracesE (RelaxedHoareCompLinSpec.HL VE) M (σ0, []) s.
    Proof.
      split.
      - intros (evs & c & Hex & Hs).
        destruct (RelaxedHoareCompLinSpec.lift_exec VE M _ _ _ Hex []
                    ltac:(split; [constructor | split; [intros k [] | intros k []]])) as (u & Hex').
        exists evs, (RelaxedHoareCompLinSpec.lift_cfg VE c u). split; [exact Hex' |].
        destruct Hs as [-> | (k & op & Herr & ->)]; [left; reflexivity |].
        right. exists k, op. split; [exact (error_lift k op c u Herr) | reflexivity].
      - intros (evs & c & Hex & Hs). exists evs, (RelaxedHoareCompLinSpec.drop_cfg VE c).
        split; [exact (RelaxedHoareCompLinSpec.drop_exec VE M _ _ _ Hex) |].
        destruct Hs as [-> | (k & op & Herr & ->)]; [left; reflexivity |].
        right. exists k, op. split; [exact (error_drop k op c Herr) | reflexivity].
    Qed.
  End HLE.

  Corollary complinE_hlift_under {E F : RelaxedSig.t} (M : RelaxedModuleImpl E F) (VE : LTS E) (σ0 : State VE)
      (VF : LTS F) (v0 : State VF) :
    RCompLinErr M VE σ0 VF v0 <-> RCompLinErr M (RelaxedHoareCompLinSpec.HL VE) (σ0, []) VF v0.
  Proof. split; intros HC s Hs; apply HC; apply (hliftE VE M σ0 s); exact Hs. Qed.

  Corollary rtraces_closed_hlift {F : RelaxedSig.t} (VF : LTS F) (v : State VF) s :
    RTracesClosed VF v s <-> RTracesClosed (RelaxedHoareCompLinSpec.HL VF) (v, []) s.
  Proof.
    split.
    - intros [H | (p & k & op & tl & H & Heq)]; [left; apply (hliftE VF idF v s); exact H |].
      right. exists p, k, op, tl. split; [apply (hliftE VF idF v); exact H | exact Heq].
    - intros [H | (p & k & op & tl & H & Heq)]; [left; apply (hliftE VF idF v s); exact H |].
      right. exists p, k, op, tl. split; [apply (hliftE VF idF v); exact H | exact Heq].
  Qed.

  (** ** Part 4: [EIe δ bad] and [EI δ] have the same error-free traces

      [TaggedModuleConfig] is indexed by the LTS, so a configuration over
      [EIe δ bad] is not a configuration over [EI δ]; the two record types
      have convertible fields, and [cfg_ie] / [cfg_ei] copy them. *)

  Section EIeEI.
    Context {F : RelaxedSig.t} {St : Type}.
    Context (δ : St -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> St -> Prop).
    Context (bad : St * list (Op F) -> tid -> Sig.op (RelaxedSig.effect F) -> Prop).
    Context {G : RelaxedSig.t} (M : RelaxedModuleImpl F G).

    Definition cfg_ie (c : @TaggedModuleConfig F G (EIe δ bad)) : @TaggedModuleConfig F G (RelaxedHoareSpec.EI δ) :=
      @Build_TaggedModuleConfig F G (RelaxedHoareSpec.EI δ) (tm_lts_state c) (tm_calls c) (tm_queue c) (tm_used_underlay c).

    Definition cfg_ei (c : @TaggedModuleConfig F G (RelaxedHoareSpec.EI δ)) : @TaggedModuleConfig F G (EIe δ bad) :=
      @Build_TaggedModuleConfig F G (EIe δ bad) (tm_lts_state c) (tm_calls c) (tm_queue c) (tm_used_underlay c).

    Lemma step_ie ev c c' :
      module_step_tagged (EIe δ bad) M ev c c' -> module_step_tagged (RelaxedHoareSpec.EI δ) M ev (cfg_ie c) (cfg_ie c').
    Proof.
      destruct 1 as [t h op q pool Q used tr ret Hcf Hprod Hft
                    | cand q q' pool Q Q' used Hsel Hlts
                    | t h op ret q pool pool' Q used Hfin Hdone]; cbn.
      - exact (tagged_invoke (RelaxedHoareSpec.EI δ) M t h op q pool Q used tr ret Hcf Hprod Hft).
      - exact (tagged_underlay (RelaxedHoareSpec.EI δ) M cand q q' pool Q Q' used Hsel Hlts).
      - exact (tagged_return (RelaxedHoareSpec.EI δ) M t h op ret q pool pool' Q used Hfin Hdone).
    Qed.

    Lemma step_ei ev c c' :
      module_step_tagged (RelaxedHoareSpec.EI δ) M ev c c' -> module_step_tagged (EIe δ bad) M ev (cfg_ei c) (cfg_ei c').
    Proof.
      destruct 1 as [t h op q pool Q used tr ret Hcf Hprod Hft
                    | cand q q' pool Q Q' used Hsel Hlts
                    | t h op ret q pool pool' Q used Hfin Hdone]; cbn.
      - exact (tagged_invoke (EIe δ bad) M t h op q pool Q used tr ret Hcf Hprod Hft).
      - exact (tagged_underlay (EIe δ bad) M cand q q' pool Q Q' used Hsel Hlts).
      - exact (tagged_return (EIe δ bad) M t h op ret q pool pool' Q used Hfin Hdone).
    Qed.

    Lemma exec_ie c evs c' :
      module_execution_tagged (EIe δ bad) M c evs c' ->
      module_execution_tagged (RelaxedHoareSpec.EI δ) M (cfg_ie c) evs (cfg_ie c').
    Proof.
      induction 1 as [c | c1 c2 c3 ev evs Hst Hex IH]; [constructor |].
      econstructor; [exact (step_ie _ _ _ Hst) | exact IH].
    Qed.

    Lemma exec_ei c evs c' :
      module_execution_tagged (RelaxedHoareSpec.EI δ) M c evs c' ->
      module_execution_tagged (EIe δ bad) M (cfg_ei c) evs (cfg_ei c').
    Proof.
      induction 1 as [c | c1 c2 c3 ev evs Hst Hex IH]; [constructor |].
      econstructor; [exact (step_ei _ _ _ Hst) | exact IH].
    Qed.

    Theorem mtraces_eie_ei (σ : St * list (Op F)) (s : list (ThreadEvent G)) :
      MTraces (EIe δ bad) M σ s <-> MTraces (RelaxedHoareSpec.EI δ) M σ s.
    Proof.
      split.
      - intros (evs & c & Hex & Hov). exists evs, (cfg_ie c). split; [exact (exec_ie _ _ _ Hex) | exact Hov].
      - intros (evs & c & Hex & Hov). exists evs, (cfg_ei c). split; [exact (exec_ei _ _ _ Hex) | exact Hov].
    Qed.
  End EIeEI.

  Corollary rtraces_eie_ei {F : RelaxedSig.t} {St : Type}
      (δ : St -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> St -> Prop)
      (bad : St * list (Op F) -> tid -> Sig.op (RelaxedSig.effect F) -> Prop) (σ : St * list (Op F)) s :
    RTraces (EIe δ bad) σ s <-> RTraces (RelaxedHoareSpec.EI δ) σ s.
  Proof. exact (mtraces_eie_ei δ bad idF σ s). Qed.

  (** ** Part 5: what [RCompLinErr] into [EIe δ bad] means for complete
      traces *)

  (** Every complete overlay trace of [M] over [VE] that the
      specification does not license is relaxed-linearizable to the
      sequential specification [seq_legal δ s0].  Axioms: those of
      [RelaxedHoareCompLinSpec.cc_rel_lin]. *)
  Theorem complin_err_rel_lin {E F : RelaxedSig.t} {St : Type}
      (δ : St -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> St -> Prop)
      (bad : St * list (Op F) -> tid -> Sig.op (RelaxedSig.effect F) -> Prop) (s0 : St)
      (M : RelaxedModuleImpl E F) (VE : LTS E) (σ0 : State VE) :
    RCompLinErr M VE σ0 (EIe δ bad) (s0, []) ->
    forall s, MTraces VE M σ0 s -> PrefixView.complete s -> ~ Licensed (EIe δ bad) (s0, []) s ->
      rel_lin (@PrefixView.sel F) s (semi_independent F) (RelaxedHoareSpec.seq_legal δ s0).
  Proof.
    intros HC s Hs Hc Hnl.
    destruct (rtraces_closed_split (EIe δ bad) (s0, []) s (HC _ (mtraces_in_mtracesE VE M σ0 s Hs))) as [Hr | Hl];
      [| contradiction].
    apply (RelaxedHoareCompLinSpec.cc_rel_lin δ s0 s); [| exact Hc].
    apply (rtraces_eie_ei δ bad (s0, []) s). exact Hr.
  Qed.

  (** ** Part 6: call-pool keys are the invoked overlay keys *)

  Section Keys.
    Context {F : RelaxedSig.t}.

    Lemma ikeys_app (l l' : list (ThreadEvent F)) :
      invocation_keys (l ++ l') = invocation_keys l ++ invocation_keys l'.
    Proof. induction l as [| e l IH]; [reflexivity |]. cbn. destruct (te_ev F e); cbn; rewrite IH; reflexivity. Qed.

    Lemma in_ikeys_of_inv (l : list (ThreadEvent F)) t h o :
      In (Build_ThreadEvent t (InvEv h o)) l -> In (t, h) (invocation_keys l).
    Proof.
      induction l as [| e l IH]; intros Hin; [destruct Hin |].
      destruct Hin as [-> | Hin]; [left; reflexivity |].
      cbn. destruct (te_ev F e); [right |]; exact (IH Hin).
    Qed.

    Lemma inv_of_in_ikeys (l : list (ThreadEvent F)) t h :
      In (t, h) (invocation_keys l) -> exists o, In (Build_ThreadEvent t (InvEv h o)) l.
    Proof.
      induction l as [| [t' [h' o' | h' o' r']] l IH]; cbn; intros Hin; [destruct Hin | |].
      - destruct Hin as [Heq | Hin].
        + injection Heq as <- <-. exists o'. left. reflexivity.
        + destruct (IH Hin) as (o & Ho). exists o. right. exact Ho.
      - destruct (IH Hin) as (o & Ho). exists o. right. exact Ho.
    Qed.
  End Keys.

  Section PoolKeys.
    Context {E F : RelaxedSig.t} (VE : LTS E) (M : RelaxedModuleImpl E F).

    Lemma finish_call_src_key t h op (ret : Sig.ar op) (pool pool' : CallPool F) :
      finish_call t h op ret pool pool' -> In (t, h) (map call_key pool).
    Proof. induction 1; [left; reflexivity | right; assumption]. Qed.

    Lemma pool_keys_step ev c c' :
      module_step_tagged VE M ev c c' ->
      map call_key (tm_calls c') = rev (invocation_keys (overlay_events [ev])) ++ map call_key (tm_calls c).
    Proof.
      destruct 1 as [t h op q pool Q used tr ret Hcf Hprod Hft
                    | cand q q' pool Q Q' used Hsel Hlts
                    | t h op ret q pool pool' Q used Hfin Hdone]; cbn; [reflexivity | reflexivity |].
      symmetry. exact (finish_call_keys _ _ _ _ _ _ Hfin).
    Qed.

    Lemma pool_keys_exec c evs c' :
      module_execution_tagged VE M c evs c' ->
      map call_key (tm_calls c') = rev (invocation_keys (overlay_events evs)) ++ map call_key (tm_calls c).
    Proof.
      induction 1 as [c | c1 c2 c3 ev evs Hst Hex IH]; [reflexivity |].
      rewrite IH, (pool_keys_step _ _ _ Hst).
      change (ev :: evs) with ([ev] ++ evs). rewrite overlay_events_app, ikeys_app, rev_app_distr, app_assoc.
      reflexivity.
    Qed.

    (** The keys of the call pool are exactly the overlay keys invoked so
        far, newest first; returned calls stay as [DeadCall]
        ([RelaxedHoareGSim.returned_not_fresh]). *)
    Theorem pool_keys_trace σ0 evs c :
      module_execution_tagged VE M (initial_tagged_module VE σ0) evs c ->
      map call_key (tm_calls c) = rev (invocation_keys (overlay_events evs)).
    Proof. intros Hex. rewrite (pool_keys_exec _ _ _ Hex), app_nil_r. reflexivity. Qed.

    Corollary pool_keys_in σ0 evs c k :
      module_execution_tagged VE M (initial_tagged_module VE σ0) evs c ->
      In k (map call_key (tm_calls c)) <-> In k (invocation_keys (overlay_events evs)).
    Proof. intros Hex. rewrite (pool_keys_trace σ0 evs c Hex). split; [apply in_rev | apply in_rev]. Qed.

    Lemma pool_wf_step ev c c' :
      module_step_tagged VE M ev c c' -> NoDup (map call_key (tm_calls c)) -> NoDup (map call_key (tm_calls c')).
    Proof.
      destruct 1 as [t h op q pool Q used tr ret Hcf Hprod Hft
                    | cand q q' pool Q Q' used Hsel Hlts
                    | t h op ret q pool pool' Q used Hfin Hdone]; cbn; intros Hnd.
      - constructor; [exact Hcf | exact Hnd].
      - exact Hnd.
      - rewrite <- (finish_call_keys _ _ _ _ _ _ Hfin). exact Hnd.
    Qed.

    Lemma pool_wf_exec c evs c' :
      module_execution_tagged VE M c evs c' -> NoDup (map call_key (tm_calls c)) -> NoDup (map call_key (tm_calls c')).
    Proof. induction 1 as [c | c1 c2 c3 ev evs Hst Hex IH]; [auto |]. intros Hnd. exact (IH (pool_wf_step _ _ _ Hst Hnd)). Qed.

    (** Overlay keys are never reused. *)
    Corollary ov_inv_keys_nodup σ0 evs c :
      module_execution_tagged VE M (initial_tagged_module VE σ0) evs c ->
      NoDup (invocation_keys (overlay_events evs)).
    Proof.
      intros Hex. pose proof (pool_wf_exec _ _ _ Hex (NoDup_nil _)) as Hnd.
      rewrite (pool_keys_trace σ0 evs c Hex) in Hnd. apply NoDup_rev in Hnd. rewrite rev_involutive in Hnd. exact Hnd.
    Qed.

    Definition ResInPool (c : @TaggedModuleConfig E F VE) (ov : list (ThreadEvent F)) : Prop :=
      forall t h o (r : Sig.ar o), In (Build_ThreadEvent t (ResEv h o r)) ov -> In (t, h) (map call_key (tm_calls c)).

    Lemma res_in_pool_step ev c c' ov :
      module_step_tagged VE M ev c c' -> ResInPool c ov -> ResInPool c' (ov ++ overlay_events [ev]).
    Proof.
      intros Hst Hrp t0 h0 o0 r0 Hin. rewrite (pool_keys_step _ _ _ Hst). apply in_or_app.
      destruct Hst as [t h op q pool Q used tr ret Hcf Hprod Hft
                      | cand q q' pool Q Q' used Hsel Hlts
                      | t h op ret q pool pool' Q used Hfin Hdone]; cbn in *.
      - right. apply in_app_or in Hin as [Hin | [Heq | []]]; [exact (Hrp _ _ _ _ Hin) |].
        apply (f_equal (te_ev F)) in Heq. discriminate Heq.
      - right. rewrite app_nil_r in Hin. exact (Hrp _ _ _ _ Hin).
      - right.
        apply in_app_or in Hin as [Hin | [Heq | []]]; [exact (Hrp _ _ _ _ Hin) |].
        assert (Ht : t = t0) by exact (f_equal (te_tid F) Heq).
        assert (Hh : h = h0) by exact (f_equal (fun e => event_handle (te_ev F e)) Heq).
        subst t0 h0. exact (finish_call_src_key _ _ _ _ _ _ Hfin).
    Qed.

    Lemma res_in_pool_exec c evs c' ov :
      module_execution_tagged VE M c evs c' -> ResInPool c ov -> ResInPool c' (ov ++ overlay_events evs).
    Proof.
      intros Hex. revert ov. induction Hex as [c | c1 c2 c3 ev evs Hst Hex IH]; intros ov Hrp.
      - rewrite app_nil_r. exact Hrp.
      - change (ev :: evs) with ([ev] ++ evs). rewrite overlay_events_app, app_assoc.
        apply IH. exact (res_in_pool_step _ _ _ _ Hst Hrp).
    Qed.

    (** A responded overlay key is in the pool. *)
    Theorem res_key_in_pool σ0 evs c :
      module_execution_tagged VE M (initial_tagged_module VE σ0) evs c -> ResInPool c (overlay_events evs).
    Proof. intros Hex. exact (res_in_pool_exec _ _ _ [] Hex ltac:(intros t h o r [])). Qed.
  End PoolKeys.

  (** ** Part 7: licensing an erroring invocation through the copy-cat *)

  Section Fresh.
    Context {F : RelaxedSig.t}.

    Lemma length_filter_fst (t : tid) (l1 l2 : list (CallKey F)) :
      map fst l1 = map fst l2 ->
      length (filter (fun k => Pos.eqb (fst k) t) l1) = length (filter (fun k => Pos.eqb (fst k) t) l2).
    Proof.
      revert l2. induction l1 as [| [t1 h1] l1 IH]; intros [| [t2 h2] l2] H; cbn in H; try discriminate H; [reflexivity |].
      injection H as H1 H2. subst t2. cbn. destruct (Pos.eqb t1 t); cbn; [f_equal |]; exact (IH l2 H2).
    Qed.

    Lemma nodup_snd_same_fst (t : tid) (l : list (CallKey F)) :
      (forall k, In k l -> fst k = t) -> NoDup l -> NoDup (map snd l).
    Proof.
      induction l as [| [t1 h1] l IH]; intros Hf Hnd; cbn; [constructor |].
      apply NoDup_cons_iff in Hnd as [Hn Hnd]. constructor.
      - intros Hin. apply in_map_iff in Hin as ([t2 h2] & Hh & Hin). cbn in Hh. subst h2. apply Hn.
        assert (H1 : t1 = t) by exact (Hf _ (or_introl eq_refl)).
        assert (H2 : t2 = t) by exact (Hf _ (or_intror Hin)).
        subst t1 t2. exact Hin.
      - apply IH; [intros k Hk; apply Hf; right; exact Hk | exact Hnd].
    Qed.
  End Fresh.

  (** Handles [nat] are inexhaustible. *)
  Lemma nat_inexhaustible (l : list nat) : exists n, ~ In n l.
  Proof.
    assert (Hle : forall x, In x l -> x <= fold_right Nat.max 0 l).
    { induction l as [| a l IH]; cbn; intros x Hx; [destruct Hx |].
      destruct Hx as [-> | Hx]; [lia | specialize (IH x Hx); lia]. }
    exists (S (fold_right Nat.max 0 l)). intros Hin. specialize (Hle _ Hin). lia.
  Qed.

  Section CopyCatErr.
    Context {F : RelaxedSig.t} (V : LTS F).

    Abbreviation Cfg := (@TaggedModuleConfig F F V).

    Lemma ov_one_over (e : ThreadEvent F) : overlay_events [@OverlayEvent F F e] = [e].
    Proof. reflexivity. Qed.

    Lemma ov_one_under (e : ThreadEvent F) : overlay_events [@UnderlayEvent F F e] = [].
    Proof. reflexivity. Qed.

    Lemma sel_sub (cand : TaggedScheduledEvent F F) Q Q' y :
      select_frontier_tagged cand Q Q' -> In y Q' -> In y Q.
    Proof. induction 1 as [suffix | earlier Q Q' Hc Hs IH]; intros Hy; [right; exact Hy |]. destruct Hy as [-> | Hy]; [left; reflexivity | right; exact (IH Hy)]. Qed.

    (** *** One underlay key per copy-cat call, on the call's thread *)

    Lemma cc_used_threads_step ev (c c' : Cfg) :
      module_step_tagged V idF ev c c' ->
      map fst (tm_used_underlay c') = map fst (tm_used_underlay c) ++ map fst (invocation_keys (overlay_events [ev])).
    Proof.
      destruct 1 as [t h op q pool Q used tr ret Hcf Hprod Hft
                    | cand q q' pool Q Q' used Hsel Hlts
                    | t h op ret q pool pool' Q used Hfin Hdone]; cbn.
      - destruct (cc_trace t op tr ret Hprod) as (h' & ->). cbn. rewrite map_app. reflexivity.
      - rewrite app_nil_r. reflexivity.
      - rewrite app_nil_r. reflexivity.
    Qed.

    Lemma cc_used_threads_exec (c c' : Cfg) evs :
      module_execution_tagged V idF c evs c' ->
      map fst (tm_used_underlay c') = map fst (tm_used_underlay c) ++ map fst (invocation_keys (overlay_events evs)).
    Proof.
      induction 1 as [c | c1 c2 c3 ev evs Hst Hex IH]; [exact (eq_sym (app_nil_r _)) |].
      rewrite IH, (cc_used_threads_step _ _ _ Hst).
      change (ev :: evs) with ([ev] ++ evs). rewrite overlay_events_app, ikeys_app, map_app, app_assoc. reflexivity.
    Qed.

    (** The copy-cat's used underlay keys have, in order, the threads of
        its overlay invocations. *)
    Theorem cc_used_threads v evs (c : Cfg) :
      module_execution_tagged V idF (initial_tagged_module V v) evs c ->
      map fst (tm_used_underlay c) = map fst (invocation_keys (overlay_events evs)).
    Proof. intros Hex. exact (cc_used_threads_exec _ _ _ Hex). Qed.

    (** *** A queued underlay invocation belongs to a pending call *)

    Definition CCPend (ov : list (ThreadEvent F)) (c : Cfg) : Prop :=
      forall y, In y (tm_queue c) ->
        te_tid F (untag (ts_event y)) = fst (ts_owner y) /\
        forall h' o, te_ev F (untag (ts_event y)) = InvEv h' o ->
          In (Build_ThreadEvent (fst (ts_owner y)) (InvEv (snd (ts_owner y)) o)) ov /\
          forall o' (r : Sig.ar o'), ~ In (Build_ThreadEvent (fst (ts_owner y)) (ResEv (snd (ts_owner y)) o' r)) ov.

    Lemma cc_pending_step ev (c c' : Cfg) ov :
      module_step_tagged V idF ev c c' -> ResInPool V c ov -> CCPend ov c -> CCPend (ov ++ overlay_events [ev]) c'.
    Proof.
      intros Hst Hrp Hp.
      destruct Hst as [t h op q pool Q used tr ret Hcf Hprod Hft
                      | cand q q' pool Q Q' used Hsel Hlts
                      | t h op ret q pool pool' Q used Hfin Hdone].
      - rewrite ov_one_over. destruct (cc_trace t op tr ret Hprod) as (h' & ->).
        intros y Hy. cbn [tm_queue] in Hy. apply in_app_or in Hy as [Hy | Hy].
        + destruct (Hp y Hy) as (Ht & Hi). split; [exact Ht |]. intros h0 o Hev. destruct (Hi h0 o Hev) as (Hin & Hno).
          split; [apply in_or_app; left; exact Hin |].
          intros o' r Hin'. apply in_app_or in Hin' as [Hin' | [Heq | []]]; [exact (Hno o' r Hin') |].
          apply (f_equal (te_ev F)) in Heq. discriminate Heq.
        + cbn in Hy. destruct Hy as [<- | [<- | []]].
          * cbn. split; [reflexivity |]. intros h0 o Hev.
            assert (Ho : op = o) by exact (f_equal (@event_op F) Hev). subst o.
            split; [apply in_or_app; right; left; reflexivity |].
            intros o' r Hin'. apply in_app_or in Hin' as [Hin' | [Heq | []]].
            -- apply Hcf. exact (Hrp _ _ _ _ Hin').
            -- apply (f_equal (te_ev F)) in Heq. discriminate Heq.
          * cbn. split; [reflexivity |]. intros h0 o Hev. discriminate Hev.
      - rewrite ov_one_under, app_nil_r. intros y Hy. exact (Hp y (sel_sub _ _ _ _ Hsel Hy)).
      - rewrite ov_one_over. intros y Hy. cbn [tm_queue] in Hy. destruct (Hp y Hy) as (Ht & Hi).
        split; [exact Ht |]. intros h0 o Hev. destruct (Hi h0 o Hev) as (Hin & Hno).
        split; [apply in_or_app; left; exact Hin |].
        intros o' r Hin'. apply in_app_or in Hin' as [Hin' | [Heq | []]]; [exact (Hno o' r Hin') |].
        apply Hdone. assert (Ht' : t = fst (ts_owner y)) by exact (f_equal (te_tid F) Heq).
        assert (Hh' : h = snd (ts_owner y)) by exact (f_equal (fun e => event_handle (te_ev F e)) Heq).
        rewrite Ht', Hh', <- surjective_pairing. exact (in_map ts_owner _ _ Hy).
    Qed.

    Lemma cc_pending_exec (c c' : Cfg) evs ov :
      module_execution_tagged V idF c evs c' -> ResInPool V c ov -> CCPend ov c -> CCPend (ov ++ overlay_events evs) c'.
    Proof.
      intros Hex. revert ov. induction Hex as [c | c1 c2 c3 ev evs Hst Hex IH]; intros ov Hrp Hp.
      - assert (Happ : ov ++ overlay_events (@nil (ModuleEvent F F)) = ov) by exact (app_nil_r ov).
        rewrite Happ. exact Hp.
      - change (ev :: evs) with ([ev] ++ evs). rewrite overlay_events_app, app_assoc.
        apply IH; [exact (res_in_pool_step V idF _ _ _ _ Hst Hrp) | exact (cc_pending_step _ _ _ _ Hst Hrp Hp)].
    Qed.

    Theorem cc_pending v evs (c : Cfg) :
      module_execution_tagged V idF (initial_tagged_module V v) evs c -> CCPend (overlay_events evs) c.
    Proof. intros Hex. exact (cc_pending_exec _ _ _ [] Hex ltac:(intros t h o r []) ltac:(intros y [])). Qed.

    (** *** The licence, at a configuration *)

    (** From a reachable copy-cat configuration with overlay trace [ov]:
        invoke a fresh overlay key [(t, h)] of operation [op], with an
        unused underlay handle [h'] and committed result [r0]; its
        underlay invocation is on the frontier (a queued response never
        blocks the copy-cat's untagged invocation, and a queued invocation
        of thread [t] belongs to a call pending in [ov], whose operation
        is semi-independent of [op] by hypothesis); it is an [Error] of
        [V]. *)
    Lemma cc_license_cfg v evs (c : Cfg) t h h' op (r0 : Sig.ar op) :
      module_execution_tagged V idF (initial_tagged_module V v) evs c ->
      (forall o, ~ In (Build_ThreadEvent t (InvEv h o)) (overlay_events evs)) ->
      ~ In (t, h') (tm_used_underlay c) ->
      Error V (Build_ThreadEvent t (InvEv h' op)) (tm_lts_state c) ->
      (forall h2 op2, In (Build_ThreadEvent t (InvEv h2 op2)) (overlay_events evs) ->
         (forall op3 (r : Sig.ar op3), ~ In (Build_ThreadEvent t (ResEv h2 op3 r)) (overlay_events evs)) ->
         semi_independent F op2 op) ->
      MTracesE V idF v (map TEv (overlay_events evs ++ [Build_ThreadEvent t (InvEv h op)]) ++ [TErr (t, h) op]).
    Proof.
      intros Hex Hnew Hh' Herr Hsi.
      pose proof (cc_pending v evs c Hex) as Hpend.
      pose proof (pool_keys_in V idF v evs c (t, h) Hex) as Hkeys.
      destruct c as [q pool Q used]. cbn [tm_lts_state tm_calls tm_queue tm_used_underlay] in Hh', Herr, Hpend, Hkeys.
      assert (Hcf : call_fresh (t, h) pool).
      { intros Hin. apply Hkeys in Hin. destruct (inv_of_in_ikeys _ _ _ Hin) as (o & Ho). exact (Hnew o Ho). }
      assert (Hft : trace_fresh used (map untag [cc_inv_ev t h' op; cc_res_ev t h' op r0])).
      { split; cbn.
        - constructor; [intros [] | constructor].
        - intros key [<- | []]. exact Hh'. }
      assert (Hcross : forall y, In y Q ->
                tagged_can_cross (ts_event y) (ts_event (Build_TaggedScheduledEvent (t, h) (cc_inv_ev t h' op)))).
      { intros y Hy. destruct (Hpend y Hy) as (Ht & Hi).
        destruct (Pos.eq_dec (te_tid F (untag (ts_event y))) t) as [Heq | Hne]; [| left; exact Hne].
        right. split; [exact Heq |]. unfold must_precede.
        destruct (te_ev F (untag (ts_event y))) as [h2 o2 | h2 o2 r2] eqn:Hy2; cbn.
        - intros Hn. apply Hn. destruct (Hi h2 o2 eq_refl) as (Hin & Hno).
          rewrite <- Ht, Heq in Hin, Hno. exact (Hsi _ _ Hin Hno).
        - exact (resolved_in_empty h2). }
      exists (evs ++ [OverlayEvent (Build_ThreadEvent t (InvEv h op))]),
             (Build_TaggedModuleConfig q (Build_CallEntry t h (ActiveCall op r0) :: pool)
                (Q ++ [Build_TaggedScheduledEvent (t, h) (cc_inv_ev t h' op);
                       Build_TaggedScheduledEvent (t, h) (cc_res_ev t h' op r0)])
                (used ++ [(t, h')])).
      split.
      - eapply exec_snoc; [exact Hex |].
        exact (tagged_invoke V idF t h op q pool Q used [cc_inv_ev t h' op; cc_res_ev t h' op r0] r0
                 Hcf (idF_produces t h' op r0) Hft).
      - right. exists (t, h), op. split.
        + exact (tagged_error V (Build_TaggedScheduledEvent (t, h) (cc_inv_ev t h' op)) op r0 q
                   (Build_CallEntry t h (ActiveCall op r0) :: pool)
                   (Q ++ [Build_TaggedScheduledEvent (t, h) (cc_inv_ev t h' op);
                          Build_TaggedScheduledEvent (t, h) (cc_res_ev t h' op r0)])
                   (Q ++ [Build_TaggedScheduledEvent (t, h) (cc_res_ev t h' op r0)])
                   (used ++ [(t, h')])
                   (select_of_cross _ Q [Build_TaggedScheduledEvent (t, h) (cc_res_ev t h' op r0)] Hcross)
                   (or_introl eq_refl) Herr).
        + rewrite overlay_events_app. reflexivity.
    Qed.

    (** An unused underlay handle of thread [t] exists, by pigeonhole and
        [classic] (handles have no decidable equality). *)
    Lemma cc_fresh_handle_cl v evs (c : Cfg) t h :
      module_execution_tagged V idF (initial_tagged_module V v) evs c ->
      (forall o, ~ In (Build_ThreadEvent t (InvEv h o)) (overlay_events evs)) ->
      exists h', ~ In (t, h') (tm_used_underlay c).
    Proof.
      intros Hex Hnew. apply NNPP. intros Hall.
      assert (Hall' : forall x, In (t, x) (tm_used_underlay c)).
      { intros x. apply NNPP. intros Hx. apply Hall. exists x. exact Hx. }
      pose proof (length_filter_fst t _ _ (cc_used_threads v evs c Hex)) as Hlen.
      assert (Hnd : NoDup (h :: map snd (filter (fun k => Pos.eqb (fst k) t) (invocation_keys (overlay_events evs))))).
      { constructor.
        - intros Hin. apply in_map_iff in Hin as ([t2 h2] & Hh2 & Hin). cbn in Hh2. subst h2.
          apply filter_In in Hin as (Hin & Hft). cbn in Hft. apply Pos.eqb_eq in Hft. subst t2.
          destruct (inv_of_in_ikeys _ _ _ Hin) as (o & Ho). exact (Hnew o Ho).
        - apply (nodup_snd_same_fst t).
          + intros k Hk. apply filter_In in Hk as (_ & Hk). apply Pos.eqb_eq. exact Hk.
          + apply NoDup_filter. exact (ov_inv_keys_nodup V idF v evs c Hex). }
      assert (Hincl : incl (h :: map snd (filter (fun k => Pos.eqb (fst k) t) (invocation_keys (overlay_events evs))))
                           (map snd (filter (fun k => Pos.eqb (fst k) t) (tm_used_underlay c)))).
      { intros x _. apply in_map_iff. exists (t, x). split; [reflexivity |].
        apply filter_In. split; [exact (Hall' x) | cbn; apply Pos.eqb_refl]. }
      pose proof (NoDup_incl_length Hnd Hincl) as Hle. cbn [length] in Hle. rewrite !length_map in Hle. lia.
    Qed.

    (** *** The licence, on traces *)

    (** Closed version: the handle type is inexhaustible. *)
    Theorem cc_license_gen (Hinf : forall l : list (RelaxedSig.handle F), exists h', ~ In h' l)
        v p t h op (r0 : Sig.ar op) :
      RTraces V v p ->
      (forall o, ~ In (Build_ThreadEvent t (InvEv h o)) p) ->
      (forall σ h', Error V (Build_ThreadEvent t (InvEv h' op)) σ) ->
      (forall h2 op2, In (Build_ThreadEvent t (InvEv h2 op2)) p ->
         (forall op3 (r : Sig.ar op3), ~ In (Build_ThreadEvent t (ResEv h2 op3 r)) p) ->
         semi_independent F op2 op) ->
      Licensed V v (p ++ [Build_ThreadEvent t (InvEv h op)]).
    Proof.
      intros (evs & c & Hex & <-) Hnew Herr Hsi.
      destruct (Hinf (map snd (tm_used_underlay c))) as (h' & Hh').
      exists (map TEv (overlay_events evs ++ [Build_ThreadEvent t (InvEv h op)])), (t, h), op, [].
      split; [| rewrite app_nil_r; reflexivity].
      apply (cc_license_cfg v evs c t h h' op r0 Hex Hnew); [| exact (Herr _ h') | exact Hsi].
      intros Hin. apply Hh'. exact (in_map snd _ _ Hin).
    Qed.

    (** Without a hypothesis on handles; uses [classic]. *)
    Theorem cc_license_gen_cl v p t h op (r0 : Sig.ar op) :
      RTraces V v p ->
      (forall o, ~ In (Build_ThreadEvent t (InvEv h o)) p) ->
      (forall σ h', Error V (Build_ThreadEvent t (InvEv h' op)) σ) ->
      (forall h2 op2, In (Build_ThreadEvent t (InvEv h2 op2)) p ->
         (forall op3 (r : Sig.ar op3), ~ In (Build_ThreadEvent t (ResEv h2 op3 r)) p) ->
         semi_independent F op2 op) ->
      Licensed V v (p ++ [Build_ThreadEvent t (InvEv h op)]).
    Proof.
      intros (evs & c & Hex & <-) Hnew Herr Hsi.
      destruct (cc_fresh_handle_cl v evs c t h Hex Hnew) as (h' & Hh').
      exists (map TEv (overlay_events evs ++ [Build_ThreadEvent t (InvEv h op)])), (t, h), op, [].
      split; [| rewrite app_nil_r; reflexivity].
      exact (cc_license_cfg v evs c t h h' op r0 Hex Hnew Hh' (Herr _ h') Hsi).
    Qed.
  End CopyCatErr.

  (** *** The instance [EIe δ bad] (plan §2.1, [cc_license_indep])

      From a copy-cat trace [p] over [EI δ] from [(s0, [])], a key [(t,
      h)] not invoked in [p], a state-independent error [forall σ, bad σ
      t op], and every call of [t] pending in [p] semi-independent of
      [op] (in [F]): the specification [EIe δ bad] licenses [p ++ [inv t h
      op]]. *)
  Theorem cc_license_indep {F : RelaxedSig.t} {St : Type}
      (δ : St -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> St -> Prop)
      (bad : St * list (Op F) -> tid -> Sig.op (RelaxedSig.effect F) -> Prop) (s0 : St)
      (Hinf : forall l : list (RelaxedSig.handle F), exists h', ~ In h' l)
      p t h op (r0 : Sig.ar op) :
    RTraces (RelaxedHoareSpec.EI δ) (s0, []) p ->
    (forall o, ~ In (Build_ThreadEvent t (InvEv h o)) p) ->
    (forall σ, bad σ t op) ->
    (forall h2 op2, In (Build_ThreadEvent t (InvEv h2 op2)) p ->
       (forall op3 (r : Sig.ar op3), ~ In (Build_ThreadEvent t (ResEv h2 op3 r)) p) ->
       semi_independent F op2 op) ->
    Licensed (EIe δ bad) (s0, []) (p ++ [Build_ThreadEvent t (InvEv h op)]).
  Proof.
    intros Hp Hnew Hbad Hsi.
    apply (cc_license_gen (EIe δ bad) Hinf (s0, []) p t h op r0); [| exact Hnew | | exact Hsi].
    - apply (rtraces_eie_ei δ bad (s0, []) p). exact Hp.
    - intros σ h'. exact (Hbad σ).
  Qed.

  Theorem cc_license_indep_cl {F : RelaxedSig.t} {St : Type}
      (δ : St -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> St -> Prop)
      (bad : St * list (Op F) -> tid -> Sig.op (RelaxedSig.effect F) -> Prop) (s0 : St)
      p t h op (r0 : Sig.ar op) :
    RTraces (RelaxedHoareSpec.EI δ) (s0, []) p ->
    (forall o, ~ In (Build_ThreadEvent t (InvEv h o)) p) ->
    (forall σ, bad σ t op) ->
    (forall h2 op2, In (Build_ThreadEvent t (InvEv h2 op2)) p ->
       (forall op3 (r : Sig.ar op3), ~ In (Build_ThreadEvent t (ResEv h2 op3 r)) p) ->
       semi_independent F op2 op) ->
    Licensed (EIe δ bad) (s0, []) (p ++ [Build_ThreadEvent t (InvEv h op)]).
  Proof.
    intros Hp Hnew Hbad Hsi.
    apply (cc_license_gen_cl (EIe δ bad) (s0, []) p t h op r0); [| exact Hnew | | exact Hsi].
    - apply (rtraces_eie_ei δ bad (s0, []) p). exact Hp.
    - intros σ h'. exact (Hbad σ).
  Qed.

End RelaxedHoareErrSpec.
