(** * The implementation-side error obligation has teeth: the negative
      half of [m8_gap] (task RLHL-latch L.10, part 1; plan §2.1,
      RLHL-3c.md "m-8", design A §8; RD-10)

    Purpose.  [RelaxedHoareErrSpec.RCompLinErr] obliges an implementation
    to have every one of its error traces licensed by its own
    specification (author decision m-8 / D5 (i), research-intent §8,
    2026-10-15).  For LatchSet's underlay [EIhl δcoh] this obligation is
    vacuous ([Error := False]).  This file exercises it on an underlay
    that does have errors: a lower lock with a precondition, and a module
    [Mbad] that misuses it.

    ** Objects

    - [E_lock]: the lower lock.  Operations [LAcq t] (acquire, carrying
      the acquirer's thread id) and [LRel] (release), all of arity [unit];
      handles [nat]; semi-independence ∅; modes [Local].
    - [δlock] on [option tid]: [LAcq t] from [None] to [Some t]; [LRel]
      from [Some _] to [None].  An acquire of a held lock and a release of
      a free lock have no successor (they block in [EI δlock]).
    - [bad_lock σ t o], the precondition (as an error predicate,
      [RelaxedHoareErrSpec.EIe]): [LAcq t'] is an error unless [t' = t]
      (the caller passes its own id); [LRel] is an error unless the lock
      is held by the caller ([fst σ = Some t]).  "Release only when held
      by the caller".
    - [G1]: the overlay, one operation [Go : unit], handles [nat],
      semi-independence ∅; [δG] always succeeds; its specification [EI δG]
      has no error.
    - [Mbad Go t := acquire; release; release] (each [call]ed: [Future]
      then [Wait]).  The second release is a misuse.

    ** Results (all closed under the global context, Rocq 9.3.0)

    - [mbad_produces]: the method trace [mtr t] of [Mbad Go t] (six
      events, explicit dependency tags).
    - [mbad_err_trace]: [[TEv inv(t0,0,Go); TErr (t0,0) Go]] is in
      [MTracesE (EIe δlock bad_lock) Mbad (None, [])].  One execution:
      the overlay invocation of [(t0, 0)], then acquire and the first
      release (invocation and response each) at the head of the queue;
      the second release's invocation is then on the frontier and is an
      [Error] of [EIe δlock bad_lock] (the lock is free), owned by the
      active call [(t0, 0)].
    - [m8_gap_neg_any]: for every error-free overlay presentation [VF]
      and every [v0], [~ RCompLinErr Mbad (EIe δlock bad_lock) (None, [])
      VF v0].  [m8_gap_neg]: the instance [VF := EI δG] (plan §2.1).
    - [mbad_err_trace_licensed] (contrast; a use of
      [RelaxedHoareErrSpec.cc_license_indep] with the empty prefix
      [p := []], so its semi-independence side condition is vacuous
      here; LatchSet's L.11 is where that condition is exercised): over
      the overlay
      specification [EIe δG bad_go] whose precondition forbids [Go]
      altogether, the same error trace is in [RTracesClosed].  So the
      rejection above is caused by the overlay specification having no
      matching precondition, not by the shape of the trace.

    ** K / S / P / R

    - K: every declaration of this file is closed (no [classic], no
      [eq_rect_eq]); results are compared by computation and
      [discriminate] on non-dependent constructors only.
    - S: [m8_gap_neg_any] is universal over error-free overlay
      presentations.  [mbad_err_trace_licensed] is about one trace, not
      [RCompLinErr] for all traces of [Mbad].
    - P: the paper has no error clause (see [RelaxedHoareErrSpec], P).
    - R: latest-review m-8: a spec-side licence alone is unsound for
      layering (counterexample "acquire; release; release" over a lower
      lock that does not block on misuse).  [m8_gap_neg] shows that the
      decided notion [RCompLinErr], with the implementation-side
      obligation, rejects that module.

    ** Deviations from the plan, and provisional decisions

    - The plan's lock ([δlock false Acq tt true], [bad_lock (s, _) _ Rel
      := s = false]) cannot say "held by the caller": [δ] in [ei_step]
      receives no thread id (m-37).  The task asks for "release only when
      held by the caller", so the acquire carries the acquirer's id
      ([LAcq t], the "tid-carrying operations" alternative of m-37) and
      [bad_lock] uses the thread argument of [EIe]'s [bad] (D5 (ii),
      RD-9).  The negative half needs only "release while free".
    - RD-10 (negative half only in the first deliverable): followed.
    - The positive half of [m8_gap] (the old [RLHL2Hyps] over [EIhl
      δlock] holds for [Mbad] because the misuse blocks) is NOT here: it
      needs a full RLHL invariant (design A §8 estimates about 250 lines)
      and was optional ("only if cheap").  Note that with overlapping
      same-thread calls a [Go] call of [Mbad] can return over [EI δlock]
      (another call of the same thread may re-acquire before the second
      release), so that invariant is not trivial.  Hence [m8_no_rlhl2E]
      (design A §8) is also not here; it would need the deferred
      [RLHL2HypsE] anyway. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.PArith.PArith.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedGSim.
Require Import models.simlin.RelaxedHoareSpec.
Require Import models.simlin.RelaxedHoareCompLin.
Require Import models.simlin.RelaxedHoareErrSpec.

Import ListNotations.


Module RelaxedHoareLockErr.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedTraceLin.
  Import RelaxedGSim.
  Import RelaxedHoareCompLin.
  Import RelaxedHoareErrSpec.

  (** ** The lower lock, with a precondition *)

  Inductive LOp : Type := LAcq (t : tid) | LRel.

  Definition LSig : Sig.t := {| Sig.op := LOp; Sig.ar := fun _ => unit |}.

  Definition E_lock : RelaxedSig.t :=
    {| effect := LSig; handle := nat; semi_independent := fun _ _ => False; mode := fun _ => Local |}.

  Definition δlock (s : option tid) (o : Sig.op (RelaxedSig.effect E_lock)) (_ : Sig.ar o) (s' : option tid) : Prop :=
    match o with
    | LAcq t => s = None /\ s' = Some t
    | LRel => (exists t, s = Some t) /\ s' = None
    end.

  (** "Acquire with your own id; release only when held by the caller." *)
  Definition bad_lock (σ : option tid * list (Op E_lock)) (t : tid) (o : Sig.op (RelaxedSig.effect E_lock)) : Prop :=
    match o with
    | LAcq t' => t' <> t
    | LRel => fst σ <> Some t
    end.

  (** ** The overlay and the misusing module *)

  Inductive GOp : Type := Go.

  Definition GSig : Sig.t := {| Sig.op := GOp; Sig.ar := fun _ => unit |}.

  Definition G1 : RelaxedSig.t :=
    {| effect := GSig; handle := nat; semi_independent := fun _ _ => False; mode := fun _ => Local |}.

  Definition δG (s : unit) (o : Sig.op (RelaxedSig.effect G1)) (_ : Sig.ar o) (s' : unit) : Prop := True.

  (** acquire; release; release *)
  Definition Mbad : RelaxedModuleImpl E_lock G1 :=
    fun op t =>
      match op return Prog E_lock (@Sig.ar GSig op) with
      | Go =>
          Future (E := E_lock) (LAcq t) (fun f1 => Wait f1 (fun _ =>
          Future (E := E_lock) LRel (fun f2 => Wait f2 (fun _ =>
          Future (E := E_lock) LRel (fun f3 => Wait f3 (fun _ => Ret tt))))))
      end.

  (** ** The method trace *)

  Definition fe_acq (t : tid) : FutureEntry E_lock := @Build_FutureEntry E_lock 0 (@Resolved E_lock (LAcq t) tt).
  Definition fe_rel1 : FutureEntry E_lock := @Build_FutureEntry E_lock 1 (@Resolved E_lock LRel tt).

  Definition m_ia (t : tid) : TaggedEvent E_lock :=
    Build_TaggedEvent (Build_ThreadEvent t (@InvEv E_lock 0 (LAcq t))) (resolved_in (@empty_store E_lock)).
  Definition m_ra (t : tid) : TaggedEvent E_lock :=
    Build_TaggedEvent (Build_ThreadEvent t (@ResEv E_lock 0 (LAcq t) tt)) no_deps.
  Definition m_ir1 (t : tid) : TaggedEvent E_lock :=
    Build_TaggedEvent (Build_ThreadEvent t (@InvEv E_lock 1 LRel)) (resolved_in [fe_acq t]).
  Definition m_rr1 (t : tid) : TaggedEvent E_lock :=
    Build_TaggedEvent (Build_ThreadEvent t (@ResEv E_lock 1 LRel tt)) no_deps.
  Definition m_ir2 (t : tid) : TaggedEvent E_lock :=
    Build_TaggedEvent (Build_ThreadEvent t (@InvEv E_lock 2 LRel)) (resolved_in [fe_rel1; fe_acq t]).
  Definition m_rr2 (t : tid) : TaggedEvent E_lock :=
    Build_TaggedEvent (Build_ThreadEvent t (@ResEv E_lock 2 LRel tt)) no_deps.

  Definition mtr (t : tid) : list (TaggedEvent E_lock) := [m_ia t; m_ra t; m_ir1 t; m_rr1 t; m_ir2 t; m_rr2 t].

  Lemma mbad_produces t : program_produces_tagged t (Mbad Go t) (mtr t) tt.
  Proof.
    eexists. split.
    - unfold mtr, initial_program.
      eapply tagged_execution_emit; [apply (tagged_future (E := E_lock) t (LAcq t) _ 0); intros [] |].
      eapply tagged_execution_emit; [apply (tagged_wait_pending (E := E_lock) t (LAcq t) 0 tt); apply resolve_here |].
      eapply tagged_execution_emit; [apply (tagged_future (E := E_lock) t LRel _ 1); cbn; intros [H | []]; discriminate H |].
      eapply tagged_execution_emit; [apply (tagged_wait_pending (E := E_lock) t LRel 1 tt); apply resolve_here |].
      eapply tagged_execution_emit;
        [apply (tagged_future (E := E_lock) t LRel _ 2); cbn; intros [H | [H | []]]; discriminate H |].
      eapply tagged_execution_emit; [apply (tagged_wait_pending (E := E_lock) t LRel 2 tt); apply resolve_here |].
      apply tagged_execution_refl.
    - constructor. repeat constructor.
  Qed.

  (** ** The error trace of [Mbad] over [EIe δlock bad_lock] *)

  Definition t0 : tid := 1%positive.

  Definition qe (m : TaggedEvent E_lock) : TaggedScheduledEvent E_lock G1 := @Build_TaggedScheduledEvent E_lock G1 (t0, 0) m.

  Theorem mbad_err_trace :
    MTracesE (EIe δlock bad_lock) Mbad (None, [])
      [TEv (Build_ThreadEvent t0 (@InvEv G1 0 Go)); @TErr G1 (t0, 0) Go].
  Proof.
    exists [OverlayEvent (Build_ThreadEvent t0 (@InvEv G1 0 Go));
            UnderlayEvent (Build_ThreadEvent t0 (@InvEv E_lock 0 (LAcq t0)));
            UnderlayEvent (Build_ThreadEvent t0 (@ResEv E_lock 0 (LAcq t0) tt));
            UnderlayEvent (Build_ThreadEvent t0 (@InvEv E_lock 1 LRel));
            UnderlayEvent (Build_ThreadEvent t0 (@ResEv E_lock 1 LRel tt))].
    exists (@Build_TaggedModuleConfig E_lock G1 (EIe δlock bad_lock) (None, [])
              [@Build_CallEntry G1 t0 0 (@ActiveCall G1 Go tt)] [qe (m_ir2 t0); qe (m_rr2 t0)]
              [(t0, 0); (t0, 1); (t0, 2)]).
    split.
    - eapply tagged_module_execution_cons.
      { apply (tagged_invoke (EIe δlock bad_lock) Mbad t0 0 Go (None, []) [] [] [] (mtr t0) tt).
        - intros [].
        - exact (mbad_produces t0).
        - split; cbn.
          + repeat constructor; cbn; intros Hin; repeat destruct Hin as [Hin | Hin]; try discriminate Hin; exact Hin.
          + intros key _ []. }
      eapply tagged_module_execution_cons.
      { apply (tagged_underlay (EIe δlock bad_lock) Mbad (qe (m_ia t0)) (None, []) (Some t0, [@Build_Op E_lock (t0, 0) (LAcq t0) tt])).
        - apply tagged_select_here.
        - cbn. exists tt, (Some t0). split; [split; reflexivity | reflexivity]. }
      eapply tagged_module_execution_cons.
      { apply (tagged_underlay (EIe δlock bad_lock) Mbad (qe (m_ra t0)) (Some t0, [@Build_Op E_lock (t0, 0) (LAcq t0) tt]) (Some t0, [])).
        - apply tagged_select_here.
        - cbn. exists [], []. split; reflexivity. }
      eapply tagged_module_execution_cons.
      { apply (tagged_underlay (EIe δlock bad_lock) Mbad (qe (m_ir1 t0)) (Some t0, []) (None, [@Build_Op E_lock (t0, 1) LRel tt])).
        - apply tagged_select_here.
        - cbn. exists tt, None. split; [split; [exists t0; reflexivity | reflexivity] | reflexivity]. }
      eapply tagged_module_execution_cons.
      { apply (tagged_underlay (EIe δlock bad_lock) Mbad (qe (m_rr1 t0)) (None, [@Build_Op E_lock (t0, 1) LRel tt]) (None, [])).
        - apply tagged_select_here.
        - cbn. exists [], []. split; reflexivity. }
      apply tagged_module_execution_refl.
    - right. exists (t0, 0), Go. split; [| reflexivity].
      exact (tagged_error (EIe δlock bad_lock)
               (qe (m_ir2 t0))
               Go tt (None, []) [@Build_CallEntry G1 t0 0 (@ActiveCall G1 Go tt)] [qe (m_ir2 t0); qe (m_rr2 t0)]
               [qe (m_rr2 t0)] [(t0, 0); (t0, 1); (t0, 2)] (tagged_select_here _ _) (or_introl eq_refl)
               ltac:(cbn; discriminate)).
  Qed.

  (** ** Rejection by every error-free overlay specification *)

  Lemma noerr_rejects_err_trace {F : RelaxedSig.t} (VF : LTS F) (v : State VF) e k op :
    (forall ev q, ~ Error VF ev q) -> ~ RTracesClosed VF v [TEv e; TErr k op].
  Proof.
    intros Hne H. destruct (rtraces_closed_noerr VF v _ Hne H) as (s' & Hs' & _).
    apply (TErr_notin_map s' k op). rewrite <- Hs'. right. left. reflexivity.
  Qed.

  Theorem m8_gap_neg_any (VF : LTS G1) (v0 : State VF) :
    (forall ev q, ~ Error VF ev q) -> ~ RCompLinErr Mbad (EIe δlock bad_lock) (None, []) VF v0.
  Proof. intros Hne HC. exact (noerr_rejects_err_trace VF v0 _ _ _ Hne (HC _ mbad_err_trace)). Qed.

  (** The negative half of [m8_gap] (plan §2.1). *)
  Theorem m8_gap_neg : ~ RCompLinErr Mbad (EIe δlock bad_lock) (None, []) (RelaxedHoareSpec.EI δG) (tt, []).
  Proof. apply m8_gap_neg_any. intros ev q H. exact H. Qed.

  (** ** Contrast: an overlay precondition that forbids [Go] licenses the
      error (a non-vacuous use of [cc_license_indep]) *)

  Definition bad_go (σ : unit * list (Op G1)) (t : tid) (o : Sig.op (RelaxedSig.effect G1)) : Prop := True.

  Theorem mbad_err_trace_licensed :
    RTracesClosed (EIe δG bad_go) (tt, []) [TEv (Build_ThreadEvent t0 (@InvEv G1 0 Go)); @TErr G1 (t0, 0) Go].
  Proof.
    assert (Hl : Licensed (EIe δG bad_go) (tt, []) ([] ++ [Build_ThreadEvent t0 (@InvEv G1 0 Go)])).
    { apply (cc_license_indep δG bad_go tt nat_inexhaustible [] t0 0 Go tt).
      - exists [], (initial_tagged_module (RelaxedHoareSpec.EI δG) (tt, [])). split; [constructor | reflexivity].
      - intros o [].
      - intros σ. exact Logic.I.
      - intros h2 op2 []. }
    destruct Hl as (p & k & op & tl & Hp & Heq).
    right. exists p, k, op, (tl ++ [@TErr G1 (t0, 0) Go]). split; [exact Hp |].
    rewrite app_assoc, <- Heq. reflexivity.
  Qed.

End RelaxedHoareLockErr.
