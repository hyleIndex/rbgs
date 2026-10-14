(** * RLHL, part 7: copy-cat (CompLin-style) soundness for every execution (RLHL-3a)

    Author decision on latest-review M-20 / Q3 (research-intent §8): state
    RLHL soundness like the original RG simulation, [CompLin.CompLin]
    (Def. 4.1) proved by [CompLinSound.cal_to_CompLin], with the relaxed
    copy-cat run over the overlay's sequential specification LTS ([EI],
    effect at the abstract invocation).  This file does that for every
    execution, complete or not.

    ** Definitions

    - [idF : RelaxedModuleImpl F F]: the relaxed copy-cat (identity
      module).  An overlay call [op] issues one untagged future for [op]
      on the underlay and waits for it ([idF_call]: it is
      [RelaxedLang.call op]).  Run in the tagged module semantics, its
      underlay invocations are ordered only by (F2), so semi-independent
      invocations of one thread may overtake one another; this is where
      relaxation comes from.
    - [MTraces VE M σ0 s]: [s] is the overlay trace ([overlay_events]) of
      some execution ([module_execution_tagged], any length, pending calls
      allowed) of [M] over [VE] from [initial_tagged_module VE σ0].  The
      analogue of [CompLin.ImplTraces].
    - [RTraces V v := MTraces V idF v]: the copy-cat's overlay traces.
    - [RCompLin M VE σ0 VF v0 := forall s, MTraces VE M σ0 s -> RTraces VF v0
      s].  The analogue of [CompLin.CompLin] *without* the error clause
      ([ImplTracesClosed]): the tagged module semantics has no error
      transition and [GSimRel] no error clause, so underlay [Error] is
      invisible (partial correctness, as in [RelaxedHoareGSim] item 7).

    ** Results

    - [gsim_complin]: [GSimRel VE VF M S] and [S (initial_tagged_module VE
      σ0) (PossOk v0 [])] give [RCompLin M VE σ0 VF v0], for every [VE],
      every [VF] and every execution (no completeness hypothesis, no
      hypothesis on [VF]).  Proof as in [CompLinSound]: the run of
      [RelaxedGSim.rinv_exec] (which holds for incomplete executions) is
      reified ([reify], the analogue of [abs_reaches_reify]) into one
      execution of [idF] over [VF] with the same overlay trace.  The
      replay: a concrete invocation of [k] is the copy-cat's overlay
      invocation of [k] with underlay handle [snd k]; [AInv k m] is the
      emission of its underlay invocation; [ARet k m r] the emission of
      its underlay response; a concrete response the copy-cat's overlay
      return.  The underlay steps are the [VF] steps of the run's
      abstract part ([ri_path]).  Each emission is on the dependency
      frontier because of [TValid]: an older same-thread call that is not
      semi-independent has its abstract invocation, hence its copy-cat
      invocation, earlier (F2); a response needs only its own invocation
      (F1); the copy-cat's tags are empty (F3).  The invariant is [CInv].
    - [rlhl_complin]: [RLHL2Hyps I R G M σ0 v0 -> RCompLin M VE σ0 VF v0],
      through [RelaxedHoareGSim.rlhl_gsim].
    - [rlhl_complin_ei]: the same for [VF := RelaxedHoareSpec.EI δ] and
      [v0 := (s0, [])], the author's layering: each layer is verified over
      the sequential-specification LTS of the layer below (as in LinCCAL),
      so [VE] is meant to be [EI δE] of the layer below (the counter
      instance uses [CounterHL.HVE], an atomic-at-invocation FAA LTS in
      the same style, not literally [EI]).
    - [cc_trace]: every method trace of the copy-cat is an invocation with
      some underlay handle followed by its response with the call's
      result.  Not used by [gsim_complin]; used by the counter checks.
    - Instance and sanity checks: [RelaxedHoareChecks.CounterCompLin]
      ([counter_complin]; [ooo_copycat_trace]: the out-of-order overlay
      trace of [inc_ooo_exec] is a copy-cat trace; [junkF_not_rtrace]: the
      overlay junk trace [Inv(t0,1) Inv(t0,2) Res(t0,2,0)] is not, since
      (F2) orders the older call's increment first; this agrees with the
      REW reading of prefixes, relaxedlin.tex:29, on this trace).

    ** Relation to the paper and to [CompLin], and differences

    - Paper: Appendix/relaxedlin.tex:665-667, Prop. "Soundness": the global
      simulation from the initial state gives [ν_E ; cc_E ; M[Threads] ⊆
      ν_F ; cc_F].  Here [RTraces VF v0] plays [ν_F ; cc_F] (the copy-cat
      [idF] run over the LTS [VF] that presents [ν_F]), and [MTraces VE M
      σ0] plays [ν_E ; cc_E ; M]; no separate copy-cat on the [E] side is
      composed in: the relaxation of [M]'s own underlay events is [M]'s
      dependency frontier (F1)-(F3).  That the two left-hand sides agree is
      not mechanized.  The hypothesis is [GSimRel] (universal) or
      [RLHL2Hyps], not the paper's thread-local simulation (see
      [RelaxedHoareGSim], items 1-2).
    - Traces are lists of overlay [ThreadEvent]s, not plays; [RTraces]
      quantifies over every copy-cat execution (any underlay handles, any
      committed results); [reify] exhibits one.
    - All executions: the conclusion covers incomplete traces (research
      intent §7 Q3, as decided under M-20).  The stamp-based [VT] route of
      latest-review M-18 ([RelaxedHoareGSim.rlhl_rel_lin_pres]) remains a
      complete-trace route only.
    - Single possibility: [GSimRel] carries one possibility (author decision,
      research-intent §8); the paper's possibility sets and its
      Completeness proposition are out of scope.
    - Generic [VE]: nothing here is about a memory model.
    - Not here: vertical composition of two RLHL-verified layers (the
      relaxed analogue of [CompLinVComp], RLHL-3c), and the link from
      [RTraces (EI δ)] to [RelaxedTraceLin.rel_lin] for complete traces
      (task RLHL-3a item 5, not done).  For complete executions,
      [RelaxedHoareGSim.rlhl_rel_lin_ei] gives relaxed linearizability
      directly from [RLHL2Hyps]; that [RTraces (EI δ)] contains only
      relaxed-linearizable complete traces (which would make
      [rlhl_complin_ei] imply it) is open.

    Assumptions: [reify], [cc_trace] and every other lemma of the
    replay are closed (no [eq_rect_eq]: results are compared through
    response events, [some_inj], [abs_res_step_any]).  [rinv_val],
    [rinv_reify], [gsim_complin], [rlhl_complin], [rlhl_complin_ei] use
    [Classical_Prop.classic], once, in [rinv_val]: the copy-cat commits its
    result at the overlay invocation, so the replay must know whether the
    run has an abstract response for the call, which is not decidable
    (handles have no decidable equality). *)

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
Require Import models.simlin.RelaxedPossibility.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedGSim.
Require Import models.view.PrefixView.
Require Import models.view.ViewPossibility.
Require Import models.simlin.RelaxedHoareBase.
Require Import models.simlin.RelaxedHoare.
Require Import models.simlin.RelaxedHoareSpec.
Require Import models.simlin.RelaxedHoareGSim.

Import ListNotations.


Module RelaxedHoareCompLin.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedPossibility.
  Import RelaxedTraceLin.
  Import ViewPossibility.
  Import RelaxedGSim.

  (** ** The relaxed copy-cat and the trace sets *)

  (** [idF]: the identity module [F -> F].  Every overlay call [op] issues
      one untagged future for [op] on the underlay and waits for it; this
      is [RelaxedLang.call op] ([idF_call]).  The untagged [Future] carries
      the tag "every handle resolved so far", which is empty at the start
      of the body, so (F3) never orders it; (F1) orders its response after
      its invocation, and (F2) orders its invocation after the invocations
      of the older calls of the same thread that are not semi-independent
      of it. *)
  Definition idF {F : RelaxedSig.t} : RelaxedModuleImpl F F :=
    fun op _ => Future op (fun f => Wait f (fun r => Ret r)).

  Lemma idF_call {F : RelaxedSig.t} (op : Sig.op (RelaxedSig.effect F)) t : idF op t = call op.
  Proof. reflexivity. Qed.

  (** The overlay traces of every execution, complete or not, of [M] over
      [VE] from [σ0]: the analogue of [CompLin.ImplTraces]. *)
  Definition MTraces {E F : RelaxedSig.t} (VE : LTS E) (M : RelaxedModuleImpl E F) (σ0 : State VE)
      (s : list (ThreadEvent F)) : Prop :=
    exists evs c, module_execution_tagged VE M (initial_tagged_module VE σ0) evs c /\ overlay_events evs = s.

  (** The overlay traces of the copy-cat run over [V] from [v]. *)
  Definition RTraces {F : RelaxedSig.t} (V : LTS F) (v : State V) (s : list (ThreadEvent F)) : Prop :=
    MTraces V idF v s.

  (** The relaxed analogue of [CompLin.CompLin] (Def. 4.1), without the
      error clause: the tagged module semantics has no error transition. *)
  Definition RCompLin {E F : RelaxedSig.t} (M : RelaxedModuleImpl E F) (VE : LTS E) (σ0 : State VE)
      (VF : LTS F) (v0 : State VF) : Prop :=
    forall s, MTraces VE M σ0 s -> RTraces VF v0 s.

  (** ** Module executions *)

  Section ExecFacts.
    Context {E F : RelaxedSig.t} (VE : LTS E) (M : RelaxedModuleImpl E F).

    Lemma exec_snoc c1 evs c2 ev c3 :
      module_execution_tagged VE M c1 evs c2 -> module_step_tagged VE M ev c2 c3 ->
      module_execution_tagged VE M c1 (evs ++ [ev]) c3.
    Proof.
      induction 1 as [c | c1 c2 c2' ev' evs Hst Hex IH]; intros Hs; cbn.
      - econstructor; [exact Hs | constructor].
      - econstructor; [exact Hst | apply IH; exact Hs].
    Qed.

    Lemma overlay_events_app (evs1 evs2 : list (ModuleEvent E F)) :
      overlay_events (evs1 ++ evs2) = overlay_events evs1 ++ overlay_events evs2.
    Proof. unfold overlay_events. apply flat_map_app. Qed.

    Lemma select_of_cross (cand : TaggedScheduledEvent E F) pre post :
      (forall y, In y pre -> tagged_can_cross (ts_event y) (ts_event cand)) ->
      select_frontier_tagged cand (pre ++ cand :: post) (pre ++ post).
    Proof.
      induction pre as [| y pre IH]; intros Hc; cbn.
      - apply tagged_select_here.
      - apply tagged_select_next; [apply Hc; left; reflexivity |].
        apply IH. intros z Hz. apply Hc. right. exact Hz.
    Qed.

    (** Cutting an execution where its overlay trace is cut. *)
    Lemma overlay_events_split (evs : list (ModuleEvent E F)) s1 s2 :
      overlay_events evs = s1 ++ s2 ->
      exists evs1 evs2, evs = evs1 ++ evs2 /\ overlay_events evs1 = s1 /\ overlay_events evs2 = s2.
    Proof.
      revert s1. induction evs as [| ev evs IH]; intros s1 Hov.
      - destruct s1 as [| e1 s1]; [| discriminate Hov]. exists [], []. cbn in Hov. auto.
      - destruct s1 as [| e1 s1].
        + exists [], (ev :: evs). auto.
        + destruct ev as [eu | eo]; cbn in Hov.
          * destruct (IH (e1 :: s1) Hov) as (evs1 & evs2 & -> & H1 & H2).
            exists (UnderlayEvent eu :: evs1), evs2. auto.
          * injection Hov as <- Hov. destruct (IH s1 Hov) as (evs1 & evs2 & -> & H1 & H2).
            exists (OverlayEvent eo :: evs1), evs2. split; [reflexivity |].
            split; [change (overlay_events (OverlayEvent eo :: evs1)) with (eo :: overlay_events evs1); rewrite H1; reflexivity
                   | exact H2].
    Qed.

    Lemma exec_app_inv c evs1 evs2 c'' :
      module_execution_tagged VE M c (evs1 ++ evs2) c'' ->
      exists c', module_execution_tagged VE M c evs1 c' /\ module_execution_tagged VE M c' evs2 c''.
    Proof.
      revert c. induction evs1 as [| ev evs1 IH]; intros c Hex.
      - exists c. split; [constructor | exact Hex].
      - remember ((ev :: evs1) ++ evs2) as l eqn:Hl.
        destruct Hex as [c | c1 c2 c3 ev' trace Hst Hex']; [discriminate Hl |].
        injection Hl as -> ->. destruct (IH _ Hex') as (c' & H1 & H2).
        exists c'. split; [econstructor; [exact Hst | exact H1] | exact H2].
    Qed.
  End ExecFacts.

  (** latest-review m-32: [MTraces] (hence [RTraces]) is prefix-closed, as
      [CompLin.ImplTraces] is: each module event contributes at most one
      overlay event. *)
  Theorem mtraces_prefix {E F : RelaxedSig.t} (VE : LTS E) (M : RelaxedModuleImpl E F) (σ0 : State VE) s1 s2 :
    MTraces VE M σ0 (s1 ++ s2) -> MTraces VE M σ0 s1.
  Proof.
    intros (evs & c & Hex & Hov). destruct (overlay_events_split evs s1 s2 Hov) as (evs1 & evs2 & -> & H1 & _).
    destruct (exec_app_inv VE M _ _ _ _ Hex) as (c' & Hex1 & _). exists evs1, c'. split; [exact Hex1 | exact H1].
  Qed.

  Corollary rtraces_prefix {F : RelaxedSig.t} (V : LTS F) (v : State V) s1 s2 :
    RTraces V v (s1 ++ s2) -> RTraces V v s1.
  Proof. exact (mtraces_prefix V idF v s1 s2). Qed.

  (** ** List facts *)

  Lemma nth_app_cases {A : Type} (l l' : list A) p y :
    nth_error (l ++ l') p = Some y ->
    (p < length l /\ nth_error l p = Some y) \/ (length l <= p /\ nth_error l' (p - length l) = Some y).
  Proof.
    intros H. destruct (Nat.lt_ge_cases p (length l)) as [Hlt | Hge].
    - left. rewrite nth_error_app1 in H by exact Hlt. auto.
    - right. rewrite nth_error_app2 in H by exact Hge. auto.
  Qed.

  Lemma nth_remove {A : Type} (pre post : list A) x p y :
    nth_error (pre ++ post) p = Some y ->
    exists p', nth_error (pre ++ x :: post) p' = Some y /\
               (p < length pre -> p' = p) /\ (length pre <= p -> p' = S p).
  Proof.
    intros H. destruct (nth_app_cases _ _ _ _ H) as [(Hlt & Hp) | (Hge & Hp)].
    - exists p. split; [rewrite nth_error_app1 by exact Hlt; exact Hp |]. split; [auto | lia].
    - exists (S p). split; [| split; [lia | auto]].
      rewrite nth_error_app2 by lia. replace (S p - length pre) with (S (p - length pre)) by lia. exact Hp.
  Qed.

  (** [injection] would also decompose the dependent result of [ResEv]
      (and then need [eq_rect_eq]); this projection does not. *)
  Lemma some_inj {A : Type} (x y : A) : Some x = Some y -> x = y.
  Proof. intros H. exact (f_equal (fun o => match o with Some e => e | None => x end) H). Qed.

  Lemma nth_two {A : Type} (a b : A) i x :
    nth_error [a; b] i = Some x -> (i = 0 /\ x = a) \/ (i = 1 /\ x = b).
  Proof.
    destruct i as [| [| i]]; cbn; intros H.
    - injection H as <-. auto.
    - injection H as <-. auto.
    - destruct i; discriminate H.
  Qed.

  Lemma in_remove_ne {A : Type} (pre post : list A) x y :
    In y (pre ++ x :: post) -> y <> x -> In y (pre ++ post).
  Proof.
    intros Hin Hne. apply in_app_or in Hin as [Hin | [Heq | Hin]];
      [apply in_or_app; left; exact Hin | congruence | apply in_or_app; right; exact Hin].
  Qed.

  Lemma in_remove_in {A : Type} (pre post : list A) x y :
    In y (pre ++ post) -> In y (pre ++ x :: post).
  Proof.
    intros Hin. apply in_app_or in Hin as [Hin | Hin]; apply in_or_app; [left | right; right]; exact Hin.
  Qed.

  Lemma in_nth_pre {A : Type} (pre post : list A) x y :
    In y pre -> exists p, p < length pre /\ nth_error (pre ++ x :: post) p = Some y.
  Proof.
    intros Hin. apply In_nth_error in Hin as (p & Hp).
    exists p. assert (Hlt : p < length pre) by (apply nth_error_Some; congruence).
    split; [exact Hlt |]. rewrite nth_error_app1 by exact Hlt. exact Hp.
  Qed.

  (** ** Call pools *)

  Section CallPools.
    Context {F : RelaxedSig.t}.

    Lemma finish_keep t h op (ret : Sig.ar op) (calls calls' : CallPool F) e :
      finish_call t h op ret calls calls' -> In e calls -> call_key e <> (t, h) -> In e calls'.
    Proof.
      induction 1 as [tail | t' h' cell pool pool' Hneq Hf IH]; intros [<- | Hin] Hk.
      - exfalso. apply Hk. reflexivity.
      - right. exact Hin.
      - left. reflexivity.
      - right. exact (IH Hin Hk).
    Qed.

    Lemma finish_of_in t h op (ret : Sig.ar op) (calls : CallPool F) :
      NoDup (map call_key calls) -> In (Build_CallEntry t h (ActiveCall op ret)) calls ->
      exists calls', finish_call t h op ret calls calls'.
    Proof.
      induction calls as [| e calls IH]; intros Hnd Hin; [destruct Hin |].
      cbn in Hnd. apply NoDup_cons_iff in Hnd as [Hne Hnd].
      destruct Hin as [-> | Hin].
      - eexists. apply finish_here.
      - destruct (IH Hnd Hin) as (calls' & Hf). destruct e as [t' h' cell].
        exists (Build_CallEntry t' h' cell :: calls'). apply finish_next; [| exact Hf].
        intros Heq. apply Hne. change (call_key (Build_CallEntry t' h' cell)) with (t', h'). rewrite Heq.
        change (t, h) with (call_key (Build_CallEntry t h (ActiveCall op ret))). apply in_map. exact Hin.
    Qed.
  End CallPools.

  (** ** The copy-cat's method traces *)

  Section CopyCatProg.
    Context {F : RelaxedSig.t}.

    Definition cc_inv_ev (t : tid) (h : RelaxedSig.handle F) (op : Sig.op (RelaxedSig.effect F)) : TaggedEvent F :=
      Build_TaggedEvent (Build_ThreadEvent t (InvEv h op)) (resolved_in (@empty_store F)).

    Definition cc_res_ev (t : tid) (h : RelaxedSig.handle F) (op : Sig.op (RelaxedSig.effect F)) (r : Sig.ar op) :
        TaggedEvent F :=
      Build_TaggedEvent (Build_ThreadEvent t (ResEv h op r)) no_deps.

    (** The copy-cat invoking overlay call [op] with underlay handle [h]
        and committed result [r]. *)
    Lemma idF_produces t h op (r : Sig.ar op) :
      program_produces_tagged t (idF op t) [cc_inv_ev t h op; cc_res_ev t h op r] r.
    Proof.
      exists (Build_ProgramConfig (Ret r) [Build_FutureEntry h (Resolved op r)]). split.
      - eapply tagged_execution_emit.
        { apply (@tagged_future F (Sig.ar op) t op (fun f => Wait f (fun x => Ret x)) h (@empty_store F)).
          intros []. }
        eapply tagged_execution_emit.
        { apply (@tagged_wait_pending F (Sig.ar op) t op h r (fun x => Ret x)). apply resolve_here. }
        apply tagged_execution_refl.
      - constructor. constructor; [exact Logic.I | constructor].
    Qed.

    (** Queue entries of the copy-cat in which the underlay key of an
        overlay call is its overlay key. *)
    Definition ient (k : CallKey F) (m : Sig.op (RelaxedSig.effect F)) : TaggedScheduledEvent F F :=
      Build_TaggedScheduledEvent k (cc_inv_ev (fst k) (snd k) m).

    Definition rent (k : CallKey F) (m : Sig.op (RelaxedSig.effect F)) (r : Sig.ar m) : TaggedScheduledEvent F F :=
      Build_TaggedScheduledEvent k (cc_res_ev (fst k) (snd k) m r).

    Lemma ient_ne_rent k m k' m' (r : Sig.ar m') : ient k m <> rent k' m' r.
    Proof. intros H. apply (f_equal (fun x => te_ev F (untag (ts_event x)))) in H. discriminate H. Qed.

    Lemma ient_owner_eq k m k' m' : ient k m = ient k' m' -> k = k'.
    Proof. intros H. exact (f_equal ts_owner H). Qed.

    Lemma rent_owner_eq k m (r : Sig.ar m) k' m' (r' : Sig.ar m') : rent k m r = rent k' m' r' -> k = k'.
    Proof. intros H. exact (f_equal ts_owner H). Qed.
  End CopyCatProg.

  (** *** Every method trace of the copy-cat

      [cc_trace]: a trace of [idF op t] with result [r] is the invocation
      of some underlay handle [h] followed by its response with the result
      [r].  The proof reads the program through views computed by [match]
      ([fut_view], [wait_view], [ret_match]), so it never inverts a
      dependent equality (no [eq_rect_eq]); the result is identified up to
      the response event ([ret_match]). *)

  Section CopyCatTraces.
    Context {F : RelaxedSig.t} (t : tid) (op0 : Sig.op (RelaxedSig.effect F)).

    Definition ret_match (h : RelaxedSig.handle F) (o : Sig.op (RelaxedSig.effect F)) (x : Sig.ar o)
        (p : Prog F (Sig.ar op0)) : Prop :=
      match p with Ret y => @ResEv F h o x = @ResEv F h op0 y | _ => False end.

    Definition wait_view (h0 : RelaxedSig.handle F) (p : Prog F (Sig.ar op0)) : Prop :=
      match p with
      | Wait f k =>
          match f in FutureRef _ A return (A -> Prog F (Sig.ar op0)) -> Prop with
          | MkFutureRef o h => fun k => h = h0 /\ o = op0 /\ forall x : Sig.ar o, ret_match h o x (k x)
          end k
      | _ => False
      end.

    Definition fut_view (p : Prog F (Sig.ar op0)) : Prop :=
      match p with
      | Future o k => o = op0 /\ forall h, wait_view h (k (MkFutureRef o h))
      | _ => False
      end.

    Definition all_res (H : FutureStore F) : Prop :=
      forall e, In e H -> match fe_cell F e with Resolved _ _ => True | Pending _ => False end.

    Lemma resolve_store_in h op (ret : Sig.ar op) (H H' : FutureStore F) :
      resolve_store h op ret H H' -> In (Build_FutureEntry h (Pending op)) H.
    Proof. induction 1; [left; reflexivity | right; assumption]. Qed.

    Lemma resolve_store_single h0 op0' h op (ret : Sig.ar op) (H' : FutureStore F) :
      resolve_store h op ret [Build_FutureEntry h0 (Pending op0')] H' ->
      h = h0 /\ op = op0' /\ H' = [Build_FutureEntry h (Resolved op ret)].
    Proof.
      intros Hr. inversion Hr as [tail Htl | h' cell H1 H1' Hneq Hres]; subst.
      - auto.
      - inversion Hres.
    Qed.

    Lemma entry_res_ev h o (x : Sig.ar o) h' o' (x' : Sig.ar o') :
      Build_FutureEntry h (Resolved o x) = Build_FutureEntry h' (Resolved o' x') ->
      h = h' /\ @ResEv F h o x = @ResEv F h' o' x'.
    Proof.
      intros Heq. split; [exact (f_equal (fe_handle F) Heq) |].
      exact (f_equal (fun e => match fe_cell F e with
                               | Resolved o1 x1 => @ResEv F (fe_handle F e) o1 x1
                               | Pending o1 => @InvEv F (fe_handle F e) o1 end) Heq).
    Qed.

    Lemma pending_not_resolved h o h' o' (x' : Sig.ar o') :
      Build_FutureEntry h (Pending o) <> Build_FutureEntry h' (@Resolved F o' x').
    Proof. intros Heq. apply (f_equal (fe_cell F)) in Heq. discriminate Heq. Qed.

    Lemma terminal_ret (y r : Sig.ar op0) (H : FutureStore F) :
      program_terminal (Build_ProgramConfig (Ret y) H) r -> y = r.
    Proof. intros Ht. inversion Ht. reflexivity. Qed.

    Lemma stage_ret (c c' : ProgramConfig F (Sig.ar op0)) tr r :
      program_execution_tagged t c tr c' -> program_terminal c' r -> all_res (pc_futures c) ->
      (exists y, pc_prog c = Ret y) -> tr = [] /\ c' = c.
    Proof.
      intros Hex Hterm Hall (y & Hy). destruct Hex as [c | c1 c2 c3 tr Hstep Hex | c1 c2 c3 m tr Hstep Hex].
      - auto.
      - exfalso. remember (@TSilent F) as a eqn:Ha.
        destruct Hstep as [o k h H Hf | o d k h H Hf | o h ret k H Hr | o h ret k H H' Hr | o h ret p H H' Hr | p H];
          try discriminate Ha; cbn in Hy; discriminate Hy.
      - exfalso. remember (TEmit m) as a eqn:Ha.
        destruct Hstep as [o k h H Hf | o d k h H Hf | o h ret k H Hr | o h ret k H H' Hr | o h ret p H H' Hr | p H];
          try discriminate Ha; cbn in Hy, Hall; try discriminate Hy.
        exact (Hall _ (resolve_store_in _ _ _ _ _ Hr)).
    Qed.

    Lemma stage_wait_resolved h (x : Sig.ar op0) (c c' : ProgramConfig F (Sig.ar op0)) tr r :
      program_execution_tagged t c tr c' -> program_terminal c' r -> wait_view h (pc_prog c) ->
      pc_futures c = [Build_FutureEntry h (Resolved op0 x)] ->
      tr = [] /\ @ResEv F h op0 x = @ResEv F h op0 r.
    Proof.
      intros Hex Hterm Hv Hst. destruct Hex as [c | c1 c2 c3 tr Hstep Hex | c1 c2 c3 m tr Hstep Hex].
      - exfalso. destruct Hterm. exact Hv.
      - remember (@TSilent F) as a eqn:Ha.
        destruct Hstep as [o k h' H Hf | o d k h' H Hf | o h' ret k H Hres | o h' ret k H H' Hr | o h' ret p H H' Hr | p H];
          try discriminate Ha; cbn in Hv, Hst; [| destruct Hv].
        destruct Hv as (-> & -> & Hk). subst H.
        destruct Hres as [Heq | []]. destruct (entry_res_ev _ _ _ _ _ _ Heq) as (_ & Hev).
        specialize (Hk ret). unfold ret_match in Hk. destruct (k ret) as [| | | y |] eqn:Hkr; try contradiction.
        destruct (stage_ret _ _ _ _ Hex Hterm) as (-> & ->).
        + intros e [<- | []]. exact Logic.I.
        + exists y. cbn. first [reflexivity | exact Hkr].
        + split; [reflexivity |]. rewrite <- (terminal_ret _ _ _ Hterm). exact (eq_trans Hev Hk).
      - exfalso. remember (TEmit m) as a eqn:Ha.
        destruct Hstep as [o k h' H Hf | o d k h' H Hf | o h' ret k H Hres | o h' ret k H H' Hr | o h' ret p H H' Hr | p H];
          try discriminate Ha; cbn in Hv, Hst; try contradiction; subst H;
          destruct (resolve_store_in _ _ _ _ _ Hr) as [Heq | []]; exact (pending_not_resolved _ _ _ _ _ (eq_sym Heq)).
    Qed.

    Lemma stage_wait_pending h (c c' : ProgramConfig F (Sig.ar op0)) tr r :
      program_execution_tagged t c tr c' -> program_terminal c' r -> wait_view h (pc_prog c) ->
      pc_futures c = [Build_FutureEntry h (Pending op0)] ->
      tr = [cc_res_ev t h op0 r].
    Proof.
      intros Hex Hterm Hv Hst. destruct Hex as [c | c1 c2 c3 tr Hstep Hex | c1 c2 c3 m tr Hstep Hex].
      - exfalso. destruct Hterm. exact Hv.
      - exfalso. remember (@TSilent F) as a eqn:Ha.
        destruct Hstep as [o k h' H Hf | o d k h' H Hf | o h' ret k H Hres | o h' ret k H H' Hr | o h' ret p H H' Hr | p H];
          try discriminate Ha; cbn in Hv, Hst; [| destruct Hv].
        subst H. destruct Hres as [Heq | []]. exact (pending_not_resolved _ _ _ _ _ Heq).
      - remember (TEmit m) as a eqn:Ha.
        destruct Hstep as [o k h' H Hf | o d k h' H Hf | o h' ret k H Hres | o h' ret k H H' Hr | o h' ret p H H' Hr | p H];
          try discriminate Ha; cbn in Hv, Hst; try contradiction; subst H; injection Ha as <-.
        + destruct Hv as (-> & -> & Hk). destruct (resolve_store_single _ _ _ _ _ _ Hr) as (_ & _ & ->).
          specialize (Hk ret). unfold ret_match in Hk. destruct (k ret) as [| | | y |] eqn:Hkr; try contradiction.
          destruct (stage_ret _ _ _ _ Hex Hterm) as (-> & ->).
          * intros e [<- | []]. exact Logic.I.
          * exists y. cbn. first [reflexivity | exact Hkr].
          * rewrite <- (terminal_ret _ _ _ Hterm). unfold cc_res_ev. rewrite Hk. reflexivity.
        + destruct (resolve_store_single _ _ _ _ _ _ Hr) as (-> & -> & ->).
          destruct (stage_wait_resolved h ret _ _ _ _ Hex Hterm Hv eq_refl) as (-> & Hev).
          unfold cc_res_ev. rewrite Hev. reflexivity.
    Qed.

    Theorem cc_trace tr r :
      program_produces_tagged t (idF op0 t) tr r ->
      exists h, tr = [cc_inv_ev t h op0; cc_res_ev t h op0 r].
    Proof.
      intros (c' & Hex & Hterm). unfold initial_program in Hex.
      remember (Build_ProgramConfig (idF op0 t) (@empty_store F)) as c0 eqn:Hc0.
      assert (Hv : fut_view (pc_prog c0)).
      { rewrite Hc0. cbn. split; [reflexivity |]. intros h. cbn. split; [reflexivity |]. split; [reflexivity |].
        intros x. reflexivity. }
      assert (Hst : pc_futures c0 = []) by (rewrite Hc0; reflexivity).
      clear Hc0.
      destruct Hex as [c | c1 c2 c3 tr Hstep Hex | c1 c2 c3 m tr Hstep Hex].
      - exfalso. destruct Hterm. exact Hv.
      - exfalso. remember (@TSilent F) as a eqn:Ha.
        destruct Hstep; try discriminate Ha; cbn in Hv; exact Hv.
      - remember (TEmit m) as a eqn:Ha.
        destruct Hstep as [o k h H Hf | o d k h H Hf | o h ret k H Hr | o h ret k H H' Hr | o h ret p H H' Hr | p H];
          try discriminate Ha; cbn in Hv, Hst; try contradiction; subst H; injection Ha as <-.
        + destruct Hv as (-> & Hk). exists h.
          rewrite (stage_wait_pending h _ _ _ _ Hex Hterm (Hk h) eq_refl). reflexivity.
        + inversion Hr.
    Qed.
  End CopyCatTraces.

  (** ** Reifying a run into one copy-cat execution

      The analogue of [CompLinSound.abs_reaches_reify].  Fix a run [R]
      ([ViewPossibility.PStep]) whose abstract part is a path of [VF] from
      [v0], valid in the sense of [RelaxedGSim.TValid], with a well-formed
      concrete part and unique abstract steps per key.  [Hval] fixes, for
      every concretely invoked call, the result the copy-cat commits at its
      invocation: the result of the call's abstract response if the run
      has one.  Then [R] is replayed, step by step, as an execution of
      [idF] over [VF]:

      - [CEv] of an invocation of [k]: the copy-cat's overlay invocation
        of [k], with underlay handle [snd k] and the committed result;
      - [AInv k m]: the emission of the copy-cat's underlay invocation of
        [k] (the [VF] step of the run);
      - [ARet k m r]: the emission of its underlay response;
      - [CEv] of a response of [k]: the copy-cat's overlay return.

      The invariant [CInv R1 R2 cf] relates the copy-cat configuration
      [cf] reached after the prefix [R1] to the rest [R2]. *)

  Section Reify.
    Context {F : RelaxedSig.t} (VF : LTS F) (v0 : State VF).

    Abbreviation inv L := (inv_at (@PrefixView.sel F) L).
    Abbreviation res L := (res_at (@PrefixView.sel F) L).
    Abbreviation iev k m := (Build_ThreadEvent (fst k) (@InvEv F (snd k) m)).
    Abbreviation rev_ k m r := (Build_ThreadEvent (fst k) (@ResEv F (snd k) m r)).
    Abbreviation Cfg := (@TaggedModuleConfig F F VF).

    Context (R : list (PStep F)) (vfin : State VF).
    Context (HP : vf_path VF v0 (abs R) vfin).
    Context (HV : TValid (RelaxedSig.semi_independent F) R).
    Context (Hwf : PrefixView.wf (conc R)).
    Context (Hauinv : forall a a' k m m', inv (abs R) a k m -> inv (abs R) a' k m' -> a = a').
    Context (Hau : AUniq R).
    Context (Hval : forall i k m, inv (conc R) i k m ->
               exists ret : Sig.ar m, forall b r, res (abs R) b k m r -> rev_ k m r = rev_ k m ret).

    Record CInv (R1 R2 : list (PStep F)) (cf : Cfg) : Prop := {
      ci_path : vf_path VF (tm_lts_state cf) (abs R2) vfin;
      ci_cwf : NoDup (map call_key (tm_calls cf));
      ci_ckeys : forall k, In k (map call_key (tm_calls cf)) -> exists i m, inv (conc R1) i k m;
      ci_used : forall k, In k (tm_used_underlay cf) -> exists i m, inv (conc R1) i k m;
      ci_act : forall i k m, inv (conc R1) i k m -> (forall j m' (r' : Sig.ar m'), ~ res (conc R1) j k m' r') ->
        exists ret, In (Build_CallEntry (fst k) (snd k) (ActiveCall m ret)) (tm_calls cf);
      ci_ret : forall e, In e (tm_calls cf) ->
        match ce_cell F e with
        | ActiveCall m ret => forall b r, res (abs R) b (call_key e) m r -> rev_ (call_key e) m r = rev_ (call_key e) m ret
        | DeadCall => True
        end;
      ci_shape : forall x, In x (tm_queue cf) ->
        exists i m, inv (conc R1) i (ts_owner x) m /\
          ((x = ient (ts_owner x) m /\ forall a m', ~ inv (abs R1) a (ts_owner x) m') \/
           (exists ret, x = rent (ts_owner x) m ret /\
              In (Build_CallEntry (fst (ts_owner x)) (snd (ts_owner x)) (ActiveCall m ret)) (tm_calls cf) /\
              forall b m' (r' : Sig.ar m'), ~ res (abs R1) b (ts_owner x) m' r'));
      ci_qinv : forall i k m, inv (conc R1) i k m -> (forall a m', ~ inv (abs R1) a k m') ->
        In (ient k m) (tm_queue cf);
      ci_qres : forall i k m, inv (conc R1) i k m -> (forall b m' (r' : Sig.ar m'), ~ res (abs R1) b k m' r') ->
        exists ret, In (rent k m ret) (tm_queue cf) /\
                    In (Build_CallEntry (fst k) (snd k) (ActiveCall m ret)) (tm_calls cf);
      ci_ord : forall p q y x, nth_error (tm_queue cf) p = Some y -> nth_error (tm_queue cf) q = Some x -> p < q ->
        (ts_owner y = ts_owner x /\ (exists m, y = ient (ts_owner x) m) /\ (exists m ret, x = rent (ts_owner x) m ret)) \/
        (exists iy ix my mx, inv (conc R1) iy (ts_owner y) my /\ inv (conc R1) ix (ts_owner x) mx /\ iy < ix);
    }.

    (** *** Facts about prefixes of [R] *)

    Lemma conc_inv_lift R1 R2 i k m : inv (conc R1) i k m -> inv (conc (R1 ++ R2)) i k m.
    Proof. intros H. rewrite conc_app. exact (inv_app_l _ _ _ _ _ H). Qed.

    (** Positions of invocations in a prefix of the concrete trace are
        unique per key. *)
    Lemma conc_inv_pos R1 R2 i j k m m' :
      R = R1 ++ R2 -> inv (conc R1) i k m -> inv (conc R1) j k m' -> i = j /\ m = m'.
    Proof.
      intros HR Hi Hj. rewrite HR in Hwf.
      pose proof (conc_inv_lift R1 R2 _ _ _ Hi) as Hi'. pose proof (conc_inv_lift R1 R2 _ _ _ Hj) as Hj'.
      pose proof (proj1 Hwf _ _ _ _ _ Hi' Hj') as <-. split; [reflexivity |].
      exact (proj2 (PrefixView.inv_det _ _ _ _ _ _ Hi' Hj')).
    Qed.

    (** An abstract invocation in a prefix follows a concrete one in it. *)
    Lemma abs_inv_conc1 R1 R2 a k m :
      R = R1 ++ R2 -> inv (abs R1) a k m -> exists i, inv (conc R1) i k m.
    Proof.
      intros HR Ha. destruct (abs_inv_step _ _ _ _ Ha) as (q1 & q2 & Hq).
      assert (HR' : R = q1 ++ AInv k m :: (q2 ++ R2)) by (rewrite HR, Hq, <- app_assoc; reflexivity).
      destruct (HV q1 _ _ HR') as ((i & Hi) & _). exists i.
      rewrite Hq, conc_app. exact (inv_app_l _ _ _ _ _ Hi).
    Qed.

    (** [ViewPossibility.abs_res_step] also identifies the result, through
        [ResEvInversion] ([eq_rect_eq]); the result is not needed here. *)
    Lemma abs_res_step_any (run : list (PStep F)) b k m (r : Sig.ar m) :
      res (abs run) b k m r -> exists r1 r2 (r' : Sig.ar m), run = r1 ++ ARet k m r' :: r2.
    Proof.
      intros Hb. apply res_In in Hb. apply in_flat_map in Hb as (st & Hst & Hin).
      destruct st as [e | k' m' | k' m' r']; cbn in Hin; [destruct Hin | |].
      - destruct Hin as [Heq | []]. exfalso. exact (inv_not_res _ _ _ _ _ Heq).
      - destruct Hin as [Heq | []]. destruct (res_ev_inj _ _ _ _ _ _ Heq) as [-> ->].
        destruct (in_split _ _ Hst) as (r1 & r2 & ->). exists r1, r2, r'. reflexivity.
    Qed.

    (** An abstract response in a prefix follows an abstract invocation in it. *)
    Lemma abs_res_ainv1 R1 R2 b k m (r : Sig.ar m) :
      R = R1 ++ R2 -> res (abs R1) b k m r -> exists a, inv (abs R1) a k m.
    Proof.
      intros HR Hb. destruct (abs_res_step_any _ _ _ _ _ Hb) as (q1 & q2 & r' & Hq).
      assert (HR' : R = q1 ++ ARet k m r' :: (q2 ++ R2)) by (rewrite HR, Hq, <- app_assoc; reflexivity).
      destruct (HV q1 _ _ HR') as (a & Ha). exists a.
      rewrite Hq, abs_app. exact (inv_app_l _ _ _ _ _ Ha).
    Qed.

    Lemma abs_any_conc1 R1 R2 b k m (r : Sig.ar m) :
      R = R1 ++ R2 -> res (abs R1) b k m r -> exists i, inv (conc R1) i k m.
    Proof.
      intros HR Hb. destruct (abs_res_ainv1 R1 R2 _ _ _ _ HR Hb) as (a & Ha).
      exact (abs_inv_conc1 R1 R2 _ _ _ HR Ha).
    Qed.

    Lemma vf_path_cons_inv v e l v'' :
      vf_path VF v (e :: l) v'' -> exists v', Step VF e v v' /\ vf_path VF v' l v''.
    Proof. intros H. inversion H; subst. eauto. Qed.

    (** *** The initial configuration *)

    Lemma cinv_init : CInv [] R (initial_tagged_module VF v0).
    Proof.
      constructor; cbn.
      - exact HP.
      - constructor.
      - intros k [].
      - intros k [].
      - intros i k m Hi. exfalso. exact (inv_nil _ _ _ Hi).
      - intros e [].
      - intros x [].
      - intros i k m Hi. exfalso. exact (inv_nil _ _ _ Hi).
      - intros i k m Hi. exfalso. exact (inv_nil _ _ _ Hi).
      - intros p q y x Hp. destruct p; discriminate Hp.
    Qed.

    (** *** Step 1: a concrete invocation *)

    Lemma step_cinv R1 R2 t h m cf :
      R = R1 ++ CEv (Build_ThreadEvent t (InvEv h m)) :: R2 ->
      CInv R1 (CEv (Build_ThreadEvent t (InvEv h m)) :: R2) cf ->
      exists cf', module_step_tagged VF idF (OverlayEvent (Build_ThreadEvent t (InvEv h m))) cf cf' /\
                  CInv (R1 ++ [CEv (Build_ThreadEvent t (InvEv h m))]) R2 cf'.
    Proof.
      intros HR HI.
      assert (HRc : conc R = conc R1 ++ iev (t, h) m :: conc R2) by (rewrite HR, conc_app; reflexivity).
      assert (Hnew : inv (conc R) (length (conc R1)) (t, h) m).
      { rewrite HRc. eexists. split; [| reflexivity]. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
      assert (Hfresh : forall i m', ~ inv (conc R1) i (t, h) m').
      { intros i m' Hi. pose proof (inv_lt _ _ _ _ Hi) as Hlt.
        assert (Hi' : inv (conc R) i (t, h) m') by (rewrite HRc; exact (inv_app_l _ _ _ _ _ Hi)).
        pose proof (proj1 Hwf _ _ _ _ _ Hi' Hnew). lia. }
      assert (Hnoabs : forall a m', ~ inv (abs R1) a (t, h) m').
      { intros a m' Ha. destruct (abs_inv_conc1 R1 _ _ _ _ HR Ha) as (i & Hi). exact (Hfresh _ _ Hi). }
      assert (Hnoares : forall b m' (r' : Sig.ar m'), ~ res (abs R1) b (t, h) m' r').
      { intros b m' r' Hb. destruct (abs_any_conc1 R1 _ _ _ _ _ HR Hb) as (i & Hi). exact (Hfresh _ _ Hi). }
      destruct (Hval _ _ _ Hnew) as (ret & Hret).
      assert (HC1 : conc (R1 ++ [CEv (Build_ThreadEvent t (InvEv h m))]) = conc R1 ++ [iev (t, h) m])
        by (rewrite conc_app; reflexivity).
      assert (HA1 : abs (R1 ++ [CEv (Build_ThreadEvent t (InvEv h m))]) = abs R1)
        by (rewrite abs_app; apply app_nil_r).
      destruct cf as [q calls Q used].
      destruct HI as [Hpath Hcwf Hckeys Hused Hact Hret0 Hshape Hqinv Hqres Hord];
        cbn [tm_lts_state tm_calls tm_queue tm_used_underlay] in *.
      assert (Hcf : call_fresh (t, h) calls).
      { intros Hin. destruct (Hckeys _ Hin) as (i & m' & Hi). exact (Hfresh _ _ Hi). }
      exists (Build_TaggedModuleConfig q (Build_CallEntry t h (ActiveCall m ret) :: calls)
                (Q ++ [ient (t, h) m; rent (t, h) m ret]) (used ++ [(t, h)])).
      split.
      - apply (tagged_invoke VF idF t h m q calls Q used [cc_inv_ev t h m; cc_res_ev t h m ret] ret Hcf).
        + apply idF_produces.
        + split; [cbn; constructor; [intros [] | constructor] |].
          intros key [<- | []] Hin. destruct (Hused _ Hin) as (i & m' & Hi). exact (Hfresh _ _ Hi).
      - constructor; cbn [tm_lts_state tm_calls tm_queue tm_used_underlay]; rewrite ?HC1, ?HA1.
        + exact Hpath.
        + constructor; [exact Hcf | exact Hcwf].
        + intros k' [Hk | Hk].
          * subst k'. exists (length (conc R1)), m. apply (inv_snoc_new (conc R1) (t, h) m).
          * destruct (Hckeys _ Hk) as (i & m' & Hi). exists i, m'. exact (inv_app_l _ _ _ _ _ Hi).
        + intros k' Hk. apply in_app_or in Hk as [Hk | [<- | []]].
          * destruct (Hused _ Hk) as (i & m' & Hi). exists i, m'. exact (inv_app_l _ _ _ _ _ Hi).
          * exists (length (conc R1)), m. apply (inv_snoc_new (conc R1) (t, h) m).
        + intros i k' m' Hi Hnr. apply inv_snoc in Hi as [Hi | (_ & Hx)].
          * destruct (Hact i k' m' Hi (fun j m'' r'' Hj => Hnr j m'' r'' (res_app_l _ _ _ _ _ _ Hj))) as (ret' & Hin).
            exists ret'. right. exact Hin.
          * apply (inv_ev_inj (t, h) k' m m') in Hx as [<- <-]. exists ret. left. reflexivity.
        + intros e [<- | He]; [exact Hret | exact (Hret0 e He)].
        + intros x Hx. apply in_app_or in Hx as [Hx | Hx].
          * destruct (Hshape x Hx) as (i & m' & Hi & [[Heq Hna] | (r' & Heq & Hin & Hnr)]);
              exists i, m'; (split; [exact (inv_app_l _ _ _ _ _ Hi) |]).
            -- left. split; [exact Heq | exact Hna].
            -- right. exists r'. split; [exact Heq |]. split; [right; exact Hin | exact Hnr].
          * destruct Hx as [<- | [<- | []]]; exists (length (conc R1)), m;
              (split; [apply (inv_snoc_new (conc R1) (t, h) m) |]).
            -- left. split; [reflexivity | exact Hnoabs].
            -- right. exists ret. split; [reflexivity |]. split; [left; reflexivity | exact Hnoares].
        + intros i k' m' Hi Hna. apply inv_snoc in Hi as [Hi | (_ & Hx)].
          * apply in_or_app. left. exact (Hqinv i k' m' Hi Hna).
          * apply (inv_ev_inj (t, h) k' m m') in Hx as [<- <-]. apply in_or_app. right. left. reflexivity.
        + intros i k' m' Hi Hnr. apply inv_snoc in Hi as [Hi | (_ & Hx)].
          * destruct (Hqres i k' m' Hi Hnr) as (ret' & Hq & Hc). exists ret'.
            split; [apply in_or_app; left; exact Hq | right; exact Hc].
          * apply (inv_ev_inj (t, h) k' m m') in Hx as [<- <-]. exists ret.
            split; [apply in_or_app; right; right; left; reflexivity | left; reflexivity].
        + intros p q1 y x Hp Hq Hpq.
          destruct (nth_app_cases Q _ p y Hp) as [(Hp1 & Hp2) | (Hp1 & Hp2)];
            destruct (nth_app_cases Q _ q1 x Hq) as [(Hq1 & Hq2) | (Hq1 & Hq2)].
          * destruct (Hord p q1 y x Hp2 Hq2 Hpq) as [Hl | (iy & ix & my & mx & Hiy & Hix & Hlt)]; [left; exact Hl |].
            right. exists iy, ix, my, mx. split; [exact (inv_app_l _ _ _ _ _ Hiy) |].
            split; [exact (inv_app_l _ _ _ _ _ Hix) | exact Hlt].
          * right. destruct (Hshape y (nth_error_In _ _ Hp2)) as (iy & my & Hiy & _).
            exists iy, (length (conc R1)), my, m. split; [exact (inv_app_l _ _ _ _ _ Hiy) |].
            split; [| exact (inv_lt _ _ _ _ Hiy)].
            destruct (nth_two _ _ _ _ Hq2) as [(_ & ->) | (_ & ->)]; apply (inv_snoc_new (conc R1) (t, h) m).
          * lia.
          * left. destruct (nth_two _ _ _ _ Hp2) as [(E1 & ->) | (E1 & ->)];
              destruct (nth_two _ _ _ _ Hq2) as [(E2 & ->) | (E2 & ->)]; try lia. cbn.
            split; [reflexivity |]. split; [exists m; reflexivity | exists m, ret; reflexivity].
    Qed.

    (** *** Removing the emitted entry from the queue *)

    Lemma ord_remove (Q pre post : list (TaggedScheduledEvent F F)) x0 R1 :
      Q = pre ++ x0 :: post ->
      (forall p q y x, nth_error Q p = Some y -> nth_error Q q = Some x -> p < q ->
        (ts_owner y = ts_owner x /\ (exists m, y = ient (ts_owner x) m) /\ (exists m ret, x = rent (ts_owner x) m ret)) \/
        (exists iy ix my mx, inv (conc R1) iy (ts_owner y) my /\ inv (conc R1) ix (ts_owner x) mx /\ iy < ix)) ->
      forall p q y x, nth_error (pre ++ post) p = Some y -> nth_error (pre ++ post) q = Some x -> p < q ->
        (ts_owner y = ts_owner x /\ (exists m, y = ient (ts_owner x) m) /\ (exists m ret, x = rent (ts_owner x) m ret)) \/
        (exists iy ix my mx, inv (conc R1) iy (ts_owner y) my /\ inv (conc R1) ix (ts_owner x) mx /\ iy < ix).
    Proof.
      intros HQ Hord p q y x Hp Hq Hpq.
      destruct (nth_remove pre post x0 p y Hp) as (p' & Hp' & Hp1 & Hp2).
      destruct (nth_remove pre post x0 q x Hq) as (q' & Hq' & Hq1 & Hq2).
      rewrite <- HQ in Hp', Hq'. apply (Hord p' q' y x Hp' Hq').
      destruct (Nat.lt_ge_cases p (length pre)); destruct (Nat.lt_ge_cases q (length pre)).
      - rewrite Hp1, Hq1 by assumption. exact Hpq.
      - rewrite Hp1, Hq2 by assumption. lia.
      - lia.
      - rewrite Hp2, Hq2 by assumption. lia.
    Qed.

    (** Two queue entries of one owner: the earlier is the invocation entry
        and the later the response entry. *)
    Lemma same_owner_pos R1 R2 (Q : list (TaggedScheduledEvent F F)) p q y x :
      R = R1 ++ R2 ->
      (forall p q y x, nth_error Q p = Some y -> nth_error Q q = Some x -> p < q ->
        (ts_owner y = ts_owner x /\ (exists m, y = ient (ts_owner x) m) /\ (exists m ret, x = rent (ts_owner x) m ret)) \/
        (exists iy ix my mx, inv (conc R1) iy (ts_owner y) my /\ inv (conc R1) ix (ts_owner x) mx /\ iy < ix)) ->
      nth_error Q p = Some y -> nth_error Q q = Some x -> p < q -> ts_owner y = ts_owner x ->
      (exists m, y = ient (ts_owner x) m) /\ (exists m ret, x = rent (ts_owner x) m ret).
    Proof.
      intros HR Hord Hp Hq Hpq Hown.
      destruct (Hord p q y x Hp Hq Hpq) as [(_ & H1 & H2) | (iy & ix & my & mx & Hiy & Hix & Hlt)]; [auto |].
      rewrite Hown in Hiy. destruct (conc_inv_pos R1 R2 _ _ _ _ _ HR Hiy Hix) as (-> & _). lia.
    Qed.

    (** *** Step 2: an abstract invocation *)

    Lemma step_ainv R1 R2 k m cf :
      R = R1 ++ AInv k m :: R2 -> CInv R1 (AInv k m :: R2) cf ->
      exists cf', module_step_tagged VF idF (UnderlayEvent (untag (ts_event (ient k m)))) cf cf' /\
                  CInv (R1 ++ [AInv k m]) R2 cf'.
    Proof.
      intros HR HI.
      destruct (HV R1 _ R2 HR) as ((i0 & Hi0) & Hpo).
      assert (HRa : abs R = abs R1 ++ iev k m :: abs R2) by (rewrite HR, abs_app; reflexivity).
      assert (Hnoabs : forall a m', ~ inv (abs R1) a k m').
      { intros a m' Ha. pose proof (inv_lt _ _ _ _ Ha) as Hlt.
        assert (Ha' : inv (abs R) a k m') by (rewrite HRa; exact (inv_app_l _ _ _ _ _ Ha)).
        assert (Hn : inv (abs R) (length (abs R1)) k m).
        { rewrite HRa. eexists. split; [| reflexivity]. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
        pose proof (Hauinv _ _ _ _ _ Ha' Hn). lia. }
      assert (HC1 : conc (R1 ++ [AInv k m]) = conc R1) by (rewrite conc_app; apply app_nil_r).
      assert (HA1 : abs (R1 ++ [AInv k m]) = abs R1 ++ [iev k m]) by (rewrite abs_app; reflexivity).
      destruct cf as [q calls Q used].
      destruct HI as [Hpath Hcwf Hckeys Hused Hact Hret0 Hshape Hqinv Hqres Hord];
        cbn [tm_lts_state tm_calls tm_queue tm_used_underlay] in *.
      assert (Hpath1 : vf_path VF q (iev k m :: abs R2) vfin) by exact Hpath.
      destruct (vf_path_cons_inv _ _ _ _ Hpath1) as (q' & Hst & Hpath').
      pose proof (Hqinv i0 k m Hi0 Hnoabs) as HinQ.
      apply In_nth_error in HinQ as (p & Hp).
      destruct (nth_error_split Q p Hp) as (pre & post & HQ & Hlen).
      assert (Hcross : forall y, In y pre -> tagged_can_cross (ts_event y) (ts_event (ient k m))).
      { intros y Hy. destruct (in_nth_pre pre post (ient k m) y Hy) as (py & Hpy & Hny). rewrite <- HQ in Hny.
        destruct (Hord py p y (ient k m) Hny Hp ltac:(lia))
          as [(_ & _ & (m2 & ret2 & Heq)) | (iy & ix & my & mx & Hiy & Hix & Hlt)].
        - exfalso. exact (ient_ne_rent _ _ _ _ _ Heq).
        - cbn [ts_owner ient] in Hix. destruct (conc_inv_pos R1 _ _ _ _ _ _ HR Hix Hi0) as (-> & ->).
          destruct (Hshape y (nth_error_In _ _ Hny)) as (iy' & my' & Hiy' & [[Hy_eq Hna] | (r2 & Hy_eq & _ & _)]).
          + destruct (conc_inv_pos R1 _ _ _ _ _ _ HR Hiy' Hiy) as (<- & <-).
            rewrite Hy_eq. unfold tagged_can_cross, must_precede. cbn.
            destruct (Pos.eq_dec (fst (ts_owner y)) (fst k)) as [Ht | Ht]; [right | left; exact Ht].
            split; [exact Ht |]. intros Hn.
            destruct (Hpo i0 iy' (ts_owner y) my' Hi0 Hiy' Hlt Ht Hn) as (a & Ha). exact (Hna _ _ Ha).
          + rewrite Hy_eq. unfold tagged_can_cross, must_precede. cbn.
            destruct (Pos.eq_dec (fst (ts_owner y)) (fst k)) as [Ht | Ht]; [right | left; exact Ht].
            split; [exact Ht |]. intros (op' & ret' & Hres). exact Hres. }
      (* Every other entry of [k] is its response entry. *)
      assert (Hothers : forall y, In y (pre ++ post) -> ts_owner y = k -> exists m'' r'', y = rent k m'' r'').
      { intros y Hy Hown. apply In_nth_error in Hy as (py & Hpy).
        destruct (nth_remove pre post (ient k m) py y Hpy) as (py' & Hpy' & H1 & H2). rewrite <- HQ in Hpy'.
        destruct (Nat.lt_ge_cases py (length pre)) as [Hlt | Hge].
        - rewrite (H1 Hlt) in Hpy'.
          destruct (same_owner_pos R1 _ Q py p y (ient k m) HR Hord Hpy' Hp ltac:(lia) Hown) as (_ & (m2 & ret2 & Heq)).
          exfalso. exact (ient_ne_rent _ _ _ _ _ Heq).
        - rewrite (H2 Hge) in Hpy'.
          destruct (same_owner_pos R1 _ Q p (S py) (ient k m) y HR Hord Hp Hpy' ltac:(lia) (eq_sym Hown))
            as (_ & (m2 & ret2 & Heq)).
          rewrite Hown in Heq. eauto. }
      exists (Build_TaggedModuleConfig q' calls (pre ++ post) used).
      split.
      - apply (tagged_underlay VF idF (ient k m) q q' calls Q (pre ++ post) used).
        + rewrite HQ. apply select_of_cross. exact Hcross.
        + exact Hst.
      - constructor; cbn [tm_lts_state tm_calls tm_queue tm_used_underlay]; rewrite ?HC1, ?HA1.
        + exact Hpath'.
        + exact Hcwf.
        + exact Hckeys.
        + exact Hused.
        + exact Hact.
        + exact Hret0.
        + intros y Hy. assert (HyQ : In y Q) by (rewrite HQ; exact (in_remove_in _ _ _ _ Hy)).
          destruct (Hshape y HyQ) as (i & m' & Hi & [[Heq Hna] | (r' & Heq & Hin & Hnr)]);
            exists i, m'; (split; [exact Hi |]).
          * left. split; [exact Heq |]. intros a m'' Ha. apply inv_snoc in Ha as [Ha | (_ & Hx)]; [exact (Hna _ _ Ha) |].
            apply inv_ev_inj in Hx as [Hk _].
            destruct (Hothers y Hy (eq_sym Hk)) as (m3 & r3 & Heq3).
            rewrite Heq3 in Heq. exact (ient_ne_rent _ _ _ _ _ (eq_sym Heq)).
          * right. exists r'. split; [exact Heq |]. split; [exact Hin |].
            intros b m'' r'' Hb. apply res_snoc in Hb as [Hb | (_ & Hx)]; [exact (Hnr _ _ _ Hb) |].
            exact (inv_not_res _ _ _ _ _ Hx).
        + intros i k' m' Hi Hna.
          assert (Hq : In (ient k' m') Q) by (apply (Hqinv i k' m' Hi); intros a m'' Ha; exact (Hna a m'' (inv_app_l _ _ _ _ _ Ha))).
          rewrite HQ in Hq. apply (in_remove_ne pre post (ient k m)); [exact Hq |].
          intros Heq. apply ient_owner_eq in Heq. subst k'. exact (Hna (length (abs R1)) m (inv_snoc_new _ _ _)).
        + intros i k' m' Hi Hnr.
          destruct (Hqres i k' m' Hi) as (ret' & Hq & Hc).
          { intros b m'' r'' Hb. exact (Hnr b m'' r'' (res_app_l _ _ _ _ _ _ Hb)). }
          exists ret'. split; [| exact Hc]. rewrite HQ in Hq. apply (in_remove_ne pre post (ient k m)); [exact Hq |].
          intros Heq. exact (ient_ne_rent _ _ _ _ _ (eq_sym Heq)).
        + exact (ord_remove Q pre post (ient k m) R1 HQ Hord).
    Qed.

    (** *** Step 3: an abstract response *)

    Lemma step_aret R1 R2 t h m (r : Sig.ar m) cf :
      R = R1 ++ ARet (t, h) m r :: R2 -> CInv R1 (ARet (t, h) m r :: R2) cf ->
      exists ev cf', module_step_tagged VF idF ev cf cf' /\ overlay_events [ev] = [] /\
                     CInv (R1 ++ [ARet (t, h) m r]) R2 cf'.
    Proof.
      intros HR HI.
      destruct (HV R1 _ R2 HR) as (a0 & Ha0).
      destruct (abs_inv_conc1 R1 _ _ _ _ HR Ha0) as (i0 & Hi0).
      assert (HRa : abs R = abs R1 ++ rev_ (t, h) m r :: abs R2) by (rewrite HR, abs_app; reflexivity).
      assert (Hnew : res (abs R) (length (abs R1)) (t, h) m r).
      { rewrite HRa. eexists. split; [| reflexivity]. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
      assert (Hnores : forall b m' (r' : Sig.ar m'), ~ res (abs R1) b (t, h) m' r').
      { intros b m' r' Hb. pose proof (res_lt _ _ _ _ _ Hb) as Hlt.
        assert (Hb' : res (abs R) b (t, h) m' r') by (rewrite HRa; exact (res_app_l _ _ _ _ _ _ Hb)).
        pose proof (Hau _ _ _ _ _ _ _ Hb' Hnew). lia. }
      assert (HC1 : conc (R1 ++ [ARet (t, h) m r]) = conc R1) by (rewrite conc_app; apply app_nil_r).
      assert (HA1 : abs (R1 ++ [ARet (t, h) m r]) = abs R1 ++ [rev_ (t, h) m r]) by (rewrite abs_app; reflexivity).
      destruct cf as [q calls Q used].
      destruct HI as [Hpath Hcwf Hckeys Hused Hact Hret0 Hshape Hqinv Hqres Hord];
        cbn [tm_lts_state tm_calls tm_queue tm_used_underlay] in *.
      destruct (Hqres i0 (t, h) m Hi0 Hnores) as (ret & HinQ & HinC).
      assert (Hev : rev_ (t, h) m r = rev_ (t, h) m ret) by exact (Hret0 _ HinC _ _ Hnew).
      assert (Hpath1 : vf_path VF q (rev_ (t, h) m r :: abs R2) vfin) by exact Hpath.
      destruct (vf_path_cons_inv _ _ _ _ Hpath1) as (q' & Hst & Hpath').
      rewrite Hev in Hst.
      apply In_nth_error in HinQ as (p & Hp).
      destruct (nth_error_split Q p Hp) as (pre & post & HQ & Hlen).
      (* An invocation entry in the queue is not [(t, h)]'s. *)
      assert (Hnoinv : forall y m', In y Q -> y = ient (ts_owner y) m' -> ts_owner y <> (t, h)).
      { intros y m' Hy Heq Hown. destruct (Hshape y Hy) as (iy & my & Hiy & [[Heq' Hna] | (r2 & Heq' & _ & _)]).
        - rewrite Hown in Hna. exact (Hna _ _ Ha0).
        - rewrite Heq' in Heq. exact (ient_ne_rent _ _ _ _ _ (eq_sym Heq)). }
      assert (Hcross : forall y, In y pre -> tagged_can_cross (ts_event y) (ts_event (rent (t, h) m ret))).
      { intros y Hy. assert (HyQ : In y Q) by (rewrite HQ; apply in_or_app; left; exact Hy).
        destruct (Hshape y HyQ) as (iy & my & Hiy & [[Hy_eq Hna] | (r2 & Hy_eq & _ & _)]).
        - pose proof (Hnoinv y my HyQ Hy_eq) as Hne.
          rewrite Hy_eq. unfold tagged_can_cross, must_precede. cbn.
          destruct (Pos.eq_dec (fst (ts_owner y)) t) as [Ht | Ht]; [right | left; exact Ht].
          split; [exact Ht |]. intros Hh. apply Hne. destruct (ts_owner y) as [ty hy]. cbn in Ht, Hh. subst. reflexivity.
        - rewrite Hy_eq. unfold tagged_can_cross, must_precede. cbn.
          destruct (Pos.eq_dec (fst (ts_owner y)) t) as [Ht | Ht]; [right | left; exact Ht].
          split; [exact Ht | intros []]. }
      (* No other entry of [(t, h)] remains. *)
      assert (Hothers : forall y, In y (pre ++ post) -> ts_owner y <> (t, h)).
      { intros y Hy Hown. assert (HyQ : In y Q) by (rewrite HQ; exact (in_remove_in _ _ _ _ Hy)).
        apply In_nth_error in Hy as (py & Hpy).
        destruct (nth_remove pre post (rent (t, h) m ret) py y Hpy) as (py' & Hpy' & H1 & H2). rewrite <- HQ in Hpy'.
        destruct (Nat.lt_ge_cases py (length pre)) as [Hlt | Hge].
        - rewrite (H1 Hlt) in Hpy'.
          destruct (same_owner_pos R1 _ Q py p y (rent (t, h) m ret) HR Hord Hpy' Hp ltac:(lia) Hown)
            as ((m2 & Heq) & _).
          exact (Hnoinv y m2 HyQ (eq_trans Heq (f_equal (fun k => ient k m2) (eq_sym Hown))) Hown).
        - rewrite (H2 Hge) in Hpy'.
          destruct (same_owner_pos R1 _ Q p (S py) (rent (t, h) m ret) y HR Hord Hp Hpy' ltac:(lia) (eq_sym Hown))
            as ((m2 & Heq) & _).
          exact (ient_ne_rent _ _ _ _ _ (eq_sym Heq)). }
      exists (UnderlayEvent (untag (ts_event (rent (t, h) m ret)))), (Build_TaggedModuleConfig q' calls (pre ++ post) used).
      split; [| split; [reflexivity |]].
      - apply (tagged_underlay VF idF (rent (t, h) m ret) q q' calls Q (pre ++ post) used).
        + rewrite HQ. apply select_of_cross. exact Hcross.
        + exact Hst.
      - constructor; cbn [tm_lts_state tm_calls tm_queue tm_used_underlay]; rewrite ?HC1, ?HA1.
        + exact Hpath'.
        + exact Hcwf.
        + exact Hckeys.
        + exact Hused.
        + exact Hact.
        + exact Hret0.
        + intros y Hy. assert (HyQ : In y Q) by (rewrite HQ; exact (in_remove_in _ _ _ _ Hy)).
          destruct (Hshape y HyQ) as (i & m' & Hi & [[Heq Hna] | (r' & Heq & Hin & Hnr)]);
            exists i, m'; (split; [exact Hi |]).
          * left. split; [exact Heq |]. intros a m'' Ha. apply inv_snoc in Ha as [Ha | (_ & Hx)]; [exact (Hna _ _ Ha) |].
            exact (inv_not_res _ _ _ _ _ (eq_sym Hx)).
          * right. exists r'. split; [exact Heq |]. split; [exact Hin |].
            intros b m'' r'' Hb. apply res_snoc in Hb as [Hb | (_ & Hx)]; [exact (Hnr _ _ _ Hb) |].
            apply res_ev_inj in Hx as [Hk _]. exact (Hothers y Hy (eq_sym Hk)).
        + intros i k' m' Hi Hna.
          assert (Hq : In (ient k' m') Q) by (apply (Hqinv i k' m' Hi); intros a m'' Ha; exact (Hna a m'' (inv_app_l _ _ _ _ _ Ha))).
          rewrite HQ in Hq. apply (in_remove_ne pre post (rent (t, h) m ret)); [exact Hq |].
          intros Heq. exact (ient_ne_rent _ _ _ _ _ Heq).
        + intros i k' m' Hi Hnr.
          destruct (Hqres i k' m' Hi) as (ret' & Hq & Hc).
          { intros b m'' r'' Hb. exact (Hnr b m'' r'' (res_app_l _ _ _ _ _ _ Hb)). }
          exists ret'. split; [| exact Hc]. rewrite HQ in Hq. apply (in_remove_ne pre post (rent (t, h) m ret)); [exact Hq |].
          intros Heq. apply rent_owner_eq in Heq. subst k'. exact (Hnr (length (abs R1)) m r (res_snoc_new _ _ _ _)).
        + exact (ord_remove Q pre post (rent (t, h) m ret) R1 HQ Hord).
    Qed.

    (** *** Step 4: a concrete response *)

    Lemma step_cret R1 R2 t h m (r : Sig.ar m) cf :
      R = R1 ++ CEv (Build_ThreadEvent t (ResEv h m r)) :: R2 ->
      CInv R1 (CEv (Build_ThreadEvent t (ResEv h m r)) :: R2) cf ->
      exists ev cf', module_step_tagged VF idF ev cf cf' /\
                     overlay_events [ev] = [Build_ThreadEvent t (ResEv h m r)] /\
                     CInv (R1 ++ [CEv (Build_ThreadEvent t (ResEv h m r))]) R2 cf'.
    Proof.
      intros HR HI.
      destruct (HV R1 _ R2 HR (t, h) m r eq_refl) as (b0 & Hb0).
      destruct (abs_res_ainv1 R1 _ _ _ _ _ HR Hb0) as (a0 & Ha0).
      assert (HRc : conc R = conc R1 ++ rev_ (t, h) m r :: conc R2) by (rewrite HR, conc_app; reflexivity).
      assert (Hnew : res (conc R) (length (conc R1)) (t, h) m r).
      { rewrite HRc. eexists. split; [| reflexivity]. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
      destruct (proj2 (proj2 Hwf) _ _ _ _ Hnew) as (i1 & Hi1lt & Hi1).
      assert (Hi1' : inv (conc R1) i1 (t, h) m) by (rewrite HRc in Hi1; exact (inv_app_lt _ _ _ _ _ Hi1lt Hi1)).
      assert (Hnoconc : forall j m' (r' : Sig.ar m'), ~ res (conc R1) j (t, h) m' r').
      { intros j m' r' Hj. pose proof (res_lt _ _ _ _ _ Hj) as Hlt.
        assert (Hj' : res (conc R) j (t, h) m' r') by (rewrite HRc; exact (res_app_l _ _ _ _ _ _ Hj)).
        pose proof (proj1 (proj2 Hwf) _ _ _ _ _ _ _ Hj' Hnew). lia. }
      assert (HC1 : conc (R1 ++ [CEv (Build_ThreadEvent t (ResEv h m r))]) = conc R1 ++ [rev_ (t, h) m r])
        by (rewrite conc_app; reflexivity).
      assert (HA1 : abs (R1 ++ [CEv (Build_ThreadEvent t (ResEv h m r))]) = abs R1)
        by (rewrite abs_app; apply app_nil_r).
      destruct cf as [q calls Q used].
      destruct HI as [Hpath Hcwf Hckeys Hused Hact Hret0 Hshape Hqinv Hqres Hord];
        cbn [tm_lts_state tm_calls tm_queue tm_used_underlay] in *.
      destruct (Hact i1 (t, h) m Hi1' Hnoconc) as (ret & HinC). cbn [fst snd] in HinC.
      assert (Hev : rev_ (t, h) m r = rev_ (t, h) m ret).
      { apply (Hret0 _ HinC b0 r). rewrite HR, abs_app. exact (res_app_l _ _ _ _ _ _ Hb0). }
      destruct (finish_of_in t h m ret calls Hcwf HinC) as (calls' & Hfin).
      assert (Hdone : owner_done_tagged (t, h) Q).
      { intros Hin. apply in_map_iff in Hin as (x & Hxo & Hx).
        destruct (Hshape x Hx) as (ix & mx & Hix & [[_ Hna] | (r2 & _ & _ & Hnr)]); rewrite Hxo in *.
        - exact (Hna _ _ Ha0).
        - exact (Hnr _ _ _ Hb0). }
      assert (Hnotq : forall x, In x Q -> ts_owner x <> (t, h)).
      { intros x Hx Hown. apply Hdone. rewrite <- Hown. apply in_map. exact Hx. }
      exists (OverlayEvent (Build_ThreadEvent t (ResEv h m ret))), (Build_TaggedModuleConfig q calls' Q used).
      split; [| split].
      - apply (tagged_return VF idF t h m ret q calls calls' Q used Hfin Hdone).
      - cbn. f_equal. exact (eq_sym Hev).
      - constructor; cbn [tm_lts_state tm_calls tm_queue tm_used_underlay]; rewrite ?HC1, ?HA1.
        + exact Hpath.
        + exact (finish_call_well_formed _ _ _ _ _ _ Hfin Hcwf).
        + intros k' Hk. rewrite <- (finish_call_keys _ _ _ _ _ _ Hfin) in Hk.
          destruct (Hckeys _ Hk) as (i & m' & Hi). exists i, m'. exact (inv_app_l _ _ _ _ _ Hi).
        + intros k' Hk. destruct (Hused _ Hk) as (i & m' & Hi). exists i, m'. exact (inv_app_l _ _ _ _ _ Hi).
        + intros i k' m' Hi Hnr. apply inv_snoc in Hi as [Hi | (_ & Hx)]; [| exfalso; exact (inv_not_res _ _ _ _ _ (eq_sym Hx))].
          assert (Hk' : k' <> (t, h)).
          { intros ->. exact (Hnr (length (conc R1)) m r (res_snoc_new _ _ _ _)). }
          destruct (Hact i k' m' Hi (fun j m'' r'' Hj => Hnr j m'' r'' (res_app_l _ _ _ _ _ _ Hj))) as (ret' & Hin).
          exists ret'. apply (finish_keep _ _ _ _ _ _ _ Hfin Hin). destruct k'. exact Hk'.
        + intros e He. destruct (finish_back _ _ _ _ _ _ _ Hfin He) as [He' | ->]; [exact (Hret0 e He') | exact Logic.I].
        + intros x Hx. destruct (Hshape x Hx) as (i & m' & Hi & [[Heq Hna] | (r' & Heq & Hin & Hnr)]);
            exists i, m'; (split; [exact (inv_app_l _ _ _ _ _ Hi) |]).
          * left. split; [exact Heq | exact Hna].
          * right. exists r'. split; [exact Heq |]. split; [| exact Hnr].
            apply (finish_keep _ _ _ _ _ _ _ Hfin Hin). intros Hkx. apply (Hnotq x Hx).
            rewrite (surjective_pairing (ts_owner x)). exact Hkx.
        + intros i k' m' Hi Hna. apply inv_snoc in Hi as [Hi | (_ & Hx)]; [| exfalso; exact (inv_not_res _ _ _ _ _ (eq_sym Hx))].
          exact (Hqinv i k' m' Hi Hna).
        + intros i k' m' Hi Hnr. apply inv_snoc in Hi as [Hi | (_ & Hx)]; [| exfalso; exact (inv_not_res _ _ _ _ _ (eq_sym Hx))].
          destruct (Hqres i k' m' Hi Hnr) as (ret' & Hq & Hc). exists ret'. split; [exact Hq |].
          apply (finish_keep _ _ _ _ _ _ _ Hfin Hc). cbn. destruct k' as [t' h']. exact (Hnotq _ Hq).
        + intros p q1 y x Hp Hq Hpq. destruct (Hord p q1 y x Hp Hq Hpq) as [Hl | (iy & ix & my & mx & Hiy & Hix & Hlt)];
            [left; exact Hl |].
          right. exists iy, ix, my, mx. split; [exact (inv_app_l _ _ _ _ _ Hiy) |].
          split; [exact (inv_app_l _ _ _ _ _ Hix) | exact Hlt].
    Qed.

    (** *** Replaying the whole run *)

    Lemma reify_step R1 st R2 cf :
      R = R1 ++ st :: R2 -> CInv R1 (st :: R2) cf ->
      exists ev cf', module_step_tagged VF idF ev cf cf' /\ overlay_events [ev] = conc [st] /\
                     CInv (R1 ++ [st]) R2 cf'.
    Proof.
      intros HR HI. destruct st as [[t [h m | h m r]] | [t h] m | [t h] m r].
      - destruct (step_cinv R1 R2 t h m cf HR HI) as (cf' & Hst & HI').
        exists (OverlayEvent (Build_ThreadEvent t (InvEv h m))), cf'. auto.
      - exact (step_cret R1 R2 t h m r cf HR HI).
      - destruct (step_ainv R1 R2 (t, h) m cf HR HI) as (cf' & Hst & HI').
        eexists. exists cf'. split; [exact Hst |]. split; [reflexivity | exact HI'].
      - exact (step_aret R1 R2 t h m r cf HR HI).
    Qed.

    Lemma reify_loop : forall R2 R1 evs cf, R = R1 ++ R2 ->
      module_execution_tagged VF idF (initial_tagged_module VF v0) evs cf ->
      overlay_events evs = conc R1 -> CInv R1 R2 cf ->
      exists evs' cf', module_execution_tagged VF idF (initial_tagged_module VF v0) evs' cf' /\
                       overlay_events evs' = conc R.
    Proof.
      induction R2 as [| st R2 IH]; intros R1 evs cf HR Hex Hov HI.
      - rewrite app_nil_r in HR. subst R1. exists evs, cf. auto.
      - destruct (reify_step R1 st R2 cf HR HI) as (ev & cf' & Hst & Hev & HI').
        apply (IH (R1 ++ [st]) (evs ++ [ev]) cf').
        + rewrite <- app_assoc. exact HR.
        + exact (exec_snoc VF idF _ _ _ _ _ Hex Hst).
        + rewrite overlay_events_app, conc_app, Hov, Hev. reflexivity.
        + exact HI'.
    Qed.

    (** The reified execution: one execution of the copy-cat over [VF]
        from [v0] whose overlay trace is the concrete trace of [R]. *)
    Theorem reify :
      exists evs cf, module_execution_tagged VF idF (initial_tagged_module VF v0) evs cf /\
                     overlay_events evs = conc R.
    Proof.
      apply (reify_loop R [] [] (initial_tagged_module VF v0)); [reflexivity | constructor | reflexivity |].
      exact cinv_init.
    Qed.
  End Reify.

  (** ** The committed results *)

  Section CommittedResult.
    Context {F : RelaxedSig.t} (VF : LTS F) (v0 : State VF).

    Abbreviation inv L := (inv_at (@PrefixView.sel F) L).
    Abbreviation res L := (res_at (@PrefixView.sel F) L).
    Abbreviation rev_ k m r := (Build_ThreadEvent (fst k) (@ResEv F (snd k) m r)).

    (** The hypothesis [Hval] of [reify] for the run of a simulated
        execution: the result of the call's abstract response if the run
        has one (unique by [AUniq]), otherwise the result the module [M]
        itself committed at the call's invocation (the call is then still
        active in [M]'s call pool, by [ri_cdead] and [TValid]).  This is the
        only use of [Classical_Prop.classic] in the file: whether the run
        has an abstract response for the call is not decidable, because
        handles have no decidable equality. *)
    Lemma rinv_val run calls v pool :
      RInv VF v0 run calls v pool ->
      forall i k m, inv (conc run) i k m ->
        exists ret : Sig.ar m, forall b r, res (abs run) b k m r -> rev_ k m r = rev_ k m ret.
    Proof.
      intros HI i k m Hi.
      pose proof (ri_lwf _ _ _ _ _ _ HI) as Hwf.
      destruct (classic (exists b (r : Sig.ar m), res (abs run) b k m r)) as [(b0 & r0 & Hb0) | Hno].
      - exists r0. intros b r Hb. pose proof (ri_aures _ _ _ _ _ _ HI _ _ _ _ _ _ _ Hb Hb0) as <-.
        destruct Hb as (x & Hx & Hs). destruct Hb0 as (x' & Hx' & Hs'). rewrite Hx in Hx'. injection Hx' as <-.
        unfold PrefixView.sel in Hs, Hs'. rewrite Hs in Hs'. exact (some_inj _ _ Hs').
      - pose proof (ri_cin _ _ _ _ _ _ HI _ _ _ Hi) as Hk. apply in_map_iff in Hk as (e & Hke & He).
        destruct e as [t h [m' ret' |]]; cbn in Hke; subst k.
        + destruct (ri_cact _ _ _ _ _ _ HI _ _ _ _ He) as ((i' & Hi') & _).
          pose proof (inv_op_unique _ _ _ _ _ _ Hwf Hi' Hi) as Hm. subst m'.
          exists ret'. intros b r Hb. exfalso. apply Hno. exists b, r. exact Hb.
        + exfalso. destruct (ri_cdead _ _ _ _ _ _ HI _ _ He) as (j & m'' & r'' & Hj).
          pose proof (res_op_inv _ _ _ _ _ _ _ Hwf Hj Hi) as Hm. subst m''.
          destruct (conc_res_step _ _ _ _ _ Hj) as (r1 & r2 & Hrun).
          destruct (ri_valid _ _ _ _ _ _ HI r1 _ r2 Hrun (t, h) m r'' eq_refl) as (b & Hb).
          apply Hno. exists b, r''. rewrite Hrun, abs_app. exact (res_app_l _ _ _ _ _ _ Hb).
    Qed.

    (** Every execution of the run's invariant is reified. *)
    Theorem rinv_reify run calls v pool :
      RInv VF v0 run calls v pool ->
      exists evs cf, module_execution_tagged VF idF (initial_tagged_module VF v0) evs cf /\
                     overlay_events evs = conc run.
    Proof.
      intros HI.
      exact (reify VF v0 run v (ri_path _ _ _ _ _ _ HI) (ri_valid _ _ _ _ _ _ HI) (ri_lwf _ _ _ _ _ _ HI)
               (ri_auinv _ _ _ _ _ _ HI) (ri_aures _ _ _ _ _ _ HI) (rinv_val _ _ _ _ HI)).
    Qed.
  End CommittedResult.

  (** ** Soundness: copy-cat trace inclusion for every execution *)

  (** The relaxed analogue of [CompLinSound.cal_to_CompLin]: a global
      simulation [GSimRel VE VF M S] that relates the initial module
      configuration to the initial possibility [PossOk v0 []] gives
      [RCompLin M VE σ0 VF v0].  No completeness hypothesis: every
      execution of [M] over [VE], with pending calls or not.  No
      hypothesis on [VF]. *)
  Theorem gsim_complin {E F : RelaxedSig.t} (VE : LTS E) (VF : LTS F) (M : RelaxedModuleImpl E F)
      (S : TaggedModuleConfig VE -> Poss VF -> Prop) (σ0 : State VE) (v0 : State VF) :
    GSimRel VE VF M S -> S (initial_tagged_module VE σ0) (PossOk v0 []) ->
    RCompLin M VE σ0 VF v0.
  Proof.
    intros HS H0 s (evs & c & Hex & <-).
    destruct (rinv_exec VE VF M v0 S _ _ _ HS Hex [] v0 [] H0 (RInv_init VF v0)) as (run & v & pool & _ & HI & Hc).
    cbn [app] in HI.
    destruct (rinv_reify VF v0 run _ _ _ HI) as (evs' & cf & Hex' & Hov).
    exists evs', cf. split; [exact Hex' |]. rewrite Hov. exact Hc.
  Qed.

  Section RLHL.
    Import RelaxedHoareBase RelaxedHoareGSim.

    (** RLHL-3a: the RLHL hypotheses give copy-cat trace inclusion for
        every execution, over any [VE] and [VF]. *)
    Theorem rlhl_complin {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}
        (I : Assn VE VF) (R G : CallKey F -> PRel VE VF) (M : RelaxedModuleImpl E F)
        (σ0 : State VE) (v0 : State VF) :
      RLHL2Hyps I R G M σ0 v0 -> RCompLin M VE σ0 VF v0.
    Proof.
      intros HH. destruct (rlhl_gsim I R G M σ0 v0 HH) as (S & HS & H0).
      exact (gsim_complin VE VF M S σ0 v0 HS H0).
    Qed.

    (** The author's layering (research-intent §8, M-20): the overlay is the
        effect-at-invocation LTS of the sequential specification [δ]. *)
    Corollary rlhl_complin_ei {E F : RelaxedSig.t} {VE : LTS E} {St : Type}
        (δ : St -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> St -> Prop) (s0 : St)
        (I : Assn VE (RelaxedHoareSpec.EI δ)) (R G : CallKey F -> PRel VE (RelaxedHoareSpec.EI δ))
        (M : RelaxedModuleImpl E F) (σ0 : State VE) :
      RLHL2Hyps I R G M σ0 (s0, []) -> RCompLin M VE σ0 (RelaxedHoareSpec.EI δ) (s0, []).
    Proof. exact (rlhl_complin I R G M σ0 (s0, [])). Qed.

    (** latest-review m-32: the paper-facing form, from derivations.  The
        premises are those of [RelaxedHoareGSim.rlhl_sound] without [HVF]
        and [Hcomplete]: derivations ([RelaxedHoare.MethodProvable]) for
        every thread and operation and the five side conditions of
        [RelaxedHoareGSim.rlhl2_of_provable].  It is [rlhl2_of_provable]
        followed by [rlhl_complin]; nothing is added. *)
    Theorem rlhl_sound_complin {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}
        (I : Assn VE VF) (R G : CallKey F -> PRel VE VF) (M : RelaxedModuleImpl E F)
        (σ0 : State VE) (v0 : State VF)
        (Hprov : forall t op, exists Ω Q, RelaxedHoare.MethodProvable I R G M t op Ω Q)
        (Hgr : forall k k' s s', k <> k' -> G k s s' -> R k' s s')
        (Hir : forall k k' op tr ret s p', k <> k' ->
           program_produces_tagged (fst k) (M op (fst k)) tr ret -> I s ->
           poss_invoke VF (fst k) (snd k) op (ps_poss s) p' ->
           R k' s (ps_mem s, p', ps_ghost s ++ ghost_new k tr))
        (Hrr : forall k k' op r s p2, k <> k' -> I s ->
           poss_return VF (fst k) (snd k) op r (ps_poss s) p2 -> NoOwn k (ps_ghost s) ->
           R k' s (ps_mem s, p2, ps_ghost s))
        (Hok : forall s, I s -> exists v pool, ps_poss s = PossOk v pool /\ lin_pool_well_formed pool)
        (Hinit : I (σ0, PossOk v0 [], [])) :
      RCompLin M VE σ0 VF v0.
    Proof. exact (rlhl_complin I R G M σ0 v0 (rlhl2_of_provable I R G M σ0 v0 Hprov Hgr Hir Hrr Hok Hinit)). Qed.
  End RLHL.
End RelaxedHoareCompLin.
