(** Thread-local semantics for programs with explicit futures. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Relations.Relation_Operators.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import LinCCAL.
Require Import RelaxedLTS.
Require Import RelaxedLang.

Import ListNotations.


Module RelaxedSemantics.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.

  (** ** Future store *)

  (** A store entry remembers the operation associated with a raw handle.
      A response changes only the cell, never the handle or its operation. *)
  Inductive FutureCell (E : RelaxedSig.t) : Type :=
  | Pending
      (op : Sig.op (RelaxedSig.effect E))
  | Resolved
      (op : Sig.op (RelaxedSig.effect E))
      (ret : Sig.ar op).

  Arguments FutureCell _ : clear implicits.
  Arguments Pending {E} _.
  Arguments Resolved {E} _ _.

  Record FutureEntry (E : RelaxedSig.t) : Type := {
    fe_handle : RelaxedSig.handle E;
    fe_cell : FutureCell E;
  }.

  Arguments FutureEntry _ : clear implicits.
  Arguments Build_FutureEntry {E} _ _.

  Definition FutureStore (E : RelaxedSig.t) : Type :=
    list (FutureEntry E).

  Definition empty_store {E} : FutureStore E := [].

  Definition add_pending {E}
      (h : RelaxedSig.handle E)
      (op : Sig.op (RelaxedSig.effect E))
      (H : FutureStore E) : FutureStore E :=
    Build_FutureEntry h (Pending op) :: H.

  Definition handle_fresh {E}
      (h : RelaxedSig.handle E) (H : FutureStore E) : Prop :=
    ~ In h (map (fe_handle E) H).

  Definition store_well_formed {E} (H : FutureStore E) : Prop :=
    NoDup (map (fe_handle E) H).

  Definition pending_at {E}
      (h : RelaxedSig.handle E)
      (op : Sig.op (RelaxedSig.effect E))
      (H : FutureStore E) : Prop :=
    In (Build_FutureEntry h (Pending op)) H.

  Definition resolved_at {E}
      (h : RelaxedSig.handle E)
      (op : Sig.op (RelaxedSig.effect E))
      (ret : Sig.ar op)
      (H : FutureStore E) : Prop :=
    In (Build_FutureEntry h (Resolved op ret)) H.

  (** Relational replacement avoids imposing decidable equality on the
      abstract handle type.  [resolve_store] replaces exactly one pending
      cell by its response and leaves every other entry unchanged. *)
  Inductive resolve_store {E}
      (h : RelaxedSig.handle E)
      (op : Sig.op (RelaxedSig.effect E))
      (ret : Sig.ar op) : FutureStore E -> FutureStore E -> Prop :=
  | resolve_here tail :
      resolve_store h op ret
        (Build_FutureEntry h (Pending op) :: tail)
        (Build_FutureEntry h (Resolved op ret) :: tail)
  | resolve_next h' cell H H'
      (Hneq : h' <> h)
      (Hresolve : resolve_store h op ret H H') :
      resolve_store h op ret
        (Build_FutureEntry h' cell :: H)
        (Build_FutureEntry h' cell :: H').

  Definition cell_is_resolved {E} (cell : FutureCell E) : Prop :=
    match cell with
    | Pending _ => False
    | Resolved _ _ => True
    end.

  Definition all_resolved {E} (H : FutureStore E) : Prop :=
    Forall (fun entry => cell_is_resolved (fe_cell E entry)) H.

  Lemma empty_store_well_formed {E : RelaxedSig.t} :
    store_well_formed (@empty_store E).
  Proof.
    constructor.
  Qed.

  Lemma add_pending_well_formed
      {E : RelaxedSig.t}
      (h : RelaxedSig.handle E)
      (op : Sig.op (RelaxedSig.effect E))
      (H : FutureStore E) :
    handle_fresh h H ->
    store_well_formed H ->
    store_well_formed (add_pending h op H).
  Proof.
    intros Hfresh Hwf.
    unfold handle_fresh, store_well_formed, add_pending in *.
    cbn. constructor; assumption.
  Qed.

  Lemma resolve_store_pending
      {E : RelaxedSig.t}
      (h : RelaxedSig.handle E)
      (op : Sig.op (RelaxedSig.effect E))
      (ret : Sig.ar op)
      (H H' : FutureStore E) :
    resolve_store h op ret H H' ->
    pending_at h op H.
  Proof.
    intro Hresolve.
    induction Hresolve; cbn; auto.
  Qed.

  Lemma resolve_store_resolved
      {E : RelaxedSig.t}
      (h : RelaxedSig.handle E)
      (op : Sig.op (RelaxedSig.effect E))
      (ret : Sig.ar op)
      (H H' : FutureStore E) :
    resolve_store h op ret H H' ->
    resolved_at h op ret H'.
  Proof.
    intro Hresolve.
    induction Hresolve; cbn; auto.
  Qed.

  Lemma resolve_store_handles
      {E : RelaxedSig.t}
      (h : RelaxedSig.handle E)
      (op : Sig.op (RelaxedSig.effect E))
      (ret : Sig.ar op)
      (H H' : FutureStore E) :
    resolve_store h op ret H H' ->
    map (fe_handle E) H = map (fe_handle E) H'.
  Proof.
    intro Hresolve.
    induction Hresolve; cbn; congruence.
  Qed.

  Lemma resolve_store_well_formed
      {E : RelaxedSig.t}
      (h : RelaxedSig.handle E)
      (op : Sig.op (RelaxedSig.effect E))
      (ret : Sig.ar op)
      (H H' : FutureStore E) :
    resolve_store h op ret H H' ->
    store_well_formed H ->
    store_well_formed H'.
  Proof.
    intros Hresolve Hwf.
    unfold store_well_formed in *.
    erewrite <- resolve_store_handles; eauto.
  Qed.

  (** ** Program traces before linking the shared underlay LTS *)

  Inductive Action (E : RelaxedSig.t) : Type :=
  | Silent
  | Emit (ev : RelaxedLTSSpec.ThreadEvent E).

  Arguments Action _ : clear implicits.
  Arguments Silent {E}.
  Arguments Emit {E} _.

  Record ProgramConfig (E : RelaxedSig.t) (R : Type) : Type := {
    pc_prog : RelaxedLang.Prog E R;
    pc_futures : FutureStore E;
  }.

  Arguments ProgramConfig _ _ : clear implicits.
  Arguments Build_ProgramConfig {E R} _ _.
  Arguments pc_prog {E R} _.
  Arguments pc_futures {E R} _.

  Section ProgramSemantics.
    Context {E : RelaxedSig.t}.
    Context {R : Type}.

    (** This relation generates a method's event continuation without
        committing it to a particular shared underlay state. *)
    Inductive program_step (t : tid) :
        Action E -> ProgramConfig E R -> ProgramConfig E R -> Prop :=
    | program_future op k h H
        (Hfresh : handle_fresh h H) :
        program_step t
          (Emit (Build_ThreadEvent t (InvEv h op)))
          (Build_ProgramConfig (Future op k) H)
          (Build_ProgramConfig
            (k (MkFutureRef op h))
            (add_pending h op H))

    (** The positional semantics ignores dependency tags. *)
    | program_futureD op deps k h H
        (Hfresh : handle_fresh h H) :
        program_step t
          (Emit (Build_ThreadEvent t (InvEv h op)))
          (Build_ProgramConfig (FutureD op deps k) H)
          (Build_ProgramConfig
            (k (MkFutureRef op h))
            (add_pending h op H))

    | program_wait_resolved op h ret k H
        (Hresolved : resolved_at h op ret H) :
        program_step t Silent
          (Build_ProgramConfig
            (Wait (MkFutureRef op h) k) H)
          (Build_ProgramConfig (k ret) H)

    | program_wait_pending op h ret k H H'
        (Hresolve : resolve_store h op ret H H') :
        program_step t
          (Emit (Build_ThreadEvent t (ResEv h op ret)))
          (Build_ProgramConfig
            (Wait (MkFutureRef op h) k) H)
          (Build_ProgramConfig (k ret) H')

    | program_resolve op h ret p H H'
        (Hresolve : resolve_store h op ret H H') :
        program_step t
          (Emit (Build_ThreadEvent t (ResEv h op ret)))
          (Build_ProgramConfig p H)
          (Build_ProgramConfig p H')

    | program_tau p H :
        program_step t Silent
          (Build_ProgramConfig (Tau p) H)
          (Build_ProgramConfig p H).

    Inductive program_terminal : ProgramConfig E R -> R -> Prop :=
    | program_terminal_ret H r
        (Hresolved : all_resolved H) :
        program_terminal (Build_ProgramConfig (Ret r) H) r.

    Definition initial_program
        (p : RelaxedLang.Prog E R) : ProgramConfig E R :=
      Build_ProgramConfig p empty_store.

    Inductive program_execution (t : tid) :
        ProgramConfig E R ->
        list (RelaxedLTSSpec.ThreadEvent E) ->
        ProgramConfig E R -> Prop :=
    | program_execution_refl c :
        program_execution t c [] c
    | program_execution_silent c1 c2 c3 trace
        (Hstep : program_step t Silent c1 c2)
        (Hexec : program_execution t c2 trace c3) :
        program_execution t c1 trace c3
    | program_execution_emit c1 c2 c3 ev trace
        (Hstep : program_step t (Emit ev) c1 c2)
        (Hexec : program_execution t c2 trace c3) :
        program_execution t c1 (ev :: trace) c3.

    Definition program_produces
        (t : tid)
        (p : RelaxedLang.Prog E R)
        (trace : list (RelaxedLTSSpec.ThreadEvent E))
        (r : R) : Prop :=
      exists c',
        program_execution t (initial_program p) trace c' /\
        program_terminal c' r.

    Lemma program_step_store_well_formed t action c c' :
      program_step t action c c' ->
      store_well_formed (pc_futures c) ->
      store_well_formed (pc_futures c').
    Proof.
      intros Hstep Hwf.
      inversion Hstep; subst; cbn in *; eauto using
        add_pending_well_formed, resolve_store_well_formed.
    Qed.

    Lemma program_step_emit_tid t ev c c' :
      program_step t (Emit ev) c c' ->
      te_tid E ev = t.
    Proof.
      intro Hstep.
      inversion Hstep; reflexivity.
    Qed.

    Lemma program_execution_store_well_formed t c trace c' :
      program_execution t c trace c' ->
      store_well_formed (pc_futures c) ->
      store_well_formed (pc_futures c').
    Proof.
      intro Hexec.
      induction Hexec; intros Hwf; eauto using
        program_step_store_well_formed.
    Qed.

    Lemma program_execution_trace_tid t c trace c' :
      program_execution t c trace c' ->
      Forall (fun ev => te_tid E ev = t) trace.
    Proof.
      intro Hexec.
      induction Hexec.
      - constructor.
      - exact IHHexec.
      - constructor.
        + eapply program_step_emit_tid; eauto.
        + exact IHHexec.
    Qed.

    Lemma program_produces_trace_tid t p trace r :
      program_produces t p trace r ->
      Forall (fun ev => te_tid E ev = t) trace.
    Proof.
      intros [c' [Hexec _]].
      eapply program_execution_trace_tid; eauto.
    Qed.

  End ProgramSemantics.

  (** ** Dependency-tagged program traces (WSC edit, 2026-09-28)

      The paper's local semantics produces \emph{tagged} event lists: every
      invocation event carries the set of handles it depends on, and the
      module-level scheduler emits from a dag frontier in which a response
      blocks only the invocations tagged with it.  [program_step] above is
      the untagged (positional) semantics; the tagged semantics below
      mirrors it rule by rule and records, on every invocation event, its
      effective tag: for [FutureD op deps k] the handles of [deps] that are
      resolved at the time of the invocation (an unresolved handle cannot
      have contributed a value, which is the paper's side condition that
      the arguments of an invocation are values), and for an untagged
      [Future op k] every handle resolved so far. *)

  Record TaggedEvent (E : RelaxedSig.t) : Type := {
    tev_ev : RelaxedLTSSpec.ThreadEvent E;
    tev_deps : RelaxedSig.handle E -> Prop;
  }.

  Arguments TaggedEvent _ : clear implicits.
  Arguments Build_TaggedEvent {E} _ _.
  Arguments tev_ev {E} _.
  Arguments tev_deps {E} _.

  (** Tags are erased when an event enters a global trace. *)
  Definition untag {E} (m : TaggedEvent E) : RelaxedLTSSpec.ThreadEvent E :=
    tev_ev m.

  Definition no_deps {E} : RelaxedSig.handle E -> Prop := fun _ => False.

  Definition resolved_in {E} (H : FutureStore E) (h : RelaxedSig.handle E) : Prop :=
    exists op ret, resolved_at h op ret H.

  Inductive TAction (E : RelaxedSig.t) : Type :=
  | TSilent
  | TEmit (m : TaggedEvent E).

  Arguments TAction _ : clear implicits.
  Arguments TSilent {E}.
  Arguments TEmit {E} _.

  Definition untag_action {E} (a : TAction E) : Action E :=
    match a with
    | TSilent => Silent
    | TEmit m => Emit (untag m)
    end.

  Section TaggedProgramSemantics.
    Context {E : RelaxedSig.t}.
    Context {R : Type}.

    Inductive program_step_tagged (t : tid) :
        TAction E -> ProgramConfig E R -> ProgramConfig E R -> Prop :=
    | tagged_future op k h H
        (Hfresh : handle_fresh h H) :
        program_step_tagged t
          (TEmit (Build_TaggedEvent (Build_ThreadEvent t (InvEv h op)) (resolved_in H)))
          (Build_ProgramConfig (Future op k) H)
          (Build_ProgramConfig
            (k (MkFutureRef op h))
            (add_pending h op H))

    | tagged_futureD op deps k h H
        (Hfresh : handle_fresh h H) :
        program_step_tagged t
          (TEmit (Build_TaggedEvent (Build_ThreadEvent t (InvEv h op))
                    (fun q => deps q /\ resolved_in H q)))
          (Build_ProgramConfig (FutureD op deps k) H)
          (Build_ProgramConfig
            (k (MkFutureRef op h))
            (add_pending h op H))

    | tagged_wait_resolved op h ret k H
        (Hresolved : resolved_at h op ret H) :
        program_step_tagged t TSilent
          (Build_ProgramConfig
            (Wait (MkFutureRef op h) k) H)
          (Build_ProgramConfig (k ret) H)

    | tagged_wait_pending op h ret k H H'
        (Hresolve : resolve_store h op ret H H') :
        program_step_tagged t
          (TEmit (Build_TaggedEvent (Build_ThreadEvent t (ResEv h op ret)) no_deps))
          (Build_ProgramConfig
            (Wait (MkFutureRef op h) k) H)
          (Build_ProgramConfig (k ret) H')

    | tagged_resolve op h ret p H H'
        (Hresolve : resolve_store h op ret H H') :
        program_step_tagged t
          (TEmit (Build_TaggedEvent (Build_ThreadEvent t (ResEv h op ret)) no_deps))
          (Build_ProgramConfig p H)
          (Build_ProgramConfig p H')

    | tagged_tau p H :
        program_step_tagged t TSilent
          (Build_ProgramConfig (Tau p) H)
          (Build_ProgramConfig p H).

    Inductive program_execution_tagged (t : tid) :
        ProgramConfig E R ->
        list (TaggedEvent E) ->
        ProgramConfig E R -> Prop :=
    | tagged_execution_refl c :
        program_execution_tagged t c [] c
    | tagged_execution_silent c1 c2 c3 trace
        (Hstep : program_step_tagged t TSilent c1 c2)
        (Hexec : program_execution_tagged t c2 trace c3) :
        program_execution_tagged t c1 trace c3
    | tagged_execution_emit c1 c2 c3 m trace
        (Hstep : program_step_tagged t (TEmit m) c1 c2)
        (Hexec : program_execution_tagged t c2 trace c3) :
        program_execution_tagged t c1 (m :: trace) c3.

    Definition program_produces_tagged
        (t : tid)
        (p : RelaxedLang.Prog E R)
        (trace : list (TaggedEvent E))
        (r : R) : Prop :=
      exists c',
        program_execution_tagged t (initial_program p) trace c' /\
        program_terminal c' r.

    (** *** Erasure: a tagged step is an untagged step *)

    Lemma program_step_tagged_untag t a c c' :
      program_step_tagged t a c c' -> program_step t (untag_action a) c c'.
    Proof.
      intros Hstep. inversion Hstep; subst; cbn.
      - apply program_future; auto.
      - apply program_futureD; auto.
      - apply program_wait_resolved; auto.
      - apply program_wait_pending; auto.
      - apply program_resolve; auto.
      - apply program_tau.
    Qed.

    Lemma program_execution_tagged_untag t c trace c' :
      program_execution_tagged t c trace c' ->
      program_execution t c (map untag trace) c'.
    Proof.
      intros Hexec. induction Hexec.
      - apply program_execution_refl.
      - eapply program_execution_silent; eauto.
        apply (program_step_tagged_untag _ _ _ _ Hstep).
      - cbn. eapply program_execution_emit; eauto.
        apply (program_step_tagged_untag _ _ _ _ Hstep).
    Qed.

    Lemma program_produces_tagged_untag t p trace r :
      program_produces_tagged t p trace r ->
      program_produces t p (map untag trace) r.
    Proof.
      intros (c' & Hexec & Hterm). exists c'. split; auto.
      apply program_execution_tagged_untag. exact Hexec.
    Qed.

    (** *** Lifting: every untagged step has a tagged counterpart *)

    Lemma program_step_untag_tagged t a c c' :
      program_step t a c c' ->
      exists a', program_step_tagged t a' c c' /\ untag_action a' = a.
    Proof.
      intros Hstep. inversion Hstep; subst.
      - eexists. split; [apply tagged_future; auto | reflexivity].
      - eexists. split; [apply tagged_futureD; auto | reflexivity].
      - eexists. split; [apply tagged_wait_resolved; eauto | reflexivity].
      - eexists. split; [apply tagged_wait_pending; eauto | reflexivity].
      - eexists. split; [apply tagged_resolve; eauto | reflexivity].
      - eexists. split; [apply tagged_tau | reflexivity].
    Qed.

    Lemma program_execution_untag_tagged t c trace c' :
      program_execution t c trace c' ->
      exists trace', program_execution_tagged t c trace' c' /\ map untag trace' = trace.
    Proof.
      intros Hexec. induction Hexec as [c | c1 c2 c3 trace Hstep Hexec IH | c1 c2 c3 ev trace Hstep Hexec IH].
      - exists []. split; [apply tagged_execution_refl | reflexivity].
      - destruct IH as (trace' & Hexec' & Heq).
        destruct (program_step_untag_tagged _ _ _ _ Hstep) as (a' & Hstep' & Ha').
        destruct a' as [| m]; cbn in Ha'; [| discriminate].
        exists trace'. split; auto. eapply tagged_execution_silent; eauto.
      - destruct IH as (trace' & Hexec' & Heq).
        destruct (program_step_untag_tagged _ _ _ _ Hstep) as (a' & Hstep' & Ha').
        destruct a' as [| m]; cbn in Ha'; [discriminate |].
        inversion Ha'; subst ev.
        exists (m :: trace'). split; [eapply tagged_execution_emit; eauto | cbn; congruence].
    Qed.

    Lemma program_produces_untag_tagged t p trace r :
      program_produces t p trace r ->
      exists trace', program_produces_tagged t p trace' r /\ map untag trace' = trace.
    Proof.
      intros (c' & Hexec & Hterm).
      destruct (program_execution_untag_tagged _ _ _ _ Hexec) as (trace' & Hexec' & Heq).
      exists trace'. split; auto. exists c'. auto.
    Qed.

    (** *** Dependency soundness at the local level (Lemma lem:wsc-dep, first half)

        A handle in the tag of an emitted invocation was resolved when the
        invocation was issued, and a handle becomes resolved only by a step
        that emits its response.  Hence the response of every handle an
        invocation depends on precedes the invocation in the local trace. *)

    Definition is_response_of {E'} (q : RelaxedSig.handle E') (ev : RelaxedLTSSpec.ThreadEvent E') : Prop :=
      match te_ev E' ev with
      | ResEv h _ _ => h = q
      | InvEv _ _ => False
      end.

    Lemma resolved_in_add_pending (H : FutureStore E) h op q :
      resolved_in (add_pending h op H) q -> resolved_in H q.
    Proof.
      intros (op' & ret & Hin). unfold add_pending in Hin. cbn in Hin.
      destruct Hin as [Heq | Hin]; [discriminate |]. exists op', ret. exact Hin.
    Qed.

    Lemma resolved_in_resolve_store (H H' : FutureStore E) h op ret q :
      resolve_store h op ret H H' -> resolved_in H' q -> q = h \/ resolved_in H q.
    Proof.
      intros Hres. induction Hres as [tail | h' cell H H' Hneq Hres IH]; intros (op' & ret' & Hin).
      - cbn in Hin. destruct Hin as [Heq | Hin].
        + inversion Heq; subst. left. reflexivity.
        + right. exists op', ret'. right. exact Hin.
      - cbn in Hin. destruct Hin as [Heq | Hin].
        + right. exists op', ret'. left. exact Heq.
        + destruct (IH (ex_intro _ op' (ex_intro _ ret' Hin))) as [Hq | (op'' & ret'' & Hin'')].
          * left. exact Hq.
          * right. exists op'', ret''. right. exact Hin''.
    Qed.

    (** Along a tagged execution from a configuration whose resolved
        handles all have their response in a prefix [pre], every handle
        resolved later has its response in the trace, before the position
        where it first appears resolved. *)
    Lemma tagged_execution_resolved_emitted t c trace c' :
      program_execution_tagged t c trace c' ->
      forall i m q,
        nth_error trace i = Some m ->
        tev_deps m q ->
        resolved_in (pc_futures c) q \/
        exists j r, j < i /\ nth_error trace j = Some r /\ is_response_of q (untag r).
    Proof.
      intros Hexec. induction Hexec as [c | c1 c2 c3 trace Hstep Hexec IH | c1 c2 c3 m0 trace Hstep Hexec IH];
        intros i m q Hi Hq.
      - destruct i; discriminate.
      - (* silent steps do not change the store's resolved handles *)
        destruct (IH i m q Hi Hq) as [Hres | Hres]; [| right; exact Hres].
        left. inversion Hstep; subst; cbn in *; exact Hres.
      - destruct i as [| i]; cbn in Hi.
        + inversion Hi; subst m0. clear Hi.
          (* the emitted event's tag refers to handles resolved before the step *)
          left. inversion Hstep; subst; cbn in *.
          * exact Hq.
          * destruct Hq as [_ Hq]. exact Hq.
          * destruct Hq.
          * destruct Hq.
        + destruct (IH i m q Hi Hq) as [Hres | (j & r & Hj & Hjr & Hresp)].
          * inversion Hstep; subst; cbn in *.
            -- left. eapply resolved_in_add_pending. exact Hres.
            -- left. eapply resolved_in_add_pending. exact Hres.
            -- destruct (resolved_in_resolve_store _ _ _ _ _ _ Hresolve Hres) as [-> | Hres'].
               ++ right. exists 0. eexists. split; [lia | split; [reflexivity | cbn; reflexivity]].
               ++ left. exact Hres'.
            -- destruct (resolved_in_resolve_store _ _ _ _ _ _ Hresolve Hres) as [-> | Hres'].
               ++ right. exists 0. eexists. split; [lia | split; [reflexivity | cbn; reflexivity]].
               ++ left. exact Hres'.
          * right. exists (S j), r. split; [lia | auto].
    Qed.

    Lemma program_step_tagged_emit_tid t m c c' :
      program_step_tagged t (TEmit m) c c' -> te_tid E (untag m) = t.
    Proof. intro Hstep. inversion Hstep; reflexivity. Qed.

    Lemma program_execution_tagged_trace_tid t c trace c' :
      program_execution_tagged t c trace c' ->
      Forall (fun m => te_tid E (untag m) = t) trace.
    Proof.
      intro Hexec. induction Hexec.
      - constructor.
      - exact IHHexec.
      - constructor; [eapply program_step_tagged_emit_tid; eauto | exact IHHexec].
    Qed.

    Lemma program_produces_tagged_trace_tid t p trace r :
      program_produces_tagged t p trace r ->
      Forall (fun m => te_tid E (untag m) = t) trace.
    Proof.
      intros (c' & Hexec & _). eapply program_execution_tagged_trace_tid; eauto.
    Qed.

    (** Responses carry no dependencies. *)
    Definition is_invocation {E'} (ev : RelaxedLTSSpec.ThreadEvent E') : Prop :=
      match te_ev E' ev with
      | InvEv _ _ => True
      | ResEv _ _ _ => False
      end.

    Lemma program_step_tagged_deps_invocation t m c c' q :
      program_step_tagged t (TEmit m) c c' -> tev_deps m q -> is_invocation (untag m).
    Proof.
      intros Hstep Hq. inversion Hstep; subst; cbn in *; try exact I; destruct Hq.
    Qed.

    Lemma program_execution_tagged_deps_invocation t c trace c' :
      program_execution_tagged t c trace c' ->
      Forall (fun m => forall q, tev_deps m q -> is_invocation (untag m)) trace.
    Proof.
      intro Hexec. induction Hexec.
      - constructor.
      - exact IHHexec.
      - constructor; [intros q Hq; eapply program_step_tagged_deps_invocation; eauto | exact IHHexec].
    Qed.

    Lemma program_produces_tagged_deps_invocation t p trace r :
      program_produces_tagged t p trace r ->
      Forall (fun m => forall q, tev_deps m q -> is_invocation (untag m)) trace.
    Proof.
      intros (c' & Hexec & _). eapply program_execution_tagged_deps_invocation; eauto.
    Qed.

    Lemma resolved_in_empty q : ~ resolved_in (@empty_store E) q.
    Proof. intros (op & ret & Hin). inversion Hin. Qed.

    (** In a trace produced from the initial configuration, the response of
        every handle an invocation is tagged with precedes the invocation. *)
    Lemma program_produces_tagged_dependency t p trace r :
      program_produces_tagged t p trace r ->
      forall i m q,
        nth_error trace i = Some m ->
        tev_deps m q ->
        exists j r', j < i /\ nth_error trace j = Some r' /\ is_response_of q (untag r').
    Proof.
      intros (c' & Hexec & _) i m q Hi Hq.
      destruct (tagged_execution_resolved_emitted _ _ _ _ Hexec i m q Hi Hq) as [Hres | Hres]; auto.
      exfalso. eapply resolved_in_empty. exact Hres.
    Qed.

  End TaggedProgramSemantics.

  (** ** Thread-local configurations linked to an underlay LTS *)

  Record ThreadConfig {E : RelaxedSig.t}
      (VE : RelaxedLTSSpec.LTS E) (R : Type) : Type := {
    tc_lts_state : RelaxedLTSSpec.State VE;
    tc_prog : RelaxedLang.Prog E R;
    tc_futures : FutureStore E;
  }.

  Arguments ThreadConfig {E} _ _.
  Arguments Build_ThreadConfig {E VE R} _ _ _.
  Arguments tc_lts_state {E VE R} _.
  Arguments tc_prog {E VE R} _.
  Arguments tc_futures {E VE R} _.

  Section LocalSemantics.
    Context {E : RelaxedSig.t}.
    Context (VE : RelaxedLTSSpec.LTS E).
    Context {R : Type}.

    (** [local_step] combines the program transition with the matching
        transition of the underlay LTS. *)
    Inductive local_step (t : tid) :
        Action E -> ThreadConfig VE R -> ThreadConfig VE R -> Prop :=
    | step_future op k h q q' H
        (Hfresh : handle_fresh h H)
        (Hlts : RelaxedLTSSpec.Step VE
          (Build_ThreadEvent t (InvEv h op)) q q') :
        local_step t
          (Emit (Build_ThreadEvent t (InvEv h op)))
          (Build_ThreadConfig q (Future op k) H)
          (Build_ThreadConfig q'
            (k (MkFutureRef op h))
            (add_pending h op H))

    | step_wait_resolved op h ret k q H
        (Hresolved : resolved_at h op ret H) :
        local_step t Silent
          (Build_ThreadConfig q
            (Wait (MkFutureRef op h) k) H)
          (Build_ThreadConfig q (k ret) H)

    | step_wait_pending op h ret k q q' H H'
        (Hresolve : resolve_store h op ret H H')
        (Hlts : RelaxedLTSSpec.Step VE
          (Build_ThreadEvent t (ResEv h op ret)) q q') :
        local_step t
          (Emit (Build_ThreadEvent t (ResEv h op ret)))
          (Build_ThreadConfig q
            (Wait (MkFutureRef op h) k) H)
          (Build_ThreadConfig q' (k ret) H')

    | step_resolve op h ret p q q' H H'
        (Hresolve : resolve_store h op ret H H')
        (Hlts : RelaxedLTSSpec.Step VE
          (Build_ThreadEvent t (ResEv h op ret)) q q') :
        local_step t
          (Emit (Build_ThreadEvent t (ResEv h op ret)))
          (Build_ThreadConfig q p H)
          (Build_ThreadConfig q' p H')

    | step_tau p q H :
        local_step t Silent
          (Build_ThreadConfig q (Tau p) H)
          (Build_ThreadConfig q p H).

    (** Errors are observable exactly where the underlay LTS rejects an
        invocation or a possible response. *)
    Inductive local_error (t : tid) : ThreadConfig VE R -> Prop :=
    | error_future op k h q H
        (Hfresh : handle_fresh h H)
        (Herror : RelaxedLTSSpec.Error VE
          (Build_ThreadEvent t (InvEv h op)) q) :
        local_error t (Build_ThreadConfig q (Future op k) H)
    | error_response op h ret p q H
        (Hpending : pending_at h op H)
        (Herror : RelaxedLTSSpec.Error VE
          (Build_ThreadEvent t (ResEv h op ret)) q) :
        local_error t (Build_ThreadConfig q p H).

    Inductive terminal : ThreadConfig VE R -> R -> Prop :=
    | terminal_ret q H r
        (Hresolved : all_resolved H) :
        terminal (Build_ThreadConfig q (Ret r) H) r.

    Definition initial_config
        (q : RelaxedLTSSpec.State VE)
        (p : RelaxedLang.Prog E R) : ThreadConfig VE R :=
      Build_ThreadConfig q p empty_store.

    Definition erased_step (t : tid) :
        ThreadConfig VE R -> ThreadConfig VE R -> Prop :=
      fun c c' => exists action, local_step t action c c'.

    Definition local_steps (t : tid) :=
      clos_refl_trans (ThreadConfig VE R) (erased_step t).

    (** [execution] retains the emitted underlay trace while erasing silent
        program steps. *)
    Inductive execution (t : tid) :
        ThreadConfig VE R ->
        list (RelaxedLTSSpec.ThreadEvent E) ->
        ThreadConfig VE R -> Prop :=
    | execution_refl c :
        execution t c [] c
    | execution_silent c1 c2 c3 trace
        (Hstep : local_step t Silent c1 c2)
        (Hexec : execution t c2 trace c3) :
        execution t c1 trace c3
    | execution_emit c1 c2 c3 ev trace
        (Hstep : local_step t (Emit ev) c1 c2)
        (Hexec : execution t c2 trace c3) :
        execution t c1 (ev :: trace) c3.

    Definition produces
        (t : tid)
        (c : ThreadConfig VE R)
        (trace : list (RelaxedLTSSpec.ThreadEvent E))
        (r : R) : Prop :=
      exists c', execution t c trace c' /\ terminal c' r.

    Lemma local_step_store_well_formed t action c c' :
      local_step t action c c' ->
      store_well_formed (tc_futures c) ->
      store_well_formed (tc_futures c').
    Proof.
      intros Hstep Hwf.
      inversion Hstep; subst; cbn in *; eauto using
        add_pending_well_formed, resolve_store_well_formed.
    Qed.

    Lemma local_step_emit_tid t ev c c' :
      local_step t (Emit ev) c c' ->
      te_tid E ev = t.
    Proof.
      intro Hstep.
      inversion Hstep; reflexivity.
    Qed.

    Lemma initial_config_store_well_formed q p :
      store_well_formed
        (tc_futures (initial_config q p)).
    Proof.
      apply empty_store_well_formed.
    Qed.

    Lemma execution_store_well_formed t c trace c' :
      execution t c trace c' ->
      store_well_formed (tc_futures c) ->
      store_well_formed (tc_futures c').
    Proof.
      intro Hexec.
      induction Hexec; intros Hwf; eauto using local_step_store_well_formed.
    Qed.

    Lemma execution_trace_tid t c trace c' :
      execution t c trace c' ->
      Forall (fun ev => te_tid E ev = t) trace.
    Proof.
      intro Hexec.
      induction Hexec.
      - constructor.
      - exact IHHexec.
      - constructor.
        + eapply local_step_emit_tid; eauto.
        + exact IHHexec.
    Qed.

  End LocalSemantics.

End RelaxedSemantics.
