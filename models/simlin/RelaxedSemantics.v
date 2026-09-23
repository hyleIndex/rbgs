(** Thread-local semantics for programs with explicit futures. *)

Require Import Coq.Lists.List.
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
