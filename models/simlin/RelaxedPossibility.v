(** Handle-aware abstract possibilities for relaxed simulation. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import LinCCAL.
Require Import RelaxedLTS.

Import ListNotations.


Module RelaxedPossibility.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.

  (** ** Per-call abstract linearization state *)

  (** The three phases have the same meaning as in the SC development, but
      they are now stored at an overlay [(thread, handle)] key rather than at
      a thread key alone. *)
  Inductive LinState (F : RelaxedSig.t) : Type :=
  | ls_inv
      (op : Sig.op (RelaxedSig.effect F))
  | ls_lini
      (op : Sig.op (RelaxedSig.effect F))
  | ls_linr
      (op : Sig.op (RelaxedSig.effect F))
      (ret : Sig.ar op).

  Arguments LinState _ : clear implicits.
  Arguments ls_inv {F} _.
  Arguments ls_lini {F} _.
  Arguments ls_linr {F} _ _.

  Record LinEntry (F : RelaxedSig.t) : Type := {
    lin_tid : tid;
    lin_handle : RelaxedSig.handle F;
    lin_state : LinState F;
  }.

  Arguments LinEntry _ : clear implicits.
  Arguments Build_LinEntry {F} _ _ _.

  Definition lin_key {F} (entry : LinEntry F) : CallKey F :=
    (lin_tid F entry, lin_handle F entry).

  Definition make_lin_entry {F}
      (key : CallKey F) (state : LinState F) : LinEntry F :=
    Build_LinEntry (fst key) (snd key) state.

  Lemma lin_key_make_lin_entry
      {F : RelaxedSig.t}
      (key : CallKey F)
      (state : LinState F) :
    lin_key (make_lin_entry key state) = key.
  Proof.
    destruct key. reflexivity.
  Qed.

  Definition LinPool (F : RelaxedSig.t) : Type := list (LinEntry F).

  Definition empty_lin_pool {F} : LinPool F := [].

  Definition lin_domain {F} (pool : LinPool F) : list (CallKey F) :=
    map lin_key pool.

  Definition lin_fresh {F}
      (key : CallKey F) (pool : LinPool F) : Prop :=
    ~ In key (lin_domain pool).

  Definition lin_pool_well_formed {F} (pool : LinPool F) : Prop :=
    NoDup (lin_domain pool).

  Definition lin_lookup {F}
      (key : CallKey F)
      (state : LinState F)
      (pool : LinPool F) : Prop :=
    In (make_lin_entry key state) pool.

  (** Insertion always adds a fresh key. *)
  Inductive lin_insert {F}
      (key : CallKey F)
      (state : LinState F) : LinPool F -> LinPool F -> Prop :=
  | lin_insert_fresh pool
      (Hfresh : lin_fresh key pool) :
      lin_insert key state pool (make_lin_entry key state :: pool).

  (** Update and removal are relational so the relaxed signature does not
      need to assume decidable equality for handles.  A matching key with an
      unexpected state cannot be skipped. *)
  Inductive lin_update {F}
      (key : CallKey F)
      (before after : LinState F) : LinPool F -> LinPool F -> Prop :=
  | lin_update_here tail :
      lin_update key before after
        (make_lin_entry key before :: tail)
        (make_lin_entry key after :: tail)
  | lin_update_next entry pool pool'
      (Hneq : lin_key entry <> key)
      (Hupdate : lin_update key before after pool pool') :
      lin_update key before after
        (entry :: pool) (entry :: pool').

  (** A later invocation may be linearized before an older invocation of
      the same thread only when the signature explicitly permits that
      directed crossing.  Older calls whose invocation has already been
      linearized no longer block the candidate. *)
  Definition older_entry_allows_invocation {F}
      (t : tid)
      (op : Sig.op (RelaxedSig.effect F))
      (entry : LinEntry F) : Prop :=
    lin_tid F entry <> t \/
    match lin_state F entry with
    | ls_inv older_op =>
        RelaxedSig.semi_independent F older_op op
    | ls_lini _ => True
    | ls_linr _ _ => True
    end.

  Definition invocation_ready {F}
      (t : tid)
      (op : Sig.op (RelaxedSig.effect F))
      (older : LinPool F) : Prop :=
    Forall (older_entry_allows_invocation t op) older.

  (** Locating a pending invocation and checking its older suffix is useful
      both for successful abstract invocation steps and for invocation
      errors.  In particular, an error transition must not bypass the RLHL
      crossing discipline. *)
  Inductive lin_invocation_enabled {F}
      (t : tid)
      (h : RelaxedSig.handle F)
      (op : Sig.op (RelaxedSig.effect F)) : LinPool F -> Prop :=
  | lin_invocation_enabled_here older
      (Hready : invocation_ready t op older) :
      lin_invocation_enabled t h op
        (make_lin_entry (t, h) (ls_inv op) :: older)
  | lin_invocation_enabled_next entry pool
      (Hneq : lin_key entry <> (t, h))
      (Henabled : lin_invocation_enabled t h op pool) :
      lin_invocation_enabled t h op (entry :: pool).

  (** Pools are newest-first because [lin_insert] adds at the head.  When
      this relation reaches the selected call, its tail is therefore
      exactly the set of calls issued earlier than the selected call.
      Entries skipped on the way to the target are newer and need no
      crossing check. *)
  Inductive lin_invoke_update {F}
      (t : tid)
      (h : RelaxedSig.handle F)
      (op : Sig.op (RelaxedSig.effect F)) :
      LinPool F -> LinPool F -> Prop :=
  | lin_invoke_update_here older
      (Hready : invocation_ready t op older) :
      lin_invoke_update t h op
        (make_lin_entry (t, h) (ls_inv op) :: older)
        (make_lin_entry (t, h) (ls_lini op) :: older)
  | lin_invoke_update_next entry pool pool'
      (Hneq : lin_key entry <> (t, h))
      (Hupdate : lin_invoke_update t h op pool pool') :
      lin_invoke_update t h op
        (entry :: pool) (entry :: pool').

  Inductive lin_remove {F}
      (key : CallKey F)
      (state : LinState F) : LinPool F -> LinPool F -> Prop :=
  | lin_remove_here tail :
      lin_remove key state
        (make_lin_entry key state :: tail) tail
  | lin_remove_next entry pool pool'
      (Hneq : lin_key entry <> key)
      (Hremove : lin_remove key state pool pool') :
      lin_remove key state
        (entry :: pool) (entry :: pool').

  (** ** Pool-operation properties *)

  Lemma empty_lin_pool_well_formed {F : RelaxedSig.t} :
    lin_pool_well_formed (@empty_lin_pool F).
  Proof.
    constructor.
  Qed.

  Lemma lin_insert_well_formed
      {F : RelaxedSig.t}
      (key : CallKey F)
      (state : LinState F)
      (pool pool' : LinPool F) :
    lin_insert key state pool pool' ->
    lin_pool_well_formed pool ->
    lin_pool_well_formed pool'.
  Proof.
    intros Hinsert Hwf.
    inversion Hinsert; subst.
    destruct key as [t h].
    unfold lin_pool_well_formed, lin_fresh, lin_domain in *.
    cbn in *. constructor; assumption.
  Qed.

  Lemma lin_insert_lookup
      {F : RelaxedSig.t}
      (key : CallKey F)
      (state : LinState F)
      (pool pool' : LinPool F) :
    lin_insert key state pool pool' ->
    lin_lookup key state pool'.
  Proof.
    intro Hinsert.
    inversion Hinsert; subst; cbn; auto.
  Qed.

  Lemma lin_update_keys
      {F : RelaxedSig.t}
      (key : CallKey F)
      (before after : LinState F)
      (pool pool' : LinPool F) :
    lin_update key before after pool pool' ->
    lin_domain pool = lin_domain pool'.
  Proof.
    intro Hupdate.
    induction Hupdate.
    - reflexivity.
    - cbn. f_equal. exact IHHupdate.
  Qed.

  Lemma lin_update_source
      {F : RelaxedSig.t}
      (key : CallKey F)
      (before after : LinState F)
      (pool pool' : LinPool F) :
    lin_update key before after pool pool' ->
    lin_lookup key before pool.
  Proof.
    intro Hupdate.
    induction Hupdate; cbn; auto.
  Qed.

  Lemma lin_update_target
      {F : RelaxedSig.t}
      (key : CallKey F)
      (before after : LinState F)
      (pool pool' : LinPool F) :
    lin_update key before after pool pool' ->
    lin_lookup key after pool'.
  Proof.
    intro Hupdate.
    induction Hupdate; cbn; auto.
  Qed.

  Lemma lin_update_other_lookup
      {F : RelaxedSig.t}
      (key other : CallKey F)
      (before after other_state : LinState F)
      (pool pool' : LinPool F) :
    lin_update key before after pool pool' ->
    other <> key ->
    lin_lookup other other_state pool ->
    lin_lookup other other_state pool'.
  Proof.
    intros Hupdate Hother Hlookup.
    induction Hupdate; cbn in *.
    - destruct Hlookup as [Heq | Hin].
      + exfalso. apply Hother.
        apply (f_equal lin_key) in Heq.
        now do 2 rewrite lin_key_make_lin_entry in Heq.
      + right. exact Hin.
    - destruct Hlookup as [Heq | Hin].
      + left. exact Heq.
      + right. apply IHHupdate. exact Hin.
  Qed.

  Lemma lin_update_well_formed
      {F : RelaxedSig.t}
      (key : CallKey F)
      (before after : LinState F)
      (pool pool' : LinPool F) :
    lin_update key before after pool pool' ->
    lin_pool_well_formed pool ->
    lin_pool_well_formed pool'.
  Proof.
    intros Hupdate Hwf.
    unfold lin_pool_well_formed in *.
    erewrite <- lin_update_keys; eauto.
  Qed.

  Lemma lin_update_not_refl
      {F : RelaxedSig.t}
      (key : CallKey F)
      (before after : LinState F)
      (pool pool' : LinPool F) :
    before <> after ->
    lin_update key before after pool pool' ->
    pool <> pool'.
  Proof.
    intros Hphase Hupdate.
    induction Hupdate; intro Heq.
    - injection Heq as Hentry.
      exact (Hphase Hentry).
    - injection Heq as Htail.
      exact (IHHupdate Htail).
  Qed.

  Lemma invocation_ready_same_thread_pending
      {F : RelaxedSig.t}
      (t : tid)
      (older_h : RelaxedSig.handle F)
      (older_op op : Sig.op (RelaxedSig.effect F))
      (older : LinPool F) :
    invocation_ready t op
      (make_lin_entry (t, older_h) (ls_inv older_op) :: older) ->
    RelaxedSig.semi_independent F older_op op.
  Proof.
    intro Hready.
    inversion Hready as [| entry entries Hhead Htail]; subst.
    unfold older_entry_allows_invocation in Hhead.
    cbn in Hhead.
    destruct Hhead as [Hdifferent | Hindependent].
    - exfalso. apply Hdifferent. reflexivity.
    - exact Hindependent.
  Qed.

  Lemma lin_invocation_enabled_lookup
      {F : RelaxedSig.t}
      (t : tid)
      (h : RelaxedSig.handle F)
      (op : Sig.op (RelaxedSig.effect F))
      (pool : LinPool F) :
    lin_invocation_enabled t h op pool ->
    lin_lookup (t, h) (ls_inv op) pool.
  Proof.
    intro Henabled.
    induction Henabled; cbn; auto.
  Qed.

  Lemma lin_invoke_update_enabled
      {F : RelaxedSig.t}
      (t : tid)
      (h : RelaxedSig.handle F)
      (op : Sig.op (RelaxedSig.effect F))
      (pool pool' : LinPool F) :
    lin_invoke_update t h op pool pool' ->
    lin_invocation_enabled t h op pool.
  Proof.
    intro Hupdate.
    induction Hupdate.
    - apply lin_invocation_enabled_here. exact Hready.
    - apply lin_invocation_enabled_next; assumption.
  Qed.

  Lemma lin_invoke_update_is_update
      {F : RelaxedSig.t}
      (t : tid)
      (h : RelaxedSig.handle F)
      (op : Sig.op (RelaxedSig.effect F))
      (pool pool' : LinPool F) :
    lin_invoke_update t h op pool pool' ->
    lin_update (t, h) (ls_inv op) (ls_lini op) pool pool'.
  Proof.
    intro Hupdate.
    induction Hupdate.
    - apply lin_update_here.
    - apply lin_update_next; assumption.
  Qed.

  Lemma lin_invoke_update_keys
      {F : RelaxedSig.t}
      (t : tid)
      (h : RelaxedSig.handle F)
      (op : Sig.op (RelaxedSig.effect F))
      (pool pool' : LinPool F) :
    lin_invoke_update t h op pool pool' ->
    lin_domain pool = lin_domain pool'.
  Proof.
    intro Hupdate.
    eapply (@lin_update_keys F
      (t, h) (ls_inv op) (ls_lini op) pool pool').
    exact (lin_invoke_update_is_update t h op pool pool' Hupdate).
  Qed.

  Lemma lin_invoke_update_well_formed
      {F : RelaxedSig.t}
      (t : tid)
      (h : RelaxedSig.handle F)
      (op : Sig.op (RelaxedSig.effect F))
      (pool pool' : LinPool F) :
    lin_invoke_update t h op pool pool' ->
    lin_pool_well_formed pool ->
    lin_pool_well_formed pool'.
  Proof.
    intros Hupdate Hwf.
    eapply (@lin_update_well_formed F
      (t, h) (ls_inv op) (ls_lini op) pool pool').
    - exact (lin_invoke_update_is_update t h op pool pool' Hupdate).
    - exact Hwf.
  Qed.

  Lemma lin_invoke_update_not_refl
      {F : RelaxedSig.t}
      (t : tid)
      (h : RelaxedSig.handle F)
      (op : Sig.op (RelaxedSig.effect F))
      (pool pool' : LinPool F) :
    lin_invoke_update t h op pool pool' ->
    pool <> pool'.
  Proof.
    intro Hupdate.
    eapply (@lin_update_not_refl F
      (t, h) (ls_inv op) (ls_lini op) pool pool').
    - discriminate.
    - exact (lin_invoke_update_is_update t h op pool pool' Hupdate).
  Qed.

  Lemma lin_remove_source
      {F : RelaxedSig.t}
      (key : CallKey F)
      (state : LinState F)
      (pool pool' : LinPool F) :
    lin_remove key state pool pool' ->
    lin_lookup key state pool.
  Proof.
    intro Hremove.
    induction Hremove; cbn; auto.
  Qed.

  Lemma lin_remove_other_lookup
      {F : RelaxedSig.t}
      (key other : CallKey F)
      (state other_state : LinState F)
      (pool pool' : LinPool F) :
    lin_remove key state pool pool' ->
    other <> key ->
    lin_lookup other other_state pool ->
    lin_lookup other other_state pool'.
  Proof.
    intros Hremove Hother Hlookup.
    induction Hremove; cbn in *.
    - destruct Hlookup as [Heq | Hin].
      + exfalso. apply Hother.
        apply (f_equal lin_key) in Heq.
        now do 2 rewrite lin_key_make_lin_entry in Heq.
      + exact Hin.
    - destruct Hlookup as [Heq | Hin].
      + left. exact Heq.
      + right. apply IHHremove. exact Hin.
  Qed.

  Lemma lin_remove_domain_subset
      {F : RelaxedSig.t}
      (key : CallKey F)
      (state : LinState F)
      (pool pool' : LinPool F) :
    lin_remove key state pool pool' ->
    forall other,
      In other (lin_domain pool') -> In other (lin_domain pool).
  Proof.
    intro Hremove.
    induction Hremove; intros other Hin; cbn in *.
    - right. exact Hin.
    - destruct Hin as [Heq | Hin].
      + left. exact Heq.
      + right. eapply IHHremove; eauto.
  Qed.

  Lemma lin_remove_absent
      {F : RelaxedSig.t}
      (key : CallKey F)
      (state : LinState F)
      (pool pool' : LinPool F) :
    lin_remove key state pool pool' ->
    lin_pool_well_formed pool ->
    ~ In key (lin_domain pool').
  Proof.
    intros Hremove Hwf.
    destruct key as [t h].
    induction Hremove.
    - unfold lin_pool_well_formed, lin_domain in Hwf.
      cbn in Hwf. inversion Hwf; assumption.
    - unfold lin_pool_well_formed, lin_domain in Hwf.
      cbn in Hwf. inversion Hwf; subst.
      cbn. intros [Heq | Hin].
      + apply Hneq. exact Heq.
      + eapply IHHremove; eauto.
  Qed.

  Lemma lin_remove_well_formed
      {F : RelaxedSig.t}
      (key : CallKey F)
      (state : LinState F)
      (pool pool' : LinPool F) :
    lin_remove key state pool pool' ->
    lin_pool_well_formed pool ->
    lin_pool_well_formed pool'.
  Proof.
    intros Hremove Hwf.
    induction Hremove.
    - unfold lin_pool_well_formed, lin_domain in *.
      cbn in Hwf. inversion Hwf; assumption.
    - unfold lin_pool_well_formed, lin_domain in *.
      cbn in Hwf. inversion Hwf; subst.
      cbn. constructor.
      + intro Hin.
        apply H1.
        eapply lin_remove_domain_subset; eauto.
      + apply IHHremove. exact H2.
  Qed.

  (** ** Possibilities and abstract LTS steps *)

  Inductive Poss {F : RelaxedSig.t}
      (VF : RelaxedLTSSpec.LTS F) : Type :=
  | PossOk
      (state : RelaxedLTSSpec.State VF)
      (pool : LinPool F)
  | PossError.

  Arguments Poss {F} _.
  Arguments PossOk {F VF} _ _.
  Arguments PossError {F VF}.

  Definition poss_pool_option {F : RelaxedSig.t}
      {VF : RelaxedLTSSpec.LTS F}
      (p : Poss VF) : option (LinPool F) :=
    match p with
    | PossOk _ pool => Some pool
    | PossError => None
    end.

  Section PossibilitySemantics.
    Context {F : RelaxedSig.t}.
    Context (VF : RelaxedLTSSpec.LTS F).

    Inductive poss_step_at :
        CallKey F -> Poss VF -> Poss VF -> Prop :=
    | psa_inv t h op state state' pool pool'
        (Hlin : lin_invoke_update t h op pool pool')
        (Hlts : RelaxedLTSSpec.Step VF
          (Build_ThreadEvent t (InvEv h op)) state state') :
        poss_step_at (t, h)
          (PossOk state pool)
          (PossOk state' pool')

    | psa_ret t h op ret state state' pool pool'
        (Hlin : lin_update (t, h)
          (ls_lini op) (ls_linr op ret) pool pool')
        (Hlts : RelaxedLTSSpec.Step VF
          (Build_ThreadEvent t (ResEv h op ret)) state state') :
        poss_step_at (t, h)
          (PossOk state pool)
          (PossOk state' pool')

    | psa_inv_error t h op state pool
        (Hlin : lin_invocation_enabled t h op pool)
        (Herror : RelaxedLTSSpec.Error VF
          (Build_ThreadEvent t (InvEv h op)) state) :
        poss_step_at (t, h) (PossOk state pool) PossError

    | psa_ret_error t h op ret state pool
        (Hlin : lin_lookup (t, h) (ls_lini op) pool)
        (Herror : RelaxedLTSSpec.Error VF
          (Build_ThreadEvent t (ResEv h op ret)) state) :
        poss_step_at (t, h) (PossOk state pool) PossError.

    Definition poss_step (p p' : Poss VF) : Prop :=
      exists owner, poss_step_at owner p p'.

    Lemma ps_inv t h op state state' pool pool'
        (Hlin : lin_invoke_update t h op pool pool')
        (Hlts : RelaxedLTSSpec.Step VF
          (Build_ThreadEvent t (InvEv h op)) state state') :
      poss_step (PossOk state pool) (PossOk state' pool').
    Proof.
      exists (t, h). eapply psa_inv; eauto.
    Qed.

    Lemma ps_ret t h op ret state state' pool pool'
        (Hlin : lin_update (t, h)
          (ls_lini op) (ls_linr op ret) pool pool')
        (Hlts : RelaxedLTSSpec.Step VF
          (Build_ThreadEvent t (ResEv h op ret)) state state') :
      poss_step (PossOk state pool) (PossOk state' pool').
    Proof.
      exists (t, h). eapply psa_ret; eauto.
    Qed.

    Lemma ps_inv_error t h op state pool
        (Hlin : lin_invocation_enabled t h op pool)
        (Herror : RelaxedLTSSpec.Error VF
          (Build_ThreadEvent t (InvEv h op)) state) :
      poss_step (PossOk state pool) PossError.
    Proof.
      exists (t, h). eapply psa_inv_error; eauto.
    Qed.

    Lemma ps_ret_error t h op ret state pool
        (Hlin : lin_lookup (t, h) (ls_lini op) pool)
        (Herror : RelaxedLTSSpec.Error VF
          (Build_ThreadEvent t (ResEv h op ret)) state) :
      poss_step (PossOk state pool) PossError.
    Proof.
      exists (t, h). eapply psa_ret_error; eauto.
    Qed.

    Definition poss_steps :=
      clos_refl_trans (Poss VF) poss_step.

    Definition poss_steps_nonempty :=
      clos_trans (Poss VF) poss_step.

    Definition poss_steps_at (owner : CallKey F) :=
      clos_refl_trans (Poss VF) (poss_step_at owner).

    Definition poss_steps_at_nonempty (owner : CallKey F) :=
      clos_trans (Poss VF) (poss_step_at owner).

    (** The paper indexes simulation obligations by an active thread.  With
        explicit futures, one such thread may own several live handles, so
        its abstract transition nondeterministically selects any one of
        those handles. *)
    Definition poss_step_by_thread
        (t : tid) (p p' : Poss VF) : Prop :=
      exists h, poss_step_at (t, h) p p'.

    Definition poss_steps_by_thread (t : tid) :=
      clos_refl_trans (Poss VF) (poss_step_by_thread t).

    Definition poss_steps_by_thread_nonempty (t : tid) :=
      clos_trans (Poss VF) (poss_step_by_thread t).

    Lemma poss_step_at_is_step owner p p' :
      poss_step_at owner p p' -> poss_step p p'.
    Proof.
      intro Hstep. exists owner. exact Hstep.
    Qed.

    (** An owner step cannot be discharged by reflexivity: successful
        [TInvoke]/[TReturn] steps change the selected phase, while error
        steps change the outer possibility constructor. *)
    Lemma poss_step_at_not_refl owner p p' :
      poss_step_at owner p p' -> p <> p'.
    Proof.
      intro Hstep.
      destruct Hstep as
        [alpha h op state state' pool pool' Hlin Hlts
        | alpha h op ret state state' pool pool' Hlin Hlts
        | alpha h op state pool Hlin Herror
        | alpha h op ret state pool Hlin Herror];
        intro Heq;
        apply (f_equal poss_pool_option) in Heq; cbn in Heq.
      - injection Heq as Hpool.
        exact (lin_invoke_update_not_refl
          alpha h op pool pool' Hlin Hpool).
      - injection Heq as Hpool.
        eapply (@lin_update_not_refl F
          (alpha, h) (ls_lini op) (ls_linr op ret) pool pool').
        + discriminate.
        + exact Hlin.
        + exact Hpool.
      - discriminate.
      - discriminate.
    Qed.

    Lemma poss_steps_at_is_steps owner p p' :
      poss_steps_at owner p p' -> poss_steps p p'.
    Proof.
      intro Hsteps.
      induction Hsteps.
      - apply rt_step. now apply poss_step_at_is_step with (owner := owner).
      - apply rt_refl.
      - eapply rt_trans; eauto.
    Qed.

    Lemma poss_steps_at_is_thread_steps t h p p' :
      poss_steps_at (t, h) p p' ->
      poss_steps_by_thread t p p'.
    Proof.
      intro Hsteps.
      induction Hsteps.
      - apply rt_step. exists h. exact H.
      - apply rt_refl.
      - eapply rt_trans; eauto.
    Qed.

    Lemma poss_steps_by_thread_is_steps t p p' :
      poss_steps_by_thread t p p' -> poss_steps p p'.
    Proof.
      intro Hsteps.
      induction Hsteps.
      - apply rt_step. destruct H as [h Hstep].
        now apply poss_step_at_is_step with (owner := (t, h)).
      - apply rt_refl.
      - eapply rt_trans; eauto.
    Qed.


    (** Abstract linearization steps preserve the set and order of live
        call keys.  Reaching [PossError] is permitted, but there is no path
        from [PossError] back to a successful possibility. *)
    Definition poss_domain_progress (p p' : Poss VF) : Prop :=
      match p, p' with
      | PossOk _ pool, PossOk _ pool' =>
          lin_domain pool = lin_domain pool'
      | PossOk _ _, PossError => True
      | PossError, PossOk _ _ => False
      | PossError, PossError => True
      end.

    Lemma poss_step_domain_progress p p' :
      poss_step p p' -> poss_domain_progress p p'.
    Proof.
      intros [owner Hstep].
      destruct Hstep; cbn; try exact I.
      - eapply lin_invoke_update_keys; eauto.
      - eapply lin_update_keys; eauto.
    Qed.

    Lemma poss_domain_progress_refl p :
      poss_domain_progress p p.
    Proof.
      destruct p; cbn; auto.
    Qed.

    Lemma poss_domain_progress_trans p1 p2 p3 :
      poss_domain_progress p1 p2 ->
      poss_domain_progress p2 p3 ->
      poss_domain_progress p1 p3.
    Proof.
      destruct p1, p2, p3; cbn; intros; try contradiction; auto.
      etransitivity; eauto.
    Qed.

    Lemma poss_steps_domain_progress p p' :
      poss_steps p p' -> poss_domain_progress p p'.
    Proof.
      unfold poss_steps.
      apply clos_refl_trans_ind.
      - apply poss_step_domain_progress.
      - apply poss_domain_progress_refl.
      - intros. eapply poss_domain_progress_trans; eauto.
    Qed.

    Lemma poss_steps_from_error p :
      poss_steps PossError p -> p = PossError.
    Proof.
      intro Hsteps.
      pose proof (poss_steps_domain_progress _ _ Hsteps) as Hprogress.
      destruct p; cbn in Hprogress; [contradiction | reflexivity].
    Qed.

    (** Overlay events change only the phase pool.  The abstract LTS itself
        moves later through [poss_step]. *)
    Inductive poss_invoke
        (t : tid)
        (h : RelaxedSig.handle F)
        (op : Sig.op (RelaxedSig.effect F)) :
        Poss VF -> Poss VF -> Prop :=
    | poss_invoke_ok state pool pool'
        (Hinsert : lin_insert (t, h) (ls_inv op) pool pool') :
        poss_invoke t h op
          (PossOk state pool) (PossOk state pool').

    Inductive poss_return
        (t : tid)
        (h : RelaxedSig.handle F)
        (op : Sig.op (RelaxedSig.effect F))
        (ret : Sig.ar op) :
        Poss VF -> Poss VF -> Prop :=
    | poss_return_ok state pool pool'
        (Hremove : lin_remove (t, h) (ls_linr op ret) pool pool') :
        poss_return t h op ret
          (PossOk state pool) (PossOk state pool').

    (** [SInvoke + SReturn] from the simulation definition.  Unlike
        [poss_step], these transitions only update the overlay phase pool;
        they do not execute the abstract specification LTS. *)
    Inductive poss_overlay_step : Poss VF -> Poss VF -> Prop :=
    | poss_overlay_invoke t h op p p'
        (Hinvoke : poss_invoke t h op p p') :
        poss_overlay_step p p'
    | poss_overlay_return t h op ret p p'
        (Hreturn : poss_return t h op ret p p') :
        poss_overlay_step p p'.

    Definition poss_overlay_steps :=
      clos_refl_trans (Poss VF) poss_overlay_step.

    Definition poss_overlay_step_by_thread
        (t : tid) (p p' : Poss VF) : Prop :=
      (exists h op, poss_invoke t h op p p') \/
      (exists h op ret, poss_return t h op ret p p').

    Definition poss_overlay_steps_by_thread (t : tid) :=
      clos_refl_trans (Poss VF) (poss_overlay_step_by_thread t).

    Definition poss_return_after_steps
        (t : tid)
        (h : RelaxedSig.handle F)
        (op : Sig.op (RelaxedSig.effect F))
        (ret : Sig.ar op)
        (p p' : Poss VF) : Prop :=
      exists middle,
        poss_steps_at (t, h) p middle /\
        poss_return t h op ret middle p'.


    Lemma poss_step_ok_domain state pool state' pool' :
      poss_step (PossOk state pool) (PossOk state' pool') ->
      lin_domain pool = lin_domain pool'.
    Proof.
      intros [owner Hstep].
      inversion Hstep; subst.
      - eapply lin_invoke_update_keys; eauto.
      - eapply lin_update_keys; eauto.
    Qed.

    Lemma poss_step_ok_well_formed state pool state' pool' :
      poss_step (PossOk state pool) (PossOk state' pool') ->
      lin_pool_well_formed pool ->
      lin_pool_well_formed pool'.
    Proof.
      intros [owner Hstep] Hwf.
      inversion Hstep; subst.
      - eapply lin_invoke_update_well_formed; eauto.
      - eapply lin_update_well_formed; eauto.
    Qed.

    Lemma poss_steps_ok_domain state pool state' pool' :
      poss_steps
        (PossOk state pool) (PossOk state' pool') ->
      lin_domain pool = lin_domain pool'.
    Proof.
      intro Hsteps.
      exact (poss_steps_domain_progress _ _ Hsteps).
    Qed.

    Lemma poss_steps_ok_well_formed state pool state' pool' :
      poss_steps
        (PossOk state pool) (PossOk state' pool') ->
      lin_pool_well_formed pool ->
      lin_pool_well_formed pool'.
    Proof.
      intros Hsteps Hwf.
      unfold lin_pool_well_formed in *.
      erewrite <- poss_steps_ok_domain; eauto.
    Qed.

    Lemma poss_invoke_well_formed t h op state pool pool' :
      poss_invoke t h op
        (PossOk state pool) (PossOk state pool') ->
      lin_pool_well_formed pool ->
      lin_pool_well_formed pool'.
    Proof.
      intros Hinvoke Hwf.
      inversion Hinvoke; subst.
      eapply lin_insert_well_formed; eauto.
    Qed.

    Lemma poss_return_well_formed t h op ret state pool pool' :
      poss_return t h op ret
        (PossOk state pool) (PossOk state pool') ->
      lin_pool_well_formed pool ->
      lin_pool_well_formed pool'.
    Proof.
      intros Hreturn Hwf.
      inversion Hreturn; subst.
      eapply lin_remove_well_formed; eauto.
    Qed.

  End PossibilitySemantics.

End RelaxedPossibility.
