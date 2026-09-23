(** Litmus tests for the handle-aware relaxed possibility semantics. *)

Require Import Coq.Lists.List.
Require Import Coq.PArith.PArith.
Require Import Coq.Relations.Relation_Operators.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedPossibility.

Import ListNotations.


Module RelaxedMemoryLitmusExamples.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedPossibility.

  Inductive Location : Type :=
  | Data
  | Flag.

  Inductive MemoryOp : Type :=
  | MRead (location : Location)
  | MWrite (location : Location) (value : bool).

  Definition memory_arity (op : MemoryOp) : Type :=
    match op with
    | MRead _ => bool
    | MWrite _ _ => unit
    end.

  Canonical Structure MemoryEffect : Sig.t :=
    {|
      Sig.op := MemoryOp;
      Sig.ar := memory_arity;
    |}.

  Definition op_location (op : MemoryOp) : Location :=
    match op with
    | MRead location => location
    | MWrite location _ => location
    end.

  Definition memory_signature
      (independent : MemoryOp -> MemoryOp -> Prop)
      (operation_mode : MemoryOp -> FenceMode) : RelaxedSig.t :=
    {|
      RelaxedSig.effect := MemoryEffect;
      RelaxedSig.handle := nat;
      RelaxedSig.semi_independent := independent;
      RelaxedSig.mode := operation_mode;
    |}.

  (** Coherence drops program-order edges between different locations. *)
  Definition coh_independent (older later : MemoryOp) : Prop :=
    op_location older <> op_location later.

  Definition coh_mode (_ : MemoryOp) : FenceMode := Local.

  Definition CohSig : RelaxedSig.t :=
    memory_signature coh_independent coh_mode.

  Lemma CohSig_well_formed : RelaxedSig.well_formed CohSig.
  Proof.
    constructor.
    - intros op Hsame. apply Hsame. reflexivity.
    - intros older later Hind. exact I.
    - intros older later Hind. exact I.
  Qed.

  (** For message passing, a write to [Flag] is release and a read from
      [Flag] is acquire.  The other operations remain local. *)
  Definition mp_mode (op : MemoryOp) : FenceMode :=
    match op with
    | MWrite Flag _ => LFence
    | MRead Flag => RFence
    | _ => Local
    end.

  Definition mp_independent (older later : MemoryOp) : Prop :=
    op_location older <> op_location later /\
    mp_mode older ≤f LFence /\
    mp_mode later ≤f RFence.

  Definition MPSig : RelaxedSig.t :=
    memory_signature mp_independent mp_mode.

  Lemma MPSig_well_formed : RelaxedSig.well_formed MPSig.
  Proof.
    constructor.
    - intros op [Hlocation _]. apply Hlocation. reflexivity.
    - intros older later [_ [Hleft _]]. exact Hleft.
    - intros older later [_ [_ Hright]]. exact Hright.
  Qed.

  Record MemoryState : Type := {
    data_value : bool;
    flag_value : bool;
  }.

  Definition read_location
      (location : Location) (state : MemoryState) : bool :=
    match location with
    | Data => data_value state
    | Flag => flag_value state
    end.

  Definition write_location
      (location : Location) (value : bool)
      (state : MemoryState) : MemoryState :=
    match location with
    | Data => Build_MemoryState value (flag_value state)
    | Flag => Build_MemoryState (data_value state) value
    end.

  Definition memory_step
      (independent : MemoryOp -> MemoryOp -> Prop)
      (operation_mode : MemoryOp -> FenceMode) :
      ThreadEvent (memory_signature independent operation_mode) ->
      MemoryState -> MemoryState -> Prop :=
    fun event source target =>
      match te_ev _ event with
      | InvEv _ operation =>
          match operation with
          | MRead _ => target = source
          | MWrite location value =>
              target = write_location location value source
          end
      | ResEv _ operation returned =>
          match operation as selected
                return memory_arity selected -> Prop with
          | MRead location => fun observed =>
              target = source /\
              observed = read_location location source
          | MWrite _ _ => fun _ => target = source
          end returned
      end.

  Definition MemoryLTS
      (independent : MemoryOp -> MemoryOp -> Prop)
      (operation_mode : MemoryOp -> FenceMode) :
      RelaxedLTSSpec.LTS
        (memory_signature independent operation_mode) :=
    {|
      RelaxedLTSSpec.State := MemoryState;
      RelaxedLTSSpec.Step := memory_step independent operation_mode;
      RelaxedLTSSpec.Error := fun _ _ => False;
    |}.

  Definition CohLTS : RelaxedLTSSpec.LTS CohSig :=
    MemoryLTS coh_independent coh_mode.

  Definition MPLTS : RelaxedLTSSpec.LTS MPSig :=
    MemoryLTS mp_independent mp_mode.

  Definition memory_zero : MemoryState :=
    Build_MemoryState false false.

  Definition memory_data_one : MemoryState :=
    Build_MemoryState true false.

  Definition memory_one_one : MemoryState :=
    Build_MemoryState true true.

  Definition thread_one : tid := 1%positive.
  Definition thread_two : tid := 2%positive.

  (** ** Load buffering under coherence

      Program order is:

      - thread one: read Flag; write Data := 1
      - thread two: read Data; write Flag := 1

      Pools are newest-first, so all four invocations appear below in the
      reverse of their concrete issue order. *)

  Definition lb_t1_read : CallKey CohSig := (thread_one, 0).
  Definition lb_t1_write : CallKey CohSig := (thread_one, 1).
  Definition lb_t2_read : CallKey CohSig := (thread_two, 0).
  Definition lb_t2_write : CallKey CohSig := (thread_two, 1).

  Definition lb_pool0 : LinPool CohSig :=
    [ make_lin_entry lb_t2_write
        (@ls_inv CohSig (MWrite Flag true));
      make_lin_entry lb_t2_read
        (@ls_inv CohSig (MRead Data));
      make_lin_entry lb_t1_write
        (@ls_inv CohSig (MWrite Data true));
      make_lin_entry lb_t1_read
        (@ls_inv CohSig (MRead Flag)) ].

  Definition lb_pool1 : LinPool CohSig :=
    [ make_lin_entry lb_t2_write
        (@ls_inv CohSig (MWrite Flag true));
      make_lin_entry lb_t2_read
        (@ls_inv CohSig (MRead Data));
      make_lin_entry lb_t1_write
        (@ls_lini CohSig (MWrite Data true));
      make_lin_entry lb_t1_read
        (@ls_inv CohSig (MRead Flag)) ].

  Definition lb_pool2 : LinPool CohSig :=
    [ make_lin_entry lb_t2_write
        (@ls_lini CohSig (MWrite Flag true));
      make_lin_entry lb_t2_read
        (@ls_inv CohSig (MRead Data));
      make_lin_entry lb_t1_write
        (@ls_lini CohSig (MWrite Data true));
      make_lin_entry lb_t1_read
        (@ls_inv CohSig (MRead Flag)) ].

  Definition lb_pool3 : LinPool CohSig :=
    [ make_lin_entry lb_t2_write
        (@ls_lini CohSig (MWrite Flag true));
      make_lin_entry lb_t2_read
        (@ls_inv CohSig (MRead Data));
      make_lin_entry lb_t1_write
        (@ls_lini CohSig (MWrite Data true));
      make_lin_entry lb_t1_read
        (@ls_lini CohSig (MRead Flag)) ].

  Definition lb_pool4 : LinPool CohSig :=
    [ make_lin_entry lb_t2_write
        (@ls_lini CohSig (MWrite Flag true));
      make_lin_entry lb_t2_read
        (@ls_inv CohSig (MRead Data));
      make_lin_entry lb_t1_write
        (@ls_lini CohSig (MWrite Data true));
      make_lin_entry lb_t1_read
        (@ls_linr CohSig (MRead Flag) true) ].

  Definition lb_pool5 : LinPool CohSig :=
    [ make_lin_entry lb_t2_write
        (@ls_lini CohSig (MWrite Flag true));
      make_lin_entry lb_t2_read
        (@ls_lini CohSig (MRead Data));
      make_lin_entry lb_t1_write
        (@ls_lini CohSig (MWrite Data true));
      make_lin_entry lb_t1_read
        (@ls_linr CohSig (MRead Flag) true) ].

  Definition lb_pool6 : LinPool CohSig :=
    [ make_lin_entry lb_t2_write
        (@ls_lini CohSig (MWrite Flag true));
      make_lin_entry lb_t2_read
        (@ls_linr CohSig (MRead Data) true);
      make_lin_entry lb_t1_write
        (@ls_lini CohSig (MWrite Data true));
      make_lin_entry lb_t1_read
        (@ls_linr CohSig (MRead Flag) true) ].

  Lemma lb_linearize_thread_one_write :
    poss_step CohLTS
      (@PossOk CohSig CohLTS memory_zero lb_pool0)
      (@PossOk CohSig CohLTS memory_data_one lb_pool1).
  Proof.
    eapply (@ps_inv CohSig CohLTS
      thread_one 1 (MWrite Data true)).
    - unfold lb_pool0, lb_pool1,
        lb_t1_write, lb_t1_read, lb_t2_write, lb_t2_read,
        thread_one, thread_two.
      eapply lin_invoke_update_next;
        [rewrite lin_key_make_lin_entry; discriminate |].
      eapply lin_invoke_update_next;
        [rewrite lin_key_make_lin_entry; discriminate |].
      apply lin_invoke_update_here.
      constructor.
      + cbn. right. discriminate.
      + constructor.
    - reflexivity.
  Qed.

  Lemma lb_linearize_thread_two_write :
    poss_step CohLTS
      (@PossOk CohSig CohLTS memory_data_one lb_pool1)
      (@PossOk CohSig CohLTS memory_one_one lb_pool2).
  Proof.
    eapply (@ps_inv CohSig CohLTS
      thread_two 1 (MWrite Flag true)).
    - unfold lb_pool1, lb_pool2,
        lb_t1_write, lb_t1_read, lb_t2_write, lb_t2_read,
        thread_one, thread_two.
      apply lin_invoke_update_here.
      constructor.
      + cbn. right. discriminate.
      + constructor.
        * cbn. left. discriminate.
        * constructor.
          -- cbn. left. discriminate.
          -- constructor.
    - reflexivity.
  Qed.

  Lemma lb_linearize_thread_one_read :
    poss_step CohLTS
      (@PossOk CohSig CohLTS memory_one_one lb_pool2)
      (@PossOk CohSig CohLTS memory_one_one lb_pool3).
  Proof.
    eapply (@ps_inv CohSig CohLTS
      thread_one 0 (MRead Flag)).
    - unfold lb_pool2, lb_pool3,
        lb_t1_write, lb_t1_read, lb_t2_write, lb_t2_read,
        thread_one, thread_two.
      eapply lin_invoke_update_next;
        [rewrite lin_key_make_lin_entry; discriminate |].
      eapply lin_invoke_update_next;
        [rewrite lin_key_make_lin_entry; discriminate |].
      eapply lin_invoke_update_next;
        [rewrite lin_key_make_lin_entry; discriminate |].
      apply lin_invoke_update_here. constructor.
    - reflexivity.
  Qed.

  Lemma lb_return_thread_one_read_one :
    poss_step CohLTS
      (@PossOk CohSig CohLTS memory_one_one lb_pool3)
      (@PossOk CohSig CohLTS memory_one_one lb_pool4).
  Proof.
    eapply (@ps_ret CohSig CohLTS
      thread_one 0 (MRead Flag) true).
    - unfold lb_pool3, lb_pool4,
        lb_t1_write, lb_t1_read, lb_t2_write, lb_t2_read,
        thread_one, thread_two.
      eapply lin_update_next;
        [rewrite lin_key_make_lin_entry; discriminate |].
      eapply lin_update_next;
        [rewrite lin_key_make_lin_entry; discriminate |].
      eapply lin_update_next;
        [rewrite lin_key_make_lin_entry; discriminate |].
      apply lin_update_here.
    - split; reflexivity.
  Qed.

  Lemma lb_linearize_thread_two_read :
    poss_step CohLTS
      (@PossOk CohSig CohLTS memory_one_one lb_pool4)
      (@PossOk CohSig CohLTS memory_one_one lb_pool5).
  Proof.
    eapply (@ps_inv CohSig CohLTS
      thread_two 0 (MRead Data)).
    - unfold lb_pool4, lb_pool5,
        lb_t1_write, lb_t1_read, lb_t2_write, lb_t2_read,
        thread_one, thread_two.
      eapply lin_invoke_update_next;
        [rewrite lin_key_make_lin_entry; discriminate |].
      apply lin_invoke_update_here.
      constructor.
      + cbn. left. discriminate.
      + constructor.
        * cbn. left. discriminate.
        * constructor.
    - reflexivity.
  Qed.

  Lemma lb_return_thread_two_read_one :
    poss_step CohLTS
      (@PossOk CohSig CohLTS memory_one_one lb_pool5)
      (@PossOk CohSig CohLTS memory_one_one lb_pool6).
  Proof.
    eapply (@ps_ret CohSig CohLTS
      thread_two 0 (MRead Data) true).
    - unfold lb_pool5, lb_pool6,
        lb_t1_write, lb_t1_read, lb_t2_write, lb_t2_read,
        thread_one, thread_two.
      eapply lin_update_next;
        [rewrite lin_key_make_lin_entry; discriminate |].
      apply lin_update_here.
    - split; reflexivity.
  Qed.

  (** Both reads return one even though each read was invoked before its
      same-thread write. *)
  Theorem load_buffering_one_one_is_specified :
    poss_steps CohLTS
      (@PossOk CohSig CohLTS memory_zero lb_pool0)
      (@PossOk CohSig CohLTS memory_one_one lb_pool6).
  Proof.
    eapply rt_trans.
    - apply rt_step. exact lb_linearize_thread_one_write.
    - eapply rt_trans.
      + apply rt_step. exact lb_linearize_thread_two_write.
      + eapply rt_trans.
        * apply rt_step. exact lb_linearize_thread_one_read.
        * eapply rt_trans.
          -- apply rt_step. exact lb_return_thread_one_read_one.
          -- eapply rt_trans.
             ++ apply rt_step. exact lb_linearize_thread_two_read.
             ++ apply rt_step. exact lb_return_thread_two_read_one.
  Qed.

  (** ** Release/acquire message passing *)

  Definition mp_writer_data : CallKey MPSig := (thread_one, 0).
  Definition mp_writer_flag : CallKey MPSig := (thread_one, 1).
  Definition mp_reader_flag : CallKey MPSig := (thread_two, 0).
  Definition mp_reader_data : CallKey MPSig := (thread_two, 1).

  Definition mp_writer_pending : LinPool MPSig :=
    [ make_lin_entry mp_writer_flag
        (@ls_inv MPSig (MWrite Flag true));
      make_lin_entry mp_writer_data
        (@ls_inv MPSig (MWrite Data true)) ].

  Definition mp_reader_pending : LinPool MPSig :=
    [ make_lin_entry mp_reader_data
        (@ls_inv MPSig (MRead Data));
      make_lin_entry mp_reader_flag
        (@ls_inv MPSig (MRead Flag)) ].

  (** Release prevents the Flag write from overtaking the older Data
      write in the writer thread. *)
  Lemma release_flag_cannot_overtake_data :
    ~ exists pool' : LinPool MPSig,
        @lin_invoke_update MPSig thread_one 1 (MWrite Flag true)
          mp_writer_pending pool'.
  Proof.
    intros [pool' Hupdate].
    pose proof (@lin_invoke_update_enabled MPSig
      thread_one 1 (MWrite Flag true)
      mp_writer_pending pool' Hupdate) as Henabled.
    inversion Henabled as
      [older Hready | entry pool Hneq Hnext]; subst.
    - pose proof
        (@invocation_ready_same_thread_pending MPSig
          thread_one 0 (MWrite Data true) (MWrite Flag true)
          [] Hready) as Hindependent.
      cbn in Hindependent.
      destruct Hindependent as [_ [_ Himpossible]].
      exact Himpossible.
    - apply Hneq. reflexivity.
  Qed.

  (** Acquire prevents the later Data read from overtaking the older Flag
      read in the reader thread. *)
  Lemma data_read_cannot_overtake_acquire_flag :
    ~ exists pool' : LinPool MPSig,
        @lin_invoke_update MPSig thread_two 1 (MRead Data)
          mp_reader_pending pool'.
  Proof.
    intros [pool' Hupdate].
    pose proof (@lin_invoke_update_enabled MPSig
      thread_two 1 (MRead Data)
      mp_reader_pending pool' Hupdate) as Henabled.
    inversion Henabled as
      [older Hready | entry pool Hneq Hnext]; subst.
    - pose proof
        (@invocation_ready_same_thread_pending MPSig
          thread_two 0 (MRead Flag) (MRead Data)
          [] Hready) as Hindependent.
      cbn in Hindependent.
      destruct Hindependent as [_ [Himpossible _]].
      exact Himpossible.
    - apply Hneq. reflexivity.
  Qed.

  Definition mp_event
      (t : tid) (event : Event MPSig) : ThreadEvent MPSig :=
    Build_ThreadEvent t event.

  (** Once the two fence-preserved orders are respected, the sequential
      cell specification cannot return Flag=1 followed by stale Data=0. *)
  Lemma ordered_message_passing_cannot_read_stale_data :
    ~ exists state1 state2 state3 state4 state5 state6,
        RelaxedLTSSpec.Step MPLTS
          (mp_event thread_one (@InvEv MPSig 0 (MWrite Data true)))
          memory_zero state1 /\
        RelaxedLTSSpec.Step MPLTS
          (mp_event thread_one (@InvEv MPSig 1 (MWrite Flag true)))
          state1 state2 /\
        RelaxedLTSSpec.Step MPLTS
          (mp_event thread_two (@InvEv MPSig 0 (MRead Flag)))
          state2 state3 /\
        RelaxedLTSSpec.Step MPLTS
          (mp_event thread_two (@ResEv MPSig 0 (MRead Flag) true))
          state3 state4 /\
        RelaxedLTSSpec.Step MPLTS
          (mp_event thread_two (@InvEv MPSig 1 (MRead Data)))
          state4 state5 /\
        RelaxedLTSSpec.Step MPLTS
          (mp_event thread_two (@ResEv MPSig 1 (MRead Data) false))
          state5 state6.
  Proof.
    intros [state1 [state2 [state3 [state4 [state5 [state6
      [Hdata [Hflag [Hreadflag [Hretflag [Hreaddata Hretdata]]]]]]]]]]].
    unfold RelaxedLTSSpec.Step, MPLTS, MemoryLTS,
      memory_step, mp_event in
      Hdata, Hflag, Hreadflag, Hretflag, Hreaddata, Hretdata.
    cbn [RelaxedLTSSpec.te_ev memory_zero
      write_location read_location] in *.
    destruct Hretflag as [Hretflag_state Hflag_value].
    destruct Hretdata as [Hretdata_state Hdata_value].
    subst.
    cbn [data_value memory_zero write_location read_location]
      in Hdata_value.
    discriminate Hdata_value.
  Qed.

  Theorem release_acquire_message_passing_is_disallowed :
    (~ exists pool' : LinPool MPSig,
        @lin_invoke_update MPSig thread_one 1 (MWrite Flag true)
          mp_writer_pending pool') /\
    (~ exists pool' : LinPool MPSig,
        @lin_invoke_update MPSig thread_two 1 (MRead Data)
          mp_reader_pending pool') /\
    (~ exists state1 state2 state3 state4 state5 state6,
        RelaxedLTSSpec.Step MPLTS
          (mp_event thread_one (@InvEv MPSig 0 (MWrite Data true)))
          memory_zero state1 /\
        RelaxedLTSSpec.Step MPLTS
          (mp_event thread_one (@InvEv MPSig 1 (MWrite Flag true)))
          state1 state2 /\
        RelaxedLTSSpec.Step MPLTS
          (mp_event thread_two (@InvEv MPSig 0 (MRead Flag)))
          state2 state3 /\
        RelaxedLTSSpec.Step MPLTS
          (mp_event thread_two (@ResEv MPSig 0 (MRead Flag) true))
          state3 state4 /\
        RelaxedLTSSpec.Step MPLTS
          (mp_event thread_two (@InvEv MPSig 1 (MRead Data)))
          state4 state5 /\
        RelaxedLTSSpec.Step MPLTS
          (mp_event thread_two (@ResEv MPSig 1 (MRead Data) false))
          state5 state6).
  Proof.
    repeat split.
    - exact release_flag_cannot_overtake_data.
    - exact data_read_cannot_overtake_acquire_flag.
    - exact ordered_message_passing_cannot_read_stale_data.
  Qed.

  (** If the Data read is issued without waiting for the Flag response,
      keeping both invocation orders is not enough: Data may return zero
      before the writes, while Flag returns one afterwards. *)
  Example no_wait_allows_the_bad_response_order :
    exists state1 state2 state3 state4 state5 state6,
      RelaxedLTSSpec.Step MPLTS
        (mp_event thread_two (@InvEv MPSig 0 (MRead Flag)))
        memory_zero state1 /\
      RelaxedLTSSpec.Step MPLTS
        (mp_event thread_two (@InvEv MPSig 1 (MRead Data)))
        state1 state2 /\
      RelaxedLTSSpec.Step MPLTS
        (mp_event thread_two (@ResEv MPSig 1 (MRead Data) false))
        state2 state3 /\
      RelaxedLTSSpec.Step MPLTS
        (mp_event thread_one (@InvEv MPSig 0 (MWrite Data true)))
        state3 state4 /\
      RelaxedLTSSpec.Step MPLTS
        (mp_event thread_one (@InvEv MPSig 1 (MWrite Flag true)))
        state4 state5 /\
      RelaxedLTSSpec.Step MPLTS
        (mp_event thread_two (@ResEv MPSig 0 (MRead Flag) true))
        state5 state6.
  Proof.
    exists memory_zero, memory_zero, memory_zero,
      memory_data_one, memory_one_one, memory_one_one.
    repeat split; reflexivity.
  Qed.

  (** ** One combined possibility theorem

      The reader's Data invocation is inserted only after [wait] has
      observed the Flag response.  This is the first possibility in which
      that invocation can exist in the message-passing program. *)

  Definition mp_before_data_pool : LinPool MPSig :=
    [ make_lin_entry mp_reader_flag
        (@ls_linr MPSig (MRead Flag) true);
      make_lin_entry mp_writer_flag
        (@ls_lini MPSig (MWrite Flag true));
      make_lin_entry mp_writer_data
        (@ls_lini MPSig (MWrite Data true)) ].

  Definition mp_wait_boundary_pool : LinPool MPSig :=
    [ make_lin_entry mp_reader_data
        (@ls_inv MPSig (MRead Data));
      make_lin_entry mp_reader_flag
        (@ls_linr MPSig (MRead Flag) true);
      make_lin_entry mp_writer_flag
        (@ls_lini MPSig (MWrite Flag true));
      make_lin_entry mp_writer_data
        (@ls_lini MPSig (MWrite Data true)) ].

  Definition mp_flag_one_data_zero_pool : LinPool MPSig :=
    [ make_lin_entry mp_reader_data
        (@ls_linr MPSig (MRead Data) false);
      make_lin_entry mp_reader_flag
        (@ls_linr MPSig (MRead Flag) true);
      make_lin_entry mp_writer_flag
        (@ls_lini MPSig (MWrite Flag true));
      make_lin_entry mp_writer_data
        (@ls_lini MPSig (MWrite Data true)) ].

  Definition mp_before_data_poss : Poss MPLTS :=
    @PossOk MPSig MPLTS memory_one_one mp_before_data_pool.

  Definition mp_wait_boundary_poss : Poss MPLTS :=
    @PossOk MPSig MPLTS memory_one_one mp_wait_boundary_pool.

  Definition mp_flag_one_data_zero_poss : Poss MPLTS :=
    @PossOk MPSig MPLTS memory_one_one mp_flag_one_data_zero_pool.

  Lemma wait_boundary_inserts_data_after_flag_response :
    poss_invoke MPLTS thread_two 1 (MRead Data)
      mp_before_data_poss mp_wait_boundary_poss.
  Proof.
    apply poss_invoke_ok.
    apply lin_insert_fresh.
    unfold lin_fresh, lin_domain, mp_before_data_poss,
      mp_wait_boundary_poss, mp_before_data_pool,
      mp_wait_boundary_pool, mp_reader_data, mp_reader_flag,
      mp_writer_flag, mp_writer_data, thread_one, thread_two.
    cbn. intros [Heq | [Heq | [Heq | Hnone]]];
      discriminate || contradiction.
  Qed.

  Definition mp_operation_safe (operation : MemoryOp) : Prop :=
    match operation with
    | MWrite Data false => False
    | _ => True
    end.

  Definition mp_response_safe
      (operation : MemoryOp) : memory_arity operation -> Prop :=
    match operation with
    | MRead Data => fun returned => returned = true
    | _ => fun _ => True
    end.

  Definition mp_lin_state_safe (state : LinState MPSig) : Prop :=
    match state with
    | ls_inv operation => mp_operation_safe operation
    | ls_lini operation => mp_operation_safe operation
    | ls_linr operation returned =>
        mp_operation_safe operation /\
        mp_response_safe operation returned
    end.

  Definition mp_entry_safe (entry : LinEntry MPSig) : Prop :=
    mp_lin_state_safe (lin_state MPSig entry).

  Definition mp_pool_safe (pool : LinPool MPSig) : Prop :=
    Forall mp_entry_safe pool.

  Definition mp_poss_safe (possibility : Poss MPLTS) : Prop :=
    match possibility with
    | PossOk state pool =>
        data_value state = true /\ mp_pool_safe pool
    | PossError => False
    end.

  Lemma mp_safe_invocation_selected t h operation pool pool' :
    @lin_invoke_update MPSig t h operation pool pool' ->
    mp_pool_safe pool ->
    mp_operation_safe operation.
  Proof.
    intros Hupdate Hsafe.
    induction Hupdate.
    - inversion Hsafe as [| safe_head safe_tail Hhead Htail]; subst.
      exact Hhead.
    - inversion Hsafe as [| safe_head safe_tail Hhead Htail]; subst.
      apply IHHupdate. exact Htail.
  Qed.

  Lemma mp_safe_invocation_update t h operation pool pool' :
    @lin_invoke_update MPSig t h operation pool pool' ->
    mp_pool_safe pool ->
    mp_pool_safe pool'.
  Proof.
    intros Hupdate Hsafe.
    induction Hupdate.
    - inversion Hsafe as [| safe_head safe_tail Hhead Htail]; subst.
      constructor; assumption.
    - inversion Hsafe as [| safe_head safe_tail Hhead Htail]; subst.
      constructor; [exact Hhead |].
      apply IHHupdate. exact Htail.
  Qed.

  Lemma mp_safe_return_selected t h operation returned pool pool' :
    @lin_update MPSig (t, h)
      (ls_lini operation) (ls_linr operation returned) pool pool' ->
    mp_pool_safe pool ->
    mp_operation_safe operation.
  Proof.
    intros Hupdate Hsafe.
    induction Hupdate.
    - inversion Hsafe as [| safe_head safe_tail Hhead Htail]; subst.
      exact Hhead.
    - inversion Hsafe as [| safe_head safe_tail Hhead Htail]; subst.
      apply IHHupdate. exact Htail.
  Qed.

  Lemma mp_safe_return_update t h operation returned pool pool' :
    @lin_update MPSig (t, h)
      (ls_lini operation) (ls_linr operation returned) pool pool' ->
    mp_pool_safe pool ->
    mp_response_safe operation returned ->
    mp_pool_safe pool'.
  Proof.
    intros Hupdate Hsafe Hresponse.
    induction Hupdate.
    - inversion Hsafe as [| safe_head safe_tail Hhead Htail]; subst.
      constructor.
      + split; assumption.
      + exact Htail.
    - inversion Hsafe as [| safe_head safe_tail Hhead Htail]; subst.
      constructor; [exact Hhead |].
      apply IHHupdate. exact Htail.
  Qed.

  Lemma mp_invoke_preserves_data_true t h operation source target :
    RelaxedLTSSpec.Step MPLTS
      (mp_event t (@InvEv MPSig h operation)) source target ->
    mp_operation_safe operation ->
    data_value source = true ->
    data_value target = true.
  Proof.
    intros Hstep Hsafe Hdata.
    unfold RelaxedLTSSpec.Step, MPLTS, MemoryLTS,
      memory_step, mp_event in Hstep.
    cbn [RelaxedLTSSpec.te_ev] in Hstep.
    destruct operation as [location | location value].
    - subst. exact Hdata.
    - destruct location, value;
        cbn [mp_operation_safe write_location data_value] in *;
        subst; auto; contradiction.
  Qed.

  Lemma mp_return_preserves_data_and_response
      t h operation returned source target :
    RelaxedLTSSpec.Step MPLTS
      (mp_event t (@ResEv MPSig h operation returned)) source target ->
    mp_operation_safe operation ->
    data_value source = true ->
    data_value target = true /\
    mp_response_safe operation returned.
  Proof.
    intros Hstep Hsafe Hdata.
    unfold RelaxedLTSSpec.Step, MPLTS, MemoryLTS,
      memory_step, mp_event in Hstep.
    cbn [RelaxedLTSSpec.te_ev] in Hstep.
    destruct operation as [location | location value].
    - destruct location.
      + destruct Hstep as [Hstate Hreturned]. subst.
        split; [exact Hdata |].
        unfold mp_response_safe.
        exact Hdata.
      + destruct Hstep as [Hstate Hreturned]. subst.
        split; [exact Hdata | exact I].
    - subst. split; [exact Hdata | exact I].
  Qed.

  Lemma mp_poss_step_preserves_safe source target :
    poss_step MPLTS source target ->
    mp_poss_safe source ->
    mp_poss_safe target.
  Proof.
    intros [owner Hstep] Hsafe.
    destruct Hstep as
      [t h operation state state' pool pool' Hlin Hlts
      | t h operation returned state state' pool pool' Hlin Hlts
      | t h operation state pool Hlin Herror
      | t h operation returned state pool Hlin Herror].
    - cbn in Hsafe |- *.
      destruct Hsafe as [Hdata Hpool].
      pose proof (mp_safe_invocation_selected
        t h operation pool pool' Hlin Hpool) as Hoperation.
      split.
      + eapply mp_invoke_preserves_data_true; eauto.
      + eapply mp_safe_invocation_update; eauto.
    - cbn in Hsafe |- *.
      destruct Hsafe as [Hdata Hpool].
      pose proof (mp_safe_return_selected
        t h operation returned pool pool' Hlin Hpool) as Hoperation.
      destruct (mp_return_preserves_data_and_response
        t h operation returned state state'
        Hlts Hoperation Hdata) as [Hdata' Hresponse].
      split; [exact Hdata' |].
      eapply mp_safe_return_update; eauto.
    - unfold MPLTS, MemoryLTS, RelaxedLTSSpec.Error in Herror.
      exact Herror.
    - unfold MPLTS, MemoryLTS, RelaxedLTSSpec.Error in Herror.
      exact Herror.
  Qed.

  Lemma mp_poss_steps_preserve_safe source target :
    poss_steps MPLTS source target ->
    mp_poss_safe source ->
    mp_poss_safe target.
  Proof.
    intro Hsteps.
    induction Hsteps.
    - apply mp_poss_step_preserves_safe. exact H.
    - auto.
    - intros Hsafe. apply IHHsteps2. apply IHHsteps1. exact Hsafe.
  Qed.

  Lemma mp_wait_boundary_safe :
    mp_poss_safe mp_wait_boundary_poss.
  Proof.
    unfold mp_poss_safe, mp_wait_boundary_poss,
      mp_wait_boundary_pool, mp_pool_safe, mp_entry_safe,
      mp_lin_state_safe, mp_operation_safe, mp_response_safe.
    cbn. repeat constructor.
  Qed.

  Lemma mp_flag_one_data_zero_not_safe :
    ~ mp_poss_safe mp_flag_one_data_zero_poss.
  Proof.
    unfold mp_poss_safe, mp_flag_one_data_zero_poss,
      mp_flag_one_data_zero_pool, mp_pool_safe, mp_entry_safe,
      mp_lin_state_safe, mp_operation_safe, mp_response_safe.
    cbn. intros [_ Hsafe].
    inversion Hsafe as [| safe_head safe_tail Hhead Htail]; subst.
    destruct Hhead as [_ Hfalse]. discriminate Hfalse.
  Qed.

  Theorem wait_boundary_disallows_message_passing_result :
    ~ poss_steps MPLTS
        mp_wait_boundary_poss mp_flag_one_data_zero_poss.
  Proof.
    intro Hsteps.
    apply mp_flag_one_data_zero_not_safe.
    eapply mp_poss_steps_preserve_safe.
    - exact Hsteps.
    - exact mp_wait_boundary_safe.
  Qed.

End RelaxedMemoryLitmusExamples.
