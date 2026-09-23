(** Executable proof examples for the relaxed future semantics. *)

Require Import Coq.Lists.List.
Require Import Coq.PArith.PArith.
Require Import Coq.Relations.Relation_Operators.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedPossibility.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedRGISimulation.
Require Import models.simlin.RelaxedAssertion.
Require Import models.simlin.RelaxedProofState.
Require Import models.simlin.RelaxedLogic.

Import ListNotations.


Module RelaxedSemanticsExamples.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedPossibility.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedRGISimulation.
  Import RelaxedAssertions.
  Import RelaxedProofState.
  Import RelaxedLogic.

  (** Three unit-returning operations are enough to test scheduling. *)
  Inductive ToyOp : Type :=
  | First
  | Second
  | Blocked.

  Definition ToyAr (_ : ToyOp) : Type := unit.

  Canonical Structure ToyEffect : Sig.t :=
    {|
      Sig.op := ToyOp;
      Sig.ar := ToyAr;
    |}.

  (** Only [First -> Second] is semi-independent. *)
  Definition toy_independent (op1 op2 : ToyOp) : Prop :=
    match op1, op2 with
    | First, Second => True
    | _, _ => False
    end.

  Definition ToySig : RelaxedSig.t :=
    {|
      RelaxedSig.effect := ToyEffect;
      RelaxedSig.handle := nat;
      RelaxedSig.semi_independent := toy_independent;
      RelaxedSig.mode := fun _ => Local;
    |}.

  Lemma ToySig_well_formed : RelaxedSig.well_formed ToySig.
  Proof.
    constructor.
    - intros [] H; contradiction.
    - intros [] [] H; cbn in *; try contradiction; exact I.
    - intros [] [] H; cbn in *; try contradiction; exact I.
  Qed.

  (** The LTS accepts every toy event and leaves its unit state unchanged. *)
  Definition ToyLTS : RelaxedLTSSpec.LTS ToySig :=
    {|
      RelaxedLTSSpec.State := unit;
      RelaxedLTSSpec.Step := fun _ _ _ => True;
      RelaxedLTSSpec.Error := fun _ _ => False;
    |}.

  Definition toy_tid : tid := 1%positive.

  Definition inv_first (h : nat) : ThreadEvent ToySig :=
    Build_ThreadEvent toy_tid (@InvEv ToySig h First).

  Definition inv_second (h : nat) : ThreadEvent ToySig :=
    Build_ThreadEvent toy_tid (@InvEv ToySig h Second).

  Definition inv_blocked (h : nat) : ThreadEvent ToySig :=
    Build_ThreadEvent toy_tid (@InvEv ToySig h Blocked).

  Definition res_first (h : nat) : ThreadEvent ToySig :=
    Build_ThreadEvent toy_tid (@ResEv ToySig h First tt).

  Definition res_second (h : nat) : ThreadEvent ToySig :=
    Build_ThreadEvent toy_tid (@ResEv ToySig h Second tt).

  (** Horizontal composition shares the original raw-handle namespace.
      Only operations carry a component tag. *)
  Definition ToyTensorSig : RelaxedSig.t :=
    RelaxedSig.Tens.omap ToySig ToySig eq_refl.

  Definition tensor_left_invocation : ThreadEvent ToyTensorSig :=
    Build_ThreadEvent toy_tid
      (@InvEv ToyTensorSig 7 (inl First)).

  Definition tensor_right_invocation : ThreadEvent ToyTensorSig :=
    Build_ThreadEvent toy_tid
      (@InvEv ToyTensorSig 7 (inr Second)).

  Example tensor_does_not_enlarge_the_handle_set :
    RelaxedSig.handle ToyTensorSig = nat.
  Proof.
    reflexivity.
  Qed.

  (** The two component operations use the same [(thread, handle)] key.
      Hence they cannot both be allocated by one thread as distinct pending
      futures; the shared freshness check observes this collision. *)
  Example tensor_components_share_call_keys :
    te_key tensor_left_invocation = te_key tensor_right_invocation.
  Proof.
    reflexivity.
  Qed.

  Definition tensor_same_thread_duplicate_handle_trace :=
    [tensor_left_invocation; tensor_right_invocation].

  Example tensor_same_thread_duplicate_handle_is_not_fresh :
    ~ trace_fresh [] tensor_same_thread_duplicate_handle_trace.
  Proof.
    intros [Hnodup _].
    unfold tensor_same_thread_duplicate_handle_trace,
      tensor_left_invocation, tensor_right_invocation,
      trace_fresh, invocation_keys in *.
    cbn in Hnodup.
    inversion Hnodup as [| key keys Hnotin Htail].
    apply Hnotin. left. reflexivity.
  Qed.

  Definition other_toy_tid : tid := 2%positive.

  Example different_threads_can_reuse_a_raw_handle :
    te_key tensor_left_invocation <>
    te_key
      (Build_ThreadEvent other_toy_tid
        (@InvEv ToyTensorSig 7 (inr Second))).
  Proof.
    discriminate.
  Qed.

  Definition tensor_different_thread_same_handle_trace :=
    [ tensor_left_invocation;
      Build_ThreadEvent other_toy_tid
        (@InvEv ToyTensorSig 7 (inr Second)) ].

  Example tensor_different_thread_same_handle_is_fresh :
    trace_fresh [] tensor_different_thread_same_handle_trace.
  Proof.
    unfold trace_fresh, tensor_different_thread_same_handle_trace,
      tensor_left_invocation, invocation_keys.
    split.
    - cbn. constructor.
      + intros [Heq | Hnone]; [discriminate | contradiction].
      + constructor; [cbn; tauto | constructor].
    - cbn. tauto.
  Qed.

  (** A possibility is indexed by [(thread, handle)], rather than just by
      thread.  Thus one thread may have several live futures at once. *)
  Definition first_future_key : CallKey ToySig := (toy_tid, 0).
  Definition second_future_key : CallKey ToySig := (toy_tid, 1).

  Definition two_future_pool : LinPool ToySig :=
    [ make_lin_entry first_future_key (@ls_inv ToySig First);
      make_lin_entry second_future_key (@ls_lini ToySig Second) ].

  Definition two_future_pool_after_first_inv : LinPool ToySig :=
    [ make_lin_entry first_future_key (@ls_lini ToySig First);
      make_lin_entry second_future_key (@ls_lini ToySig Second) ].

  Example two_futures_of_one_thread_coexist :
    lin_lookup first_future_key (@ls_inv ToySig First) two_future_pool /\
    lin_lookup second_future_key (@ls_lini ToySig Second) two_future_pool.
  Proof.
    split; cbn; auto.
  Qed.

  Example two_future_pool_is_well_formed :
    lin_pool_well_formed two_future_pool.
  Proof.
    unfold lin_pool_well_formed, two_future_pool,
      first_future_key, second_future_key, lin_domain.
    cbn.
    constructor.
    - intros [Heq | Hnone].
      + inversion Heq.
      + contradiction.
    - constructor; [cbn; tauto | constructor].
  Qed.

  (** Advancing handle [0] changes only its phase; handle [1] remains
      present in the pool with its original phase. *)
  Example advancing_one_future_preserves_the_other :
    lin_update first_future_key
      (@ls_inv ToySig First) (@ls_lini ToySig First)
      two_future_pool two_future_pool_after_first_inv /\
    lin_lookup second_future_key (@ls_lini ToySig Second)
      two_future_pool_after_first_inv.
  Proof.
    split.
    - apply lin_update_here.
    - cbn; auto.
  Qed.

  Example possibility_steps_only_the_selected_future :
    poss_step ToyLTS
      (@PossOk ToySig ToyLTS tt two_future_pool)
      (@PossOk ToySig ToyLTS tt two_future_pool_after_first_inv).
  Proof.
    eapply ps_inv.
    - unfold two_future_pool, two_future_pool_after_first_inv,
        first_future_key, second_future_key.
      apply lin_invoke_update_here.
      constructor.
      + unfold older_entry_allows_invocation. cbn. right. exact I.
      + constructor.
    - exact I.
  Qed.

  (** [lin_insert] makes pools newest-first.  These pools therefore model
      the actual order obtained by issuing [First] and then [Second]. *)
  Definition first_pending_pool : LinPool ToySig :=
    [make_lin_entry first_future_key (@ls_inv ToySig First)].

  Definition independent_pending_pool : LinPool ToySig :=
    [ make_lin_entry second_future_key (@ls_inv ToySig Second);
      make_lin_entry first_future_key (@ls_inv ToySig First) ].

  Definition independent_later_linearized_pool : LinPool ToySig :=
    [ make_lin_entry second_future_key (@ls_lini ToySig Second);
      make_lin_entry first_future_key (@ls_inv ToySig First) ].

  Definition independent_earlier_linearized_pool : LinPool ToySig :=
    [ make_lin_entry second_future_key (@ls_inv ToySig Second);
      make_lin_entry first_future_key (@ls_lini ToySig First) ].

  Example pending_pool_order_is_generated_by_invocations :
    lin_insert first_future_key (@ls_inv ToySig First)
      empty_lin_pool first_pending_pool /\
    lin_insert second_future_key (@ls_inv ToySig Second)
      first_pending_pool independent_pending_pool.
  Proof.
    split.
    - apply lin_insert_fresh.
      unfold lin_fresh, lin_domain. cbn. tauto.
    - apply lin_insert_fresh.
      unfold lin_fresh, lin_domain, first_pending_pool,
        first_future_key, second_future_key.
      cbn. intros [Heq | Hnone]; [inversion Heq | contradiction].
  Qed.

  (** [Second] may cross the older pending [First], precisely because the
      directed pair [(First, Second)] is semi-independent. *)
  Example later_independent_invocation_can_linearize_first :
    @lin_invoke_update ToySig toy_tid 1 Second
      independent_pending_pool independent_later_linearized_pool.
  Proof.
    unfold independent_pending_pool, independent_later_linearized_pool,
      first_future_key, second_future_key.
    apply lin_invoke_update_here.
    constructor.
    - unfold older_entry_allows_invocation. cbn. right. exact I.
    - constructor.
  Qed.

  (** Choosing the earlier invocation does not cross the newer one, so it
      needs no semi-independence premise. *)
  Example earlier_invocation_can_always_linearize_first :
    @lin_invoke_update ToySig toy_tid 0 First
      independent_pending_pool independent_earlier_linearized_pool.
  Proof.
    unfold independent_pending_pool, independent_earlier_linearized_pool,
      first_future_key, second_future_key.
    apply lin_invoke_update_next.
    - cbn. intros Heq. inversion Heq.
    - apply lin_invoke_update_here. constructor.
  Qed.

  Definition blocked_pending_pool : LinPool ToySig :=
    [ make_lin_entry second_future_key (@ls_inv ToySig Blocked);
      make_lin_entry first_future_key (@ls_inv ToySig First) ].

  (** [Blocked] cannot cross [First], because [(First, Blocked)] is absent
      from the directed semi-independence relation.  This shared enabledness
      check rules out both a normal invocation step and an error step. *)
  Example later_dependent_invocation_is_not_enabled :
    ~ @lin_invocation_enabled ToySig toy_tid 1 Blocked
        blocked_pending_pool.
  Proof.
    intro Henabled.
    unfold blocked_pending_pool, first_future_key, second_future_key
      in Henabled.
    inversion Henabled as
      [older Hready | entry pool Hneq Hnext]; subst.
    - pose proof
        (@invocation_ready_same_thread_pending ToySig
          toy_tid 0 First Blocked [] Hready) as Himpossible.
      exact Himpossible.
    - apply Hneq. reflexivity.
  Qed.

  Example later_dependent_invocation_cannot_linearize_first :
    ~ exists pool',
        @lin_invoke_update ToySig toy_tid 1 Blocked
          blocked_pending_pool pool'.
  Proof.
    intros [pool' Hupdate].
    apply later_dependent_invocation_is_not_enabled.
    eapply lin_invoke_update_enabled. exact Hupdate.
  Qed.

  Example possibility_linearizes_the_independent_later_call :
    poss_step ToyLTS
      (@PossOk ToySig ToyLTS tt independent_pending_pool)
      (@PossOk ToySig ToyLTS tt independent_later_linearized_pool).
  Proof.
    eapply ps_inv.
    - apply later_independent_invocation_can_linearize_first.
    - exact I.
  Qed.

  Example independent_later_step_is_owned_by_its_handle :
    poss_step_at ToyLTS second_future_key
      (@PossOk ToySig ToyLTS tt independent_pending_pool)
      (@PossOk ToySig ToyLTS tt independent_later_linearized_pool).
  Proof.
    unfold second_future_key.
    refine (@psa_inv ToySig ToyLTS toy_tid 1 Second tt tt
      independent_pending_pool independent_later_linearized_pool _ _).
    - apply later_independent_invocation_can_linearize_first.
    - exact I.
  Qed.

  Definition possibility_module_config :
      @ModuleConfig ToySig ToySig ToyLTS :=
    @Build_ModuleConfig ToySig ToySig ToyLTS tt [] [] [].

  Definition independent_joint_source :
      @JointState ToySig ToySig ToyLTS ToyLTS :=
    (possibility_module_config,
     @PossOk ToySig ToyLTS tt independent_pending_pool).

  Definition independent_joint_target :
      @JointState ToySig ToySig ToyLTS ToyLTS :=
    (possibility_module_config,
     @PossOk ToySig ToyLTS tt independent_later_linearized_pool).

  Definition toy_handle_concrete_guarantee
      (_ : CallKey ToySig) :
      @ConcreteRelation ToySig ToySig ToyLTS :=
    eq.

  Definition toy_handle_abstract_guarantee
      (owner : CallKey ToySig) :
      @AbstractRelation ToySig ToyLTS :=
    poss_step_at ToyLTS owner.

  Example second_handle_takes_its_own_guarantee_step :
    toy_handle_abstract_guarantee second_future_key
      (snd independent_joint_source) (snd independent_joint_target).
  Proof.
    apply independent_later_step_is_owned_by_its_handle.
  Qed.

  (** [R_sys alpha] nondeterministically chooses a future handle owned by
      [alpha]; here it chooses the second pending handle. *)
  Example second_handle_guarantee_is_thread_system_rely :
    system_rely_of toy_handle_abstract_guarantee toy_tid
      (snd independent_joint_source) (snd independent_joint_target).
  Proof.
    exists 1.
    apply second_handle_takes_its_own_guarantee_step.
  Qed.

  Definition toy_concrete_relies :
      @ConcreteRely ToySig ToySig ToyLTS :=
    {|
      concrete_thread_rely := fun _ _ _ => False;
      concrete_system_rely :=
        system_rely_of toy_handle_concrete_guarantee;
    |}.

  Definition toy_abstract_relies :
      @AbstractRely ToySig ToyLTS :=
    {|
      abstract_thread_rely := fun _ _ _ => False;
      abstract_system_rely :=
        system_rely_of toy_handle_abstract_guarantee;
    |}.

  Definition toy_joint_invariant :
      @Assertion ToySig ToySig ToyLTS ToyLTS :=
    fun _ => True.

  Example paired_system_rely_contains_second_handle_step :
    rely_lift ToyLTS ToyLTS toy_joint_invariant
      toy_concrete_relies toy_abstract_relies toy_tid
      independent_joint_source independent_joint_target.
  Proof.
    split.
    - right. split.
      + exists 1. reflexivity.
      + apply second_handle_guarantee_is_thread_system_rely.
    - split; exact I.
  Qed.

  (** A blocking call is encoded by a future followed by a wait.  The two
      emitted events use the same raw handle. *)
  Example call_generates_matching_invocation_and_response :
    program_produces toy_tid (@call ToySig First)
      [inv_first 0; res_first 0] tt.
  Proof.
    unfold program_produces, initial_program, call.
    eexists.
    split.
    - eapply program_execution_emit.
      + apply program_future.
        unfold handle_fresh. cbn. tauto.
      + eapply program_execution_emit.
        * apply program_wait_pending.
          apply resolve_here.
        * apply program_execution_refl.
    - apply program_terminal_ret.
      repeat constructor.
  Qed.

  Definition overlapping_program : Prog ToySig unit :=
    @Future ToySig unit First (fun first_future =>
    @Future ToySig unit Second (fun second_future =>
    Wait first_future (fun _ =>
    Wait second_future (fun _ => Ret tt)))).

  (** Without an intervening wait, both invocations are present in the
      continuation before either response. *)
  Example overlapping_program_trace :
    program_produces toy_tid overlapping_program
      [inv_first 0; inv_second 1; res_first 0; res_second 1] tt.
  Proof.
    unfold program_produces, initial_program, overlapping_program.
    eexists.
    split.
    - eapply program_execution_emit.
      + apply program_future.
        unfold handle_fresh. cbn. tauto.
      + eapply program_execution_emit.
        * apply program_future.
          unfold handle_fresh. cbn.
          intros [Heq | Hnone]; [discriminate | contradiction].
        * eapply program_execution_emit.
          -- apply program_wait_pending.
             eapply resolve_next.
             ++ discriminate.
             ++ apply resolve_here.
          -- eapply program_execution_emit.
             ++ apply program_wait_pending.
                apply resolve_here.
             ++ apply program_execution_refl.
    - apply program_terminal_ret.
      repeat constructor.
  Qed.

  Definition waiting_program : Prog ToySig unit :=
    @Future ToySig unit First (fun first_future =>
    Wait first_future (fun _ =>
    @Future ToySig unit Second (fun second_future =>
    Wait second_future (fun _ => Ret tt)))).

  (** An explicit wait places the first response before the later
      invocation in the generated continuation. *)
  Example waiting_program_trace :
    program_produces toy_tid waiting_program
      [inv_first 0; res_first 0; inv_second 1; res_second 1] tt.
  Proof.
    unfold program_produces, initial_program, waiting_program.
    eexists.
    split.
    - eapply program_execution_emit.
      + apply program_future.
        unfold handle_fresh. cbn. tauto.
      + eapply program_execution_emit.
        * apply program_wait_pending.
          apply resolve_here.
        * eapply program_execution_emit.
          -- apply program_future.
             unfold handle_fresh. cbn.
             intros [Heq | Hnone]; [discriminate | contradiction].
          -- eapply program_execution_emit.
             ++ apply program_wait_pending.
                apply resolve_here.
             ++ apply program_execution_refl.
    - apply program_terminal_ret.
      repeat constructor.
  Qed.

  Definition owner1 : CallKey ToySig := (toy_tid, 10).

  Definition scheduled_first : ScheduledEvent ToySig ToySig :=
    Build_ScheduledEvent owner1 (inv_first 0).

  Definition scheduled_second : ScheduledEvent ToySig ToySig :=
    Build_ScheduledEvent owner1 (inv_second 1).

  Definition scheduled_blocked : ScheduledEvent ToySig ToySig :=
    Build_ScheduledEvent owner1 (inv_blocked 2).

  Definition scheduled_response : ScheduledEvent ToySig ToySig :=
    Build_ScheduledEvent owner1 (res_first 0).

  (** The later [Second] invocation may move before [First], because the
      directed pair [(First, Second)] is in the semi-independence relation. *)
  Example independent_invocation_can_move_to_front :
    select_frontier scheduled_second
      [scheduled_first; scheduled_second]
      [scheduled_first].
  Proof.
    apply select_next.
    - right. split; [reflexivity | exact I].
    - apply select_here.
  Qed.

  (** A pair absent from semi-independence cannot be reordered. *)
  Example dependent_invocation_cannot_move_to_front :
    ~ select_frontier scheduled_blocked
        [scheduled_first; scheduled_blocked]
        [scheduled_first].
  Proof.
    intro Hselect.
    inversion Hselect; subst; cbn in *.
    destruct Hcross as [Hneq | [_ Hind]].
    - apply Hneq. reflexivity.
    - exact Hind.
  Qed.

  (** A response produced by [wait] is a same-thread barrier. *)
  Example response_cannot_be_crossed :
    ~ select_frontier scheduled_second
        [scheduled_response; scheduled_second]
        [scheduled_response].
  Proof.
    intro Hselect.
    inversion Hselect; subst; cbn in *.
    destruct Hcross as [Hneq | [_ Hind]].
    - apply Hneq. reflexivity.
    - exact Hind.
  Qed.

  Definition ToyImpl : RelaxedModuleImpl ToySig ToySig :=
    fun op _ => call op.

  Definition reorder_source :
      @ModuleConfig ToySig ToySig ToyLTS :=
    @Build_ModuleConfig ToySig ToySig ToyLTS tt []
      [scheduled_first; scheduled_second] [].

  Definition reorder_target :
      @ModuleConfig ToySig ToySig ToyLTS :=
    @Build_ModuleConfig ToySig ToySig ToyLTS
      tt [] [scheduled_first] [].

  (** The frontier rule is used by the actual module transition, not only
      by the auxiliary list relation. *)
  Example module_emits_independent_second_first :
    module_step ToyLTS ToyImpl
      (UnderlayEvent (inv_second 1))
      reorder_source reorder_target.
  Proof.
    eapply module_underlay with (candidate := scheduled_second).
    - apply independent_invocation_can_move_to_front.
    - exact I.
  Qed.

  (** A generated command may be present in the operational queue before
      its abstract specification step runs.  The logical obligation below
      records that debt explicitly. *)
  Definition obligation_source :
      @ModuleConfig ToySig ToySig ToyLTS :=
    @Build_ModuleConfig ToySig ToySig ToyLTS
      tt [] [scheduled_second] [].

  Definition obligation_target :
      @ModuleConfig ToySig ToySig ToyLTS :=
    @Build_ModuleConfig ToySig ToySig ToyLTS tt [] [] [].

  Definition obligation_poss_source : Poss ToyLTS :=
    @PossOk ToySig ToyLTS tt independent_pending_pool.

  Definition obligation_poss_target : Poss ToyLTS :=
    @PossOk ToySig ToyLTS tt independent_later_linearized_pool.

  Definition obligation_invariant :
      @RAssertion ToySig ToySig ToyLTS ToyLTS :=
    fun _ => True.

  Definition obligation_concrete_guarantee :
      @ConcreteRelation ToySig ToySig ToyLTS :=
    fun c c' =>
      module_step_at ToyLTS ToyImpl owner1
        (UnderlayEvent (inv_second 1)) c c'.

  Definition obligation_abstract_stutter :
      @AbstractRelation ToySig ToyLTS := eq.

  Definition obligation_abstract_linearize :
      @AbstractRelation ToySig ToyLTS :=
    poss_step_at ToyLTS second_future_key.

  Definition debt_pre_assertion :
      @RAssertion ToySig ToySig ToyLTS ToyLTS :=
    fun state =>
      fst state = obligation_source /\
      snd state = obligation_poss_source.

  Definition debt_post_assertion :
      @RAssertion ToySig ToySig ToyLTS ToyLTS :=
    fun _ => True.

  Definition linearization_post_assertion :
      @RAssertion ToySig ToySig ToyLTS ToyLTS :=
    fun state => snd state = obligation_poss_target.

  Lemma obligation_module_consumes_second :
    module_step_at ToyLTS ToyImpl owner1
      (UnderlayEvent (inv_second 1))
      obligation_source obligation_target.
  Proof.
    eapply module_at_underlay with (candidate := scheduled_second).
    - apply select_here.
    - exact I.
  Qed.

  Lemma scheduled_second_uupdate :
    UUpdate ToyLTS ToyLTS ToyImpl
      obligation_invariant
      obligation_concrete_guarantee
      obligation_abstract_stutter
      scheduled_second debt_pre_assertion debt_post_assertion.
  Proof.
    intros c p [Hc Hp] c' Hstep.
    cbn in Hc, Hp. rewrite Hc, Hp in *.
    exists obligation_poss_source. split.
    - apply rt_refl.
    - split; [exact I |].
      unfold invariant_lift, obligation_concrete_guarantee,
        obligation_abstract_stutter, obligation_invariant.
      cbn. repeat split; auto.
  Qed.

  Definition scheduled_second_obligation :
      EventObligation ToyLTS ToyLTS ToyImpl
        obligation_invariant
        obligation_concrete_guarantee
        obligation_abstract_stutter :=
    {|
      obligation_event := scheduled_second;
      obligation_pre := debt_pre_assertion;
      obligation_post := debt_post_assertion;
      obligation_valid := scheduled_second_uupdate;
    |}.

  Definition certified_second_source : ProgramConfig ToySig unit :=
    Build_ProgramConfig
      (@Future ToySig unit Second (fun _ => Ret tt))
      (@empty_store ToySig).

  Definition certified_second_target : ProgramConfig ToySig unit :=
    Build_ProgramConfig (Ret tt)
      (@add_pending ToySig 1 Second (@empty_store ToySig)).

  (** A [Future] command may advance its continuation before the underlay
      event runs, but the matching obligation is present immediately. *)
  Example future_step_installs_exact_obligation :
    CertifiedExecution ToyLTS ToyLTS ToyImpl
      obligation_invariant
      obligation_concrete_guarantee
      obligation_abstract_stutter
      owner1 toy_tid unit
      certified_second_source
      [scheduled_second_obligation]
      certified_second_target.
  Proof.
    unfold certified_second_source, certified_second_target.
    eapply (certify_future
      ToyLTS ToyLTS ToyImpl
      obligation_invariant
      obligation_concrete_guarantee
      obligation_abstract_stutter
      owner1 toy_tid unit Second
      (fun _ => Ret tt) 1 (@empty_store ToySig)
      scheduled_second_obligation).
    - unfold handle_fresh, empty_store. cbn. tauto.
    - reflexivity.
  Qed.

  (** Erasing proof payloads gives exactly the ordinary program trace. *)
  Example certified_future_preserves_program_semantics :
    program_execution toy_tid certified_second_source
      [inv_second 1] certified_second_target.
  Proof.
    change (program_execution toy_tid certified_second_source
      (obligation_trace ToyLTS ToyLTS ToyImpl
        obligation_invariant
        obligation_concrete_guarantee
        obligation_abstract_stutter
        [scheduled_second_obligation])
      certified_second_target).
    eapply certified_execution_is_program_execution.
    apply future_step_installs_exact_obligation.
  Qed.

  Example future_step_establishes_concrete_pending_token :
    @concrete_token_holds ToySig
      (@concrete_pending ToySig Second 1)
      (pc_futures certified_second_target).
  Proof.
    apply add_pending_establishes_token.
  Qed.

  Definition debt_finished :
      @RAssertion ToySig ToySig ToyLTS ToyLTS :=
    fun _ => True.

  (** The continuation may coexist with this debt, but scheduler safety
      forces the actual module transition and discharges the stored update
      proof before the singleton queue can be considered finished. *)
  Example singleton_obligation_is_scheduler_safe :
    DebtSafe ToyLTS ToyLTS ToyImpl
      obligation_invariant
      obligation_concrete_guarantee
      obligation_abstract_stutter
      debt_finished
      (obligation_source, obligation_poss_source)
      [scheduled_second_obligation].
  Proof.
    eapply debt_safe_pending.
    - discriminate.
    - intros selected rest Hselect.
      inversion Hselect as [suffix | earlier queue queue' Hcross Htail];
        subst.
      + split.
        * split; reflexivity.
        * intros concrete' Hstep.
          destruct (consume_obligation
            ToyLTS ToyLTS ToyImpl
            obligation_invariant
            obligation_concrete_guarantee
            obligation_abstract_stutter
            scheduled_second_obligation
            obligation_source obligation_poss_source concrete'
            (conj eq_refl eq_refl) Hstep)
            as [abstract' [Hposs [Hpost Hinvariant]]].
          exists abstract'. split; [exact Hposs |].
          split; [exact Hpost |].
          split; [exact Hinvariant |].
          apply debt_safe_done. exact I.
      + inversion Htail.
  Qed.

  Example linked_scheduler_step_consumes_the_matching_debt :
    exists selected rest abstract',
      logic_obligation_event ToyLTS ToyLTS ToyImpl
        obligation_invariant
        obligation_concrete_guarantee
        obligation_abstract_stutter selected = scheduled_second /\
      poss_steps ToyLTS obligation_poss_source abstract' /\
      logic_obligation_post ToyLTS ToyLTS ToyImpl
        obligation_invariant
        obligation_concrete_guarantee
        obligation_abstract_stutter selected
        (obligation_target, abstract') /\
      invariant_lift ToyLTS ToyLTS
        obligation_invariant
        obligation_concrete_guarantee
        obligation_abstract_stutter
        (obligation_source, obligation_poss_source)
        (obligation_target, abstract') /\
      LinkedDebtSafe ToyLTS ToyLTS ToyImpl
        obligation_invariant
        obligation_concrete_guarantee
        obligation_abstract_stutter
        debt_finished
        (obligation_target, abstract') rest.
  Proof.
    eapply linked_debt_safe_underlay_step
      with (obligations := [scheduled_second_obligation]).
    - split.
      + reflexivity.
      + apply singleton_obligation_is_scheduler_safe.
    - apply obligation_module_consumes_second.
  Qed.

  (** ** A complete Hoare derivation without an explicit [Wait] *)

  Definition hoare_true :
      @RAssertion ToySig ToySig ToyLTS ToyLTS :=
    fun _ => True.

  Definition hoare_concrete_guarantee :
      @ConcreteRelation ToySig ToySig ToyLTS :=
    fun concrete concrete' =>
      exists event,
        module_step_at ToyLTS ToyImpl owner1
          (UnderlayEvent event) concrete concrete'.

  Definition hoare_abstract_stutter :
      @AbstractRelation ToySig ToyLTS := eq.

  Lemma hoare_true_uupdate
      (candidate : ScheduledEvent ToySig ToySig) :
    se_owner candidate = owner1 ->
    UUpdate ToyLTS ToyLTS ToyImpl
      hoare_true hoare_concrete_guarantee
      hoare_abstract_stutter
      candidate hoare_true hoare_true.
  Proof.
    intros Howner concrete abstract _ concrete' Hstep.
    exists abstract. split; [apply rt_refl |].
    split; [exact I |].
    unfold invariant_lift, hoare_concrete_guarantee,
      hoare_abstract_stutter, hoare_true.
    cbn. repeat split; try reflexivity; try exact I.
    exists (se_event candidate).
    now rewrite <- Howner.
  Qed.

  Definition scheduled_second_response :
      ScheduledEvent ToySig ToySig :=
    Build_ScheduledEvent owner1 (res_second 1).

  Definition hoare_second_invocation :
      EventObligation ToyLTS ToyLTS ToyImpl
        hoare_true hoare_concrete_guarantee
        hoare_abstract_stutter :=
    {|
      obligation_event := scheduled_second;
      obligation_pre := hoare_true;
      obligation_post := hoare_true;
      obligation_valid := hoare_true_uupdate scheduled_second eq_refl;
    |}.

  Definition hoare_first_invocation :
      EventObligation ToyLTS ToyLTS ToyImpl
        hoare_true hoare_concrete_guarantee
        hoare_abstract_stutter :=
    {|
      obligation_event := scheduled_first;
      obligation_pre := hoare_true;
      obligation_post := hoare_true;
      obligation_valid := hoare_true_uupdate scheduled_first eq_refl;
    |}.

  Definition hoare_second_response :
      EventObligation ToyLTS ToyLTS ToyImpl
        hoare_true hoare_concrete_guarantee
        hoare_abstract_stutter :=
    {|
      obligation_event := scheduled_second_response;
      obligation_pre := hoare_true;
      obligation_post := hoare_true;
      obligation_valid :=
        hoare_true_uupdate scheduled_second_response eq_refl;
    |}.

  Lemma hoare_obligation_preserves_true
      (obligation : EventObligation ToyLTS ToyLTS ToyImpl
        hoare_true hoare_concrete_guarantee
        hoare_abstract_stutter) :
    ObligationPreserves ToyLTS ToyLTS ToyImpl
      hoare_true hoare_concrete_guarantee
      hoare_abstract_stutter obligation hoare_true.
  Proof.
    intros concrete abstract Hpre _ concrete' Hstep.
    destruct (consume_obligation
      ToyLTS ToyLTS ToyImpl
      hoare_true hoare_concrete_guarantee
      hoare_abstract_stutter obligation
      concrete abstract concrete' Hpre Hstep)
      as [abstract' [Hposs [Hpost Hinvariant]]].
    exists abstract'. split; [exact Hposs |].
    split; [exact Hpost |].
    split; [exact I | exact Hinvariant].
  Qed.

  Lemma response_cannot_cross_its_invocation :
    ~ event_can_cross
      (se_event scheduled_second)
      (se_event scheduled_second_response).
  Proof.
    intros [Hdifferent | [Hsame Hindependent]].
    - apply Hdifferent. reflexivity.
    - exact Hindependent.
  Qed.

  Lemma independent_invocations_are_logically_compatible :
    ObligationCompatible ToyLTS ToyLTS ToyImpl
      hoare_true hoare_concrete_guarantee
      hoare_abstract_stutter
      hoare_first_invocation hoare_second_invocation.
  Proof.
    intro Hcross. repeat split;
      apply hoare_obligation_preserves_true.
  Qed.

  Example two_reorderable_invocations_have_safe_debt :
    forall state,
      DebtSafe ToyLTS ToyLTS ToyImpl
        hoare_true hoare_concrete_guarantee
        hoare_abstract_stutter
        hoare_true state
        [hoare_first_invocation; hoare_second_invocation].
  Proof.
    intro state. eapply debt_safe_compatible_pair.
    - exact I.
    - exact I.
    - right. split; [reflexivity | exact I].
    - apply independent_invocations_are_logically_compatible.
    - intros. exact I.
  Qed.

  Definition hoare_trivial_obligation
      (obligation : EventObligation ToyLTS ToyLTS ToyImpl
        hoare_true hoare_concrete_guarantee
        hoare_abstract_stutter) : Prop :=
    (forall state,
      logic_obligation_pre ToyLTS ToyLTS ToyImpl
        hoare_true hoare_concrete_guarantee
        hoare_abstract_stutter obligation state) /\
    (forall state,
      logic_obligation_post ToyLTS ToyLTS ToyImpl
        hoare_true hoare_concrete_guarantee
        hoare_abstract_stutter obligation state).

  Definition hoare_queue_protocol
      (obligations : LogicObligations ToyLTS ToyLTS ToyImpl
        hoare_true hoare_concrete_guarantee
        hoare_abstract_stutter)
      (_ : @JointState ToySig ToySig ToyLTS ToyLTS) : Prop :=
    Forall hoare_trivial_obligation obligations.

  Lemma hoare_trivial_debt_protocol :
    DebtProtocol ToyLTS ToyLTS ToyImpl
      hoare_true hoare_concrete_guarantee
      hoare_abstract_stutter
      hoare_queue_protocol.
  Proof.
    intros obligations selected rest Hselect
      concrete abstract Hall.
    assert (Hselected : hoare_trivial_obligation selected).
    {
      apply Forall_forall with (x := selected) in Hall.
      - exact Hall.
      - eapply select_obligation_member; eauto.
    }
    destruct Hselected as [Hpre _].
    split; [apply Hpre |].
    intros concrete' Hstep.
    destruct (consume_obligation
      ToyLTS ToyLTS ToyImpl
      hoare_true hoare_concrete_guarantee
      hoare_abstract_stutter selected
      concrete abstract concrete' (Hpre (concrete, abstract)) Hstep)
      as [abstract' [Hposs [Hpost Hinvariant]]].
    exists abstract'. split; [exact Hposs |].
    split; [exact Hpost |].
    split; [exact Hinvariant |].
    unfold hoare_queue_protocol.
    eapply select_obligation_preserves_forall; eauto.
  Qed.

  (** The queue-indexed protocol constructs the whole scheduler tree for
      three debts without enumerating its frontier permutations manually. *)
  Example three_obligation_protocol_is_safe :
    forall state,
      DebtSafe ToyLTS ToyLTS ToyImpl
        hoare_true hoare_concrete_guarantee
        hoare_abstract_stutter
        hoare_true state
        [ hoare_first_invocation;
          hoare_second_invocation;
          hoare_second_response ].
  Proof.
    intro state.
    eapply debt_protocol_sound
      with (K := hoare_queue_protocol).
    - apply hoare_trivial_debt_protocol.
    - intros. exact I.
    - unfold hoare_queue_protocol, hoare_trivial_obligation.
      repeat constructor; intros; exact I.
  Qed.

  Definition hoare_post (_ : unit) :
      @RAssertion ToySig ToySig ToyLTS ToyLTS := hoare_true.

  Lemma hoare_response_debt_certificate :
    DebtCertificate ToyLTS ToyLTS ToyImpl
      hoare_true hoare_concrete_guarantee
      hoare_abstract_stutter
      hoare_true hoare_true [hoare_second_response].
  Proof.
    intros state _ _.
    eapply debt_safe_singleton_with_frame
      with (Frame := hoare_true).
    - exact I.
    - exact I.
    - apply hoare_obligation_preserves_true.
    - intros. exact I.
  Qed.

  Lemma hoare_invoke_response_debt_certificate :
    DebtCertificate ToyLTS ToyLTS ToyImpl
      hoare_true hoare_concrete_guarantee
      hoare_abstract_stutter
      hoare_true hoare_true
      [hoare_second_invocation; hoare_second_response].
  Proof.
    intros state _ _.
    eapply debt_safe_ordered_pair.
    - exact I.
    - apply response_cannot_cross_its_invocation.
    - intros. exact I.
    - change
        (ObligationPreserves ToyLTS ToyLTS ToyImpl
          hoare_true hoare_concrete_guarantee
          hoare_abstract_stutter
          hoare_second_response hoare_true).
      apply hoare_obligation_preserves_true.
    - intros. exact I.
  Qed.

  Definition no_wait_future_program : Prog ToySig unit :=
    @Future ToySig unit Second (fun _ => Ret tt).

  Definition no_wait_future_final : ProgramConfig ToySig unit :=
    Build_ProgramConfig (Ret tt)
      [@Build_FutureEntry ToySig 1 (@Resolved ToySig Second tt)].

  Example no_wait_future_has_a_hoare_derivation :
    HTripleDerivation ToyLTS ToyLTS ToyImpl
      hoare_true hoare_concrete_guarantee
      hoare_abstract_stutter
      owner1 toy_tid unit
      hoare_true no_wait_future_program (@empty_store ToySig)
      hoare_post
      [hoare_second_invocation; hoare_second_response]
      tt no_wait_future_final.
  Proof.
    unfold no_wait_future_program, no_wait_future_final.
    eapply provable_future with (handle := 1).
    - unfold handle_fresh, empty_store. cbn. tauto.
    - reflexivity.
    - eapply provable_resolve
        with (ret := tt)
          (store' :=
            [@Build_FutureEntry ToySig 1 (@Resolved ToySig Second tt)])
          (obligation := hoare_second_response).
      + apply resolve_here.
      + reflexivity.
      + eapply provable_ret.
        * constructor; [exact I | constructor].
        * intros. exact I.
      + apply hoare_response_debt_certificate.
    - apply hoare_invoke_response_debt_certificate.
  Qed.

  Definition toy_call_program : Prog ToySig unit := @call ToySig Second.

  Example toy_call_has_a_hoare_derivation :
    HTripleDerivation ToyLTS ToyLTS ToyImpl
      hoare_true hoare_concrete_guarantee
      hoare_abstract_stutter
      owner1 toy_tid unit
      hoare_true toy_call_program (@empty_store ToySig)
      hoare_post
      [hoare_second_invocation; hoare_second_response]
      tt no_wait_future_final.
  Proof.
    unfold toy_call_program, call, no_wait_future_final.
    eapply provable_future with (handle := 1).
    - unfold handle_fresh, empty_store. cbn. tauto.
    - reflexivity.
    - eapply provable_wait_pending
        with (ret := tt)
          (store' :=
            [@Build_FutureEntry ToySig 1 (@Resolved ToySig Second tt)])
          (obligation := hoare_second_response).
      + apply resolve_here.
      + reflexivity.
      + eapply provable_ret.
        * constructor; [exact I | constructor].
        * intros. exact I.
      + apply hoare_response_debt_certificate.
    - apply hoare_invoke_response_debt_certificate.
  Qed.

  Definition hoare_call_source :
      @ModuleConfig ToySig ToySig ToyLTS :=
    @Build_ModuleConfig ToySig ToySig ToyLTS tt [] [] [].

  Definition hoare_call_target :
      @ModuleConfig ToySig ToySig ToyLTS :=
    @Build_ModuleConfig ToySig ToySig ToyLTS tt
      [@Build_CallEntry ToySig toy_tid 10
        (@ActiveCall ToySig Second tt)]
      (schedule_trace owner1
        (obligation_trace ToyLTS ToyLTS ToyImpl
          hoare_true hoare_concrete_guarantee
          hoare_abstract_stutter
          [hoare_second_invocation; hoare_second_response]))
      (invocation_keys
        (obligation_trace ToyLTS ToyLTS ToyImpl
          hoare_true hoare_concrete_guarantee
          hoare_abstract_stutter
          [hoare_second_invocation; hoare_second_response])).

  Example hoare_method_invocation_splices_operational_and_logical_queues :
    module_step_at ToyLTS ToyImpl owner1
      (OverlayEvent
        (Build_ThreadEvent toy_tid (@InvEv ToySig 10 Second)))
      hoare_call_source hoare_call_target /\
    queue_invariant ToyLTS ToyLTS ToyImpl
      hoare_true hoare_concrete_guarantee
      hoare_abstract_stutter
      hoare_call_target
      [hoare_second_invocation; hoare_second_response].
  Proof.
    unfold hoare_call_source, hoare_call_target, owner1.
    eapply (htriple_invocation_splices_debt
      ToyLTS ToyLTS ToyImpl
      hoare_true hoare_concrete_guarantee
      hoare_abstract_stutter
      toy_tid 10 Second hoare_true hoare_post
      [hoare_second_invocation; hoare_second_response]
      tt no_wait_future_final tt [] [] [] []).
    - change
        (HTripleDerivation ToyLTS ToyLTS ToyImpl
          hoare_true hoare_concrete_guarantee
          hoare_abstract_stutter
          (toy_tid, 10) toy_tid unit
          hoare_true toy_call_program (@empty_store ToySig)
          hoare_post
          [hoare_second_invocation; hoare_second_response]
          tt no_wait_future_final).
      apply toy_call_has_a_hoare_derivation.
    - unfold call_fresh, call_key. cbn. tauto.
    - unfold trace_fresh, obligation_trace, invocation_keys,
        logic_obligation_event, hoare_second_invocation,
        hoare_second_response, scheduled_second,
        scheduled_second_response, inv_second, res_second.
      cbn. split.
      + repeat constructor; cbn; tauto.
      + cbn. tauto.
    - reflexivity.
  Qed.

  Example no_wait_future_triple_is_locally_sound :
    exists obligations result final,
      program_execution toy_tid
        (Build_ProgramConfig no_wait_future_program (@empty_store ToySig))
        (obligation_trace ToyLTS ToyLTS ToyImpl
          hoare_true hoare_concrete_guarantee
          hoare_abstract_stutter obligations)
        final /\
      program_terminal final result /\
      erase_obligations ToyLTS ToyLTS ToyImpl
        hoare_true hoare_concrete_guarantee
        hoare_abstract_stutter obligations =
        schedule_trace owner1
          (obligation_trace ToyLTS ToyLTS ToyImpl
            hoare_true hoare_concrete_guarantee
            hoare_abstract_stutter obligations) /\
      DebtCertificate ToyLTS ToyLTS ToyImpl
        hoare_true hoare_concrete_guarantee
        hoare_abstract_stutter
        hoare_true (hoare_post result) obligations.
  Proof.
    eapply htriple_provable_sound.
    exists [hoare_second_invocation; hoare_second_response],
      tt, no_wait_future_final.
    apply no_wait_future_has_a_hoare_derivation.
  Qed.

  Example generated_command_has_a_matching_logical_debt :
    queue_invariant ToyLTS ToyLTS ToyImpl
      obligation_invariant
      obligation_concrete_guarantee
      obligation_abstract_stutter
      obligation_source [scheduled_second_obligation].
  Proof.
    reflexivity.
  Qed.

  Example logical_debt_selection_matches_operational_selection :
    select_obligation ToyLTS ToyLTS ToyImpl
      obligation_invariant
      obligation_concrete_guarantee
      obligation_abstract_stutter
      scheduled_second_obligation
      [scheduled_second_obligation] [].
  Proof.
    apply select_obligation_here.
  Qed.

  Example operational_selection_recovers_logical_debt :
    exists
      (obligation : EventObligation ToyLTS ToyLTS ToyImpl
        obligation_invariant
        obligation_concrete_guarantee
        obligation_abstract_stutter)
      (obligations' : ObligationQueue ToyLTS ToyLTS ToyImpl
        obligation_invariant
        obligation_concrete_guarantee
        obligation_abstract_stutter),
      obligation_event ToyLTS ToyLTS ToyImpl
        obligation_invariant
        obligation_concrete_guarantee
        obligation_abstract_stutter obligation = scheduled_second /\
      select_obligation ToyLTS ToyLTS ToyImpl
        obligation_invariant
        obligation_concrete_guarantee
        obligation_abstract_stutter obligation
        [scheduled_second_obligation] obligations' /\
      erase_obligations ToyLTS ToyLTS ToyImpl
        obligation_invariant
        obligation_concrete_guarantee
        obligation_abstract_stutter obligations' = [].
  Proof.
    eapply operational_selection_has_obligation.
    - apply generated_command_has_a_matching_logical_debt.
    - apply select_here.
  Qed.

  (** Consuming an ordinary obligation permits the abstract side to stay
      put.  This is intentional: the implementation command need not be a
      linearization point. *)
  Example ordinary_command_can_stutter_abstractly :
    exists p',
      p' = obligation_poss_source /\
      poss_steps ToyLTS obligation_poss_source p' /\
      invariant_lift ToyLTS ToyLTS
        obligation_invariant
        obligation_concrete_guarantee
        obligation_abstract_stutter
        (obligation_source, obligation_poss_source)
        (obligation_target, p').
  Proof.
    exists obligation_poss_source.
    split; [reflexivity |]. split; [apply rt_refl |].
    unfold invariant_lift, obligation_concrete_guarantee,
      obligation_abstract_stutter, obligation_invariant.
    cbn. repeat split; auto using obligation_module_consumes_second.
  Qed.

  Lemma scheduled_second_lin_update :
    LinUpdate ToyLTS ToyLTS ToyImpl
      obligation_invariant
      obligation_concrete_guarantee
      obligation_abstract_linearize
      scheduled_second second_future_key
      debt_pre_assertion linearization_post_assertion.
  Proof.
    intros c p [Hc Hp] c' Hstep.
    cbn in Hc, Hp. rewrite Hc, Hp in *.
    exists obligation_poss_target. split.
    - apply independent_later_step_is_owned_by_its_handle.
    - split; [reflexivity |].
      unfold invariant_lift, obligation_concrete_guarantee,
        obligation_abstract_linearize, obligation_invariant.
      cbn. repeat split; auto.
      apply independent_later_step_is_owned_by_its_handle.
  Qed.

  Definition scheduled_second_linearization_obligation :
      LinearizationObligation ToyLTS ToyLTS ToyImpl
        obligation_invariant
        obligation_concrete_guarantee
        obligation_abstract_linearize :=
    {|
      lin_obligation_event := scheduled_second;
      lin_obligation_owner := second_future_key;
      lin_obligation_pre := debt_pre_assertion;
      lin_obligation_post := linearization_post_assertion;
      lin_obligation_valid := scheduled_second_lin_update;
    |}.

  (** In contrast, consuming an obligation declared to be a linearization
      point produces a possibility provably different from its source. *)
  Example linearization_obligation_cannot_stutter :
    exists p',
      obligation_poss_source <> p' /\
      linearization_post_assertion (obligation_target, p') /\
      invariant_lift ToyLTS ToyLTS
        obligation_invariant
        obligation_concrete_guarantee
        obligation_abstract_linearize
        (obligation_source, obligation_poss_source)
        (obligation_target, p').
  Proof.
    exact (consume_linearization_obligation
      ToyLTS ToyLTS ToyImpl
      obligation_invariant
      obligation_concrete_guarantee
      obligation_abstract_linearize
      scheduled_second_linearization_obligation
      obligation_source obligation_poss_source obligation_target
      (conj eq_refl eq_refl)
      obligation_module_consumes_second).
  Qed.

  Definition OverlapImpl : RelaxedModuleImpl ToySig ToySig :=
    fun _ _ => overlapping_program.

  Definition overlap_trace : list (ThreadEvent ToySig) :=
    [inv_first 0; inv_second 1; res_first 0; res_second 1].

  Definition overlap_initial :
      @ModuleConfig ToySig ToySig ToyLTS :=
    @Build_ModuleConfig ToySig ToySig ToyLTS tt [] [] [].

  Definition overlap_invoked :
      @ModuleConfig ToySig ToySig ToyLTS :=
    @Build_ModuleConfig ToySig ToySig ToyLTS tt
      [@Build_CallEntry ToySig toy_tid 10 (@ActiveCall ToySig First tt)]
      (schedule_trace owner1 overlap_trace)
      (invocation_keys overlap_trace).

  Definition overlap_second_first :
      @ModuleConfig ToySig ToySig ToyLTS :=
    @Build_ModuleConfig ToySig ToySig ToyLTS tt
      [@Build_CallEntry ToySig toy_tid 10 (@ActiveCall ToySig First tt)]
      [ @Build_ScheduledEvent ToySig ToySig owner1 (inv_first 0);
        @Build_ScheduledEvent ToySig ToySig owner1 (res_first 0);
        @Build_ScheduledEvent ToySig ToySig owner1 (res_second 1) ]
      [(toy_tid, 0); (toy_tid, 1)].

  Lemma overlap_module_invoke :
    module_step ToyLTS OverlapImpl
      (OverlayEvent
        (Build_ThreadEvent toy_tid (@InvEv ToySig 10 First)))
      overlap_initial overlap_invoked.
  Proof.
    unfold overlap_initial, overlap_invoked, owner1.
    cbn.
    refine (@module_invoke
      ToySig ToySig ToyLTS OverlapImpl
      toy_tid 10 First tt [] [] [] overlap_trace tt _ _ _).
    - unfold call_fresh. cbn. tauto.
    - apply overlapping_program_trace.
    - unfold trace_fresh, overlap_trace.
      split.
      + cbn.
        constructor.
        * intros [Heq | Hnone]; [inversion Heq | contradiction].
        * constructor.
          -- cbn. tauto.
          -- constructor.
      + intros key Hkey. cbn in Hkey. cbn. tauto.
  Qed.

  Lemma overlap_module_reorders_second :
    module_step ToyLTS OverlapImpl
      (UnderlayEvent (inv_second 1))
      overlap_invoked overlap_second_first.
  Proof.
    eapply module_underlay with
      (candidate := Build_ScheduledEvent owner1 (inv_second 1)).
    - apply select_next.
      + right. split; [reflexivity | exact I].
      + apply select_here.
    - exact I.
  Qed.

  Example overlap_module_reorder_has_the_overlay_owner :
    module_step_at ToyLTS OverlapImpl owner1
      (UnderlayEvent (inv_second 1))
      overlap_invoked overlap_second_first.
  Proof.
    eapply module_at_underlay with
      (candidate := Build_ScheduledEvent owner1 (inv_second 1)).
    - apply select_next.
      + right. split; [reflexivity | exact I].
      + apply select_here.
    - exact I.
  Qed.

  (** End-to-end: an overlay invocation installs the method continuation,
      after which the module emits the independent second invocation first. *)
  Example overlapping_module_execution :
    module_execution ToyLTS OverlapImpl
      overlap_initial
      [ OverlayEvent
          (Build_ThreadEvent toy_tid (@InvEv ToySig 10 First));
        UnderlayEvent (inv_second 1) ]
      overlap_second_first.
  Proof.
    eapply module_execution_cons.
    - apply overlap_module_invoke.
    - eapply module_execution_cons.
      + apply overlap_module_reorders_second.
      + apply module_execution_refl.
  Qed.

End RelaxedSemanticsExamples.
