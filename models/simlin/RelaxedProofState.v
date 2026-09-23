(** Proof states for the relaxed program logic. *)

Require Import Coq.Lists.List.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedRGISimulation.
Require Import models.simlin.RelaxedAssertion.

Import ListNotations.


Module RelaxedProofState.
  Import RelaxedSig.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedRGISimulation.
  Import RelaxedAssertions.

  Section State.
    Context {E F : RelaxedSig.t}.
    Context (VE : RelaxedLTSSpec.LTS E).
    Context (VF : RelaxedLTSSpec.LTS F).
    Context (M : RelaxedLang.RelaxedModuleImpl E F).

    Definition LogicAssertion : Type := @Assertion E F VE VF.

    Context (I : LogicAssertion).
    Context (G : @ConcreteRelation E F VE).
    Context (AG : @AbstractRelation F VF).

    Definition LogicObligation : Type :=
      EventObligation VE VF M I G AG.

    Definition LogicObligationQueue : Type :=
      list LogicObligation.

    (** A method proof carries its local program control and future store,
        while the joint state and obligation queue describe the shared
        simulation state and the underlay events still owed to it. *)
    Record LocalProofState (A : Type) : Type := {
      lps_joint : @JointState E F VE VF;
      lps_program : Prog E A;
      lps_futures : FutureStore E;
      lps_obligations : LogicObligationQueue;
    }.

    Arguments LocalProofState _ : clear implicits.

    Definition local_program_config {A}
        (state : LocalProofState A) : ProgramConfig E A :=
      Build_ProgramConfig
        (lps_program A state)
        (lps_futures A state).

    Definition LocalAssertion (A : Type) : Type :=
      LocalProofState A -> Prop.

    Definition lift_joint {A}
        (P : LogicAssertion) : LocalAssertion A :=
      fun state => P (lps_joint A state).

    Definition local_invariant {A} : LocalAssertion A :=
      lift_joint I.

    (** The logical debt queue is linked to the operational module queue.
        It need not be empty while the program continuation advances. *)
    Definition local_queue_invariant {A} : LocalAssertion A :=
      fun state =>
        queue_invariant VE VF M I G AG
          (fst (lps_joint A state))
          (lps_obligations A state).

    Definition local_well_formed {A} : LocalAssertion A :=
      fun state =>
        I (lps_joint A state) /\
        store_well_formed (lps_futures A state) /\
        local_queue_invariant state.

    (** Concrete future tokens describe the thread-local [FutureStore].
        They are deliberately separate from [FutureToken], which describes
        the overlay possibility's invocation/linearized/return phases. *)
    Inductive ConcreteFutureToken : Type :=
    | concrete_pending
        (op : Sig.op (RelaxedSig.effect E))
        (handle : RelaxedSig.handle E)
    | concrete_resolved
        (op : Sig.op (RelaxedSig.effect E))
        (handle : RelaxedSig.handle E)
        (ret : Sig.ar op).

    Definition concrete_token_holds
        (token : ConcreteFutureToken)
        (store : FutureStore E) : Prop :=
      match token with
      | concrete_pending op handle => pending_at handle op store
      | concrete_resolved op handle ret =>
          resolved_at handle op ret store
      end.

    Definition AConcreteFuture {A}
        (token : ConcreteFutureToken) : LocalAssertion A :=
      fun state => concrete_token_holds token (lps_futures A state).

    Lemma add_pending_establishes_token
        (op : Sig.op (RelaxedSig.effect E))
        (handle : RelaxedSig.handle E)
        (store : FutureStore E) :
      concrete_token_holds (concrete_pending op handle)
        (add_pending handle op store).
    Proof.
      cbn. left. reflexivity.
    Qed.

    Lemma resolve_establishes_token
        (op : Sig.op (RelaxedSig.effect E))
        (handle : RelaxedSig.handle E)
        (ret : Sig.ar op)
        (store store' : FutureStore E) :
      resolve_store handle op ret store store' ->
      concrete_token_holds (concrete_resolved op handle ret) store'.
    Proof.
      exact (resolve_store_resolved handle op ret store store').
    Qed.

    Lemma resolved_token_allows_wait
        (t : LinCCALBase.tid)
        (A : Type)
        (op : Sig.op (RelaxedSig.effect E))
        (handle : RelaxedSig.handle E)
        (ret : Sig.ar op)
        (k : Sig.ar op -> Prog E A)
        (store : FutureStore E) :
      concrete_token_holds (concrete_resolved op handle ret) store ->
      program_step t Silent
        (Build_ProgramConfig (Wait (MkFutureRef op handle) k) store)
        (Build_ProgramConfig (k ret) store).
    Proof.
      intro Hresolved.
      now apply program_wait_resolved.
    Qed.

  End State.

End RelaxedProofState.
