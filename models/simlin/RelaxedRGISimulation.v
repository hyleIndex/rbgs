(** Rely/guarantee simulation for relaxed linearizability with futures. *)

Require Import Coq.Relations.Relation_Definitions.

Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedPossibility.
Require Import models.simlin.RelaxedModuleSemantics.


Module RelaxedRGISimulation.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedPossibility.
  Import RelaxedModuleSemantics.

  Section Simulation.
    Context {E F : RelaxedSig.t}.
    Context (VE : RelaxedLTSSpec.LTS E).
    Context (VF : RelaxedLTSSpec.LTS F).
    Context (M : RelaxedLang.RelaxedModuleImpl E F).

    Definition ConcreteState : Type :=
      @ModuleConfig E F VE.

    (** We deliberately use one possibility here.  Thus the liftings over
        sets of possibilities in the paper reduce to relations and
        reflexive-transitive closures on [Poss VF]. *)
    Definition AbstractState : Type := Poss VF.

    Definition JointState : Type :=
      (ConcreteState * AbstractState)%type.

    Definition ConcreteRelation : Type :=
      relation ConcreteState.

    Definition AbstractRelation : Type :=
      relation AbstractState.

    Definition JointRelation : Type :=
      relation JointState.

    Definition Assertion : Type :=
      JointState -> Prop.

    Definition ActiveThreads : Type :=
      tid -> Prop.

    (** The paper writes [R = (R_alpha, R_sys)].  Both components are
        indexed by the active thread whose simulation obligation is being
        checked. *)
    Record ConcreteRely : Type := {
      concrete_thread_rely : tid -> ConcreteRelation;
      concrete_system_rely : tid -> ConcreteRelation;
    }.

    Record AbstractRely : Type := {
      abstract_thread_rely : tid -> AbstractRelation;
      abstract_system_rely : tid -> AbstractRelation;
    }.

    (** [(G, AG)_I] from the paper.  Both the concrete and abstract
        transition must be admitted, and the invariant contains both ends
        of the transition. *)
    Definition invariant_lift
        (I : Assertion)
        (RC : ConcreteRelation)
        (RA : AbstractRelation) : JointRelation :=
      fun source target =>
        RC (fst source) (fst target) /\
        RA (snd source) (snd target) /\
        I source /\ I target.

    (** [(R, AR)_I] is the union of the ordinary thread rely and the new
        system rely, paired pointwise on the concrete and abstract sides. *)
    Definition rely_lift
        (I : Assertion)
        (R : ConcreteRely)
        (AR : AbstractRely)
        (alpha : tid) : JointRelation :=
      fun source target =>
        ((concrete_thread_rely R alpha
            (fst source) (fst target) /\
          abstract_thread_rely AR alpha
            (snd source) (snd target)) \/
         (concrete_system_rely R alpha
            (fst source) (fst target) /\
          abstract_system_rely AR alpha
            (snd source) (snd target))) /\
        I source /\ I target.

    (** A canonical [R_sys alpha] nondeterministically executes one future
        handle owned by [alpha].  This construction is polymorphic in the
        state, and can therefore be used separately for the concrete and
        abstract rely relations. *)
    Definition system_rely_of {S : Type}
        (G : CallKey F -> relation S)
        (alpha : tid) : relation S :=
      fun source target =>
        exists h, G (alpha, h) source target.

    (** The ordinary rely of [alpha] may be generated from guarantees of
        handles owned by other threads. *)
    Definition thread_rely_of {S : Type}
        (G : CallKey F -> relation S)
        (alpha : tid) : relation S :=
      fun source target =>
        exists owner,
          fst owner <> alpha /\
          G owner source target.

    (** A concrete underlay step [s --alpha:e--> s'].  Its owner handle is
        existential because the original simulation is indexed by active
        threads, not by one distinguished future handle. *)
    Definition underlay_step
        (alpha : tid)
        (source target : ConcreteState) : Prop :=
      exists h ev,
        module_step_at VE M (alpha, h)
          (UnderlayEvent ev) source target.

    (** The [invoke_alpha] relation in the paper: the concrete overlay
        invocation and its abstract bookkeeping insertion happen together. *)
    Inductive invoke_transition
        (alpha : tid) :
        ConcreteState -> AbstractState ->
        ConcreteState -> AbstractState -> Prop :=
    | invoke_transition_intro h op c c' p p'
        (Hconcrete :
          module_step_at VE M (alpha, h)
            (OverlayEvent
              (Build_ThreadEvent alpha (@InvEv F h op))) c c')
        (Habstract : poss_invoke VF alpha h op p p') :
        invoke_transition alpha c p c' p'.

    (** The [return_alpha] relation in the paper.  The abstract call must
        already be in its linearized-return phase; [overlay_step] below
        performs the preceding abstract specification steps. *)
    Inductive return_transition
        (alpha : tid) :
        ConcreteState -> AbstractState ->
        ConcreteState -> AbstractState -> Prop :=
    | return_transition_intro h op ret c c' p p'
        (Hconcrete :
          module_step_at VE M (alpha, h)
            (OverlayEvent
              (Build_ThreadEvent alpha (@ResEv F h op ret))) c c')
        (Habstract : poss_return VF alpha h op ret p p') :
        return_transition alpha c p c' p'.

    (** [OStep]'s first disjunct is an invocation.  Its second disjunct
        takes zero or more overlay bookkeeping steps ([SInvoke + SReturn]),
        then pairs a concrete and abstract return. *)
    Inductive overlay_step
        (alpha : tid) :
        ConcreteState -> AbstractState ->
        ConcreteState -> AbstractState -> Prop :=
    | overlay_step_invoke c p c' p'
        (Hinvoke : invoke_transition alpha c p c' p') :
        overlay_step alpha c p c' p'

    | overlay_step_return c p middle c' p'
        (Hsteps : poss_overlay_steps VF p middle)
        (Hreturn : return_transition alpha c middle c' p') :
        overlay_step alpha c p c' p'.

    (** This is Definition C.3 specialized from a set of possibilities to
        one [Poss].  The three premises deliberately retain the original
        quantifier directions:

        - [UStep] is universal over concrete underlay steps;
        - [OStep] is existential for every active thread;
        - [Rely] is universal over the paired rely relation. *)
    CoInductive RGISimulation
        (A : ActiveThreads)
        (R : ConcreteRely)
        (AR : AbstractRely)
        (G : ConcreteRelation)
        (AG : AbstractRelation)
        (I : Assertion) :
        ConcreteState -> AbstractState -> Prop :=
    | RGISim c p
        (rgisim_invariant : I (c, p))

        (rgisim_ustep :
          forall alpha,
            A alpha ->
            forall c',
              underlay_step alpha c c' ->
              exists p',
                poss_steps VF p p' /\
                invariant_lift I G AG (c, p) (c', p') /\
                RGISimulation A R AR G AG I c' p')

        (rgisim_ostep :
          forall alpha,
            A alpha ->
            exists c' p',
              overlay_step alpha c p c' p' /\
              invariant_lift I G AG (c, p) (c', p') /\
              RGISimulation A R AR G AG I c' p')

        (rgisim_rely :
          forall alpha,
            A alpha ->
            forall c' p',
              rely_lift I R AR alpha (c, p) (c', p') ->
              RGISimulation A R AR G AG I c' p') :
        RGISimulation A R AR G AG I c p.

  End Simulation.

End RelaxedRGISimulation.
