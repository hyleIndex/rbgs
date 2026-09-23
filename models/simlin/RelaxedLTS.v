(** Labelled transition systems over relaxed effect signatures. *)

Require Import Coq.Program.Equality.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import LinCCAL.


Module RelaxedLTSSpec.
  Import LinCCALBase.
  Import RelaxedSig.

  (** A future handle is part of both the invocation and its matching
      response.  The thread identifier records the agent that issued the
      operation; [(thread, handle)] identifies the particular call. *)
  Variant Event (E : RelaxedSig.t) : Type :=
  | InvEv
      (h : RelaxedSig.handle E)
      (op : Sig.op (RelaxedSig.effect E))
  | ResEv
      (h : RelaxedSig.handle E)
      (op : Sig.op (RelaxedSig.effect E))
      (ret : Sig.ar op).

  Arguments Event _ : clear implicits.
  Arguments InvEv {E} _ _.
  Arguments ResEv {E} _ _ _.

  Definition event_handle {E} (ev : Event E) : RelaxedSig.handle E :=
    match ev with
    | InvEv h _ => h
    | ResEv h _ _ => h
    end.

  Definition event_op {E} (ev : Event E) :
      Sig.op (RelaxedSig.effect E) :=
    match ev with
    | InvEv _ op => op
    | ResEv _ op _ => op
    end.

  Lemma ResEvInversion {E} h op (r1 r2 : Sig.ar op) :
    @ResEv E h op r1 = @ResEv E h op r2 ->
    r1 = r2.
  Proof.
    intro Heq.
    dependent destruction Heq.
    reflexivity.
  Qed.

  Record ThreadEvent (E : RelaxedSig.t) : Type := {
    te_tid : tid;
    te_ev : Event E;
  }.

  Arguments ThreadEvent _ : clear implicits.
  Arguments Build_ThreadEvent {E} _ _.

  Definition CallKey (E : RelaxedSig.t) : Type :=
    (tid * RelaxedSig.handle E)%type.

  Definition te_key {E} (ev : ThreadEvent E) : CallKey E :=
    (te_tid E ev, event_handle (te_ev E ev)).

  Record LTS (E : RelaxedSig.t) : Type := {
    State : Type;
    Step : ThreadEvent E -> State -> State -> Prop;
    Error : ThreadEvent E -> State -> Prop;
  }.

  Arguments LTS _ : clear implicits.
  Arguments State {E} _.
  Arguments Step {E} _ _ _ _.
  Arguments Error {E} _ _ _.

  Definition NoError {E State} : ThreadEvent E -> State -> Prop :=
    fun _ _ => False.

  Ltac inversion_thread_event_eq :=
    match goal with
    | H : ?e1 = ?e2 |- _ =>
        let T := type of e1 in
        match T with
        | ThreadEvent _ => inversion H; subst
        end
    end.

  (** ** Horizontal composition *)

  Section Tensor.
    Context {E1 E2 : RelaxedSig.t}.
    Context (Hhandle : RelaxedSig.handle E1 = RelaxedSig.handle E2).
    Context (V1 : LTS E1) (V2 : LTS E2).

    Definition event_i1 (ev : Event E1) :
        Event (RelaxedSig.Tens.omap E1 E2 Hhandle) :=
      match ev with
      | InvEv h op =>
          @InvEv (RelaxedSig.Tens.omap E1 E2 Hhandle) h (inl op)
      | ResEv h op ret =>
          @ResEv (RelaxedSig.Tens.omap E1 E2 Hhandle) h (inl op) ret
      end.

    Definition event_i2 (ev : Event E2) :
        Event (RelaxedSig.Tens.omap E1 E2 Hhandle) :=
      match ev with
      | InvEv h op =>
          @InvEv (RelaxedSig.Tens.omap E1 E2 Hhandle)
            (RelaxedSig.Tens.transport_handle (eq_sym Hhandle) h) (inr op)
      | ResEv h op ret =>
          @ResEv (RelaxedSig.Tens.omap E1 E2 Hhandle)
            (RelaxedSig.Tens.transport_handle (eq_sym Hhandle) h)
            (inr op) ret
      end.

    Definition thread_event_i1 (ev : ThreadEvent E1) :
        ThreadEvent (RelaxedSig.Tens.omap E1 E2 Hhandle) :=
      Build_ThreadEvent (te_tid E1 ev) (event_i1 (te_ev E1 ev)).

    Definition thread_event_i2 (ev : ThreadEvent E2) :
        ThreadEvent (RelaxedSig.Tens.omap E1 E2 Hhandle) :=
      Build_ThreadEvent (te_tid E2 ev) (event_i2 (te_ev E2 ev)).

    (** The operation tag selects the component LTS.  The raw handle is not
        tagged and remains in the one shared handle namespace. *)
    Definition tens_step
        (ev : ThreadEvent (RelaxedSig.Tens.omap E1 E2 Hhandle))
        (src : (State V1 * State V2)%type)
        (dst : (State V1 * State V2)%type) : Prop.
    Proof.
      destruct ev as [t ev].
      destruct src as [s1 s2].
      destruct dst as [s1' s2'].
      destruct ev as [h op | h op ret].
      - destruct op as [op1 | op2].
        + exact (Step V1
            (Build_ThreadEvent t (@InvEv E1 h op1)) s1 s1' /\
                 s2 = s2').
        + exact (Step V2
            (Build_ThreadEvent t
              (@InvEv E2
                (RelaxedSig.Tens.transport_handle Hhandle h) op2))
            s2 s2' /\ s1 = s1').
      - destruct op as [op1 | op2].
        + exact (Step V1
            (Build_ThreadEvent t (@ResEv E1 h op1 ret)) s1 s1' /\
                 s2 = s2').
        + exact (Step V2
            (Build_ThreadEvent t
              (@ResEv E2
                (RelaxedSig.Tens.transport_handle Hhandle h) op2 ret))
            s2 s2' /\ s1 = s1').
    Defined.

    Definition tens_error
        (ev : ThreadEvent (RelaxedSig.Tens.omap E1 E2 Hhandle))
        (s : (State V1 * State V2)%type) : Prop.
    Proof.
      destruct ev as [t ev].
      destruct s as [s1 s2].
      destruct ev as [h op | h op ret].
      - destruct op as [op1 | op2].
        + exact (Error V1
            (Build_ThreadEvent t (@InvEv E1 h op1)) s1).
        + exact (Error V2
            (Build_ThreadEvent t
              (@InvEv E2
                (RelaxedSig.Tens.transport_handle Hhandle h) op2)) s2).
      - destruct op as [op1 | op2].
        + exact (Error V1
            (Build_ThreadEvent t (@ResEv E1 h op1 ret)) s1).
        + exact (Error V2
            (Build_ThreadEvent t
              (@ResEv E2
                (RelaxedSig.Tens.transport_handle Hhandle h) op2 ret)) s2).
    Defined.

    Definition tens_lts : LTS (RelaxedSig.Tens.omap E1 E2 Hhandle) :=
      {|
        State := (State V1 * State V2)%type;
        Step := tens_step;
        Error := tens_error;
      |}.

    Lemma tens_step_i1 ev s1 s2 s1' s2' :
      Step tens_lts (thread_event_i1 ev) (s1, s2) (s1', s2') <->
      Step V1 ev s1 s1' /\ s2 = s2'.
    Proof.
      destruct ev as [t [h op | h op ret]]; reflexivity.
    Qed.

    Lemma tens_step_i2 ev s1 s2 s1' s2' :
      Step tens_lts (thread_event_i2 ev) (s1, s2) (s1', s2') <->
      Step V2 ev s2 s2' /\ s1 = s1'.
    Proof.
      destruct ev as [t [h op | h op ret]];
        unfold tens_lts; cbn;
        unfold tens_step; cbn;
        rewrite RelaxedSig.Tens.transport_handle_inverse;
        reflexivity.
    Qed.

    Lemma tens_error_i1 ev s1 s2 :
      Error tens_lts (thread_event_i1 ev) (s1, s2) <->
      Error V1 ev s1.
    Proof.
      destruct ev as [t [h op | h op ret]]; reflexivity.
    Qed.

    Lemma tens_error_i2 ev s1 s2 :
      Error tens_lts (thread_event_i2 ev) (s1, s2) <->
      Error V2 ev s2.
    Proof.
      destruct ev as [t [h op | h op ret]];
        unfold tens_lts; cbn;
        unfold tens_error; cbn;
        rewrite RelaxedSig.Tens.transport_handle_inverse;
        reflexivity.
    Qed.

  End Tensor.

  Notation "L1 ⊗ᵣᵥ[ H ] L2" := (tens_lts H L1 L2)
    (at level 40, H at next level, left associativity).

End RelaxedLTSSpec.
