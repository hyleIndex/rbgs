(* Relaxed effect signatures. *)

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import models.EffectSignatures.


Module RelaxedSig.

  (** ** Fence modes *)

  Variant FenceMode : Type :=
  | Local
  | LFence
  | RFence
  | Fence.

  Definition fence_le (m1 m2 : FenceMode) : Prop :=
    match m1, m2 with
    | Local, _ => True
    | LFence, LFence
    | LFence, Fence
    | RFence, RFence
    | RFence, Fence
    | Fence, Fence => True
    | _, _ => False
    end.

  Infix "≤f" := fence_le (at level 70).

  Lemma fence_le_refl : Reflexive fence_le.
  Proof.
    intros []; exact I.
  Qed.

  Lemma fence_le_trans : Transitive fence_le.
  Proof.
    intros [] [] [] H12 H23; exact I || contradiction.
  Qed.

  #[global] Instance fence_le_preorder : PreOrder fence_le.
  Proof.
    split.
    - exact fence_le_refl.
    - exact fence_le_trans.
  Qed.

  Lemma fence_le_antisym :
    forall m1 m2, m1 ≤f m2 -> m2 ≤f m1 -> m1 = m2.
  Proof.
    intros [] [] H12 H21; reflexivity || contradiction.
  Qed.

  (** ** Relaxed signatures *)

  Record t : Type := {
    effect : Sig.t;
    handle : Type;
    semi_independent : relation (Sig.op effect);
    mode : Sig.op effect -> FenceMode;
  }.

  Arguments effect _ : clear implicits.
  Arguments handle _ : clear implicits.
  Arguments semi_independent _ _ _ : assert.
  Arguments mode _ _ : assert.

  Coercion effect : t >-> Sig.t.

  Definition invocation (E : t) : Type := Sig.op (effect E).

  Record well_formed (E : t) : Prop := {
    semi_independent_irreflexive :
      Irreflexive (semi_independent E);

    semi_independent_left_compatible :
      forall e1 e2,
        semi_independent E e1 e2 ->
        mode E e1 ≤f LFence;

    semi_independent_right_compatible :
      forall e1 e2,
        semi_independent E e1 e2 ->
        mode E e2 ≤f RFence;
  }.

  Arguments semi_independent_irreflexive {E} _ _.
  Arguments semi_independent_left_compatible {E} _ _ _ _.
  Arguments semi_independent_right_compatible {E} _ _ _ _.

  (** ** Tensor product *)

  Module Tens.

    (** The semi-independence relation of [E ⊗ F] contains the original
        relations of both components.  A cross-component pair is
        semi-independent exactly when the mode of the first invocation is
        at most [LFence] and the mode of the second is at most [RFence]. *)
    Inductive tensor_semi_independent (E F : t) :
      relation
        (Sig.op (Sig.Plus.omap (effect E) (effect F))) :=
    | tsi_left e1 e2
        (Hind : semi_independent E e1 e2) :
        tensor_semi_independent E F (inl e1) (inl e2)
    | tsi_right f1 f2
        (Hind : semi_independent F f1 f2) :
        tensor_semi_independent E F (inr f1) (inr f2)
    | tsi_cross_lr e f
        (Hleft : mode E e ≤f LFence)
        (Hright : mode F f ≤f RFence) :
        tensor_semi_independent E F (inl e) (inr f)
    | tsi_cross_rl f e
        (Hleft : mode F f ≤f LFence)
        (Hright : mode E e ≤f RFence) :
        tensor_semi_independent E F (inr f) (inl e).

    Definition tensor_mode (E F : t) :
      Sig.op (Sig.Plus.omap (effect E) (effect F)) -> FenceMode :=
      fun m =>
        match m with
        | inl e => mode E e
        | inr f => mode F f
        end.

    (** Horizontal composition does not allocate a disjoint sum of handle
        names.  Both components must use the same handle set, which remains
        the handle set of the composite signature. *)
    Definition omap (E F : t)
        (Hhandle : handle E = handle F) : t :=
      {|
        effect := Sig.Plus.omap (effect E) (effect F);
        handle := handle E;
        semi_independent := tensor_semi_independent E F;
        mode := tensor_mode E F;
      |}.

    Definition op_i1 {E F : t} {Hhandle : handle E = handle F} :
      invocation E -> invocation (omap E F Hhandle) :=
      @inl (invocation E) (invocation F).

    Definition op_i2 {E F : t} {Hhandle : handle E = handle F} :
      invocation F -> invocation (omap E F Hhandle) :=
      @inr (invocation E) (invocation F).

    Definition transport_handle {A B : Type}
        (H : A = B) (h : A) : B :=
      match H with
      | eq_refl => h
      end.

    Lemma transport_handle_inverse {A B : Type}
        (H : A = B) (h : B) :
      transport_handle H (transport_handle (eq_sym H) h) = h.
    Proof.
      destruct H; reflexivity.
    Qed.

    Lemma transport_handle_inverse_sym {A B : Type}
        (H : A = B) (h : A) :
      transport_handle (eq_sym H) (transport_handle H h) = h.
    Proof.
      destruct H; reflexivity.
    Qed.

    Definition handle_i1 {E F : t}
        {Hhandle : handle E = handle F} :
      handle E -> handle (omap E F Hhandle) :=
      fun h => h.

    Definition handle_i2 {E F : t}
        {Hhandle : handle E = handle F} :
      handle F -> handle (omap E F Hhandle) :=
      transport_handle (eq_sym Hhandle).

    Lemma omap_preserves_handle_set (E F : t)
        (Hhandle : handle E = handle F) :
      handle (omap E F Hhandle) = handle E.
    Proof.
      reflexivity.
    Qed.

    Lemma omap_well_formed (E F : t)
        (Hhandle : handle E = handle F) :
      well_formed E ->
      well_formed F ->
      well_formed (omap E F Hhandle).
    Proof.
      intros HE HF.
      constructor.
      - intros [e | f] Hind.
        + inversion Hind; subst.
          eapply (semi_independent_irreflexive HE); eauto.
        + inversion Hind; subst.
          eapply (semi_independent_irreflexive HF); eauto.
      - intros [e1 | f1] [e2 | f2] Hind;
          inversion Hind; subst; cbn in *.
        + eapply semi_independent_left_compatible; eauto.
        + assumption.
        + assumption.
        + eapply semi_independent_left_compatible; eauto.
      - intros [e1 | f1] [e2 | f2] Hind;
          inversion Hind; subst; cbn in *.
        + eapply semi_independent_right_compatible; eauto.
        + assumption.
        + assumption.
        + eapply semi_independent_right_compatible; eauto.
    Qed.

    (** The tensor unit has no operations but shares the ambient handle set. *)
    Definition unit (A : Type) : t :=
      {|
        effect := Sig.Plus.unit;
        handle := A;
        semi_independent := fun e => match e with end;
        mode := fun e => match e with end;
      |}.

    Lemma unit_well_formed (A : Type) :
      well_formed (unit A).
    Proof.
      constructor; intros [].
    Qed.

  End Tens.

  Declare Scope relaxed_sig_scope.
  Bind Scope relaxed_sig_scope with t.
  Delimit Scope relaxed_sig_scope with rsig.

  Notation "E ⊗ᵣ[ H ] F" := (Tens.omap E F H)
    (at level 40, H at next level, left associativity) : relaxed_sig_scope.

  Definition sc (E : Sig.t) (A : Type) : t :=
    {|
      effect := E;
      handle := A;
      semi_independent := fun _ _ => False;
      mode := fun _ => Fence;
    |}.

  Lemma sc_well_formed (E : Sig.t) (A : Type) :
    well_formed (sc E A).
  Proof.
    constructor; cbn.
    - intros e Hee. contradiction.
    - intros e1 e2 Hind. contradiction.
    - intros e1 e2 Hind. contradiction.
  Qed.

End RelaxedSig.
