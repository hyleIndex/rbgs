(** Examples for the dependency frontier (weak sequential composition):
    a read that follows a wait but does not use its value may be issued
    before the awaited response, while a write that uses the value may not.

    This is the "MP + data-then-load" shape (L11 of the model comparison):
    [r <- rd(x); wrt(u, r); rd(y)].  Under the positional frontier the
    response of [rd(x)] is a barrier for [rd(y)]; under the dependency
    frontier only [wrt(u, r)] is ordered after it. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.PArith.PArith.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.

Import ListNotations.


Module DependencyFrontierExamples.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.

  (** ** A three-location relaxed memory signature *)

  Inductive Location : Type := X | U | Y.

  Inductive MemoryOp : Type :=
  | MRead (location : Location)
  | MWrite (location : Location) (value : nat).

  Definition memory_arity (op : MemoryOp) : Type :=
    match op with
    | MRead _ => nat
    | MWrite _ _ => unit
    end.

  Canonical Structure MemoryEffect : Sig.t :=
    {| Sig.op := MemoryOp; Sig.ar := memory_arity |}.

  Definition op_location (op : MemoryOp) : Location :=
    match op with
    | MRead l => l
    | MWrite l _ => l
    end.

  (** All accesses relaxed: two operations are semi-independent iff they
      touch different locations (the [I_RC] relation with every mode
      [rlx]). *)
  Definition rlx_independent (older later : MemoryOp) : Prop :=
    op_location older <> op_location later.

  Definition RlxSig : RelaxedSig.t :=
    {|
      RelaxedSig.effect := MemoryEffect;
      RelaxedSig.handle := nat;
      RelaxedSig.semi_independent := rlx_independent;
      RelaxedSig.mode := fun _ => Local;
    |}.

  Definition thread_two : tid := 2%positive.

  (** ** The program of thread 2, with dependency tags

      [r <- rd(x); wrt(u, r); rd(y)]: the write is tagged with the handle of
      the read it uses; the second read carries no dependency. *)
  Definition data_then_load : Prog RlxSig unit :=
    @FutureD RlxSig unit (MRead X) no_deps (fun fx =>
    Wait fx (fun r =>
    @FutureD RlxSig unit (MWrite U r) (fun q => q = future_handle fx) (fun fu =>
    @FutureD RlxSig unit (MRead Y) no_deps (fun fy =>
    Wait fy (fun _ =>
    Wait fu (fun _ => Ret tt)))))).

  Definition ev (e : Event RlxSig) : ThreadEvent RlxSig :=
    Build_ThreadEvent thread_two e.

  Definition inv_rd_x : ThreadEvent RlxSig := ev (@InvEv RlxSig 0 (MRead X)).
  Definition res_rd_x (v : nat) : ThreadEvent RlxSig := ev (@ResEv RlxSig 0 (MRead X) v).
  Definition inv_wr_u (v : nat) : ThreadEvent RlxSig := ev (@InvEv RlxSig 1 (MWrite U v)).
  Definition res_wr_u (v : nat) : ThreadEvent RlxSig := ev (@ResEv RlxSig 1 (MWrite U v) tt).
  Definition inv_rd_y : ThreadEvent RlxSig := ev (@InvEv RlxSig 2 (MRead Y)).
  Definition res_rd_y (v : nat) : ThreadEvent RlxSig := ev (@ResEv RlxSig 2 (MRead Y) v).

  (** The local semantics produces the tagged list in program order; the
      tag of the write contains the read's handle [0], the tags of the reads
      are empty. *)
  Example data_then_load_trace (v w : nat) :
    exists trace,
      program_produces_tagged thread_two data_then_load trace tt /\
      map untag trace = [inv_rd_x; res_rd_x v; inv_wr_u v; inv_rd_y; res_rd_y w; res_wr_u v] /\
      (forall m, In m trace -> te_ev _ (untag m) = @InvEv RlxSig 1 (MWrite U v) -> tev_deps m 0) /\
      (forall m q, In m trace -> te_ev _ (untag m) = @InvEv RlxSig 2 (MRead Y) -> ~ tev_deps m q).
  Proof.
    eexists. split; [| split; [| split]].
    - unfold program_produces_tagged, initial_program, data_then_load.
      eexists. split.
      + eapply tagged_execution_emit.
        * apply tagged_futureD with (h := 0). unfold handle_fresh. cbn. tauto.
        * eapply tagged_execution_emit.
          -- apply (@tagged_wait_pending RlxSig unit thread_two (MRead X) 0 v). apply resolve_here.
          -- cbn. eapply tagged_execution_emit.
             ++ apply tagged_futureD with (h := 1). unfold handle_fresh. cbn.
                intros [Heq | []]. discriminate.
             ++ eapply tagged_execution_emit.
                ** apply tagged_futureD with (h := 2). unfold handle_fresh. cbn.
                   intros [Heq | [Heq | []]]; discriminate.
                ** eapply tagged_execution_emit.
                   --- apply (@tagged_wait_pending RlxSig unit thread_two (MRead Y) 2 w). apply resolve_here.
                   --- eapply tagged_execution_emit.
                       +++ apply (@tagged_wait_pending RlxSig unit thread_two (MWrite U v) 1 tt).
                           eapply resolve_next; [discriminate |]. apply resolve_here.
                       +++ apply tagged_execution_refl.
      + apply program_terminal_ret. repeat constructor.
    - reflexivity.
    - intros m Hm Hev. cbn in Hm.
      destruct Hm as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn in Hev; try discriminate.
      cbn. split; [reflexivity |]. exists (MRead X), v. cbn. left. reflexivity.
    - intros m q Hm Hev. cbn in Hm.
      destruct Hm as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn in Hev; try discriminate.
      cbn. unfold no_deps. tauto.
  Qed.

  (** ** The frontier on the scheduled queue *)

  Definition owner : CallKey RlxSig := (thread_two, 10).

  Definition tagged (e : ThreadEvent RlxSig) (d : RelaxedSig.handle RlxSig -> Prop) :
      TaggedScheduledEvent RlxSig RlxSig :=
    Build_TaggedScheduledEvent owner (Build_TaggedEvent e d).

  Definition q_rd_x : TaggedScheduledEvent RlxSig RlxSig := tagged inv_rd_x (@no_deps RlxSig).
  Definition q_res_x (v : nat) : TaggedScheduledEvent RlxSig RlxSig := tagged (res_rd_x v) (@no_deps RlxSig).
  Definition q_wr_u (v : nat) : TaggedScheduledEvent RlxSig RlxSig := tagged (inv_wr_u v) (fun q => q = 0).
  Definition q_rd_y : TaggedScheduledEvent RlxSig RlxSig := tagged inv_rd_y (@no_deps RlxSig).

  Definition queue (v : nat) : TaggedQueue RlxSig RlxSig :=
    [q_rd_x; q_res_x v; q_wr_u v; q_rd_y].

  (** [rd(y)] may be emitted first: it is semi-independent of [rd(x)] and
      of [wrt(u, r)] (F2), and it is not tagged with the response of [rd(x)]
      (F3). *)
  Example load_overtakes_wait (v : nat) :
    select_frontier_tagged q_rd_y (queue v) [q_rd_x; q_res_x v; q_wr_u v].
  Proof.
    unfold queue.
    apply tagged_select_next.
    { right. split; [reflexivity |]. cbn. intros H. apply H. discriminate. }
    apply tagged_select_next.
    { right. split; [reflexivity |]. cbn. unfold no_deps. tauto. }
    apply tagged_select_next.
    { right. split; [reflexivity |]. cbn. intros H. apply H. discriminate. }
    apply tagged_select_here.
  Qed.

  (** [wrt(u, r)] may not overtake the response it depends on (F3). *)
  Example dependent_store_waits (v : nat) queue' :
    ~ select_frontier_tagged (q_wr_u v) (queue v) queue'.
  Proof.
    intros Hsel. unfold queue in Hsel.
    inversion Hsel as [| ? ? ? Hcross Hsel']; subst.
    inversion Hsel' as [| ? ? ? Hcross' Hsel'']; subst.
    destruct Hcross' as [Hneq | [_ Hno]]; [apply Hneq; reflexivity |].
    apply Hno. cbn. reflexivity.
  Qed.

  (** Under the positional frontier the same read is blocked by the
      response. *)
  Example positional_frontier_blocks_the_load (v : nat) :
    ~ select_frontier (untag_scheduled q_rd_y)
        (map untag_scheduled (queue v))
        (map untag_scheduled [q_rd_x; q_res_x v; q_wr_u v]).
  Proof.
    intros Hsel. cbn in Hsel.
    inversion Hsel as [| ? ? ? Hcross Hsel']; subst.
    inversion Hsel' as [| ? ? ? Hcross' Hsel'']; subst.
    destruct Hcross' as [Hneq | [_ Hind]]; [apply Hneq; reflexivity | exact Hind].
  Qed.

  (** And a response is not a barrier for anything but the invocations
      tagged with it: the untagged read may even be emitted before the
      response of a read it was issued after. *)
  Example response_is_not_a_barrier (v : nat) :
    select_frontier_tagged q_rd_y [q_res_x v; q_rd_y] [q_res_x v].
  Proof.
    apply tagged_select_next.
    { right. split; [reflexivity |]. cbn. unfold no_deps. tauto. }
    apply tagged_select_here.
  Qed.

End DependencyFrontierExamples.
