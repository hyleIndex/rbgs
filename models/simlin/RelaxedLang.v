(** A coinductive language with explicit future invocation and wait. *)

Require Import Coq.Lists.List.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import LinCCAL.


Module RelaxedLang.
  Import RelaxedSig.

  (** [FutureRef E A] is a statically typed view of a raw future handle.
      The operation stored in the reference determines the response type
      [A]; the operational semantics still uses the raw handle to match the
      invocation and response events. *)
  Inductive FutureRef (E : RelaxedSig.t) : Type -> Type :=
  | MkFutureRef
      (op : Sig.op (RelaxedSig.effect E))
      (h : RelaxedSig.handle E) :
      FutureRef E (Sig.ar op).

  Arguments FutureRef _ _ : clear implicits.
  Arguments MkFutureRef {E} _ _.

  Definition future_handle {E A} (f : FutureRef E A) :
      RelaxedSig.handle E :=
    match f with
    | MkFutureRef _ h => h
    end.

  Definition future_op {E A} (f : FutureRef E A) :
      Sig.op (RelaxedSig.effect E) :=
    match f with
    | MkFutureRef op _ => op
    end.

  (** [Future op k] emits the invocation of [op], allocates a fresh raw
      handle, and passes its typed reference to [k] without waiting for a
      response.  [Wait f k] is the explicit synchronization point: it waits
      for [f] and passes the response to [k].

      [FutureD op deps k] is the dependency-tagged invocation (WSC edit,
      2026-09-28): [deps] names the raw handles whose responses the
      invocation depends on, i.e. the tag [D] of the paper's
      [x <- ?(e(v))]: the handles the arguments were computed from (data
      and address dependencies) and, for a control-ordered operation, the
      handles the enclosing branches were decided by (control
      dependencies, the paper's [kappa]) and the handles earlier address
      arguments were computed from (the paper's [A], the counterpart of the
      hardware ordering [addr;po;[W]]).  In this shallow embedding values
      flow through Coq-level binding, so the tag cannot be computed by the
      semantics from the program text as the paper's [depof] does; it is
      part of the compiled program.  The tag is consulted only by the
      module-level scheduler ([RelaxedModuleSemantics.select_frontier_tagged]):
      an invocation may be emitted before every earlier response of its
      thread that it is not tagged with.

      An untagged [Future op k] is the conservative tag "every handle
      resolved so far", which recovers the positional reading in which a
      response precedes every later invocation of the same method. *)
  CoInductive Prog (E : RelaxedSig.t) (R : Type) : Type :=
  | Future
      (op : Sig.op (RelaxedSig.effect E))
      (k : FutureRef E (Sig.ar op) -> Prog E R)
  | FutureD
      (op : Sig.op (RelaxedSig.effect E))
      (deps : RelaxedSig.handle E -> Prop)
      (k : FutureRef E (Sig.ar op) -> Prog E R)
  | Wait
      (A : Type)
      (f : FutureRef E A)
      (k : A -> Prog E R)
  | Ret (r : R)
  | Tau (p : Prog E R).

  Arguments Prog _ _ : clear implicits.
  Arguments Future {E R} _ _.
  Arguments FutureD {E R} _ _ _.
  Arguments Wait {E R A} _ _.
  Arguments Ret {E R} _.
  Arguments Tau {E R} _.

  (** A one-layer observation function, used to unfold guarded
      [CoFixpoint] definitions in proofs. *)
  Definition PP {E R} (p : Prog E R) : Prog E R :=
    match p with
    | Future op k => Future op k
    | FutureD op deps k => FutureD op deps k
    | Wait f k => Wait f k
    | Ret r => Ret r
    | Tau p' => Tau p'
    end.

  Lemma PPid {E R} : forall p : Prog E R, p = PP p.
  Proof.
    intros p. destruct p; reflexivity.
  Qed.

  Definition skip {E} : Prog E unit := Ret tt.

  CoFixpoint bindProg {E A B}
      (p : Prog E A) (k : A -> Prog E B) : Prog E B :=
    match p with
    | Future op k' =>
        Future op (fun f => bindProg (k' f) k)
    | FutureD op deps k' =>
        FutureD op deps (fun f => bindProg (k' f) k)
    | Wait f k' =>
        Wait f (fun x => bindProg (k' x) k)
    | Ret a => k a
    | Tau p' => Tau (bindProg p' k)
    end.

  Lemma bindFutureUnfold {E A B} :
    forall op k' (k : A -> Prog E B),
      bindProg (Future op k') k =
      Future op (fun f => bindProg (k' f) k).
  Proof.
    intros.
    rewrite PPid at 1.
    unfold PP, bindProg.
    reflexivity.
  Qed.

  Lemma bindFutureDUnfold {E A B} :
    forall op deps k' (k : A -> Prog E B),
      bindProg (FutureD op deps k') k =
      FutureD op deps (fun f => bindProg (k' f) k).
  Proof.
    intros.
    rewrite PPid at 1.
    unfold PP, bindProg.
    reflexivity.
  Qed.

  Lemma bindWaitUnfold {E A B X} :
    forall (f : FutureRef E X) k' (k : A -> Prog E B),
      bindProg (Wait f k') k =
      Wait f (fun x => bindProg (k' x) k).
  Proof.
    intros.
    rewrite PPid at 1.
    unfold PP, bindProg.
    reflexivity.
  Qed.

  Lemma bindRetUnfold {E A B} :
    forall a (k : A -> Prog E B),
      bindProg (Ret a) k = k a.
  Proof.
    intros.
    rewrite PPid.
    rewrite PPid at 1.
    unfold PP, bindProg.
    reflexivity.
  Qed.

  Lemma bindTauUnfold {E A B} :
    forall p (k : A -> Prog E B),
      bindProg (Tau p) k = Tau (bindProg p k).
  Proof.
    intros.
    rewrite PPid at 1.
    unfold PP, bindProg.
    reflexivity.
  Qed.

  (** Primitive programs corresponding to the two explicit commands. *)
  Definition future {E} (op : Sig.op (RelaxedSig.effect E)) :
      Prog E (FutureRef E (Sig.ar op)) :=
    Future op (fun f => Ret f).

  (** A tagged invocation.  [deps] is a predicate on raw handles; typical
      tags are [fun q => q = future_handle f] (a data dependency on the
      future [f]) and [fun _ => False] (no dependency at all). *)
  Definition futureD {E} (op : Sig.op (RelaxedSig.effect E))
      (deps : RelaxedSig.handle E -> Prop) :
      Prog E (FutureRef E (Sig.ar op)) :=
    FutureD op deps (fun f => Ret f).

  (** The tag "depends on the futures [fs]". *)
  Definition deps_of {E} (fs : list (RelaxedSig.handle E)) :
      RelaxedSig.handle E -> Prop :=
    fun q => In q fs.

  Definition wait {E A} (f : FutureRef E A) : Prog E A :=
    Wait f (fun x => Ret x).

  (** The old blocking operation is recovered by immediately waiting for
      the future returned by the invocation. *)
  Definition call {E} (op : Sig.op (RelaxedSig.effect E)) :
      Prog E (Sig.ar op) :=
    Future op (fun f => Wait f (fun r => Ret r)).

  Declare Scope relaxed_prog_scope.
  Bind Scope relaxed_prog_scope with Prog.
  Delimit Scope relaxed_prog_scope with RProg.

  Notation "'future' m >= h => p" :=
    (Future m (fun h => p))
    (at level 70, h binder, right associativity) : relaxed_prog_scope.

  Notation "'future' m [ d ] >= h => p" :=
    (FutureD m d (fun h => p))
    (at level 70, h binder, right associativity) : relaxed_prog_scope.

  Notation "'wait' h >= x => p" :=
    (Wait h (fun x => p))
    (at level 70, x binder, right associativity) : relaxed_prog_scope.

  Notation "p1 p>= x => p2" :=
    (bindProg p1 (fun x => p2))
    (at level 69, x binder, right associativity) : relaxed_prog_scope.

  Notation "p1 ;; p2" :=
    (bindProg p1 (fun _ => p2))
    (at level 65, right associativity) : relaxed_prog_scope.

End RelaxedLang.


Definition RelaxedModuleImpl
    (E F : RelaxedSig.t) : Type :=
  forall op : Sig.op (RelaxedSig.effect F),
    LinCCAL.tid -> RelaxedLang.Prog E (Sig.ar op).

Arguments RelaxedModuleImpl _ _ : clear implicits.
