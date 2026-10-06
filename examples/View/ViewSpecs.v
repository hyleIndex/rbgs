(** Ported from CSL-Lin [examples/Specs.v] (hyleIndex/CSL-Lin, master 3f7baaa).
    View-based (timestamped) specification / proof, kept as close to the
    original as possible; changes are limited to the Rocq 9.2 / rbgs
    adaptation listed in [examples/View/README.md].
    Only the modules used by the view proofs are kept: [CASRegTSOSpec], [TryStackSpec], [StackSpec], [SeqLockUnderlaySpec], [SeqLock].
    [AtomicLTS] is the identical rbgs copy in [examples/Common/AtomicLTS.v]. *)

Require Import Stdlib.FSets.FMapPositive.
Require Import Stdlib.Relations.Relation_Operators Stdlib.Relations.Operators_Properties.
Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Program.Equality.
Require Import Stdlib.Arith.PeanoNat.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import examples.Common.AtomicLTS.

Module CASRegTSOSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.

  Notation Time := positive.

  Variant ECASReg_op {A} :=
  | get
  | cas (expected desired : A).
  Arguments ECASReg_op : clear implicits.

  Definition ECASReg_ar {A} (m : ECASReg_op A) : Type :=
    match m with
    | get => A
    | cas _ _ => bool
    end.

  Canonical Structure ECASReg A :=
  {|
    Sig.op := ECASReg_op A;
    Sig.ar := ECASReg_ar
  |}.

  Record SCASRegTSO (A : Type) : Type := mkCASRegTSO {
    cas_mem : Time -> A;
    cas_view : tid -> Time;
  }.
  Arguments mkCASRegTSO {A}.
  Arguments cas_mem {A}.
  Arguments cas_view {A}.

  Definition upd_tid_time (H : tid -> Time) (t : tid) (h : Time) : tid -> Time :=
    fun t' => if Pos.eqb t t' then h else H t'.

  Definition view_advance_all (h : Time) : tid -> Time :=
    fun _ => h.

  Definition mem_write {A} (mem : Time -> A) (h : Time) (v : A) : Time -> A :=
    fun h' => if Pos.leb h h' then v else mem h'.

  Variant StepCASRegTSO {A} : @ThreadEvent (ECASReg A) ->
      SCASRegTSO A -> SCASRegTSO A -> Prop :=
  | step_get_inv t s :
      StepCASRegTSO {| te_tid := t; te_ev := InvEv get |} s s
  | step_get_res t v h s1 s2 :
      Pos.lt (cas_view s1 t) h ->
      v = cas_mem s1 h ->
      s2 = mkCASRegTSO
             (cas_mem s1)
             (upd_tid_time (cas_view s1) t h) ->
      StepCASRegTSO {| te_tid := t; te_ev := ResEv get v |} s1 s2

  | step_cas_inv t expected desired s :
      StepCASRegTSO {| te_tid := t; te_ev := InvEv (cas expected desired) |} s s
  | step_cas_success_res t expected desired h s1 s2 :
      (forall t0, Pos.lt (cas_view s1 t0) h) ->
      cas_mem s1 h = expected ->
      s2 = mkCASRegTSO
             (mem_write (cas_mem s1) h desired)
             (view_advance_all h) ->
      StepCASRegTSO
        {| te_tid := t; te_ev := ResEv (cas expected desired) true |} s1 s2
  | step_cas_fail_res t expected desired h s1 s2 :
      (forall t0, Pos.lt (cas_view s1 t0) h) ->
      cas_mem s1 h <> expected ->
      s2 = mkCASRegTSO
             (cas_mem s1)
             (view_advance_all h) ->
      StepCASRegTSO
        {| te_tid := t; te_ev := ResEv (cas expected desired) false |} s1 s2.

  Definition VCASRegTSO {A} : @LTS (ECASReg A) := VAE StepCASRegTSO NoError.

End CASRegTSOSpec.

Module TryStackSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  
  Variant ETryStack_op {A} :=
  | push (v : A)
  | pop.
  Arguments ETryStack_op : clear implicits.

  Variant TryResult {A} : Type :=
  | OK (v : A)
  | FAIL.
  Arguments TryResult : clear implicits.

  Definition ETryStack_ar {A} (m : ETryStack_op A) : Type :=
    match m with
      | push _ => TryResult unit
      | pop => TryResult (option A)
    end.
  
  Canonical Structure ETryStack A :=
  {|
    Sig.op := ETryStack_op A;
    Sig.ar := ETryStack_ar
  |}.

  Variant StepTryStack {A} : @ThreadEvent (ETryStack A) -> list A -> list A -> Prop :=
  | step_push_inv t stk v : StepTryStack {| te_tid := t; te_ev := InvEv (push v) |} stk stk
  | step_push_ok t stk v e : 
      e = ResEv (push v) (OK tt) ->
      StepTryStack {| te_tid := t; te_ev := e |} stk (v :: stk)
  | step_push_fail t stk v e :
      e = ResEv (push v) FAIL ->
      StepTryStack {| te_tid := t; te_ev := e |} stk stk

  | step_pop_inv t stk : StepTryStack {| te_tid := t; te_ev := InvEv pop |} stk stk
  | step_pop_emp t e:
      e = ResEv pop (OK None) ->
      StepTryStack {| te_tid := t; te_ev := e |} nil nil
  | step_pop_ok t v stk e :
      e = ResEv pop (OK (Some v)) ->
      StepTryStack {| te_tid := t; te_ev := e |} (v :: stk) stk
  | step_pop_fail t stk e:
      e = ResEv pop FAIL ->
      StepTryStack {| te_tid := t; te_ev := e |} stk stk.
  
  Definition VTryStack {A} : @LTS (ETryStack A) := VAE StepTryStack NoError.

End TryStackSpec.

Module StackSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  
  Variant EStack_op {A} :=
  | push (v : A)
  | pop.
  Arguments EStack_op : clear implicits.

  Definition EStack_ar {A} (m : EStack_op A) : Type :=
    match m with
      | push _ => unit
      | pop => option A
    end.
  
  Canonical Structure EStack A :=
  {|
    Sig.op := EStack_op A;
    Sig.ar := EStack_ar
  |}.

  Variant StepStack {A} : @ThreadEvent (EStack A) -> list A -> list A -> Prop :=
  | step_push_inv t stk v : StepStack {| te_tid := t; te_ev := InvEv (push v) |} stk stk
  | step_push_res t stk v : StepStack {| te_tid := t; te_ev := ResEv (push v) tt |} stk (v :: stk)

  | step_pop_inv t stk : StepStack {| te_tid := t; te_ev := InvEv pop |} stk stk
  | step_pop_emp t : StepStack {| te_tid := t; te_ev := ResEv pop None |} nil nil
  | step_pop_res t v stk : StepStack {| te_tid := t; te_ev := ResEv pop (Some v) |} (v :: stk) stk.
  
  Definition VStack {A} : @LTS (EStack A) := VAE StepStack NoError.

End StackSpec.

Module SeqLockUnderlaySpec.

  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.

  (* ------------------------------------------------------------------ *)
  (** ** Time: dense linear order
      We use [positive] as the timestamp domain, which is dense: for
      any [a < b] (under [Pos.lt]) there exist infinitely many [c] with
      [a < c < b], so a fresh timestamp strictly above any finite
      frontier always exists. *)

  Notation Time := positive.

  (* ------------------------------------------------------------------ *)
  (** ** Locations *)

  (** Memory locations {x, y} *)
  Variant MemLoc : Type := loc_x | loc_y.

  Definition MemLoc_eqb (l l' : MemLoc) : bool :=
    match l, l' with
    | loc_x, loc_x | loc_y, loc_y => true
    | _, _ => false
    end.

  (** All locations including the lock {x, y, lk} *)
  Variant AllLoc : Type := aloc_x | aloc_y | aloc_lk.

  Definition AllLoc_eqb (a a' : AllLoc) : bool :=
    match a, a' with
    | aloc_x, aloc_x | aloc_y, aloc_y | aloc_lk, aloc_lk => true
    | _, _ => false
    end.

  Definition mem_to_all (l : MemLoc) : AllLoc :=
    match l with loc_x => aloc_x | loc_y => aloc_y end.

  (* ------------------------------------------------------------------ *)
  (** ** View (TimeMap)
      A [View] is a function [AllLoc -> Time], recording per-location
      view frontiers for one thread.  *)

  Definition View : Type := AllLoc -> Time.

  (** Pointwise join (per-location max), i.e. [TimeMap.join] *)
  Definition view_join (v1 v2 : View) : View :=
    fun l => Pos.max (v1 l) (v2 l).

  (** Global frontier [H_bar(t)] = max over all locations *)
  Definition view_bar (v : View) : Time :=
    Pos.max (Pos.max (v aloc_x) (v aloc_y)) (v aloc_lk).

  (** [H(t)[l |-> h]]: set a single location to [h] *)
  Definition view_set (v : View) (l : AllLoc) (h : Time) : View :=
    fun l' => if AllLoc_eqb l l' then h else v l'.

  (** [lambda l'. max(H(t,l'), h)]: advance all locations to at least [h] *)
  Definition view_advance (v : View) (h : Time) : View :=
    fun l' => Pos.max (v l') h.

  (** Update thread [t]'s view; keep all other threads unchanged *)
  Definition upd_tid_view (H : tid -> View) (t : tid) (v' : View) : tid -> View :=
    fun t' => if Pos.eqb t t' then v' else H t'.

  (* ------------------------------------------------------------------ *)
  (** ** Shared state: memory and lock histories
      Both are modelled as functions from [Time] to values, encoding the
      full write history.  Writes use [f[>= h |-> w]] which overwrites
      every timestamp at or above [h]. *)

  (** [mem(l)(h)]: value at memory location [l] written at timestamp [h] *)
  Definition Mem := MemLoc -> Time -> nat.

  (** [lock(h) = (nxt, own)]: lock state at timestamp [h] *)
  Definition LockHist := Time -> nat * nat.

  (** [mem[l := mem(l)[>= h |-> w]]]: overwrite [l]'s history at [h] *)
  Definition mem_write (mem : Mem) (l : MemLoc) (h : Time) (w : nat) : Mem :=
    fun l' h' => if andb (MemLoc_eqb l l') (Pos.leb h h') then w else mem l' h'.

  (** [lock[>= h |-> (nxt', own')]]: overwrite lock history at [h] *)
  Definition lock_write (lk : LockHist) (h : Time) (nxt' own' : nat) : LockHist :=
    fun h' => if Pos.leb h h' then (nxt', own') else lk h'.

  (* ------------------------------------------------------------------ *)
  (** ** Operation signature *)

  Variant ESeqLockUL_op : Type :=
  | wrt        (l : MemLoc) (w : nat)   (** write [w] to memory location [l]      *)
  | rd         (l : MemLoc)              (** read from memory location [l]          *)
  | acq                                  (** acquire the seqlock                    *)
  | rel                                  (** release the seqlock                    *)
  | get_ticket                           (** read the [own] counter from the lock   *)
  | test_ticket (n : nat).               (** test if lock is busy; expected nxt = n *)

  Definition ESeqLockUL_ar (m : ESeqLockUL_op) : Type :=
    match m with
    | wrt _ _       => unit
    | rd _          => nat
    | acq           => unit
    | rel           => unit
    | get_ticket    => nat
    | test_ticket _ => bool
    end.

  Canonical Structure ESeqLockUL :=
  {|
    Sig.op := ESeqLockUL_op;
    Sig.ar := ESeqLockUL_ar;
  |}.

  (* ------------------------------------------------------------------ *)
  (** ** State type: [(sigma, H)] *)

  Record SSeqLockUL : Type := mkSLUL {
    sl_mem  : Mem;         (** shared memory history         *)
    sl_lock : LockHist;    (** shared lock history           *)
    sl_view : tid -> View; (** per-thread view frontiers H   *)
    sl_owner : option tid; (** ghost: unique lock owner      *)
  }.

  (** [H_bar(t)]: global frontier for thread [t] *)
  Definition H_bar (s : SSeqLockUL) (t : tid) : Time :=
    view_bar (sl_view s t).

  (* ------------------------------------------------------------------ *)
  (** ** Step relation
      Each rule is split into an invocation step (no state change) and a
      response step (state update + return value).  All preconditions and
      effects are placed at the response step, following AtomicLTS. *)

  Variant StepSeqLockUL : @ThreadEvent ESeqLockUL -> SSeqLockUL -> SSeqLockUL -> Prop :=

  (** [Wrt]: write [w] to [l] at a fresh timestamp [h > H_bar(t)].
      Effect: [mem[l, >=h |-> w]]; [H(t)[l |-> h]]. *)
  | step_wrt_inv t l w s :
      StepSeqLockUL {| te_tid := t; te_ev := InvEv (wrt l w) |} s s
  | step_wrt_res t l w h s1 s2 :
      sl_owner s1 = Some t ->
      (forall t0, Pos.lt (H_bar s1 t0) h) ->
      s2 = mkSLUL
             (mem_write (sl_mem s1) l h w)
             (sl_lock s1)
             (upd_tid_view (sl_view s1) t
             (view_set (sl_view s1 t) (mem_to_all l) h))
           (sl_owner s1) ->
      StepSeqLockUL {| te_tid := t; te_ev := ResEv (wrt l w) tt |} s1 s2

  (** [Rd]: read [w] from [l] at [h > H(t,l)], where [w = mem(l)(h)].
      Effect: [H(t)[l' |-> max(H(t,l'), h)]] for all [l']. *)
  | step_rd_inv t l s :
      StepSeqLockUL {| te_tid := t; te_ev := InvEv (rd l) |} s s
  | step_rd_res t l w h s1 s2 :
      Pos.lt (sl_view s1 t (mem_to_all l)) h ->
      w = sl_mem s1 l h ->
      s2 = mkSLUL
             (sl_mem s1)
             (sl_lock s1)
             (upd_tid_view (sl_view s1) t
             (view_advance (sl_view s1 t) h))
           (sl_owner s1) ->
      StepSeqLockUL {| te_tid := t; te_ev := ResEv (rd l) w |} s1 s2

  (** [Acq]: acquire the seqlock.
      Precondition: [h > H_bar(t)]; [(nxt, own) = lock(H(t,lk))]; [nxt = own].
      Effect: [lock[>=h |-> (nxt+2, own+1)]]; [H(t)[lk |-> h]]. *)
  | step_acq_inv t s :
      StepSeqLockUL {| te_tid := t; te_ev := InvEv acq |} s s
  | step_acq_res t h nxt own s1 s2 :
      (forall t0, Pos.lt (H_bar s1 t0) h) ->
      sl_lock s1 (sl_view s1 t aloc_lk) = (nxt, own) ->
      nxt = own ->
      Nat.even nxt = true ->
      sl_owner s1 = None ->
      s2 = mkSLUL
             (sl_mem s1)
             (lock_write (sl_lock s1) h (nxt + 2) (own + 1))
             (upd_tid_view (sl_view s1) t
             (view_set (sl_view s1 t) aloc_lk h))
           (Some t) ->
      StepSeqLockUL {| te_tid := t; te_ev := ResEv acq tt |} s1 s2

  (** [Rel]: release the seqlock.
      Precondition: [h > H_bar(t)]; [(nxt, own) = lock(H(t,lk))].
      Effect: [lock[>=h |-> (nxt, own+1)]]; [H(t)[lk |-> h]]. *)
  | step_rel_inv t s :
      StepSeqLockUL {| te_tid := t; te_ev := InvEv rel |} s s
  | step_rel_res t h nxt own s1 s2 :
      (forall t0, Pos.lt (H_bar s1 t0) h) ->
      sl_lock s1 (sl_view s1 t aloc_lk) = (nxt, own) ->
      nxt = own + 1 ->
      Nat.even nxt = true ->
      sl_owner s1 = Some t ->
      s2 = mkSLUL
             (sl_mem s1)
             (lock_write (sl_lock s1) h nxt (own + 1))
           (fun t' => view_advance (sl_view s1 t') h)
           None ->
      StepSeqLockUL {| te_tid := t; te_ev := ResEv rel tt |} s1 s2

  (** [GetTick]: read the [own] field at [h > H(t,lk)]; return [k = own].
      Effect: [H(t)[l' |-> max(H(t,l'), h)]] for all [l']. *)
  | step_get_ticket_inv t s :
      StepSeqLockUL {| te_tid := t; te_ev := InvEv get_ticket |} s s
  | step_get_ticket_res t k h nxt s1 s2 :
      (forall t0, Pos.lt (H_bar s1 t0) h) ->
      sl_lock s1 h = (nxt, k) ->
      s2 = mkSLUL
             (sl_mem s1)
             (sl_lock s1)
             (upd_tid_view (sl_view s1) t
             (view_advance (sl_view s1 t) h))
           (sl_owner s1) ->
      StepSeqLockUL {| te_tid := t; te_ev := ResEv get_ticket k |} s1 s2

  (** [TestTick(n)]: read lock at [h > H(t,lk)] where [nxt = n]; return
      [b = (n & 1 <> 0) \/ (own <> n)], i.e. the lock is busy.
      Effect: [H(t)[l' |-> max(H(t,l'), h)]] for all [l']. *)
  | step_test_ticket_inv t n s :
      StepSeqLockUL {| te_tid := t; te_ev := InvEv (test_ticket n) |} s s
  | step_test_ticket_res t n k h b s1 s2 :
      (forall t0, Pos.lt (H_bar s1 t0) h) ->
      sl_lock s1 h = (n, k) ->
      b = orb (Nat.odd n) (negb (Nat.eqb k n)) ->
      s2 = mkSLUL
             (sl_mem s1)
             (sl_lock s1)
             (upd_tid_view (sl_view s1) t
          (view_advance (sl_view s1 t) h))
         (sl_owner s1) ->
      StepSeqLockUL {| te_tid := t; te_ev := ResEv (test_ticket n) b |} s1 s2
  .

  Definition VSeqLockUL : @LTS ESeqLockUL := VAE StepSeqLockUL NoError.

End SeqLockUnderlaySpec.

Module SeqLock.

  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.

  Notation Time := positive.

  (* ------------------------------------------------------------------ *)
  (** ** Operation signature *)

  Variant ESeqLock_op : Type :=
  | write (vx' vy' : nat)   (** atomically write new values [(vx', vy')] *)
  | read.                    (** atomically read current values [(vx, vy)] *)

  Definition ESeqLock_ar (m : ESeqLock_op) : Type :=
    match m with
    | write _ _ => unit
    | read      => nat * nat
    end.

  Canonical Structure ESeqLock :=
  {|
    Sig.op := ESeqLock_op;
    Sig.ar := ESeqLock_ar;
  |}.

  (* ------------------------------------------------------------------ *)
  (** ** State type: [(sigma_O, H^O)]
      [sigma_O = (vx, vy)] holds the current logical values.
      [H^O_t] is a *scalar* frontier per thread: since the overlay's
      independence relation is empty, all operations are totally ordered
      per thread, so a single timestamp suffices (no per-location split). *)

  Record SSeqLock : Type := mkSL {
    sl_vx   : nat;          (** current value at x           *)
    sl_vy   : nat;          (** current value at y           *)
    sl_view : tid -> Time;  (** per-thread scalar frontier   *)
  }.

  (** [H^O[t |-> h]]: update thread [t]'s frontier to [h] *)
  Definition upd_tid_time (H : tid -> Time) (t : tid) (h : Time) : tid -> Time :=
    fun t' => if Pos.eqb t t' then h else H t'.

  (* ------------------------------------------------------------------ *)
  (** ** Step relation *)

  Variant StepSeqLock : @ThreadEvent ESeqLock -> SSeqLock -> SSeqLock -> Prop :=

  (** [Write(vx', vy')]: atomically replace both values.
      Precondition: [h > H^O_t].
      Effect: [sigma_O := (vx', vy')]; [H^O[t |-> h]]. *)
  | step_write_inv t vx' vy' s :
      StepSeqLock {| te_tid := t; te_ev := InvEv (write vx' vy') |} s s
  | step_write_res t vx' vy' h s1 s2 :
      Pos.lt (sl_view s1 t) h ->
      s2 = mkSL vx' vy' (upd_tid_time (sl_view s1) t h) ->
      StepSeqLock {| te_tid := t; te_ev := ResEv (write vx' vy') tt |} s1 s2

  (** [Read]: atomically snapshot both values.
      Precondition: [h > H^O_t].
      Effect: [sigma_O] unchanged; [H^O[t |-> h]].
      Returns: [(vx, vy)]. *)
  | step_read_inv t s :
      StepSeqLock {| te_tid := t; te_ev := InvEv read |} s s
  | step_read_res t h s1 s2 :
      Pos.lt (sl_view s1 t) h ->
      s2 = mkSL (sl_vx s1) (sl_vy s1) (upd_tid_time (sl_view s1) t h) ->
      StepSeqLock {| te_tid := t; te_ev := ResEv read (sl_vx s1, sl_vy s1) |} s1 s2
  .

  Definition VSeqLock : @LTS ESeqLock := VAE StepSeqLock NoError.

End SeqLock.
