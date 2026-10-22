(** * The ticket-lock tower over TSO: interfaces

    Three objects, each given as [ViewLift] parameters, and the two ghost
    presentations used by the proofs.

    [TSO memory  --M_TL-->  ticket lock with data  --M_SL-->  record]

    - [MemHW]: the memory with locations [l_nxt], [l_own], [l_x], [l_y].
      Reads are retroactive, writes and fetch-and-add are appended, and
      nothing synchronizes.  A write followed by a read of another
      location is unordered (TSO's store buffer); every other pair of
      operations of a thread is ordered.  This is the TSO table of
      [ViewLiftMultiWriter.tdep] plus fetch-and-add.  Like every
      timeline presentation here it is not complete for x86-TSO: it has
      no store forwarding ([ViewLiftOMCA.n6_mp_inseparable]), and writes
      enter the timeline in the order of their responses
      ([ViewLiftMultiWriter.no_issue_order_run]).
    - [TLC]: a ticket lock with the two data cells it protects.  The
      state is the version [tv] ([l_own] in the implementation), the
      holder, and the data.  When [tv] is even the lock is free and [tv]
      is the next ticket to be served; when it is odd the lock is held by
      ticket [tv - 1].  [tacq] and [trel] increment the version and are
      appended; [tgt] (the version) and [tdr] (a data read) are
      retroactive; [tdw] (a data write) is appended.  [trel] and [tdw] are
      errors unless the caller holds the lock.  The dependency table is
      the one the memory induces when every operation is timestamped at
      its access to [l_own] or to the data ([tl_dep]).
      Limitation: a data read is not ordered after the reader's own
      [tacq] ([tl_dep tacq (tdr _) = false]), although the implementation
      orders it after the read that saw the turn.  So over [TLC] a holder
      may read data older than the last release, and a client that reads
      data under the lock cannot be verified.  The SeqLock's writer does
      not read.
    - [RecP]: a record of two numbers.  [rwrite] is appended, [rread] is
      retroactive, nothing synchronizes, all pairs are ordered.  A read
      may return an overwritten record (a stale snapshot).

    Ghost presentations ([ViewLiftGhost.PG]):

    - [MemHWg]: the memory, plus the owner of each ticket handed out by a
      fetch-and-add on [l_nxt].  Used only by the proof of [M_TL].
    - [TLCm]: the lock, plus the data published by its last release
      ([rel_up]).  Used only by the proof of [M_SL].

    So the ticket lock has two presentations: [TLC] in its implementation
    proof and [TLCm] in its client's proof.  The client's proof does not
    need the ghost ([TicketTowerSeqLock]). *)

Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.micromega.Lia.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import models.view.ViewLift.
Require Import models.view.ViewLiftGhost.

Module TicketTowerSpecs.
  Import Reg LinCCALBase ViewLift.

  (** ** TSO memory *)

  Variant Loc : Type := l_nxt | l_own | l_x | l_y.

  Definition loc_eqb (a b : Loc) : bool :=
    match a, b with
    | l_nxt, l_nxt | l_own, l_own | l_x, l_x | l_y, l_y => true
    | _, _ => false
    end.

  Lemma loc_eqb_eq a b : loc_eqb a b = true <-> a = b.
  Proof. destruct a, b; simpl; split; congruence. Qed.

  Lemma loc_eqb_refl a : loc_eqb a a = true.
  Proof. destruct a; reflexivity. Qed.

  Variant HOp : Type := hR (l : Loc) | hW (l : Loc) (v : nat) | hFAA (l : Loc) (d : nat).

  Definition HAr (m : HOp) : Type :=
    match m with hR _ => nat | hW _ _ => unit | hFAA _ _ => nat end.

  Canonical Structure EHW := {| Sig.op := HOp; Sig.ar := HAr |}.

  Definition HS : Type := Loc -> nat.

  Definition hupd (s : HS) (l : Loc) (v : nat) : HS :=
    fun l' => if loc_eqb l l' then v else s l'.

  Lemma hupd_same s l v : hupd s l v l = v.
  Proof. unfold hupd. rewrite loc_eqb_refl. reflexivity. Qed.

  Lemma hupd_other s l v l' : l <> l' -> hupd s l v l' = s l'.
  Proof.
    intros Hne. unfold hupd. destruct (loc_eqb l l') eqn:Hb; [|reflexivity].
    apply loc_eqb_eq in Hb. contradiction.
  Qed.

  Definition hw_spec (s : HS) (t : tid) (m : HOp) : HAr m -> HS -> Prop :=
    match m as m0 return HAr m0 -> HS -> Prop with
    | hR l => fun r s' => r = s l /\ s' = s
    | hW l v => fun _ s' => s' = hupd s l v
    | hFAA l d => fun r s' => r = s l /\ s' = hupd s l (s l + d)
    end.

  (** Only a write followed by a read of another location is unordered. *)
  Definition hw_dep (o m : HOp) : bool :=
    match o, m with hW l _, hR l' => loc_eqb l l' | _, _ => true end.

  Definition MemHW : @Params EHW := {|
    vl_state := HS;
    vl_spec := hw_spec;
    vl_err := fun _ _ _ => False;
    vl_retro := fun m => match m with hR _ => true | _ => false end;
    vl_dep := hw_dep;
    vl_sync := fun _ => false;
  |}.

  Definition hw_init : HS := fun _ => O.

  (** The owner of each ticket: a fetch-and-add on [l_nxt] by [t] hands
      out the ticket [s l_nxt]. *)
  Definition Tk : Type := nat -> option tid.

  Definition tk_up (s : HS) (t : tid) (m : HOp) (g : Tk) : Tk :=
    match m with
    | hFAA l_nxt _ => fun j => if Nat.eqb j (s l_nxt) then Some t else g j
    | _ => g
    end.

  Definition MemHWg : @Params EHW := ViewLiftGhost.PG MemHW tk_up.

  Definition tk_init : Tk := fun _ => None.

  (** ** Ticket lock with data *)

  Variant DLoc : Type := dx | dy.

  Definition dloc_eqb (a b : DLoc) : bool :=
    match a, b with dx, dx | dy, dy => true | _, _ => false end.

  Lemma dloc_eqb_eq a b : dloc_eqb a b = true <-> a = b.
  Proof. destruct a, b; simpl; split; congruence. Qed.

  Definition dloc (l : DLoc) : Loc := match l with dx => l_x | dy => l_y end.

  Variant TOp : Type :=
  | tacq | trel | tgt | tdr (l : DLoc) | tdw (l : DLoc) (v : nat).

  Definition TAr (m : TOp) : Type :=
    match m with tgt | tdr _ => nat | _ => unit end.

  Canonical Structure ETL := {| Sig.op := TOp; Sig.ar := TAr |}.

  Record TS : Type := mkTS { tv : nat; th : option tid; tx : nat; ty : nat }.

  Definition tdat (s : TS) (l : DLoc) : nat := match l with dx => tx s | dy => ty s end.

  Definition tset (s : TS) (l : DLoc) (v : nat) : TS :=
    match l with
    | dx => mkTS (tv s) (th s) v (ty s)
    | dy => mkTS (tv s) (th s) (tx s) v
    end.

  Definition tl_spec (s : TS) (t : tid) (m : TOp) : TAr m -> TS -> Prop :=
    match m as m0 return TAr m0 -> TS -> Prop with
    | tacq => fun _ s' => th s = None /\ s' = mkTS (S (tv s)) (Some t) (tx s) (ty s)
    | trel => fun _ s' => th s = Some t /\ s' = mkTS (S (tv s)) None (tx s) (ty s)
    | tgt => fun r s' => r = tv s /\ s' = s
    | tdr l => fun r s' => r = tdat s l /\ s' = s
    | tdw l v => fun _ s' => th s = Some t /\ s' = tset s l v
    end.

  Definition tl_err (t : tid) (m : TOp) (s : TS) : Prop :=
    match m with trel | tdw _ _ => th s <> Some t | _ => False end.

  (** [tl_dep o m]: is [o] ordered before a later [m] of the same thread?
      Induced by [hw_dep] when [tacq], [trel] are timestamped at their
      write of [l_own], [tgt] at its read of [l_own], and the data
      operations at their access ([TicketTowerLock.acc]). *)
  Definition tl_dep (o m : TOp) : bool :=
    match m with
    | tgt => match o with tdw _ _ => false | _ => true end
    | tdr l => match o with tgt | tdr _ => true | tdw l' _ => dloc_eqb l' l | _ => false end
    | _ => true
    end.

  Definition TLC : @Params ETL := {|
    vl_state := TS;
    vl_spec := tl_spec;
    vl_err := tl_err;
    vl_retro := fun m => match m with tgt | tdr _ => true | _ => false end;
    vl_dep := tl_dep;
    vl_sync := fun _ => false;
  |}.

  Definition tl_init : TS := mkTS O None O O.

  (** The data published by the last release. *)
  Definition rel_up (s : TS) (t : tid) (m : TOp) (g : nat * nat) : nat * nat :=
    match m with trel => (tx s, ty s) | _ => g end.

  Definition TLCm : @Params ETL := ViewLiftGhost.PG TLC rel_up.

  Definition rel_init : nat * nat := (O, O).

  (** ** Record *)

  Variant ROp : Type := rwrite (a b : nat) | rread.

  Definition RAr (m : ROp) : Type :=
    match m with rwrite _ _ => unit | rread => (nat * nat)%type end.

  Canonical Structure ERec := {| Sig.op := ROp; Sig.ar := RAr |}.

  Definition rec_spec (s : nat * nat) (t : tid) (m : ROp) : RAr m -> nat * nat -> Prop :=
    match m as m0 return RAr m0 -> nat * nat -> Prop with
    | rwrite a b => fun _ s' => s' = (a, b)
    | rread => fun r s' => r = s /\ s' = s
    end.

  Definition RecP : @Params ERec := {|
    vl_state := (nat * nat)%type;
    vl_spec := rec_spec;
    vl_err := fun _ _ _ => False;
    vl_retro := fun m => match m with rread => true | _ => false end;
    vl_dep := fun _ _ => true;
    vl_sync := fun _ => false;
  |}.

  Definition rec_init : nat * nat := (O, O).

  (** ** Basic facts *)

  Lemma MemHWg_nosync m : vl_sync MemHWg m = false.
  Proof. reflexivity. Qed.

  Lemma TLC_nosync m : vl_sync TLC m = false.
  Proof. reflexivity. Qed.

  Lemma TLCm_nosync m : vl_sync TLCm m = false.
  Proof. reflexivity. Qed.

  Lemma RecP_nosync m : vl_sync RecP m = false.
  Proof. reflexivity. Qed.

  Lemma even_odd_succ n : Nat.even (S n) = negb (Nat.even n).
  Proof. rewrite Nat.even_succ, <- Nat.negb_even. reflexivity. Qed.
End TicketTowerSpecs.
