(** * WHWQDeq: the RLHL derivation of the dequeue of the weak
      Herlihy–Wing queue, and T4

    Task WHWQ (.rocq-review/tasks/WHWQ.md), phase P7.  The invariant,
    rely, guarantee, footprints and postcondition are those of
    [WHWQInv]; nothing there is changed.  The derivation goes through
    [RelaxedHoareRun.run_method_provable], hence [rp_run].  Results:
    [deq_provable] and T4 [whw_rlhl2] (every field of [RLHL2Hyps], from
    [enq_provable] of [WHWQProof] and [deq_provable]).  Both are closed
    under the global context.

    ** The dequeue ([dnext], from [DLd 0])

    Calls are [ld] (untagged) or [xchg s] (tagged with every earlier
    call). The [c]-th call has its invocation slot at [2 c] and its
    response slot at [2 c + 1].  The direct edges of the own dag (from
    [dprec_run]) are:
    - from every invocation to every later one ((F2): both operations
      acquire, [rc_si_not_after_acq]);
    - from a response to every later [xchg] invocation (the tag);
    - from an invocation to its own response.
    So a response floats past the [ld]s that follow it, up to the next
    [xchg]; no other pair of events is unordered.

    ** Assertions
    - The chain ([ChainK]), on the edge from each invocation to the next
      one.  [k]'s pending invocations are [l] ([KG]), a suffix of a
      dequeue footprint ([DeqTail]), and [k] is in one of three phases:
      [ls_inv] with [l <> []]; dead at [ls_lini] with [l = []]; or
      [ls_linr], a dequeue that swapped out a value whose response it has
      not yet returned.  Before the first [xchg] only the first case
      holds ([ChainA0]).
    - The record of a call ([RecLd], [RecX]), on the edge from an
      invocation to its own response.  For an [xchg], the facts [XFacts]
      of its record [y] hold: either [y <> 0] and [k] took the value [y]
      ([ls_linr]); or [y = 0] and [k] is at [ls_inv] with the scan
      extended ([KScan tl (S s)]), or dead.
    - The post of a response, on the edge to the next [xchg]: the scan
      bound for an [ld] ([KScan tl 0]); [XFacts] with the response value
      for an [xchg].
    - [StatusA] ([ls_inv] or dead), on the edge from the response of the
      last [xchg] to the first [xchg] of the next scan.  It carries the
      phase across the [ld]s in between, and it refutes the [ls_linr]
      case of the chain.  The run went on, so that response returned [0]
      ([XZero]).  A response returns its record, so the record was [0],
      and [XFacts] then excludes [ls_linr].

    ** Slots (Part 4)
    Every slot is canonical ([SlotsOK]): [dslot] reads its components
    off its position, its event and a summary [DSum] of the history
    before it.  [dkind] names the asserted in-edges: the chain, the
    previous response, the status edge, the own invocation.  [dnew] is
    the generic [NewSlotOK] lemma.  The own interference is refuted by
    the order, or it is one of the following:
    - only responses lie in the window of a chain edge;
    - only [ld]s and responses lie in the window of another edge
      ([lastx_spec]);
    - the only older edge whose window can contain a new event is the
      edge from an invocation to its own response;
    - an [xchg] has no older edge in its window.
    The machine invariant [dinv] (Part 6) carries the calls, the
    canonical slots, and the facts the next call reads: the bound [tl],
    the previous call, and [XZero].

    ** Linearization points (the updates, Part 5)
    - An [xchg] whose record is non-zero: [iq_xchg_take] ([AInv] and
      [ARet], removing the vertex of that slot; minimal by [KScan]).
    - An [xchg] with a null record that was [k]'s last pending
      invocation: [iq_xchg_dead] ([poqrd_dead]).
    - Otherwise no abstract step ([iq_emit_plain]).

    ** Scope and dependencies

    - Over [EIhl δRC], with the overlay presentation [POQueueRD] (see the
      scope of [WHWQInv]).  The dead step is taken only in the case above;
      [iq_xchg_dead] itself does not require the [xchg] to be the last
      pending invocation.
    - The derivation uses the hand-written κ tags of the [xchg]s (tag
      policy in [WHWQProg]; review gate 4, WHWQ-g4-2).  The edges from the
      previous response and the status edge ([EkPrev], [EkStatus]) are
      tag edges. *)

From Stdlib Require Import List Bool Arith.PeanoNat PArith.PArith micromega.Lia Relations.Relation_Operators.
Require Import Stdlib.FSets.FMapPositive.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedPossibility.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedHoareBase.
Require Import models.simlin.RelaxedHoareDag.
Require Import models.simlin.RelaxedHoare.
Require Import models.simlin.RelaxedHoareSound.
Require Import models.simlin.RelaxedHoareSpec.
Require Import models.simlin.RelaxedHoareCompLin.
Require Import models.simlin.RelaxedHoareCompLinSpec.
Require Import models.simlin.RelaxedHoareInherit.
Require Import models.simlin.RelaxedHoareRun.
Require Import models.simlin.RelaxedHoareReady.
Require Import examples.Relaxed.WHWQ.WHWQSpec.
Require Import examples.Relaxed.WHWQ.POQueueR.
Require Import examples.Relaxed.WHWQ.POQueueRD.
Require Import examples.Relaxed.WHWQ.WHWQProg.
Require Import examples.Relaxed.WHWQ.WHWQInv.
Require Import examples.Relaxed.WHWQ.WHWQProof.

Import ListNotations.

Module WHWQDeq.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedPossibility.
  Import RelaxedHoareCompLinSpec.
  Import RelaxedHoareBase.
  Import RelaxedHoareDag.
  Import RelaxedHoare.
  Import RelaxedHoareSound.
  Import RelaxedHoareRun.
  Import RelaxedHoareReady.
  Import WHWQSpec.
  Import POQueueR.
  Import POQueueRD.
  Import WHWQProg.
  Import WHWQInv.
  Import WHWQProof.

  Local Abbreviation ES := ERC.
  Local Abbreviation FP := (FQ positive).
  Local Abbreviation VE := (EIhl (E := ERC) δRC).
  Local Abbreviation VF := (POQueueRD.POQueueRD positive).
  Local Abbreviation POk c P := (@PossOk FP VF c P).
  Local Abbreviation QSt := (@POQueueState positive).

  (** ** Part 1. Reading the history of a run *)

  Definition rcnat (o : RCOp) : rc_ar o -> nat :=
    match o as o0 return rc_ar o0 -> nat with
    | RCRd _ _ => fun r => r
    | RCFaa _ _ _ _ => fun r => r
    | RCXchg _ _ _ _ => fun r => r
    | _ => fun _ => 0
    end.

  Definition evop (e : TaggedEvent ES) : RCOp := event_op (te_ev ES (untag e)).
  Definition evh (e : TaggedEvent ES) : nat := event_handle (te_ev ES (untag e)).
  Definition evv (e : TaggedEvent ES) : nat :=
    match te_ev ES (untag e) with ResEv _ o r => rcnat o r | InvEv _ _ => 0 end.

  Definition opat (L : list (TaggedEvent ES)) (p : nat) : RCOp :=
    match nth_error L p with Some e => evop e | None => op_faa end.
  Definition valat (L : list (TaggedEvent ES)) (p : nat) : nat :=
    match nth_error L p with Some e => evv e | None => 0 end.

  Definition isxb (o : RCOp) : bool := match o with RCXchg _ _ _ _ => true | _ => false end.
  Definition isldb (o : RCOp) : bool := match o with RCRd _ _ => true | _ => false end.
  Definition xslot (o : RCOp) : nat := match o with RCXchg l _ _ _ => Nat.pred l | _ => 0 end.

  (** The last [xchg] call, the last [ld] call before call [c]. *)
  Fixpoint lastx (L : list (TaggedEvent ES)) (c : nat) : option nat :=
    match c with
    | 0 => None
    | S c' => if isxb (opat L (2 * c')) then Some c' else lastx L c'
    end.

  Fixpoint lastld (L : list (TaggedEvent ES)) (c : nat) : option nat :=
    match c with
    | 0 => None
    | S c' => if isldb (opat L (2 * c')) then Some c' else lastld L c'
    end.

  (** The scan bound of call [c]: the response of the last [ld] before it. *)
  Definition tlh (L : list (TaggedEvent ES)) (c : nat) : nat :=
    match lastld L c with Some c' => valat L (S (2 * c')) | None => 0 end.

  (** No [xchg] before call [c]. *)
  Definition noxh (L : list (TaggedEvent ES)) (c : nat) : bool :=
    match lastx L c with None => true | Some _ => false end.

  Lemma opat_app L L' p : p < length L -> opat (L ++ L') p = opat L p.
  Proof. intros Hp. unfold opat. rewrite nth_error_app1 by exact Hp. reflexivity. Qed.

  Lemma valat_app L L' p : p < length L -> valat (L ++ L') p = valat L p.
  Proof. intros Hp. unfold valat. rewrite nth_error_app1 by exact Hp. reflexivity. Qed.

  Lemma lastx_app L L' c : 2 * c <= length L -> lastx (L ++ L') c = lastx L c.
  Proof.
    induction c as [| c IH]; intros Hc; [reflexivity |]. cbn [lastx].
    rewrite opat_app by lia. rewrite IH by lia. reflexivity.
  Qed.

  Lemma lastld_app L L' c : 2 * c <= length L -> lastld (L ++ L') c = lastld L c.
  Proof.
    induction c as [| c IH]; intros Hc; [reflexivity |]. cbn [lastld].
    rewrite opat_app by lia. rewrite IH by lia. reflexivity.
  Qed.

  Lemma lastld_lt L c c' : lastld L c = Some c' -> c' < c.
  Proof.
    induction c as [| c IH]; cbn [lastld]; [discriminate |].
    destruct (isldb (opat L (2 * c))); [intros E; injection E as <-; lia | intros H; pose proof (IH H); lia].
  Qed.

  Lemma lastx_lt L c c' : lastx L c = Some c' -> c' < c.
  Proof.
    induction c as [| c IH]; cbn [lastx]; [discriminate |].
    destruct (isxb (opat L (2 * c))); [intros E; injection E as <-; lia | intros H; pose proof (IH H); lia].
  Qed.

  Lemma tlh_app L L' c : 2 * c <= length L -> tlh (L ++ L') c = tlh L c.
  Proof.
    intros Hc. unfold tlh. rewrite lastld_app by exact Hc.
    destruct (lastld L c) as [c' |] eqn:E; [| reflexivity].
    pose proof (lastld_lt _ _ _ E). apply valat_app. lia.
  Qed.

  Lemma noxh_app L L' c : 2 * c <= length L -> noxh (L ++ L') c = noxh L c.
  Proof. intros Hc. unfold noxh. rewrite lastx_app by exact Hc. reflexivity. Qed.

  (** [lastx] finds the last [xchg]: the calls after it are not [xchg]s. *)
  Lemma lastx_spec L c c0 :
    lastx L c = Some c0 -> isxb (opat L (2 * c0)) = true /\ forall b, c0 < b < c -> isxb (opat L (2 * b)) = false.
  Proof.
    induction c as [| c IH]; cbn [lastx]; [discriminate |].
    destruct (isxb (opat L (2 * c))) eqn:Ex.
    - intros E. injection E as <-. split; [exact Ex | intros b Hb; lia].
    - intros H. destruct (IH H) as [Hx Hb]. split; [exact Hx |].
      intros b Hb'. destruct (Nat.eq_dec b c) as [-> | Hne]; [exact Ex | apply Hb; lia].
  Qed.

  Lemma lastx_none L c : lastx L c = None -> forall b, b < c -> isxb (opat L (2 * b)) = false.
  Proof.
    induction c as [| c IH]; cbn [lastx]; [intros _ b Hb; lia |].
    destruct (isxb (opat L (2 * c))) eqn:Ex; [discriminate |].
    intros H b Hb. destruct (Nat.eq_dec b c) as [-> | Hne]; [exact Ex | apply IH; [exact H | lia]].
  Qed.

  Lemma lastx_S_x L c : isxb (opat L (2 * c)) = true -> lastx L (S c) = Some c.
  Proof. intros H. cbn [lastx]. rewrite H. reflexivity. Qed.

  Lemma lastx_S_nx L c : isxb (opat L (2 * c)) = false -> lastx L (S c) = lastx L c.
  Proof. intros H. cbn [lastx]. rewrite H. reflexivity. Qed.

  Lemma lastld_S_ld L c : isldb (opat L (2 * c)) = true -> lastld L (S c) = Some c.
  Proof. intros H. cbn [lastld]. rewrite H. reflexivity. Qed.

  Lemma lastld_S_nld L c : isldb (opat L (2 * c)) = false -> lastld L (S c) = lastld L c.
  Proof. intros H. cbn [lastld]. rewrite H. reflexivity. Qed.

  Lemma xslot_xchg s : xslot (op_xchg s) = s.
  Proof. reflexivity. Qed.

  (** ** Part 2. The calls of the dequeue and its dag *)

  (** The calls of a run of [dnext]: an untagged [ld], or an [xchg]
      tagged with every earlier call. *)
  Definition DCalls (cs : list (RCall ES)) : Prop :=
    forall c x, nth_error cs c = Some x ->
      (rc_op x = op_ld /\ rc_dix x = []) \/ (exists s, rc_op x = op_xchg s /\ rc_dix x = seq 0 c).

  Lemma dcalls_nil : DCalls [].
  Proof. intros c x Hc. destruct c; discriminate. Qed.

  Lemma dcalls_snoc_ld cs hu : DCalls cs -> DCalls (cs ++ [@mkRCall ES hu op_ld []]).
  Proof.
    intros Hd c x Hc. destruct (nth_error_snoc_cases _ _ _ _ Hc) as [(_ & Hc') | (-> & ->)]; [exact (Hd c x Hc') |].
    left. split; reflexivity.
  Qed.

  Lemma dcalls_snoc_x cs hu s : DCalls cs -> DCalls (cs ++ [@mkRCall ES hu (op_xchg s) (seq 0 (length cs))]).
  Proof.
    intros Hd c x Hc. destruct (nth_error_snoc_cases _ _ _ _ Hc) as [(_ & Hc') | (-> & ->)]; [exact (Hd c x Hc') |].
    right. exists s. split; reflexivity.
  Qed.

  Lemma dcalls_acq cs c x : DCalls cs -> nth_error cs c = Some x -> rc_op x = op_ld \/ exists s, rc_op x = op_xchg s.
  Proof. intros Hd Hc. destruct (Hd c x Hc) as [(E & _) | (s & E & _)]; [left; exact E | right; exists s; exact E]. Qed.

  Lemma dcalls_nsi cs a (xa xb : RCall ES) : DCalls cs -> nth_error cs a = Some xa -> ~ rc_si (rc_op xa) (rc_op xb).
  Proof.
    intros Hd Ha. destruct (dcalls_acq cs a xa Hd Ha) as [-> | (s & ->)];
      [exact (proj1 (rc_si_not_after_acq _)) | exact (proj2 (rc_si_not_after_acq _) s)].
  Qed.

  Section Ctx.
    Context (k : CallKey FP).

    Lemma opat_run (Γ : list (Slot VE VF)) (H : FutureStore ES) (cs : list (RCall ES)) c x : RunCtx k Γ H cs -> nth_error cs c = Some x -> opat (evs Γ) (2 * c) = rc_op x.
    Proof.
      intros Hc Hx. destruct (runctx_inv_at k Γ H cs c x Hc Hx) as (si & Hsi & Hev & _).
      unfold opat. rewrite nth_error_evs, Hsi. cbn. unfold evop. rewrite Hev. reflexivity.
    Qed.

    Lemma ddp_inv (Γ : list (Slot VE VF)) (H : FutureStore ES) (cs : list (RCall ES)) a b : RunCtx k Γ H cs -> DCalls cs -> a < b -> b < length cs -> dprec (evs Γ) (2 * a) (2 * b).
    Proof.
      intros Hc Hd Hab Hb.
      destruct (nth_error cs b) as [xb |] eqn:Eb; [| apply nth_error_None in Eb; lia].
      destruct (nth_error cs a) as [xa |] eqn:Ea; [| apply nth_error_None in Ea; lia].
      apply (proj2 (dprec_run k Γ H cs (2 * a) (2 * b) Hc)). exists b, xb. split; [exact Eb |]. left.
      split; [reflexivity |]. exists a, xa. split; [exact Ea |]. split; [exact Hab |]. left. split; [reflexivity |].
      exact (dcalls_nsi cs a xa xb Hd Ea).
    Qed.

    Lemma ddp_tag (Γ : list (Slot VE VF)) (H : FutureStore ES) (cs : list (RCall ES)) a b xb : RunCtx k Γ H cs -> DCalls cs -> a < b -> nth_error cs b = Some xb ->
      isxb (rc_op xb) = true -> dprec (evs Γ) (S (2 * a)) (2 * b).
    Proof.
      intros Hc Hd Hab Eb Hx.
      assert (Hb : b < length cs) by (apply nth_error_Some; rewrite Eb; discriminate).
      destruct (nth_error cs a) as [xa |] eqn:Ea; [| apply nth_error_None in Ea; lia].
      apply (proj2 (dprec_run k Γ H cs (S (2 * a)) (2 * b) Hc)). exists b, xb. split; [exact Eb |]. left.
      split; [reflexivity |]. exists a, xa. split; [exact Ea |]. split; [exact Hab |]. right. split; [reflexivity |].
      destruct (Hd b xb Eb) as [(E & _) | (s & _ & ->)]; [rewrite E in Hx; discriminate Hx |].
      apply in_seq. lia.
    Qed.

    Lemma ddp_res (Γ : list (Slot VE VF)) (H : FutureStore ES) (cs : list (RCall ES)) a : RunCtx k Γ H cs -> a < length cs -> dprec (evs Γ) (2 * a) (S (2 * a)).
    Proof.
      intros Hc Ha. destruct (nth_error cs a) as [xa |] eqn:Ea; [| apply nth_error_None in Ea; lia].
      apply (proj2 (dprec_run k Γ H cs (2 * a) (S (2 * a)) Hc)). exists a, xa. split; [exact Ea |]. right. split; reflexivity.
    Qed.

    (** The events of a call: its invocation and its response carry the
        operation and the handle of the call. *)
    Lemma evat_inv (Γ : list (Slot VE VF)) (H : FutureStore ES) (cs : list (RCall ES)) c x e :
      RunCtx k Γ H cs -> nth_error cs c = Some x -> nth_error (evs Γ) (2 * c) = Some e ->
      evop e = rc_op x /\ evh e = rc_h x /\ evv e = 0.
    Proof.
      intros Hc Hx He. destruct (runctx_inv_at k Γ H cs c x Hc Hx) as (si & Hsi & Hev & _).
      rewrite nth_error_evs, Hsi in He. injection He as <-. unfold evop, evh, evv. rewrite Hev. cbn. auto.
    Qed.

    Lemma evat_res (Γ : list (Slot VE VF)) (H : FutureStore ES) (cs : list (RCall ES)) c x e :
      RunCtx k Γ H cs -> nth_error cs c = Some x -> nth_error (evs Γ) (S (2 * c)) = Some e ->
      evop e = rc_op x /\ evh e = rc_h x.
    Proof.
      intros Hc Hx He. destruct (runctx_res_at k Γ H cs c x Hc Hx) as (sr & v & Hsr & Hev).
      rewrite nth_error_evs, Hsr in He. injection He as <-. unfold evop, evh. rewrite Hev. cbn. auto.
    Qed.

    Lemma evat_same (Γ : list (Slot VE VF)) (H : FutureStore ES) (cs : list (RCall ES)) c e1 e2 :
      RunCtx k Γ H cs -> nth_error (evs Γ) (2 * c) = Some e1 -> nth_error (evs Γ) (S (2 * c)) = Some e2 ->
      evop e1 = evop e2 /\ evh e1 = evh e2.
    Proof.
      intros Hc H1 H2. pose proof (runctx_len k Γ H cs Hc) as Hl.
      assert (Hc2 : S (2 * c) < length (evs Γ)) by (apply nth_error_Some; rewrite H2; discriminate).
      rewrite length_evs in Hc2.
      destruct (nth_error cs c) as [x |] eqn:Ex; [| apply nth_error_None in Ex; lia].
      destruct (evat_inv Γ H cs c x e1 Hc Ex H1) as (A1 & B1 & _).
      destruct (evat_res Γ H cs c x e2 Hc Ex H2) as (A2 & B2). split; congruence.
    Qed.

    Lemma opat_run_res (Γ : list (Slot VE VF)) (H : FutureStore ES) (cs : list (RCall ES)) c x :
      RunCtx k Γ H cs -> nth_error cs c = Some x -> opat (evs Γ) (S (2 * c)) = rc_op x.
    Proof.
      intros Hc Hx. destruct (runctx_res_at k Γ H cs c x Hc Hx) as (sr & v & Hsr & Hev).
      unfold opat. rewrite nth_error_evs, Hsr. cbn. unfold evop. rewrite Hev. reflexivity.
    Qed.

    Lemma dbefore_inv (Γ : list (Slot VE VF)) (H : FutureStore ES) (cs : list (RCall ES)) a b : RunCtx k Γ H cs -> DCalls cs -> a <= b -> b < length cs -> before (evs Γ) (2 * a) (2 * b).
    Proof.
      intros Hc Hd Hab Hb. induction b as [| b IH].
      - replace a with 0 by lia. apply before_refl.
      - destruct (Nat.eq_dec a (S b)) as [-> | Hne]; [apply before_refl |].
        apply (before_step _ _ (2 * b)); [apply IH; lia | apply (ddp_inv Γ H cs b (S b) Hc Hd); lia].
    Qed.

    Lemma dbefore_inv_res (Γ : list (Slot VE VF)) (H : FutureStore ES) (cs : list (RCall ES)) a b : RunCtx k Γ H cs -> DCalls cs -> a <= b -> b < length cs ->
      before (evs Γ) (2 * a) (S (2 * b)).
    Proof.
      intros Hc Hd Hab Hb. apply (before_step _ _ (2 * b)); [exact (dbefore_inv Γ H cs a b Hc Hd Hab Hb) |].
      exact (ddp_res Γ H cs b Hc Hb).
    Qed.

    (** A response precedes every slot from the next [xchg] on. *)
    Lemma dbefore_tag (Γ : list (Slot VE VF)) (H : FutureStore ES) (cs : list (RCall ES)) a e b xe : RunCtx k Γ H cs -> DCalls cs -> a < e -> e <= b -> b < length cs ->
      nth_error cs e = Some xe -> isxb (rc_op xe) = true ->
      before (evs Γ) (S (2 * a)) (2 * b) /\ before (evs Γ) (S (2 * a)) (S (2 * b)).
    Proof.
      intros Hc Hd Hae Heb Hb Ee Hx.
      assert (B : before (evs Γ) (S (2 * a)) (2 * e)) by (apply before_dprec; exact (ddp_tag Γ H cs a e xe Hc Hd Hae Ee Hx)).
      split.
      - exact (before_trans _ _ _ _ B (dbefore_inv Γ H cs e b Hc Hd Heb Hb)).
      - exact (before_trans _ _ _ _ B (dbefore_inv_res Γ H cs e b Hc Hd Heb Hb)).
    Qed.

    (** An invocation precedes every later slot. *)
    Lemma inv_before_all (Γ : list (Slot VE VF)) (H : FutureStore ES) (cs : list (RCall ES)) b q :
      RunCtx k Γ H cs -> DCalls cs -> 2 * b <= q -> q < length Γ -> before (evs Γ) (2 * b) q.
    Proof.
      intros Hc Hd Hbq Hq. pose proof (runctx_len k Γ H cs Hc) as Hl.
      destruct (Nat.Even_or_Odd q) as [[m ->] | [m ->]].
      - apply (dbefore_inv Γ H cs b m Hc Hd); lia.
      - replace (2 * m + 1) with (S (2 * m)) by lia. apply (dbefore_inv_res Γ H cs b m Hc Hd); lia.
    Qed.

    (** A response precedes every slot from the next [xchg] on. *)
    Lemma res_before_x (Γ : list (Slot VE VF)) (H : FutureStore ES) (cs : list (RCall ES)) a e q xe :
      RunCtx k Γ H cs -> DCalls cs -> a < e -> 2 * e <= q -> q < length Γ ->
      nth_error cs e = Some xe -> isxb (rc_op xe) = true -> before (evs Γ) (S (2 * a)) q.
    Proof.
      intros Hc Hd Hae Heq Hq Ee Hx. pose proof (runctx_len k Γ H cs Hc) as Hl.
      destruct (Nat.Even_or_Odd q) as [[m ->] | [m ->]].
      - exact (proj1 (dbefore_tag Γ H cs a e m xe Hc Hd Hae ltac:(lia) ltac:(lia) Ee Hx)).
      - replace (2 * m + 1) with (S (2 * m)) by lia.
        exact (proj2 (dbefore_tag Γ H cs a e m xe Hc Hd Hae ltac:(lia) ltac:(lia) Ee Hx)).
    Qed.
  End Ctx.

  (** ** Part 2b. Parity, summaries and edge kinds *)

  Lemma even_double c : Nat.even (2 * c) = true.
  Proof. rewrite Nat.even_mul. reflexivity. Qed.

  Lemma even_sdouble c : Nat.even (S (2 * c)) = false.
  Proof. rewrite Nat.even_succ, Nat.odd_mul. reflexivity. Qed.

  Lemma div2_le j : 2 * Nat.div2 j <= j.
  Proof. pose proof (Nat.div2_odd j). lia. Qed.

  (** What a slot of the dequeue reads of the history before it. *)
  Record DSum : Type := mkDSum {
    ds_nox : bool;          (** no [xchg] before this call *)
    ds_tl : nat;            (** the scan bound of this call *)
    ds_op1 : RCOp;          (** the operation at the previous position *)
    ds_val1 : nat;          (** the value at the previous position *)
    ds_lastx : option nat   (** the last [xchg] call before this call *)
  }.

  Definition dsum (L : list (TaggedEvent ES)) (j : nat) : DSum :=
    mkDSum (noxh L (Nat.div2 j)) (tlh L (Nat.div2 j))
      (match j with 0 => op_faa | S j' => opat L j' end)
      (match j with 0 => 0 | S j' => valat L j' end)
      (lastx L (Nat.div2 j)).

  (** A summary reads only the positions before its own. *)
  Lemma dsum_app L L' j : j <= length L -> dsum (L ++ L') j = dsum L j.
  Proof.
    intros Hj. pose proof (div2_le j) as Hd. unfold dsum.
    rewrite noxh_app, tlh_app, lastx_app by lia.
    destruct j as [| j']; [reflexivity |]. rewrite opat_app, valat_app by lia. reflexivity.
  Qed.

  Lemma dsum_inv_succ L c :
    dsum L (2 * S c) = mkDSum (noxh L (S c)) (tlh L (S c)) (opat L (S (2 * c))) (valat L (S (2 * c))) (lastx L (S c)).
  Proof.
    replace (2 * S c) with (S (S (2 * c))) by lia. unfold dsum.
    change (Nat.div2 (S (S (2 * c)))) with (S (Nat.div2 (2 * c))). rewrite Nat.div2_double. reflexivity.
  Qed.

  Lemma dsum_inv L c : ds_nox (dsum L (2 * c)) = noxh L c /\ ds_tl (dsum L (2 * c)) = tlh L c /\ ds_lastx (dsum L (2 * c)) = lastx L c.
  Proof. unfold dsum. cbn [ds_nox ds_tl ds_lastx]. rewrite Nat.div2_double. auto. Qed.

  Lemma dsum_res L c :
    dsum L (S (2 * c)) = mkDSum (noxh L c) (tlh L c) (opat L (2 * c)) (valat L (2 * c)) (lastx L c).
  Proof. unfold dsum. rewrite Nat.div2_succ_double. reflexivity. Qed.

  (** The kinds of the in-edges of a slot of the dequeue: the chain (from
      the previous invocation), the previous response (into an [xchg]),
      the status (from the last [xchg] response, into the first [xchg]
      after an [ld]), the own invocation (into a response); nothing else
      is asserted. *)
  Inductive EdgeK : Type := EkNone | EkChain | EkPrev | EkStatus | EkOwn.

  Definition dkind (sm : DSum) (j : nat) (ev : TaggedEvent ES) (d : nat) : EdgeK :=
    if Nat.even j then
      if (2 <=? j) && (d =? j - 2) then EkChain
      else if isxb (evop ev) && (2 <=? j) && (d =? j - 1) then EkPrev
      else if isxb (evop ev) && isldb (ds_op1 sm) &&
              match ds_lastx sm with Some c0 => d =? S (2 * c0) | None => false end then EkStatus
      else EkNone
    else if d =? j - 1 then EkOwn else EkNone.

  Lemma dkind_spec sm j ev d :
    match dkind sm j ev d with
    | EkNone => True
    | EkChain => exists c, j = 2 * S c /\ d = 2 * c
    | EkPrev => exists c, j = 2 * S c /\ d = S (2 * c) /\ isxb (evop ev) = true
    | EkStatus => exists c c0, j = 2 * c /\ d = S (2 * c0) /\ ds_lastx sm = Some c0 /\
                    isxb (evop ev) = true /\ isldb (ds_op1 sm) = true
    | EkOwn => exists c, j = S (2 * c) /\ d = 2 * c
    end.
  Proof.
    unfold dkind. destruct (Nat.even j) eqn:Ej.
    - apply Nat.even_spec in Ej as [m Hm].
      destruct (Nat.leb_spec 2 j) as [H2 | H2]; cbn [andb].
      + destruct (Nat.eqb_spec d (j - 2)) as [Hd | Hd].
        * exists (Nat.pred m). split; lia.
        * destruct (isxb (evop ev)) eqn:Ex; cbn [andb].
          -- destruct (Nat.eqb_spec d (j - 1)) as [Hd1 | Hd1].
             ++ exists (Nat.pred m). split; [lia |]. split; [lia | reflexivity].
             ++ destruct (isldb (ds_op1 sm)) eqn:El; cbn [andb]; [| exact Logic.I].
                destruct (ds_lastx sm) as [c0 |] eqn:Ec; [| exact Logic.I].
                destruct (Nat.eqb_spec d (S (2 * c0))) as [Hd2 | Hd2]; [| exact Logic.I].
                exists m, c0. auto.
          -- exact Logic.I.
      + destruct (isxb (evop ev)) eqn:Ex; cbn [andb]; [| exact Logic.I].
        destruct (isldb (ds_op1 sm)) eqn:El; cbn [andb]; [| exact Logic.I].
        destruct (ds_lastx sm) as [c0 |] eqn:Ec; [| exact Logic.I].
        destruct (Nat.eqb_spec d (S (2 * c0))) as [Hd2 | Hd2]; [| exact Logic.I].
        exists m, c0. auto.
    - assert (Ho : Nat.odd j = true) by (rewrite <- Nat.negb_even, Ej; reflexivity).
      apply Nat.odd_spec in Ho as [m Hm].
      destruct (Nat.eqb_spec d (j - 1)) as [Hd | Hd]; [| exact Logic.I].
      exists m. split; lia.
  Qed.

  Lemma dkind_chain sm c ev : dkind sm (2 * S c) ev (2 * c) = EkChain.
  Proof.
    unfold dkind. rewrite even_double.
    destruct (Nat.leb_spec 2 (2 * S c)); [| lia]. destruct (Nat.eqb_spec (2 * c) (2 * S c - 2)); [reflexivity | lia].
  Qed.

  Lemma dkind_prev sm c ev : isxb (evop ev) = true -> dkind sm (2 * S c) ev (S (2 * c)) = EkPrev.
  Proof.
    intros Hx. unfold dkind. rewrite even_double, Hx.
    destruct (Nat.leb_spec 2 (2 * S c)); [| lia]. destruct (Nat.eqb_spec (S (2 * c)) (2 * S c - 2)); [lia |].
    destruct (Nat.eqb_spec (S (2 * c)) (2 * S c - 1)); [reflexivity | lia].
  Qed.

  Lemma dkind_status sm c c0 ev :
    isxb (evop ev) = true -> isldb (ds_op1 sm) = true -> ds_lastx sm = Some c0 -> c0 < c ->
    dkind sm (2 * S c) ev (S (2 * c0)) = EkStatus.
  Proof.
    intros Hx Hl Hc Hlt. unfold dkind. rewrite even_double, Hx, Hl, Hc.
    destruct (Nat.leb_spec 2 (2 * S c)); [| lia]. destruct (Nat.eqb_spec (S (2 * c0)) (2 * S c - 2)); [lia |].
    destruct (Nat.eqb_spec (S (2 * c0)) (2 * S c - 1)); [lia |].
    rewrite Nat.eqb_refl. reflexivity.
  Qed.

  Lemma dkind_own sm c ev : dkind sm (S (2 * c)) ev (2 * c) = EkOwn.
  Proof.
    unfold dkind. rewrite even_sdouble. destruct (Nat.eqb_spec (2 * c) (S (2 * c) - 1)); [reflexivity | lia].
  Qed.

  (** Every [xchg] response so far returned [0] (the run went on). *)
  Definition XZero (L : list (TaggedEvent ES)) : Prop :=
    forall c, isxb (opat L (S (2 * c))) = true -> valat L (S (2 * c)) = 0.

  (** ** Part 3. The assertions of the dequeue *)

  Section Deq.
    Context (t : tid) (h : nat).
    Local Abbreviation k := (@pair tid (handle FP) t h).
    Local Abbreviation Pinit := (PostInvoke Iq k deq (Oq t deq h)).

    (** A suffix of a dequeue footprint: [ld]s and [xchg]s of [t], the last
        one an [xchg]. *)
    Definition DeqTail (l : list (ThreadEvent ES)) : Prop :=
      Forall (DeqEv t) l /\ (l = [] \/ exists l0 hx sx, l = l0 ++ [IE t hx (op_xchg sx)]).

    Definition DStart : Assn VE VF := fun s =>
      KLk k (@ls_inv FP deq) s /\ exists evs, DeqShape t evs /\ KG k evs s.

    Definition ChainA0 : Assn VE VF := fun s =>
      exists l, KG k l s /\ DeqTail l /\ KLk k (@ls_inv FP deq) s /\ l <> [].

    Definition ChainA : Assn VE VF := fun s =>
      exists l, KG k l s /\ DeqTail l /\
        ((KLk k (@ls_inv FP deq) s /\ l <> []) \/ (KLk k (@ls_lini FP deq) s /\ l = []) \/
         (exists r, KLk k (@ls_linr FP deq r) s)).

    Definition ChainK (b : bool) : Assn VE VF := if b then ChainA0 else ChainA.

    (** The facts of an [xchg] record [y] at slot [s] of a scan bounded by
        [tl]. *)
    Definition XFacts (tl s y : nat) : Assn VE VF := fun st =>
      (y <> 0 /\ exists r, KLk k (@ls_linr FP deq r) st /\ Pos.to_nat r = y) \/
      (y = 0 /\ ((KLk k (@ls_inv FP deq) st /\ KScan tl (S s) st) \/ KLk k (@ls_lini FP deq) st)).

    Definition StatusA : Assn VE VF := fun st => KLk k (@ls_inv FP deq) st \/ KLk k (@ls_lini FP deq) st.

    Definition RecLd (hu : nat) : Assn VE VF := fun st =>
      exists w, KMine (t, hu) (@RelaxedTraceLin.Build_Op ES (t, hu) op_ld w) st /\ KScan w 0 st.

    Definition RecX (hu tl s : nat) : Assn VE VF := fun st =>
      exists y, KMine (t, hu) (@RelaxedTraceLin.Build_Op ES (t, hu) (op_xchg s) y) st /\ XFacts tl s y st.

    (** *** Stability: the chain under the rely and own responses; the
        other assertions also under own [ld]s *)

    Lemma dstart_stable_r : Stable Iq (Rq k) DStart.
    Proof.
      intros s s' (Hl & evs & HΩ & Hg) Hr HI. split; [exact (klk_stable_r k _ s s' Hl Hr HI) |].
      exists evs. split; [exact HΩ | exact (kg_stable_r k evs s s' Hg Hr HI)].
    Qed.

    Lemma chaina0_stable (r : PRel VE VF) :
      (forall l, Stable Iq r (KG k l)) -> (forall ls, Stable Iq r (KLk k ls)) -> Stable Iq r ChainA0.
    Proof.
      intros Hg Hl s s' (l & Hk & Ht & Hi & Hne) Hr HI. exists l.
      split; [exact (Hg l s s' Hk Hr HI) |]. split; [exact Ht |]. split; [exact (Hl _ s s' Hi Hr HI) | exact Hne].
    Qed.

    Lemma chaina_stable (r : PRel VE VF) :
      (forall l, Stable Iq r (KG k l)) -> (forall ls, Stable Iq r (KLk k ls)) -> Stable Iq r ChainA.
    Proof.
      intros Hg Hl s s' (l & Hk & Ht & Hc) Hr HI. exists l.
      split; [exact (Hg l s s' Hk Hr HI) |]. split; [exact Ht |].
      destruct Hc as [(Hi & Hne) | [(Hi & He) | (r0 & Hi)]].
      - left. split; [exact (Hl _ s s' Hi Hr HI) | exact Hne].
      - right. left. split; [exact (Hl _ s s' Hi Hr HI) | exact He].
      - right. right. exists r0. exact (Hl _ s s' Hi Hr HI).
    Qed.

    Lemma chaink_stable (r : PRel VE VF) b :
      (forall l, Stable Iq r (KG k l)) -> (forall ls, Stable Iq r (KLk k ls)) -> Stable Iq r (ChainK b).
    Proof. intros Hg Hl. destruct b; [exact (chaina0_stable r Hg Hl) | exact (chaina_stable r Hg Hl)]. Qed.

    Lemma chaink_stable_r b : Stable Iq (Rq k) (ChainK b).
    Proof. apply chaink_stable; [apply kg_stable_r | apply klk_stable_r]. Qed.

    Lemma chaink_stable_res b : Stable Iq (GRes k) (ChainK b).
    Proof. apply chaink_stable; [intros l; apply (kg_stable_res k k) | intros ls; apply (klk_stable_res k k)]. Qed.

    Lemma chaina_stable_r : Stable Iq (Rq k) ChainA.
    Proof. exact (chaink_stable_r false). Qed.

    Lemma chaina_stable_res : Stable Iq (GRes k) ChainA.
    Proof. exact (chaink_stable_res false). Qed.

    (** The assertions of class P are stable under every relation that
        keeps [k]'s phase and only lets the queue state grow. *)
    Definition KeepsP (r : PRel VE VF) : Prop :=
      (forall ls, Stable Iq r (KLk k ls)) /\ (forall a b, Stable Iq r (KScan a b)) /\
      (forall key x0, Stable Iq r (KMine key x0)).

    Lemma keepsp_r : KeepsP (Rq k).
    Proof.
      split; [apply klk_stable_r |]. split; [intros a b; apply kscan_stable_r | intros key x0; apply kmine_stable_r].
    Qed.

    Lemma keepsp_pl : KeepsP (GPl k).
    Proof.
      split; [intros ls; apply (klk_stable_pl k k) |].
      split; [intros a b; apply kscan_stable_pl | intros key x0; apply kmine_stable_pl].
    Qed.

    Lemma keepsp_res : KeepsP (GRes k).
    Proof.
      split; [intros ls; apply (klk_stable_res k k) |].
      split; [intros a b; apply kscan_stable_res | intros key x0; apply kmine_stable_res].
    Qed.

    Lemma xfacts_stable r tl s y : KeepsP r -> Stable Iq r (XFacts tl s y).
    Proof.
      intros (Hl & Hs & _) st st' Hx Hr HI. destruct Hx as [(Hy & r0 & Hk & Hv) | (Hy & [(Hi & Hsc) | Hd])].
      - left. split; [exact Hy |]. exists r0. split; [exact (Hl _ st st' Hk Hr HI) | exact Hv].
      - right. split; [exact Hy |]. left. split; [exact (Hl _ st st' Hi Hr HI) | exact (Hs _ _ st st' Hsc Hr HI)].
      - right. split; [exact Hy |]. right. exact (Hl _ st st' Hd Hr HI).
    Qed.

    Lemma statusa_stable r : KeepsP r -> Stable Iq r StatusA.
    Proof.
      intros (Hl & _) st st' [H | H] Hr HI; [left | right]; exact (Hl _ st st' H Hr HI).
    Qed.

    Lemma recld_stable r hu : KeepsP r -> Stable Iq r (RecLd hu).
    Proof.
      intros (_ & Hs & Hm) st st' (w & Hk & Hsc) Hr HI. exists w.
      split; [exact (Hm _ _ st st' Hk Hr HI) | exact (Hs _ _ st st' Hsc Hr HI)].
    Qed.

    Lemma recx_stable r hu tl s : KeepsP r -> Stable Iq r (RecX hu tl s).
    Proof.
      intros Hk st st' (y & Hm & Hx) Hr HI. exists y.
      split; [exact (proj2 (proj2 Hk) _ _ st st' Hm Hr HI) | exact (xfacts_stable r tl s y Hk st st' Hx Hr HI)].
    Qed.

    Lemma kscan_stable_p r a b : KeepsP r -> Stable Iq r (KScan a b).
    Proof. intros (_ & Hs & _). apply Hs. Qed.

    (** ** Part 4. The canonical slots *)

    (** The post of a response of [o] with value [v], in a scan bounded by
        [tl]; the in-edge from an invocation of [o] with handle [hu] to its
        response; the post of an invocation. *)
    Definition rpostS (tl : nat) (o : RCOp) (v : nat) : Assn VE VF :=
      if isxb o then XFacts tl (xslot o) v else KScan v 0.

    Definition rin (o : RCOp) (hu tl : nat) : Assn VE VF :=
      if isxb o then RecX hu tl (xslot o) else RecLd hu.

    Definition ipostS (nox : bool) (tl : nat) (ev : TaggedEvent ES) : Assn VE VF :=
      if isxb (evop ev) then (fun s => ChainA s /\ RecX (evh ev) tl (xslot (evop ev)) s)
      else (fun s => ChainK nox s /\ RecLd (evh ev) s).

    Definition dinK (sm : DSum) (ev : TaggedEvent ES) (kd : EdgeK) : Assn VE VF :=
      match kd with
      | EkNone => fun _ => True
      | EkChain => ChainK (ds_nox sm)
      | EkPrev => rpostS (ds_tl sm) (ds_op1 sm) (ds_val1 sm)
      | EkStatus => StatusA
      | EkOwn => rin (evop ev) (evh ev) (ds_tl sm)
      end.

    Definition dinS (sm : DSum) (j : nat) (ev : TaggedEvent ES) (d : nat) : Assn VE VF :=
      dinK sm ev (dkind sm j ev d).

    Definition dpostS (sm : DSum) (j : nat) (ev : TaggedEvent ES) : Assn VE VF :=
      if Nat.even j then ipostS (ds_nox sm) (ds_tl sm) ev else rpostS (ds_tl sm) (evop ev) (evv ev).

    (** The guarantees: [Gq] at an [xchg] (a possible linearization point),
        [GPl] at an [ld], [GRes] at a response. *)
    Definition dguar (j : nat) (ev : TaggedEvent ES) : PRel VE VF :=
      if Nat.even j then (if isxb (evop ev) then Gq k else GPl k) else GRes k.

    Definition dstart (j : nat) : Assn VE VF := match j with 0 => DStart | _ => fun _ => True end.

    Definition dslotS (sm : DSum) (j : nat) (ev : TaggedEvent ES) : Slot VE VF :=
      mkSlot ev (dstart j) (dinS sm j ev) (dpostS sm j ev) (dguar j ev).

    Definition dslot (L : list (TaggedEvent ES)) (j : nat) (ev : TaggedEvent ES) : Slot VE VF :=
      dslotS (dsum L j) j ev.

    (** Every slot of the context is the canonical one for its position and
        the history before it. *)
    Definition SlotsOK (Γ : list (Slot VE VF)) : Prop :=
      forall j sj, nth_error Γ j = Some sj -> sj = dslot (evs Γ) j (sl_ev sj).

    Lemma slotsok_nil : SlotsOK [].
    Proof. intros j sj Hj. destruct j; discriminate Hj. Qed.

    Lemma slotsok_snoc (Γ : list (Slot VE VF)) ev :
      SlotsOK Γ -> SlotsOK (Γ ++ [dslot (evs Γ) (length Γ) ev]).
    Proof.
      intros Hok j sj Hj. destruct (nth_error_snoc_cases _ _ _ _ Hj) as [(Hlt & Hj') | (-> & ->)].
      - rewrite (Hok j sj Hj') at 1. unfold dslot. rewrite evs_app, dsum_app by (rewrite length_evs; lia). reflexivity.
      - unfold dslot at 2. cbn [dslot dslotS sl_ev]. rewrite evs_app, dsum_app by (rewrite length_evs; lia). reflexivity.
    Qed.

    Lemma slotsok_at (Γ : list (Slot VE VF)) j sj :
      SlotsOK Γ -> nth_error Γ j = Some sj ->
      sl_start sj = dstart j /\ sl_in sj = dinS (dsum (evs Γ) j) j (sl_ev sj) /\
      sl_post sj = dpostS (dsum (evs Γ) j) j (sl_ev sj) /\ sl_guar sj = dguar j (sl_ev sj) /\
      nth_error (evs Γ) j = Some (sl_ev sj).
    Proof.
      intros Hok Hj. pose proof (Hok j sj Hj) as E. rewrite nth_error_evs, Hj. cbn [option_map].
      set (e := sl_ev sj) in *. clearbody e. subst sj. cbn [dslot dslotS sl_start sl_in sl_post sl_guar]. auto.
    Qed.

    (** *** The shapes of the components at even and odd positions *)

    Lemma dpost_inv sm c ev : dpostS sm (2 * c) ev = ipostS (ds_nox sm) (ds_tl sm) ev.
    Proof. unfold dpostS. rewrite even_double. reflexivity. Qed.

    Lemma dpost_res sm c ev : dpostS sm (S (2 * c)) ev = rpostS (ds_tl sm) (evop ev) (evv ev).
    Proof. unfold dpostS. rewrite even_sdouble. reflexivity. Qed.

    Lemma dguar_inv c ev : dguar (2 * c) ev = if isxb (evop ev) then Gq k else GPl k.
    Proof. unfold dguar. rewrite even_double. reflexivity. Qed.

    Lemma dguar_odd j ev : Nat.even j = false -> dguar j ev = GRes k.
    Proof. intros E. unfold dguar. rewrite E. reflexivity. Qed.

    Lemma dguar_gq j ev s s' : dguar j ev s s' -> Gq k s s'.
    Proof.
      unfold dguar. destruct (Nat.even j); [destruct (isxb (evop ev)) |];
        [exact (fun H => H) | exact (fun H => proj1 H) | exact (fun H => proj1 H)].
    Qed.

    Lemma dguar_keepsp j ev : Nat.even j = false \/ isxb (evop ev) = false -> KeepsP (dguar j ev).
    Proof.
      intros Hj. unfold dguar. destruct (Nat.even j) eqn:Ej; [| exact keepsp_res].
      destruct Hj as [Hj | Hx]; [discriminate Hj |]. rewrite Hx. exact keepsp_pl.
    Qed.

    (** *** Stability *)

    Lemma rpost_stable r tl o v : KeepsP r -> Stable Iq r (rpostS tl o v).
    Proof. intros Hk. unfold rpostS. destruct (isxb o); [apply xfacts_stable | apply kscan_stable_p]; exact Hk. Qed.

    Lemma rin_stable r o hu tl : KeepsP r -> Stable Iq r (rin o hu tl).
    Proof. intros Hk. unfold rin. destruct (isxb o); [apply recx_stable | apply recld_stable]; exact Hk. Qed.

    Lemma dink_stable_p r sm ev kd : kd <> EkChain -> KeepsP r -> Stable Iq r (dinK sm ev kd).
    Proof.
      intros Hn Hk. destruct kd; cbn [dinK].
      - apply Stable_true.
      - exfalso. exact (Hn eq_refl).
      - exact (rpost_stable r _ _ _ Hk).
      - exact (statusa_stable r Hk).
      - exact (rin_stable r _ _ _ Hk).
    Qed.

    Lemma dink_stable_r sm ev kd : Stable Iq (Rq k) (dinK sm ev kd).
    Proof.
      destruct kd; [| exact (chaink_stable_r _) | ..]; apply dink_stable_p; try discriminate; exact keepsp_r.
    Qed.

    Lemma dink_stable_res sm ev kd : Stable Iq (GRes k) (dinK sm ev kd).
    Proof.
      destruct kd; [| exact (chaink_stable_res _) | ..]; apply dink_stable_p; try discriminate; exact keepsp_res.
    Qed.

    Lemma dstart_stable j : Stable Iq (Rq k) (dstart j).
    Proof. destruct j as [| j]; [exact dstart_stable_r | apply Stable_true]. Qed.

    (** *** The start: the footprint of the dequeue *)

    Lemma dstart_est j : Impl Iq Pinit (dstart j).
    Proof.
      destruct j as [| j]; [| intros s _ _; exact Logic.I].
      intros s HI (p0 & γ0 & evs & (st & P0 & Hp0 & _ & HC) & Hinv & Hg & HΩ & _).
      cbn [ps_poss ps_mem ps_ghost fst snd] in Hp0, HC, Hinv. subst p0.
      destruct (RelaxedHoareInherit.pinv_inv_gen _ _ _ _ _ _ Hinv) as [Hp Hfr].
      split; [exists st, (make_lin_entry k (@ls_inv FP deq) :: P0); split; [exact Hp | left; reflexivity] |].
      exists evs. split; [exact HΩ |]. unfold KG. rewrite Hg, kg_app, kg_new.
      rewrite (kg_none k γ0); [reflexivity |]. intros e He Ho. apply Hfr. rewrite <- Ho. exact (proj1 (iq_age _ _ _ _ HC) e He).
    Qed.

    Lemma dstart_chain s : DStart s -> ChainA0 s.
    Proof.
      intros (Hl & evs & (_ & Hf & evs0 & hx & sx & Hev) & Hg). exists evs.
      split; [exact Hg |]. split; [split; [exact Hf | right; exists evs0, hx, sx; exact Hev] |].
      split; [exact Hl |]. rewrite Hev. intros E. destruct evs0; discriminate E.
    Qed.

    Lemma isxb_isldb o : isxb o = true -> isldb o = false.
    Proof. destruct o; cbn; congruence. Qed.

    (** *** The generic slot lemma

        Appending the canonical slot at position [length Γ]: the in-edges
        that carry an assertion are edges of the dag; the post of each
        source implies the edge ([XZero] for the status edge); the chain
        has only responses in its window, the other edges only [ld]s and
        responses ([lastx_spec]); an older edge whose window contains the
        new event is the edge from an invocation to its own response, of
        class P, and an [xchg] has no older edge in its window. *)
    Lemma dnew (Γ : list (Slot VE VF)) (ev : TaggedEvent ES) (Γx : list (Slot VE VF)) (Hx : FutureStore ES)
        (csx : list (RCall ES)) (rest : list (Slot VE VF)) :
      RunCtx k Γx Hx csx -> DCalls csx -> Γx = (Γ ++ [dslot (evs Γ) (length Γ) ev]) ++ rest -> SlotsOK Γ ->
      XZero (evs Γ) ->
      EvUpdate Iq (dguar (length Γ) ev) k (untag ev)
        (fun s => dstart (length Γ) s /\ forall d, dinS (dsum (evs Γ) (length Γ)) (length Γ) ev d s)
        (dpostS (dsum (evs Γ) (length Γ)) (length Γ) ev) ->
      NewSlotOK Iq Rq Gq k Pinit Γ (dslot (evs Γ) (length Γ) ev).
    Proof.
      intros Hc Hd HΓx Hok Hz Hupd.
      assert (Hlx : length Γx = 2 * length csx) by exact (runctx_len k Γx Hx csx Hc).
      assert (HLx : evs Γx = (evs Γ ++ [ev]) ++ evs rest) by (rewrite HΓx, !evs_app; reflexivity).
      assert (Hpx : length Γ < length Γx) by (rewrite HΓx, !length_app; cbn [length]; lia).
      assert (HnL : forall q, q < length Γ -> nth_error (evs Γx) q = nth_error (evs Γ) q).
      { intros q Hq. rewrite HLx, <- app_assoc, nth_error_app1 by (rewrite length_evs; exact Hq). reflexivity. }
      assert (Hnp : nth_error (evs Γx) (length Γ) = Some ev).
      { rewrite HLx, <- app_assoc, nth_error_app2 by (rewrite length_evs; lia). rewrite length_evs, Nat.sub_diag. reflexivity. }
      assert (HoL : forall q, q < length Γ -> opat (evs Γx) q = opat (evs Γ) q).
      { intros q Hq. unfold opat. rewrite (HnL q Hq). reflexivity. }
      assert (Hcall : forall c, 2 * c < length Γx -> exists x, nth_error csx c = Some x).
      { intros c Hcl. destruct (nth_error csx c) as [x |] eqn:E; [exists x; reflexivity | apply nth_error_None in E; lia]. }
      assert (Hsame : forall c, S (2 * c) < length Γ -> opat (evs Γ) (2 * c) = opat (evs Γ) (S (2 * c))).
      { intros c Hcl. rewrite <- !HoL by lia. destruct (Hcall c ltac:(lia)) as (x & Ex).
        rewrite (opat_run k Γx Hx csx c x Hc Ex), (opat_run_res k Γx Hx csx c x Hc Ex). reflexivity. }
      assert (Hopn : forall c, length Γ = 2 * c -> exists x, nth_error csx c = Some x /\ evop ev = rc_op x).
      { intros c Hpc. destruct (Hcall c ltac:(lia)) as (x & Ex). exists x. split; [exact Ex |].
        rewrite Hpc in Hnp. exact (proj1 (evat_inv k Γx Hx csx c x ev Hc Ex Hnp)). }
      remember (length Γ) as p eqn:Hp.
      remember (dslot (evs Γ) p ev) as sl eqn:Esl.
      assert (Hsl : sl_ev sl = ev /\ sl_start sl = dstart p /\ sl_in sl = dinS (dsum (evs Γ) p) p ev /\
                    sl_post sl = dpostS (dsum (evs Γ) p) p ev /\ sl_guar sl = dguar p ev)
        by (subst sl; repeat split).
      destruct Hsl as (Hse & Hss & Hsi & Hsp & Hsg).
      assert (Bx : forall a b, b <= p -> before (evs Γx) a b -> before (evs (Γ ++ [sl])) a b).
      { intros a b Hb Hbf. rewrite HΓx, evs_app in Hbf.
        apply (before_app_iff (evs (Γ ++ [sl])) (evs rest) a b) in Hbf; [exact Hbf | rewrite length_evs, length_app; cbn [length]; lia]. }
      assert (Bo : forall a b, b < p -> before (evs Γx) a b -> before (evs Γ) a b).
      { intros a b Hb Hbf. apply Bx in Hbf; [| lia]. rewrite evs_app in Hbf.
        apply (before_app_iff (evs Γ) (evs [sl]) a b) in Hbf; [exact Hbf | rewrite length_evs; lia]. }
      assert (Dx : forall a b, b <= p -> dprec (evs Γx) a b -> dprec (evs (Γ ++ [sl])) a b).
      { intros a b Hb Hdp. rewrite HΓx, evs_app in Hdp.
        apply (dprec_app_iff (evs (Γ ++ [sl])) (evs rest) a b) in Hdp; [exact Hdp | rewrite length_evs, length_app; cbn [length]; lia]. }
      constructor; try rewrite <- Hp.
      - (* ns_guar *)
        intros s s' Hg. rewrite Hsg in Hg. exact (dguar_gq _ _ s s' Hg).
      - (* ns_update: every asserted in-edge is an edge of the dag *)
        intros σ p0 γ γ' [Hst Hin] HI Hge σ' Hs. rewrite Hse in Hge, Hs. rewrite Hsp, Hsg.
        rewrite Hss in Hst. rewrite Hsi in Hin.
        apply (Hupd σ p0 γ γ'); [| exact HI | exact Hge | exact Hs].
        split; [exact Hst |]. intros d. unfold dinS.
        pose proof (dkind_spec (dsum (evs Γ) p) p ev d) as Hks.
        destruct (dkind (dsum (evs Γ) p) p ev d) eqn:Ek; [exact Logic.I | ..];
          (assert (Hdp : dprec (evs Γx) d p);
           [| pose proof (Hin d (Dx d p (le_n p) Hdp)) as H0; unfold dinS in H0; rewrite Ek in H0; exact H0]).
        + destruct Hks as (c & -> & ->). apply (ddp_inv k Γx Hx csx c (S c) Hc Hd); lia.
        + destruct Hks as (c & -> & -> & Hxe). destruct (Hopn (S c) eq_refl) as (x & Ex & Eo). rewrite Eo in Hxe.
          exact (ddp_tag k Γx Hx csx c (S c) x Hc Hd ltac:(lia) Ex Hxe).
        + destruct Hks as (c & c0 & -> & -> & Hl & Hxe & _).
          rewrite (proj2 (proj2 (dsum_inv (evs Γ) c))) in Hl. pose proof (lastx_lt _ _ _ Hl) as Hlt.
          destruct (Hopn c eq_refl) as (x & Ex & Eo). rewrite Eo in Hxe.
          exact (ddp_tag k Γx Hx csx c0 c x Hc Hd Hlt Ex Hxe).
        + destruct Hks as (c & -> & ->). apply (ddp_res k Γx Hx csx c Hc). lia.
      - (* ns_est_start *)
        rewrite Hss. exact (dstart_est p).
      - (* ns_est_in *)
        intros d sd Hdp Hsd s HI Hpost. rewrite Hsi.
        destruct (slotsok_at Γ d sd Hok Hsd) as (_ & _ & Epo & _ & Ed). rewrite Epo in Hpost.
        set (evd := sl_ev sd) in *. clearbody evd.
        assert (Hdl : d < p) by (rewrite Hp; apply nth_error_Some; rewrite Hsd; discriminate).
        assert (Edx : nth_error (evs Γx) d = Some evd) by (rewrite (HnL d Hdl); exact Ed).
        unfold dinS. pose proof (dkind_spec (dsum (evs Γ) p) p ev d) as Hks.
        destruct (dkind (dsum (evs Γ) p) p ev d) eqn:Ek; cbn [dinK]; [exact Logic.I | ..].
        + (* the chain *)
          destruct Hks as (c & -> & ->). rewrite dsum_inv_succ. cbn [ds_nox].
          rewrite dpost_inv in Hpost. destruct (dsum_inv (evs Γ) c) as (En & Et & _). rewrite En, Et in Hpost.
          assert (Eo : opat (evs Γ) (2 * c) = evop evd) by (unfold opat; rewrite Ed; reflexivity).
          unfold ipostS in Hpost. destruct (isxb (evop evd)) eqn:Ex; destruct Hpost as [Hch _]; unfold noxh.
          * rewrite lastx_S_x by (rewrite Eo; exact Ex). exact Hch.
          * rewrite lastx_S_nx by (rewrite Eo; exact Ex). exact Hch.
        + (* the previous response *)
          destruct Hks as (c & -> & -> & Hxe). rewrite dsum_inv_succ. cbn [ds_tl ds_op1 ds_val1].
          rewrite dpost_res, dsum_res in Hpost. cbn [ds_tl] in Hpost.
          assert (Eo : opat (evs Γ) (S (2 * c)) = evop evd) by (unfold opat; rewrite Ed; reflexivity).
          assert (Ev : valat (evs Γ) (S (2 * c)) = evv evd) by (unfold valat; rewrite Ed; reflexivity).
          rewrite Eo, Ev. unfold rpostS in Hpost |- *. destruct (isxb (evop evd)) eqn:Ex; [| exact Hpost].
          assert (Hnl : isldb (opat (evs Γ) (2 * c)) = false).
          { rewrite Hsame by lia. rewrite Eo. exact (isxb_isldb _ Ex). }
          unfold tlh. rewrite lastld_S_nld by exact Hnl. exact Hpost.
        + (* the status: the last [xchg] response returned [0] *)
          destruct Hks as (c & c0 & -> & -> & Hl & Hxe & Hld).
          rewrite (proj2 (proj2 (dsum_inv (evs Γ) c))) in Hl.
          destruct (lastx_spec _ _ _ Hl) as [Hx0 _]. pose proof (lastx_lt _ _ _ Hl) as Hlt.
          rewrite dpost_res, dsum_res in Hpost. cbn [ds_tl] in Hpost.
          assert (Eo : opat (evs Γ) (S (2 * c0)) = evop evd) by (unfold opat; rewrite Ed; reflexivity).
          assert (Ev : valat (evs Γ) (S (2 * c0)) = evv evd) by (unfold valat; rewrite Ed; reflexivity).
          assert (Hx1 : isxb (evop evd) = true) by (rewrite <- Eo, <- Hsame by lia; exact Hx0).
          assert (Hv0 : evv evd = 0) by (rewrite <- Ev; apply Hz; rewrite Eo; exact Hx1).
          unfold rpostS in Hpost. rewrite Hx1, Hv0 in Hpost.
          destruct Hpost as [(H0 & _) | (_ & [(Hi & _) | Hdd])]; [exfalso; exact (H0 eq_refl) | left; exact Hi | right; exact Hdd].
        + (* the own invocation *)
          destruct Hks as (c & -> & ->). rewrite dsum_res. cbn [ds_tl].
          rewrite dpost_inv in Hpost. destruct (dsum_inv (evs Γ) c) as (En & Et & _). rewrite En, Et in Hpost.
          destruct (evat_same k Γx Hx csx c evd ev Hc Edx Hnp) as [Eo Eh].
          unfold ipostS in Hpost. unfold rin. rewrite <- Eo, <- Eh.
          destruct (isxb (evop evd)); destruct Hpost as [_ Hr]; exact Hr.
      - (* ns_R_start *)
        rewrite Hss. exact (dstart_stable p).
      - (* ns_R_in *)
        intros d _. rewrite Hsi. unfold dinS. apply dink_stable_r.
      - (* ns_if_new_start *)
        intros g sg Hg. rewrite Hss. destruct p as [| p']; [| apply Stable_true].
        exfalso. assert (Hgl : g < length Γ) by (apply nth_error_Some; rewrite Hg; discriminate). lia.
      - (* ns_if_new_in *)
        intros d g sg Hdp Hg Hnb. rewrite Hsi.
        destruct (slotsok_at Γ g sg Hok Hg) as (_ & _ & _ & Egu & Eg). rewrite Egu.
        set (evg := sl_ev sg) in *. clearbody evg.
        assert (Hgl : g < p) by (rewrite Hp; apply nth_error_Some; rewrite Hg; discriminate).
        assert (Eog : opat (evs Γ) g = evop evg) by (unfold opat; rewrite Eg; reflexivity).
        unfold dinS. pose proof (dkind_spec (dsum (evs Γ) p) p ev d) as Hks.
        destruct (dkind (dsum (evs Γ) p) p ev d) eqn:Ek; [apply Stable_true | | | |].
        + (* the chain: only responses are in its window *)
          destruct Hks as (c & -> & ->).
          destruct (Nat.even g) eqn:Eg2.
          * exfalso. apply Nat.even_spec in Eg2 as [b ->]. apply Hnb. apply Bo; [lia |].
            apply (inv_before_all k Γx Hx csx b (2 * c) Hc Hd); lia.
          * rewrite (dguar_odd g evg Eg2). apply dink_stable_res.
        + (* the previous response *)
          destruct Hks as (c & -> & -> & _). apply dink_stable_p; [discriminate |]. apply dguar_keepsp.
          destruct (Nat.even g) eqn:Eg2; [right | left; reflexivity].
          destruct (isxb (evop evg)) eqn:Ex; [exfalso | reflexivity].
          apply Nat.even_spec in Eg2 as [b ->]. apply Hnb. apply Bo; [lia |].
          apply (inv_before_all k Γx Hx csx b (S (2 * c)) Hc Hd); lia.
        + (* the status edge: only [ld]s and responses are in its window *)
          destruct Hks as (c & c0 & -> & -> & Hl & _ & _). apply dink_stable_p; [discriminate |]. apply dguar_keepsp.
          rewrite (proj2 (proj2 (dsum_inv (evs Γ) c))) in Hl. pose proof (lastx_lt _ _ _ Hl) as Hlt.
          destruct (Nat.even g) eqn:Eg2; [right | left; reflexivity].
          destruct (isxb (evop evg)) eqn:Ex; [exfalso | reflexivity].
          apply Nat.even_spec in Eg2 as [b ->].
          destruct (Nat.le_gt_cases b c0) as [Hb | Hb].
          * apply Hnb. apply Bo; [lia |]. apply (inv_before_all k Γx Hx csx b (S (2 * c0)) Hc Hd); lia.
          * destruct (lastx_spec _ _ _ Hl) as [_ Hnx]. pose proof (Hnx b ltac:(lia)) as Hb'.
            rewrite Eog, Ex in Hb'. discriminate Hb'.
        + (* the own invocation *)
          destruct Hks as (c & -> & ->). apply dink_stable_p; [discriminate |]. apply dguar_keepsp.
          destruct (Nat.even g) eqn:Eg2; [right | left; reflexivity].
          destruct (isxb (evop evg)) eqn:Ex; [exfalso | reflexivity].
          apply Nat.even_spec in Eg2 as [b ->]. apply Hnb. apply Bo; [lia |].
          apply (inv_before_all k Γx Hx csx b (2 * c) Hc Hd); lia.
      - (* ns_if_old_start: the first invocation precedes everything *)
        intros y sy Hy Hnb. destruct (slotsok_at Γ y sy Hok Hy) as (Est & _). rewrite Est, Hsg.
        destruct y as [| y']; [| apply Stable_true].
        exfalso. apply Hnb. apply Bx; [lia |]. exact (inv_before_all k Γx Hx csx 0 p Hc Hd ltac:(lia) ltac:(lia)).
      - (* ns_if_old_in: only the edge from an invocation to its own response *)
        intros y sy d Hy Hnb Hdy. destruct (slotsok_at Γ y sy Hok Hy) as (_ & Ein & _ & _ & Ey). rewrite Ein, Hsg.
        assert (Hyl : y < p) by (rewrite Hp; apply nth_error_Some; rewrite Hy; discriminate).
        destruct (Nat.even y) eqn:Ey2.
        + exfalso. apply Nat.even_spec in Ey2 as [b ->]. apply Hnb. apply Bx; [lia |].
          apply (inv_before_all k Γx Hx csx b p Hc Hd); lia.
        + unfold dinS. pose proof (dkind_spec (dsum (evs Γ) y) y (sl_ev sy) d) as Hks.
          destruct (dkind (dsum (evs Γ) y) y (sl_ev sy) d) eqn:Ek.
          * apply Stable_true.
          * exfalso. destruct Hks as (c & -> & _). rewrite even_double in Ey2. discriminate Ey2.
          * exfalso. destruct Hks as (c & -> & _). rewrite even_double in Ey2. discriminate Ey2.
          * exfalso. destruct Hks as (c & c0 & -> & _). rewrite even_double in Ey2. discriminate Ey2.
          * destruct Hks as (b & -> & ->). apply dink_stable_p; [discriminate |]. apply dguar_keepsp.
            destruct (Nat.even p) eqn:Ep; [right | left; reflexivity].
            destruct (isxb (evop ev)) eqn:Ex; [exfalso | reflexivity].
            apply Nat.even_spec in Ep as [c ->].
            destruct (Hopn c eq_refl) as (x & Ex' & Eo). rewrite Eo in Ex.
            apply Hnb. apply Bx; [lia |].
            exact (res_before_x k Γx Hx csx b c (2 * c) x Hc Hd ltac:(lia) (le_n _) ltac:(lia) Ex' Ex).
    Qed.

    (** ** Part 5. The event updates *)

    Lemma evupdate_conseq_i (g : PRel VE VF) ev (P P' Q : Assn VE VF) :
      (forall s, Iq s -> P' s -> P s) -> EvUpdate Iq g k ev P Q -> EvUpdate Iq g k ev P' Q.
    Proof. intros HP HU σ p γ γ' Hpre HI. exact (HU σ p γ γ' (HP _ HI Hpre) HI). Qed.

    (** *** Reading the assertions at a concrete state *)

    Lemma klk_at st0 (P0 : LinPool FP) (σ : State VE) (γ : Ghost ES FP) ls :
      KLk k ls (σ, POk (POQReady st0) P0, γ) -> lin_lookup k ls P0.
    Proof. intros (st1 & P1 & Hp & Hl). cbn in Hp. injection Hp as <- <-. exact Hl. Qed.

    Lemma klk_mk st0 (P0 : LinPool FP) (σ : State VE) (γ : Ghost ES FP) ls :
      lin_lookup k ls P0 -> KLk k ls (σ, POk (POQReady st0) P0, γ).
    Proof. intros Hl. exists st0, P0. split; [reflexivity | exact Hl]. Qed.

    Lemma kscan_at st0 (P0 : LinPool FP) (σ : State VE) (γ : Ghost ES FP) r i :
      KScan r i (σ, POk (POQReady st0) P0, γ) -> poq_wf st0 /\ ScanC st0 r i.
    Proof. intros (st1 & P1 & Hp & Hw & Hs). cbn in Hp. injection Hp as <- <-. auto. Qed.

    Lemma kscan_mk st0 (P0 : LinPool FP) (σ : State VE) (γ : Ghost ES FP) r i :
      poq_wf st0 -> ScanC st0 r i -> KScan r i (σ, POk (POQReady st0) P0, γ).
    Proof. intros Hw Hs. exists st0, P0. auto. Qed.

    (** *** The pending invocations of the dequeue *)

    Lemma deqtail_tail y l : DeqTail (y :: l) -> DeqTail l.
    Proof.
      intros [Hf [E | (l0 & hx & sx & E)]]; [discriminate E |].
      split; [exact (Forall_inv_tail Hf) |].
      destruct l0 as [| y0 l0]; cbn in E; [left; injection E as _ E; exact E |].
      right. exists l0, hx, sx. injection E as _ E. exact E.
    Qed.

    Lemma deqtail_ld_ne hu l : DeqTail (IE t hu op_ld :: l) -> l <> [].
    Proof.
      intros [_ [E | (l0 & hx & sx & E)]]; [discriminate E |].
      destruct l0 as [| y0 l0]; cbn in E; [unfold IE, op_ld, op_xchg in E; discriminate E |].
      injection E as _ E. rewrite E. intros E'. destruct l0; discriminate E'.
    Qed.

    Lemma deqtail_owns_x (γ : Ghost ES FP) l : kg k γ = l -> DeqTail l -> l <> [] -> Owns k isX γ.
    Proof.
      intros Hg [_ [-> | (l0 & hx & sx & ->)]] Hne; [exfalso; exact (Hne eq_refl) |].
      apply (proj2 (owns_kg k isX γ)). exists (IE t hx (op_xchg sx)). rewrite Hg.
      split; [apply in_or_app; right; left; reflexivity | exists sx; reflexivity].
    Qed.

    Lemma emit_in_kg (γ γ' : Ghost ES FP) ev : ghost_emit k ev γ γ' -> is_invocation ev -> In ev (kg k γ).
    Proof.
      intros Hge Hi. destruct (ghost_emit_shape _ _ _ _ Hge Hi) as (g1 & g2 & -> & _ & _).
      apply (proj2 (kg_in k _ ev)). apply in_or_app. right. left. reflexivity.
    Qed.

    (** The emitted invocation is the first pending one: an acquire of the
        thread orders every later operation. *)
    Lemma deq_head (γ γ' : Ghost ES FP) y l hu o :
      NoDup γ -> Forall RelaxedHoareInherit.gwf γ -> kg k γ = y :: l -> DeqEv t y ->
      ghost_emit k (IE t hu o) γ γ' -> IE t hu o = y /\ kg k γ' = l.
    Proof.
      intros Hnd Hgwf Hg Hy Hge. apply (kg_head k γ γ' y l (IE t hu o) Hnd Hg Hge Logic.I). right.
      assert (Hin : In (Build_ScheduledEvent k y) γ) by (apply (proj1 (kg_in k γ y)); rewrite Hg; left; reflexivity).
      rewrite Forall_forall in Hgwf. destruct Hy as (hy & oy & -> & Hoy).
      exact (deq_blocks (Build_ScheduledEvent k (IE t hy oy)) t hu o (Hgwf _ Hin) eq_refl Hoy).
    Qed.

    Lemma chaink_split nox s : ChainK nox s ->
      exists l, KG k l s /\ DeqTail l /\
        ((KLk k (@ls_inv FP deq) s /\ l <> []) \/
         (nox = false /\ ((KLk k (@ls_lini FP deq) s /\ l = []) \/ exists r, KLk k (@ls_linr FP deq r) s))).
    Proof.
      destruct nox; cbn [ChainK].
      - intros (l & Hg & Ht & Hi & Hne). exists l. split; [exact Hg |]. split; [exact Ht |]. left. split; assumption.
      - intros (l & Hg & Ht & [Hc | Hc]); exists l; (split; [exact Hg |]); (split; [exact Ht |]);
          [left; exact Hc | right; split; [reflexivity | exact Hc]].
    Qed.

    Lemma chaink_intro nox l s : KG k l s -> DeqTail l ->
      ((KLk k (@ls_inv FP deq) s /\ l <> []) \/
       (nox = false /\ ((KLk k (@ls_lini FP deq) s /\ l = []) \/ exists r, KLk k (@ls_linr FP deq r) s))) ->
      ChainK nox s.
    Proof.
      intros Hg Ht [(Hi & Hne) | (-> & Hc)].
      - destruct nox; cbn [ChainK]; exists l; (split; [exact Hg |]); (split; [exact Ht |]); [split; assumption |].
        left. split; assumption.
      - cbn [ChainK]. exists l. split; [exact Hg |]. split; [exact Ht | right; exact Hc].
    Qed.

    (** *** The records of the dequeue's invocations *)

    Lemma inv_rec_ld (σ σ' : State VE) hu :
      eihl_rec_used (E := ES) δRC σ -> Step VE (IE t hu op_ld) σ σ' ->
      eihl_mine (E := ES) δRC (t, hu) (@RelaxedTraceLin.Build_Op ES (t, hu) op_ld (fst (fst σ) 0)) σ'.
    Proof.
      intros Hru Hs. destruct (inv_mine σ σ' t hu op_ld Hru Hs) as (r & Hm & HU).
      destruct (step_ld σ σ' t hu Hs) as [_ HU']. rewrite HU in HU'.
      apply (f_equal (fun l : list (RelaxedTraceLin.Op ES) => match l with a :: _ => rec_nat a | [] => 0 end)) in HU'.
      cbn in HU'. subst r. exact Hm.
    Qed.

    Lemma inv_rec_x (σ σ' : State VE) hu s :
      eihl_rec_used (E := ES) δRC σ -> Step VE (IE t hu (op_xchg s)) σ σ' ->
      eihl_mine (E := ES) δRC (t, hu) (@RelaxedTraceLin.Build_Op ES (t, hu) (op_xchg s) (fst (fst σ) (S s))) σ'.
    Proof.
      intros Hru Hs. destruct (inv_mine σ σ' t hu (op_xchg s) Hru Hs) as (r & Hm & HU).
      destruct (step_xchg σ σ' t hu s Hs) as [_ HU']. rewrite HU in HU'.
      apply (f_equal (fun l : list (RelaxedTraceLin.Op ES) => match l with a :: _ => rec_nat a | [] => 0 end)) in HU'.
      cbn in HU'. subst r. exact Hm.
    Qed.

    (** A null slot below the bound extends the scan: a live, complete
        vertex there would hold its value. *)
    Lemma scan_ext m st (P : LinPool FP) (γ : Ghost ES FP) s tl :
      IqC m st P γ -> m (S s) = 0 -> s < tl -> ScanC st tl s -> ScanC st tl (S s).
    Proof.
      intros HC Hz Hstl (Hr & Hscan). split; [exact Hr |].
      intros j Hj Hlive Hcomp n Hedge. destruct (Nat.eq_dec j s) as [-> | Hjs].
      - exfalso. destruct (iq_cells _ _ _ _ HC s) as [_ C2].
        destruct (C2 ltac:(lia)) as [(Hpv & _) | [(Hg & _) | (_ & _ & v & _ & Hv)]].
        + exact (proj2 Hcomp Hpv).
        + exact (proj2 Hlive Hg).
        + rewrite Hz in Hv. pose proof (Pos2Nat.is_pos v). lia.
      - apply (Hscan j); [lia | exact Hlive | exact Hcomp | exact Hedge].
    Qed.

    (** *** The [ld]: no abstract step; its record is the counter *)

    Lemma upd_ldi hu nox (P : Assn VE VF) :
      (forall s, P s -> ChainK nox s) ->
      EvUpdate Iq (GPl k) k (IE t hu op_ld) P (fun s => ChainK nox s /\ RecLd hu s).
    Proof.
      intros HP σ p γ γ' Hpre HI Hge σ' Hs.
      destruct (chaink_split nox _ (HP _ Hpre)) as (l & Hg & Ht & Hst).
      unfold KG in Hg. cbn [ps_ghost snd] in Hg.
      pose proof HI as (st & P0 & Hp & Hru & HC). cbn [ps_poss ps_mem ps_ghost fst snd] in Hp, Hru. subst p.
      unfold regs, ps_mem, ps_ghost in HC. cbn [fst snd] in HC.
      destruct l as [| y l'].
      { exfalso. pose proof (emit_in_kg γ γ' _ Hge Logic.I) as Hin. rewrite Hg in Hin. exact Hin. }
      destruct (deq_head γ γ' y l' hu op_ld (iq_gnd _ _ _ _ HC) (iq_gwf _ _ _ _ HC) Hg (Forall_inv (proj1 Ht)) Hge)
        as [Ey Hg']. subst y.
      pose proof (deqtail_tail _ _ Ht) as Ht'. pose proof (deqtail_ld_ne _ _ Ht) as Hne'.
      destruct (step_ld σ σ' t hu Hs) as [Hm' _].
      destruct (iq_emit_plain k t hu op_ld σ σ' st P0 γ γ' HI Hs) as [HI' HG].
      { intros l0. rewrite Hm'. reflexivity. }
      { exact Hge. }
      { intros ls Hls. destruct Hst as [(Hi & _) | (_ & [(_ & E) | (r & Hr)])]; [| discriminate E |].
        - rewrite (lookup_unique _ _ _ _ (iq_wf _ _ _ _ HC) Hls (klk_at _ _ _ _ _ Hi)). cbn [Coup].
          exact (deqtail_owns_x γ' l' Hg' Ht' Hne').
        - rewrite (lookup_unique _ _ _ _ (iq_wf _ _ _ _ HC) Hls (klk_at _ _ _ _ _ Hr)). exact Logic.I. }
      exists (POk (POQReady st) P0). split; [apply rt_refl |]. split; [| split; [exact HI' | split; [exact HG | reflexivity]]].
      split.
      - apply (chaink_intro nox l'); [exact Hg' | exact Ht' |].
        destruct Hst as [(Hi & _) | (Hn & [(_ & E) | (r & Hr)])]; [left; split; [exact Hi | exact Hne'] | discriminate E |].
        right. split; [exact Hn |]. right. exists r. exact Hr.
      - exists (fst (fst σ) 0). split; [exact (inv_rec_ld σ σ' hu Hru Hs) |].
        apply kscan_mk; [exact (iq_pwf _ _ _ _ HC) |]. split; [rewrite (iq_ctr _ _ _ _ HC); lia | intros j Hj; lia].
    Qed.

    Lemma upd_ldr hu (r : nat) (P : Assn VE VF) :
      (forall s, P s -> RecLd hu s) ->
      EvUpdate Iq (GRes k) k (Build_ThreadEvent t (@ResEv ES hu op_ld r)) P (KScan r 0).
    Proof.
      intros HP σ p γ γ' Hpre HI Hge σ' Hs. cbn in Hge. subst γ'.
      destruct (HP _ Hpre) as (w & Hm & Hsc).
      pose proof (mine_res_val (t, hu) op_ld r _ σ σ' Hm Hs) as E. apply ld_rec_inj in E. subst w.
      destruct (iq_response k t hu op_ld r σ σ' p γ HI Hs) as [HI' HG].
      exists p. split; [apply rt_refl |]. split; [exact Hsc | split; [exact HI' | split; [exact HG | split; reflexivity]]].
    Qed.

    (** *** The [xchg]: take the value, or die, or go on *)

    Definition XPre (tl s : nat) : Assn VE VF := fun st =>
      exists l, KG k l st /\ DeqTail l /\
        ((KLk k (@ls_inv FP deq) st /\ l <> [] /\ KScan tl s st) \/ (KLk k (@ls_lini FP deq) st /\ l = [])).

    Lemma upd_xi hu tl s (P : Assn VE VF) :
      s < tl -> (forall st, P st -> XPre tl s st) ->
      EvUpdate Iq (Gq k) k (IE t hu (op_xchg s)) P (fun st => ChainA st /\ RecX hu tl s st).
    Proof.
      intros Hstl HP σ p γ γ' Hpre HI Hge σ' Hs.
      destruct (HP _ Hpre) as (l & Hg & Ht & Hst).
      unfold KG in Hg. cbn [ps_ghost snd] in Hg.
      pose proof HI as (st & P0 & Hp & Hru & HC). cbn [ps_poss ps_mem ps_ghost fst snd] in Hp, Hru. subst p.
      unfold regs, ps_mem, ps_ghost in HC. cbn [fst snd] in HC.
      destruct l as [| y l'].
      { exfalso. pose proof (emit_in_kg γ γ' _ Hge Logic.I) as Hin. rewrite Hg in Hin. exact Hin. }
      destruct Hst as [(Hi & _ & Hsc) | (_ & E)]; [| discriminate E].
      pose proof (klk_at _ _ _ _ _ Hi) as Hl. destruct (kscan_at _ _ _ _ _ _ Hsc) as [_ Hscan].
      destruct (deq_head γ γ' y l' hu (op_xchg s) (iq_gnd _ _ _ _ HC) (iq_gwf _ _ _ _ HC) Hg (Forall_inv (proj1 Ht)) Hge)
        as [Ey Hg']. subst y.
      pose proof (deqtail_tail _ _ Ht) as Ht'. pose proof (inv_rec_x σ σ' hu s Hru Hs) as Hm.
      destruct (Nat.eq_dec (fst (fst σ) (S s)) 0) as [Hz | Hnz].
      - destruct l' as [| y' l''].
        + (* the last pending invocation, a null slot: [poqrd_dead] *)
          destruct (iq_xchg_dead t h hu s σ σ' st P0 γ γ' HI Hl Hs Hge Hz) as (P1 & Hinv & Hps & HI' & HG).
          assert (Hl1 : lin_lookup k (@ls_lini FP deq) P1)
            by exact (lin_update_target _ _ _ _ _ (lin_invoke_update_is_update _ _ _ _ _ Hinv)).
          exists (POk (POQReady st) P1). split; [exact Hps |]. split; [| split; [exact HI' | exact HG]].
          split.
          * exists []. split; [unfold KG; cbn [ps_ghost snd]; exact Hg' |]. split; [exact Ht' |].
            right. left. split; [exact (klk_mk _ _ _ _ _ Hl1) | reflexivity].
          * exists (fst (fst σ) (S s)). split; [exact Hm |]. rewrite Hz. right. split; [reflexivity |].
            right. exact (klk_mk _ _ _ _ _ Hl1).
        + (* a null slot, more to come: no abstract step, the scan goes on *)
          destruct (iq_emit_plain k t hu (op_xchg s) σ σ' st P0 γ γ' HI Hs) as [HI' HG].
          { intros l0. destruct (step_xchg σ σ' t hu s Hs) as [Hm' _]. rewrite Hm'. unfold mem_upd.
            destruct (Nat.eqb_spec (S s) l0) as [<- | _]; [exact (eq_sym Hz) | reflexivity]. }
          { exact Hge. }
          { intros ls Hls. rewrite (lookup_unique _ _ _ _ (iq_wf _ _ _ _ HC) Hls Hl). cbn [Coup].
            apply (deqtail_owns_x γ' (y' :: l'')); [exact Hg' | exact Ht' | discriminate]. }
          exists (POk (POQReady st) P0). split; [apply rt_refl |]. split; [| split; [exact HI' | exact HG]].
          split.
          * exists (y' :: l''). split; [unfold KG; cbn [ps_ghost snd]; exact Hg' |]. split; [exact Ht' |].
            left. split; [exact Hi | discriminate].
          * exists (fst (fst σ) (S s)). split; [exact Hm |]. rewrite Hz. right. split; [reflexivity |]. left.
            split; [exact Hi |]. apply kscan_mk; [exact (iq_pwf _ _ _ _ HC) |].
            exact (scan_ext _ _ _ _ _ _ HC Hz Hstl Hscan).
      - (* a value below the bound: [AInv] and [ARet] *)
        destruct (iq_xchg_take t h hu s tl σ σ' st P0 γ γ' HI Hl Hs Hge Hnz Hscan Hstl)
          as (v & P1 & P2 & Hv & Hval & Hinv & Hu2 & Hps & HI' & HG).
        assert (Hl2 : lin_lookup k (@ls_linr FP deq v) P2) by exact (lin_update_target _ _ _ _ _ Hu2).
        exists (POk (POQReady (poq_mark_garbage s st)) P2). split; [exact Hps |]. split; [| split; [exact HI' | exact HG]].
        split.
        + exists l'. split; [unfold KG; cbn [ps_ghost snd]; exact Hg' |]. split; [exact Ht' |].
          right. right. exists v. exact (klk_mk _ _ _ _ _ Hl2).
        + exists (fst (fst σ) (S s)). split; [exact Hm |]. left. split; [exact Hnz |].
          exists v. split; [exact (klk_mk _ _ _ _ _ Hl2) | exact Hval].
    Qed.

    Lemma upd_xr hu tl s (r : nat) (P : Assn VE VF) :
      (forall st, P st -> RecX hu tl s st) ->
      EvUpdate Iq (GRes k) k (Build_ThreadEvent t (@ResEv ES hu (op_xchg s) r)) P (XFacts tl s r).
    Proof.
      intros HP σ p γ γ' Hpre HI Hge σ' Hs. cbn in Hge. subst γ'.
      destruct (HP _ Hpre) as (y & Hm & Hx).
      pose proof (mine_res_val (t, hu) (op_xchg s) r _ σ σ' Hm Hs) as E. apply xchg_rec_inj in E. subst y.
      destruct (iq_response k t hu (op_xchg s) r σ σ' p γ HI Hs) as [HI' HG].
      exists p. split; [apply rt_refl |]. split; [exact Hx | split; [exact HI' | split; [exact HG | split; reflexivity]]].
    Qed.

    (** ** Part 6. The calls, the machine invariant, the return *)

    (** *** The history after a call *)

    Lemma xzero_nil : XZero [].
    Proof. intros c Hx. cbn in Hx. discriminate Hx. Qed.

    Lemma xzero_snoc L e :
      XZero L -> (Nat.even (length L) = true \/ isxb (evop e) = false \/ evv e = 0) -> XZero (L ++ [e]).
    Proof.
      intros Hz He c Hx. destruct (Nat.lt_ge_cases (S (2 * c)) (length L)) as [Hlt | Hge].
      - rewrite opat_app in Hx by exact Hlt. rewrite valat_app by exact Hlt. exact (Hz c Hx).
      - destruct (Nat.eq_dec (S (2 * c)) (length L)) as [Heq | Hne].
        + unfold opat in Hx. unfold valat. rewrite nth_error_app2 in Hx |- * by lia.
          rewrite <- Heq, Nat.sub_diag in Hx |- *. cbn in Hx |- *.
          destruct He as [Hev | [Hx' | Hv]]; [rewrite <- Heq, even_sdouble in Hev; discriminate Hev | | exact Hv].
          rewrite Hx' in Hx. discriminate Hx.
        + exfalso. unfold opat in Hx. rewrite nth_error_app2 in Hx by lia.
          rewrite (proj2 (nth_error_None [e] _)) in Hx by (cbn [length]; lia). discriminate Hx.
    Qed.

    Lemma opat_last L e : opat (L ++ [e]) (length L) = evop e.
    Proof. unfold opat. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. Qed.

    Lemma valat_last L e : valat (L ++ [e]) (length L) = evv e.
    Proof. unfold valat. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. Qed.

    Lemma evs_snoc2 (Γ : list (Slot VE VF)) a b : evs ((Γ ++ [a]) ++ [b]) = (evs Γ ++ [sl_ev a]) ++ [sl_ev b].
    Proof. rewrite !evs_app. reflexivity. Qed.

    (** The new positions of a call: its invocation at [length L], its
        response at [S (length L)]. *)
    Lemma opat_new_inv L a b : opat ((L ++ [a]) ++ [b]) (length L) = evop a.
    Proof. rewrite opat_app by (rewrite length_app; cbn; lia). apply opat_last. Qed.

    Lemma opat_new_res L a b : opat ((L ++ [a]) ++ [b]) (S (length L)) = evop b.
    Proof. replace (S (length L)) with (length (L ++ [a])) by (rewrite length_app; cbn; lia). apply opat_last. Qed.

    Lemma valat_new_res L a b : valat ((L ++ [a]) ++ [b]) (S (length L)) = evv b.
    Proof. replace (S (length L)) with (length (L ++ [a])) by (rewrite length_app; cbn; lia). apply valat_last. Qed.

    (** *** The slots of a call *)

    Definition dsi (Γ : list (Slot VE VF)) (H : FutureStore ES) (cs : list (RCall ES))
        (o : Sig.op (RelaxedSig.effect ES)) (dix : list nat) (hu : nat) : Slot VE VF :=
      dslot (evs Γ) (length Γ) (invD_tev (E := ES) k H (dep_of (map rc_h cs) dix) hu o).

    Definition dsr (Γ : list (Slot VE VF)) (H : FutureStore ES) (cs : list (RCall ES))
        (o : Sig.op (RelaxedSig.effect ES)) (dix : list nat) (hu : nat) (v : Sig.ar o) : Slot VE VF :=
      dslot (evs (Γ ++ [dsi Γ H cs o dix hu])) (length (Γ ++ [dsi Γ H cs o dix hu])) (res_tev (E := ES) k hu o v).

    (** The machine invariant: the calls and the canonical slots, and per
        state the facts the next call reads. *)
    Definition dinv (st : DSt) (cs : list (RCall ES)) (Γ : list (Slot VE VF)) (H : FutureStore ES) : Prop :=
      DCalls cs /\ SlotsOK Γ /\
      match st with
      | DLd n => length cs = n /\ XZero (evs Γ)
      | DXchg n tl s => length cs = n /\ XZero (evs Γ) /\ s < tl /\ tlh (evs Γ) n = tl /\
          exists n' x, n = S n' /\ nth_error cs n' = Some x /\
            ((s = 0 /\ rc_op x = op_ld /\ valat (evs Γ) (S (2 * n')) = tl) \/ (exists s', s = S s' /\ rc_op x = op_xchg s'))
      | DRet x => x <> 0 /\ exists n' c, length cs = S n' /\ nth_error cs n' = Some c /\ isxb (rc_op c) = true /\
          valat (evs Γ) (S (2 * n')) = x
      end.

    Lemma dinv_init : dinv (DLd 0) [] [] empty_store.
    Proof. split; [exact dcalls_nil |]. split; [exact slotsok_nil |]. split; [reflexivity | exact xzero_nil]. Qed.

    (** *** A call of [ld] *)

    Lemma dcall_ld n cs Γ H :
      RunCtx k Γ H cs -> dinv (DLd n) cs Γ H ->
      RunCallOK Iq Rq Gq k Pinit dinv cs Γ H op_ld [] (fun tl => if Nat.eqb tl 0 then DLd (S n) else DXchg (S n) tl 0)
        (dsi Γ H cs op_ld []) (dsr Γ H cs op_ld []).
    Proof.
      intros Hc (Hd & Hok & Hl & Hz). pose proof (runctx_len k Γ H cs Hc) as HlΓ. rewrite Hl in HlΓ.
      assert (Hctx : forall hu (r : nat), handle_fresh hu H ->
                RunCtx k ((Γ ++ [dsi Γ H cs op_ld [] hu]) ++ [dsr Γ H cs op_ld [] hu r])
                  (Build_FutureEntry hu (@Resolved ES op_ld r) :: H) (cs ++ [@mkRCall ES hu op_ld []])).
      { intros hu r Hf. apply (runctx_snoc k Γ H cs _ _ hu op_ld [] r _ Hc Hf); [reflexivity | reflexivity |].
        apply resolve_here. }
      assert (Hd' : forall hu, DCalls (cs ++ [@mkRCall ES hu op_ld []])) by (intros hu; exact (dcalls_snoc_ld cs hu Hd)).
      assert (Hl1 : forall hu, length (Γ ++ [dsi Γ H cs op_ld [] hu]) = S (2 * n)) by (intros hu; rewrite length_app, HlΓ; cbn; lia).
      split; [| split; [| split; [| split]]].
      - intros hu. reflexivity.
      - intros hu Hf. unfold dsi.
        apply (dnew Γ _ _ _ _ [dsr Γ H cs op_ld [] hu 0] (Hctx hu 0 Hf) (Hd' hu) eq_refl Hok Hz).
        rewrite HlΓ, dguar_inv, dpost_inv. destruct (dsum_inv (evs Γ) n) as (En & Et & _). rewrite En, Et.
        apply (evupdate_conseq_i _ _ (fun s => ChainK (noxh (evs Γ) n) s));
          [| exact (upd_ldi hu (noxh (evs Γ) n) _ (fun s H0 => H0))].
        intros s _ [Hst Hin]. destruct n as [| n'].
        + exact (dstart_chain s Hst).
        + pose proof (Hin (2 * n')) as H0. unfold dinS in H0. rewrite dkind_chain, dsum_inv_succ in H0. exact H0.
      - intros hu r. reflexivity.
      - intros hu r Hf. unfold dsr.
        apply (dnew (Γ ++ [dsi Γ H cs op_ld [] hu]) _ _ _ _ [] (Hctx hu r Hf) (Hd' hu) ltac:(rewrite app_nil_r; reflexivity)
                 (slotsok_snoc Γ _ Hok)).
        { rewrite evs_app. apply xzero_snoc; [exact Hz | left; rewrite length_evs, HlΓ; apply even_double]. }
        rewrite (Hl1 hu), (dguar_odd _ _ (even_sdouble n)), dpost_res, dsum_res.
        apply (evupdate_conseq_i _ _ (RecLd hu)); [| exact (upd_ldr hu r _ (fun s H0 => H0))].
        intros s _ [_ Hin]. pose proof (Hin (2 * n)) as H0. unfold dinS in H0. rewrite dkind_own in H0. exact H0.
      - intros hu r H' Hf _ _. cbv beta.
        assert (HL2 : evs ((Γ ++ [dsi Γ H cs op_ld [] hu]) ++ [dsr Γ H cs op_ld [] hu r]) =
                      (evs Γ ++ [invD_tev (E := ES) k H (dep_of (map rc_h cs) []) hu op_ld]) ++ [res_tev (E := ES) k hu op_ld r])
          by (rewrite evs_snoc2; reflexivity).
        assert (HlL : length (evs Γ) = 2 * n) by (rewrite length_evs; exact HlΓ).
        assert (Hok2 : SlotsOK ((Γ ++ [dsi Γ H cs op_ld [] hu]) ++ [dsr Γ H cs op_ld [] hu r]))
          by (apply slotsok_snoc, slotsok_snoc, Hok).
        assert (Hz2 : XZero (evs ((Γ ++ [dsi Γ H cs op_ld [] hu]) ++ [dsr Γ H cs op_ld [] hu r]))).
        { rewrite HL2. apply xzero_snoc; [apply xzero_snoc; [exact Hz | left; rewrite HlL; apply even_double] |].
          right. left. reflexivity. }
        destruct (Nat.eqb_spec r 0) as [-> | Hr]; unfold dinv; (split; [exact (Hd' hu) |]); (split; [exact Hok2 |]).
        + split; [rewrite length_app, Hl; cbn; lia | exact Hz2].
        + split; [rewrite length_app, Hl; cbn; lia |]. split; [exact Hz2 |]. split; [lia |].
          split.
          * unfold tlh. rewrite HL2. rewrite lastld_S_ld.
            -- rewrite <- HlL, valat_new_res. reflexivity.
            -- rewrite <- HlL, opat_new_inv. reflexivity.
          * exists n, (@mkRCall ES hu op_ld []). split; [reflexivity |].
            split; [rewrite nth_error_app2 by lia; rewrite Hl, Nat.sub_diag; reflexivity |].
            left. split; [reflexivity |]. split; [reflexivity |].
            rewrite HL2, <- HlL, valat_new_res. reflexivity.
    Qed.

    (** *** A call of [xchg] *)

    Lemma tlh_new_nld L a b c : length L = 2 * c -> isldb (evop a) = false -> tlh ((L ++ [a]) ++ [b]) (S c) = tlh L c.
    Proof.
      intros Hl Ha. unfold tlh. rewrite lastld_S_nld by (rewrite <- Hl, opat_new_inv; exact Ha).
      rewrite <- app_assoc, lastld_app by lia. destruct (lastld L c) as [c' |] eqn:E; [| reflexivity].
      apply valat_app. pose proof (lastld_lt _ _ _ E). lia.
    Qed.

    Lemma dcall_x n tl s cs Γ H :
      RunCtx k Γ H cs -> dinv (DXchg n tl s) cs Γ H ->
      RunCallOK Iq Rq Gq k Pinit dinv cs Γ H (op_xchg s) (seq 0 n)
        (fun x => if Nat.eqb x 0 then (if Nat.ltb (S s) tl then DXchg (S n) tl (S s) else DLd (S n)) else DRet x)
        (dsi Γ H cs (op_xchg s) (seq 0 n)) (dsr Γ H cs (op_xchg s) (seq 0 n)).
    Proof.
      intros Hc (Hd & Hok & Hl & Hz & Hstl & Htl & n' & x & -> & Ex & Hprev).
      pose proof (runctx_len k Γ H cs Hc) as HlΓ. rewrite Hl in HlΓ.
      assert (HlL : length (evs Γ) = 2 * S n') by (rewrite length_evs; exact HlΓ).
      assert (Hctx : forall hu (r : nat), handle_fresh hu H ->
                RunCtx k ((Γ ++ [dsi Γ H cs (op_xchg s) (seq 0 (S n')) hu]) ++ [dsr Γ H cs (op_xchg s) (seq 0 (S n')) hu r])
                  (Build_FutureEntry hu (@Resolved ES (op_xchg s) r) :: H) (cs ++ [@mkRCall ES hu (op_xchg s) (seq 0 (S n'))])).
      { intros hu r Hf. apply (runctx_snoc k Γ H cs _ _ hu (op_xchg s) (seq 0 (S n')) r _ Hc Hf); [reflexivity | reflexivity |].
        apply resolve_here. }
      assert (Hd' : forall hu, DCalls (cs ++ [@mkRCall ES hu (op_xchg s) (seq 0 (S n'))])).
      { intros hu. rewrite <- Hl. exact (dcalls_snoc_x cs hu s Hd). }
      assert (Hl1 : forall hu, length (Γ ++ [dsi Γ H cs (op_xchg s) (seq 0 (S n')) hu]) = S (2 * S n'))
        by (intros hu; rewrite length_app, HlΓ; cbn; lia).
      assert (Eop1 : opat (evs Γ) (S (2 * n')) = rc_op x) by exact (opat_run_res k Γ H cs n' x Hc Ex).
      assert (Eop2 : opat (evs Γ) (2 * n') = rc_op x) by exact (opat_run k Γ H cs n' x Hc Ex).
      split; [| split; [| split; [| split]]].
      - intros hu. reflexivity.
      - intros hu Hf. unfold dsi.
        apply (dnew Γ _ _ _ _ [dsr Γ H cs (op_xchg s) (seq 0 (S n')) hu 0] (Hctx hu 0 Hf) (Hd' hu) eq_refl Hok Hz).
        rewrite HlΓ, dguar_inv, dpost_inv. destruct (dsum_inv (evs Γ) (S n')) as (En & Et & _). rewrite En, Et, Htl.
        apply (evupdate_conseq_i _ _ (XPre tl s)); [| exact (upd_xi hu tl s _ Hstl (fun st H0 => H0))].
        intros st HI [_ Hin].
        pose proof (Hin (2 * n')) as Hch. unfold dinS in Hch. rewrite dkind_chain, dsum_inv_succ in Hch.
        cbn [dinK ds_nox] in Hch.
        pose proof (Hin (S (2 * n'))) as Hpv. unfold dinS in Hpv. rewrite dkind_prev, dsum_inv_succ in Hpv by reflexivity.
        cbn [dinK ds_tl ds_op1 ds_val1] in Hpv. rewrite Eop1 in Hpv.
        destruct Hprev as [(-> & Ex0 & Hv) | (s' & -> & Ex0)].
        + (* a new scan: the previous call is the [ld] that read [tl] *)
          rewrite Ex0, Hv in Hpv. change (KScan tl 0 st) in Hpv.
          assert (Hnx : noxh (evs Γ) (S n') = noxh (evs Γ) n')
            by (unfold noxh; rewrite lastx_S_nx; [reflexivity | rewrite Eop2, Ex0; reflexivity]).
          rewrite Hnx in Hch. destruct (noxh (evs Γ) n') eqn:Enx.
          * destruct Hch as (l & Hg & Ht & Hi & Hne). exists l. split; [exact Hg |]. split; [exact Ht |].
            left. split; [exact Hi |]. split; [exact Hne | exact Hpv].
          * (* the status edge from the last [xchg] response *)
            destruct (lastx (evs Γ) n') as [c0 |] eqn:Elx; [| unfold noxh in Enx; rewrite Elx in Enx; discriminate Enx].
            pose proof (Hin (S (2 * c0))) as Hsa. unfold dinS in Hsa.
            rewrite dkind_status in Hsa;
              [| reflexivity
               | rewrite dsum_inv_succ; cbn [ds_op1]; rewrite Eop1, Ex0; reflexivity
               | rewrite dsum_inv_succ; cbn [ds_lastx]; rewrite lastx_S_nx; [exact Elx | rewrite Eop2, Ex0; reflexivity]
               | exact (lastx_lt _ _ _ Elx)].
            cbn [dinK] in Hsa.
            destruct Hch as (l & Hg & Ht & [(Hi & Hne) | [(Hdd & El) | (r0 & Hr)]]).
            -- exists l. split; [exact Hg |]. split; [exact Ht |]. left. split; [exact Hi |]. split; [exact Hne | exact Hpv].
            -- exists l. split; [exact Hg |]. split; [exact Ht |]. right. split; [exact Hdd | exact El].
            -- exfalso. destruct Hsa as [Hs1 | Hs1]; pose proof (klk_unique k _ _ st HI Hr Hs1) as E; discriminate E.
        + (* the scan goes on: the previous call is the [xchg] of the previous slot, with response [0] *)
          rewrite Ex0 in Hpv.
          assert (Hv0 : valat (evs Γ) (S (2 * n')) = 0) by (apply Hz; rewrite Eop1, Ex0; reflexivity).
          rewrite Hv0, Htl in Hpv. change (XFacts tl s' 0 st) in Hpv.
          assert (Hnx : noxh (evs Γ) (S n') = false)
            by (unfold noxh; rewrite lastx_S_x; [reflexivity | rewrite Eop2, Ex0; reflexivity]).
          rewrite Hnx in Hch. destruct Hch as (l & Hg & Ht & Hcs).
          destruct Hpv as [(H0 & _) | (_ & [(Hi & Hsc) | Hdd])]; [exfalso; exact (H0 eq_refl) | |].
          * exists l. split; [exact Hg |]. split; [exact Ht |]. left.
            destruct Hcs as [(_ & Hne) | [(Hdd & _) | (r0 & Hr)]];
              [| exfalso; pose proof (klk_unique k _ _ st HI Hi Hdd) as E; discriminate E
               | exfalso; pose proof (klk_unique k _ _ st HI Hi Hr) as E; discriminate E].
            split; [exact Hi |]. split; [exact Hne | exact Hsc].
          * exists l. split; [exact Hg |]. split; [exact Ht |]. right.
            destruct Hcs as [(Hi & _) | [(_ & El) | (r0 & Hr)]];
              [exfalso; pose proof (klk_unique k _ _ st HI Hdd Hi) as E; discriminate E |
               | exfalso; pose proof (klk_unique k _ _ st HI Hdd Hr) as E; discriminate E].
            split; [exact Hdd | exact El].
      - intros hu r. reflexivity.
      - intros hu r Hf. unfold dsr.
        apply (dnew (Γ ++ [dsi Γ H cs (op_xchg s) (seq 0 (S n')) hu]) _ _ _ _ [] (Hctx hu r Hf) (Hd' hu)
                 ltac:(rewrite app_nil_r; reflexivity) (slotsok_snoc Γ _ Hok)).
        { rewrite evs_app. apply xzero_snoc; [exact Hz | left; rewrite length_evs, HlΓ; apply even_double]. }
        assert (Ht1 : tlh (evs (Γ ++ [dsi Γ H cs (op_xchg s) (seq 0 (S n')) hu])) (S n') = tl)
          by (rewrite evs_app, tlh_app by (rewrite length_evs; lia); exact Htl).
        rewrite (Hl1 hu), (dguar_odd _ _ (even_sdouble (S n'))), dpost_res, dsum_res. cbn [ds_tl]. rewrite Ht1.
        apply (evupdate_conseq_i _ _ (RecX hu tl s)); [| exact (upd_xr hu tl s r _ (fun st H0 => H0))].
        intros st _ [_ Hin]. pose proof (Hin (2 * S n')) as H0. unfold dinS in H0. rewrite dkind_own in H0.
        cbn [dinK ds_tl] in H0. exact H0.
      - intros hu r H' Hf _ _. cbv beta.
        assert (HL2 : evs ((Γ ++ [dsi Γ H cs (op_xchg s) (seq 0 (S n')) hu]) ++ [dsr Γ H cs (op_xchg s) (seq 0 (S n')) hu r]) =
                      (evs Γ ++ [invD_tev (E := ES) k H (dep_of (map rc_h cs) (seq 0 (S n'))) hu (op_xchg s)]) ++
                        [res_tev (E := ES) k hu (op_xchg s) r])
          by (rewrite evs_snoc2; reflexivity).
        assert (Hok2 : SlotsOK ((Γ ++ [dsi Γ H cs (op_xchg s) (seq 0 (S n')) hu]) ++ [dsr Γ H cs (op_xchg s) (seq 0 (S n')) hu r]))
          by (apply slotsok_snoc, slotsok_snoc, Hok).
        assert (Hlen2 : length (cs ++ [@mkRCall ES hu (op_xchg s) (seq 0 (S n'))]) = S (S n'))
          by (rewrite length_app, Hl; cbn [length]; lia).
        assert (Hnth : nth_error (cs ++ [@mkRCall ES hu (op_xchg s) (seq 0 (S n'))]) (S n') = Some (@mkRCall ES hu (op_xchg s) (seq 0 (S n'))))
          by (rewrite nth_error_app2 by lia; rewrite Hl, Nat.sub_diag; reflexivity).
        destruct (Nat.eqb_spec r 0) as [Hr | Hr].
        + subst r.
          assert (Hz2 : XZero (evs ((Γ ++ [dsi Γ H cs (op_xchg s) (seq 0 (S n')) hu]) ++ [dsr Γ H cs (op_xchg s) (seq 0 (S n')) hu 0]))).
          { rewrite HL2. apply xzero_snoc; [apply xzero_snoc; [exact Hz | left; rewrite HlL; apply even_double] |].
            right. right. reflexivity. }
          destruct (Nat.ltb_spec (S s) tl) as [Hlt | Hge]; unfold dinv; (split; [exact (Hd' hu) |]); (split; [exact Hok2 |]).
          * split; [exact Hlen2 |]. split; [exact Hz2 |]. split; [exact Hlt |]. split.
            -- rewrite HL2, tlh_new_nld; [exact Htl | exact HlL | reflexivity].
            -- exists (S n'), (@mkRCall ES hu (op_xchg s) (seq 0 (S n'))). split; [reflexivity |]. split; [exact Hnth |].
               right. exists s. split; reflexivity.
          * split; [exact Hlen2 | exact Hz2].
        + unfold dinv. split; [exact (Hd' hu) |]. split; [exact Hok2 |]. split; [exact Hr |].
          exists (S n'), (@mkRCall ES hu (op_xchg s) (seq 0 (S n'))). split; [exact Hlen2 |]. split; [exact Hnth |].
          split; [reflexivity |]. rewrite HL2, <- HlL, valat_new_res. reflexivity.
    Qed.

    (** *** The return *)

    Definition XLast (x : nat) : Assn VE VF := fun st => exists r, KLk k (@ls_linr FP deq r) st /\ Pos.to_nat r = x.

    Lemma dclose x cs Γ H :
      RunCtx k Γ H cs -> dinv (DRet x) cs Γ H ->
      Close Iq Rq Gq k Pinit (fun r => Qq k deq r) (Pos.of_nat x) Γ H /\ Oq t deq h (own_invs Γ).
    Proof.
      intros Hc (Hd & Hok & Hx & n' & c & Hl & Ec & Hxc & Hv).
      pose proof (runctx_len k Γ H cs Hc) as HlΓ. rewrite Hl in HlΓ.
      destruct (runctx_store k Γ H cs Hc) as (_ & Hall & Hnd).
      split.
      - apply (close_done Iq Rq Gq k Pinit (fun r => Qq k deq r) (Pos.of_nat x) Γ H
                 (fun d => if Nat.eqb d (S (2 * n')) then XLast x else fun _ => True) (fun _ => True) Hall).
        (* every slot precedes the last response, the response of an [xchg] *)
        assert (Hball : forall g, g < length Γ -> before (evs Γ) g (S (2 * n'))).
        { intros g Hg. destruct (Nat.Even_or_Odd g) as [[b ->] | [b ->]].
          - apply (inv_before_all k Γ H cs b (S (2 * n')) Hc Hd); lia.
          - replace (2 * b + 1) with (S (2 * b)) by lia. destruct (Nat.eq_dec b n') as [-> | Hb]; [apply before_refl |].
            apply (res_before_x k Γ H cs b n' (S (2 * n')) c Hc Hd); [lia | lia | lia | exact Ec | exact Hxc]. }
        constructor.
        + intros d sd Hsd s HI Hp. destruct (Nat.eqb_spec d (S (2 * n'))) as [-> | _]; [| exact Logic.I].
          destruct (slotsok_at Γ _ sd Hok Hsd) as (_ & _ & Epo & _ & Ed). rewrite Epo, dpost_res in Hp.
          destruct (evat_res k Γ H cs n' c (sl_ev sd) Hc Ec Ed) as [Eo _].
          assert (Ev : evv (sl_ev sd) = x) by (rewrite <- Hv; unfold valat; rewrite Ed; reflexivity).
          unfold rpostS in Hp. rewrite Eo, Hxc, Ev in Hp.
          destruct Hp as [(_ & r & Hr & Hrx) | (E & _)]; [exists r; split; [exact Hr | exact Hrx] | exfalso; exact (Hx E)].
        + intros s _ _. exact Logic.I.
        + intros d g sg Hd' Hg Hnb. destruct (Nat.eqb_spec d (S (2 * n'))) as [-> | _]; [| apply Stable_true].
          exfalso. apply Hnb. apply Hball. apply nth_error_Some. rewrite Hg. discriminate.
        + intros g sg _. apply Stable_true.
        + intros d. destruct (Nat.eqb d (S (2 * n'))); [| apply Stable_true].
          intros s s' (r & Hr & Hrx) HR HI. exists r. split; [exact (klk_stable_r k _ s s' Hr HR HI) | exact Hrx].
        + apply Stable_true.
        + intros s HI _ Hfin.
          destruct (runctx_res_at k Γ H cs n' c Hc Ec) as (sr & v & Hsr & Hev).
          pose proof (Hfin (S (2 * n')) sr Hsr ltac:(unfold is_response; rewrite Hev; exact Logic.I)) as Hk.
          rewrite Nat.eqb_refl in Hk. destruct Hk as (r & (st & P & Hp & Hlk) & Hrx).
          exists st, P. split; [exact Hp |]. rewrite <- Hrx, Pos2Nat.id. exact Hlk.
      - (* the footprint: [ld]s and [xchg]s, the last one an [xchg] *)
        rewrite (own_invs_run k Γ H cs Hc). cbn [Oq]. unfold DeqShape.
        destruct (nth_error_split cs n' Ec) as (l1 & l2 & Ecs & Hl1).
        assert (El2 : l2 = []) by (destruct l2; [reflexivity | rewrite Ecs, length_app in Hl; cbn in Hl; lia]). subst l2.
        destruct (dcalls_acq cs n' c Hd Ec) as [Eo | (s & Eo)]; [rewrite Eo in Hxc; discriminate Hxc |].
        split; [| split].
        + rewrite map_map. exact Hnd.
        + apply Forall_forall. intros e He. apply in_map_iff in He as (c' & <- & Hc').
          apply In_nth_error in Hc' as (j & Hj). destruct (dcalls_acq cs j c' Hd Hj) as [Eo' | (s' & Eo')].
          * exists (rc_h c'), op_ld. split; [rewrite Eo'; reflexivity | left; reflexivity].
          * exists (rc_h c'), (op_xchg s'). split; [rewrite Eo'; reflexivity | right; exists s'; reflexivity].
        + exists (map (fun c0 => Build_ThreadEvent (fst k) (@InvEv ES (rc_h c0) (rc_op c0))) l1), (rc_h c), s.
          rewrite Ecs, map_app. cbn [map]. rewrite Eo. reflexivity.
    Qed.

    (** *** The machine *)

    Lemma dstep_ok st cs Γ H :
      RunCtx k Γ H cs -> dinv st cs Γ H ->
      RunStepOK Iq Rq Gq k Pinit dinv
        (fun a Γ' H' => Close Iq Rq Gq k Pinit (fun r => Qq k deq r) a Γ' H' /\ Oq t deq h (own_invs Γ'))
        cs Γ H (dnext st).
    Proof.
      intros Hc Hi. destruct st as [n | n tl s | x]; cbn [dnext RunStepOK].
      - exists (dsi Γ H cs op_ld []), (dsr Γ H cs op_ld []). exact (dcall_ld n cs Γ H Hc Hi).
      - exists (dsi Γ H cs (op_xchg s) (seq 0 n)), (dsr Γ H cs (op_xchg s) (seq 0 n)). exact (dcall_x n tl s cs Γ H Hc Hi).
      - exact (dclose x cs Γ H Hc Hi).
    Qed.
  End Deq.

  (** ** Part 7. The dequeue derivation, and T4 *)

  Theorem deq_provable t :
    MethodProvable Iq Rq Gq Mwhw t deq (fun h => Oq t deq h) (fun h r => Qq (t, h) deq r).
  Proof.
    apply (run_method_provable Iq Rq Gq Mwhw t deq _ _ dnext (DLd 0) (fun h => dinv t h)).
    - reflexivity.
    - intros h s Hs. exact (iq_postinvoke t h deq s Hs).
    - intros h r s Hq HI Hno. exact (qq_ret t h deq r s Hq HI Hno).
    - intros h. exact (dinv_init t h).
    - intros h st cs Γ H Hc Hi. exact (dstep_ok t h st cs Γ H Hc Hi).
  Qed.

  (** T4: every field of [RLHL2Hyps] for the weak Herlihy–Wing queue
      over [EIhl δRC], with the overlay presentation [POQueueRD]. *)
  Theorem whw_rlhl2 : RLHL2Hyps (VE := VE) (VF := VF) Iq Rq Gq Mwhw ((mem0, []), []) poqr_init.
  Proof.
    apply whw_rlhl2_of_provable. intros t [v |]; [exact (enq_provable t v) | exact (deq_provable t)].
  Qed.

End WHWQDeq.
