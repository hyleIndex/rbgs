(** * RLHL, part 4: soundness of the judgement (A4).

    [method_sound]: [MethodProvable I R G M t op Ω Q] implies
    [MethodSem I R G M t op], the semantic per-call triple (with the ghost
    thread frontier) of
    [RelaxedHoareBase], for *every* tagged trace and result the method
    body can produce ([program_produces_tagged]), i.e. for every guessed
    underlay response and every interleaving of asynchronous
    ([tagged_resolve]) responses.

    Proof structure.  We walk the derivation along the actual execution
    of the body ([walk], by induction on [program_execution_tagged]; each
    step is destructed while the configuration is a variable, and the
    derivation is read through the small-inversion view
    [RelaxedHoare.rp_unfold], so no [inversion] on a step at a [Wait] and
    no [JMeq]/[eq_rect_eq] is involved).  The invariant [W] relates the
    slot context [Γ] built by the derivation, the lazy store [Hl] of the
    derivation, the actual store [Ha], and the actual tagged prefix [trp]:

    - [lazier Hl Ha]: [Hl] differs from [Ha] only in handles that are
      resolved in [Ha] and still pending in [Hl] (early responses not yet
      placed);
    - every slot event occurs in [trp]; every event of [trp] is a slot
      event or such an early response;
    - every edge of the context's dag is an edge of [trp], in trace order
      and with the actual tags (lazy tags are smaller: [resolved_in Hl ⊆
      resolved_in Ha]);
    - bookkeeping facts on handles (freshness, uniqueness, responses after
      their invocation), all derived from handles, never from the
      injectivity of [ResEv];
    - [w_invs]: the invocations of [trp] and of [Γ] agree, in order
      (invocations are placed at their actual position; only responses
      are lazy).

    An early [tagged_resolve] step only extends [trp] and [Ha]; the
    response gets its slot later, at its [Wait] ([rp_wait_pending] used
    with the actual value) or at return ([close_resolve]).  At the end,
    [Close] yields [BarrierWith], [W] yields [RelaxedHoareDag.Corr], and
    [RelaxedHoareDag.ctx_triple] gives the certificate.  For the (init)
    clause of [MethodSem], the state [(σ, p', γ ++ ghost_new k tr)]
    satisfies [PostInvoke I k op (Ω h)] with [evs := inv_events (map untag
    tr)]: [Ω h] holds for these by the [Ret] obligation and [w_invs], and
    they are invocations of thread [t] by
    [program_execution_tagged_trace_tid].

    Assumptions: closed (checked with [Print Assumptions]). *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Relations.Relation_Operators.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedPossibility.
Require Import models.simlin.RelaxedModuleFacts.
Require Import models.simlin.RelaxedHoareBase.
Require Import models.simlin.RelaxedHoareDag.
Require Import models.simlin.RelaxedHoare.

Import ListNotations.


Module RelaxedHoareSound.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedPossibility.
  Import RelaxedModuleFacts.
  Import RelaxedHoareBase.
  Import RelaxedHoareDag.
  Import RelaxedHoare.

  (** ** Stores *)

  Section Stores.
    Context {E : RelaxedSig.t}.

    Definition cell_op (c : FutureCell E) : Sig.op (RelaxedSig.effect E) :=
      match c with
      | Pending op => op
      | Resolved op _ => op
      end.

    Definition entry_inv (t : tid) (e : FutureEntry E) : ThreadEvent E :=
      Build_ThreadEvent t (InvEv (fe_handle E e) (cell_op (fe_cell E e))).

    Definition entry_res (t : tid) (e : FutureEntry E) : option (ThreadEvent E) :=
      match fe_cell E e with
      | Pending _ => None
      | Resolved op r => Some (Build_ThreadEvent t (ResEv (fe_handle E e) op r))
      end.

    Lemma store_entry_unique (H : FutureStore E) e1 e2 :
      store_well_formed H -> In e1 H -> In e2 H -> fe_handle E e1 = fe_handle E e2 -> e1 = e2.
    Proof. intros Hwf H1 H2 Heq. eapply (nodup_map_in_inj (fe_handle E)); eauto. Qed.

    Lemma entry_res_handle t e ev :
      entry_res t e = Some ev -> fe_handle E e = event_handle (te_ev E ev).
    Proof.
      destruct e as [h [op | op r]]; cbn; intros Heq; [discriminate |].
      injection Heq as <-. reflexivity.
    Qed.

    Lemma entry_res_resolved t e ev :
      entry_res t e = Some ev -> cell_is_resolved (fe_cell E e).
    Proof. destruct e as [h [op | op r]]; cbn; intros Heq; [discriminate | exact Logic.I]. Qed.

    Lemma resolve_store_fwd h op r (H H' : FutureStore E) e :
      resolve_store h op r H H' -> In e H -> In e H' \/ e = Build_FutureEntry h (Pending op).
    Proof.
      intros Hres. induction Hres as [tail | h' cell H0 H0' Hneq Hres IH]; intros Hin.
      - destruct Hin as [<- | Hin]; [right; reflexivity | left; right; exact Hin].
      - destruct Hin as [<- | Hin]; [left; left; reflexivity |].
        destruct (IH Hin) as [Hin' | Heq]; [left; right; exact Hin' | right; exact Heq].
    Qed.

    Lemma resolve_store_keep_resolved h op r (H H' : FutureStore E) e :
      resolve_store h op r H H' -> In e H -> cell_is_resolved (fe_cell E e) -> In e H'.
    Proof.
      intros Hres Hin Hc. destruct (resolve_store_fwd _ _ _ _ _ _ Hres Hin) as [Hin' | ->];
        [exact Hin' | destruct Hc].
    Qed.

    Lemma resolve_store_exists h op r (H : FutureStore E) :
      pending_at h op H -> store_well_formed H -> exists H', resolve_store h op r H H'.
    Proof.
      induction H as [| e H IH]; intros Hp Hwf; [destruct Hp |].
      unfold store_well_formed in Hwf. cbn in Hwf. inversion Hwf as [| ? ? Hnin Hwf']; subst.
      destruct Hp as [-> | Hp].
      - eexists. apply resolve_here.
      - destruct (IH Hp Hwf') as (H' & Hres). destruct e as [h' cell].
        exists (Build_FutureEntry h' cell :: H'). apply resolve_next; [| exact Hres].
        intros ->. apply Hnin. apply in_map_iff. exists (Build_FutureEntry h (Pending op)).
        split; [reflexivity | exact Hp].
    Qed.

    (** *** The lazy store relation *)

    Definition lazy_entry (el ea : FutureEntry E) : Prop :=
      fe_handle E el = fe_handle E ea /\
      match fe_cell E el with
      | Resolved _ _ => ea = el
      | Pending op => fe_cell E ea = Pending op \/ exists r, fe_cell E ea = Resolved op r
      end.

    Definition lazier (Hl Ha : FutureStore E) : Prop := Forall2 lazy_entry Hl Ha.

    Lemma lazier_handles Hl Ha : lazier Hl Ha -> map (fe_handle E) Hl = map (fe_handle E) Ha.
    Proof.
      intros Hlz. induction Hlz as [| el ea Hl Ha [Hh _] _ IH]; cbn; [reflexivity |].
      rewrite Hh, IH. reflexivity.
    Qed.

    Lemma lazier_wf Hl Ha : lazier Hl Ha -> store_well_formed Ha -> store_well_formed Hl.
    Proof. unfold store_well_formed. intros Hlz. rewrite (lazier_handles _ _ Hlz). auto. Qed.

    Lemma lazier_fresh Hl Ha h : lazier Hl Ha -> handle_fresh h Ha -> handle_fresh h Hl.
    Proof. unfold handle_fresh. intros Hlz. rewrite (lazier_handles _ _ Hlz). auto. Qed.

    Lemma lazier_in_l Hl Ha el : lazier Hl Ha -> In el Hl -> exists ea, In ea Ha /\ lazy_entry el ea.
    Proof.
      intros Hlz. induction Hlz as [| el0 ea0 Hl Ha Hle _ IH]; intros Hin; [destruct Hin |].
      destruct Hin as [<- | Hin]; [exists ea0; split; [left; reflexivity | exact Hle] |].
      destruct (IH Hin) as (ea & Hea & Hl'). exists ea. split; [right; exact Hea | exact Hl'].
    Qed.

    Lemma lazier_in_r Hl Ha ea : lazier Hl Ha -> In ea Ha -> exists el, In el Hl /\ lazy_entry el ea.
    Proof.
      intros Hlz. induction Hlz as [| el0 ea0 Hl Ha Hle _ IH]; intros Hin; [destruct Hin |].
      destruct Hin as [<- | Hin]; [exists el0; split; [left; reflexivity | exact Hle] |].
      destruct (IH Hin) as (el & Hel & Hl'). exists el. split; [right; exact Hel | exact Hl'].
    Qed.

    (** A lazily resolved entry is an actual entry. *)
    Lemma lazier_resolved_entry Hl Ha h op r :
      lazier Hl Ha -> resolved_at h op r Hl -> resolved_at h op r Ha.
    Proof.
      intros Hlz Hin. destruct (lazier_in_l _ _ _ Hlz Hin) as (ea & Hea & _ & Hle).
      cbn in Hle. subst ea. exact Hea.
    Qed.

    Lemma lazier_resolved_in Hl Ha q : lazier Hl Ha -> resolved_in Hl q -> resolved_in Ha q.
    Proof.
      intros Hlz (op & r & Hin). exists op, r. eapply lazier_resolved_entry; eauto.
    Qed.

    (** An actually pending handle is lazily pending. *)
    Lemma lazier_pending Hl Ha h op : lazier Hl Ha -> pending_at h op Ha -> pending_at h op Hl.
    Proof.
      intros Hlz Hin. destruct (lazier_in_r _ _ _ Hlz Hin) as (el & Hel & Hh & Hle).
      destruct el as [hl [opl | opl rl]]; cbn in Hh, Hle; subst hl.
      - destruct Hle as [Hc | (r & Hc)]; [| discriminate]. injection Hc as ->. exact Hel.
      - discriminate.
    Qed.

    (** An actually resolved handle that is lazily resolved has the same
        entry in both stores. *)
    Lemma lazier_resolved_back Hl Ha h op r0 r :
      lazier Hl Ha -> store_well_formed Ha ->
      resolved_at h op r0 Hl -> resolved_at h op r Ha -> resolved_at h op r Hl.
    Proof.
      intros Hlz Hwf Hl0 Ha0.
      pose proof (lazier_resolved_entry _ _ _ _ _ Hlz Hl0) as Ha1.
      assert (Heq : Build_FutureEntry h (Resolved op r) = Build_FutureEntry h (Resolved op r0))
        by (eapply store_entry_unique; eauto).
      unfold resolved_at. rewrite Heq. exact Hl0.
    Qed.

    Lemma lazier_add Hl Ha h op :
      lazier Hl Ha -> lazier (add_pending h op Hl) (add_pending h op Ha).
    Proof. intros Hlz. constructor; [| exact Hlz]. split; [reflexivity | left; reflexivity]. Qed.

    Lemma lazier_cons_inv el ea Hl Ha :
      lazier (el :: Hl) (ea :: Ha) -> lazy_entry el ea /\ lazier Hl Ha.
    Proof. intros H. inversion H; subst. split; assumption. Qed.

    Lemma lazier_nil_l Ha : lazier [] Ha -> Ha = [].
    Proof. intros H. inversion H. reflexivity. Qed.

    Lemma lazier_cons_l el Hl Ha :
      lazier (el :: Hl) Ha -> exists ea Ha0, Ha = ea :: Ha0.
    Proof. intros H. inversion H; subst. eauto. Qed.

    Lemma resolve_store_cons_inv h op r e (H H' : FutureStore E) :
      resolve_store h op r (e :: H) H' ->
      (e = Build_FutureEntry h (Pending op) /\ H' = Build_FutureEntry h (Resolved op r) :: H) \/
      (fe_handle E e <> h /\ exists H0', H' = e :: H0' /\ resolve_store h op r H H0').
    Proof.
      intros Hres. inversion Hres as [tail Heq1 Heq2 | h' cell H0 H0' Hneq Hres' Heq1 Heq2].
      - left. split; reflexivity.
      - right. split; [exact Hneq |]. exists H0'. split; [reflexivity | exact Hres'].
    Qed.

    Lemma lazier_resolve_both Hl Ha Hl' Ha' h op r :
      lazier Hl Ha -> resolve_store h op r Hl Hl' -> resolve_store h op r Ha Ha' ->
      lazier Hl' Ha'.
    Proof.
      intros Hlz Hrl. revert Ha Ha' Hlz.
      induction Hrl as [tail | h' cell H0 H0' Hneq Hrl IH]; intros Ha Ha' Hlz Hra.
      - destruct (lazier_cons_l _ _ _ Hlz) as (ea & Ha0 & ->).
        destruct (lazier_cons_inv _ _ _ _ Hlz) as [[Hh _] Hlz0]. cbn in Hh.
        destruct (resolve_store_cons_inv _ _ _ _ _ _ Hra) as [[-> ->] | [Hne _]].
        + constructor; [split; reflexivity | exact Hlz0].
        + exfalso. apply Hne. symmetry. exact Hh.
      - destruct (lazier_cons_l _ _ _ Hlz) as (ea & Ha0 & ->).
        destruct (lazier_cons_inv _ _ _ _ Hlz) as [[Hh Hle] Hlz0]. cbn in Hh.
        destruct (resolve_store_cons_inv _ _ _ _ _ _ Hra) as [[-> ->] | [Hne (Ha0' & -> & Hra0)]].
        + exfalso. apply Hneq. exact Hh.
        + constructor; [split; assumption | eapply IH; eauto].
    Qed.

    (** An early (asynchronous) actual response. *)
    Lemma lazier_resolve_actual Hl Ha Ha' h op r :
      lazier Hl Ha -> resolve_store h op r Ha Ha' -> lazier Hl Ha'.
    Proof.
      intros Hlz Hra. revert Hl Hlz.
      induction Hra as [tail | h' cell H0 H0' Hneq Hra IH]; intros Hl Hlz.
      - destruct Hl as [| el Hl0]; [apply lazier_nil_l in Hlz; discriminate |].
        destruct (lazier_cons_inv _ _ _ _ Hlz) as [Hle Hlz0].
        destruct el as [hl cl]. destruct Hle as [Hh Hle]. cbn in Hh, Hle. subst hl.
        constructor; [| exact Hlz0]. split; [reflexivity |]. cbn.
        destruct cl as [opl | opl rl].
        + destruct Hle as [Hc | (r' & Hc)]; [| discriminate]. injection Hc as ->.
          right. exists r. reflexivity.
        + discriminate.
      - destruct Hl as [| el Hl0]; [apply lazier_nil_l in Hlz; discriminate |].
        destruct (lazier_cons_inv _ _ _ _ Hlz) as [Hle Hlz0].
        constructor; [exact Hle | apply IH; exact Hlz0].
    Qed.

    (** Lazy placement of an early response. *)
    Lemma lazier_resolve_lazy Hl Ha Hl' h op r :
      lazier Hl Ha -> store_well_formed Ha -> resolve_store h op r Hl Hl' ->
      resolved_at h op r Ha -> lazier Hl' Ha.
    Proof.
      intros Hlz Hwf Hrl. revert Ha Hlz Hwf.
      induction Hrl as [tail | h' cell H0 H0' Hneq Hrl IH]; intros Ha Hlz Hwf Hra.
      - destruct (lazier_cons_l _ _ _ Hlz) as (ea & Ha0 & ->).
        destruct (lazier_cons_inv _ _ _ _ Hlz) as [[Hh _] Hlz0]. cbn in Hh.
        unfold store_well_formed in Hwf. cbn in Hwf. apply NoDup_cons_iff in Hwf as [Hnin _].
        destruct Hra as [Hra | Hra].
        + constructor; [| exact Hlz0]. split; [exact Hh |]. cbn. exact Hra.
        + exfalso. apply Hnin. rewrite <- Hh. apply in_map_iff.
          eexists. split; [| exact Hra]. reflexivity.
      - destruct (lazier_cons_l _ _ _ Hlz) as (ea & Ha0 & ->).
        destruct (lazier_cons_inv _ _ _ _ Hlz) as [[Hh Hle] Hlz0]. cbn in Hh.
        unfold store_well_formed in Hwf. cbn in Hwf. apply NoDup_cons_iff in Hwf as [Hnin Hwf'].
        constructor; [split; assumption |]. apply IH; [exact Hlz0 | exact Hwf' |].
        destruct Hra as [Hra | Hra]; [| exact Hra].
        exfalso. apply Hneq. rewrite Hh, Hra. reflexivity.
    Qed.

    Lemma must_precede_transfer (x x' y y' : TaggedEvent E) :
      must_precede x y -> untag x' = untag x -> untag y' = untag y ->
      (forall q, tev_deps y q -> tev_deps y' q) -> must_precede x' y'.
    Proof.
      unfold must_precede. intros Hm Hx Hy Hd. rewrite Hx, Hy.
      destruct (te_ev E (untag x)); destruct (te_ev E (untag y)); auto.
    Qed.

    Lemma nodup_snoc {A : Type} (l : list A) a : NoDup l -> ~ In a l -> NoDup (l ++ [a]).
    Proof.
      intros Hnd Hnin. induction Hnd as [| x l Hx Hnd IH]; cbn; [constructor; [intros [] | constructor] |].
      constructor.
      - intros Hin. apply in_app_or in Hin. destruct Hin as [Hin | [<- | []]]; [exact (Hx Hin) |].
        apply Hnin. left. reflexivity.
      - apply IH. intros Hin. apply Hnin. right. exact Hin.
    Qed.
  End Stores.

  (** ** The walk invariant *)

  Section Walk.
    Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.
    Context (I : Assn VE VF) (R G : CallKey F -> PRel VE VF).
    Context (k : CallKey F) (Pinit : Assn VE VF).

    Local Abbreviation t := (fst k).
    Local Abbreviation SlotT := (Slot VE VF).

    Record W (Γ : list SlotT) (Hl Ha : FutureStore E) (trp : list (TaggedEvent E)) : Prop := {
      w_lazy : lazier Hl Ha;
      w_wf : store_well_formed Ha;
      w_ctx : CtxOK I R G k Pinit Γ;
      w_slot_in : forall j sj, nth_error Γ j = Some sj ->
        exists i m, nth_error trp i = Some m /\ untag m = untag (sl_ev sj);
      w_slot_res : forall j sj q, nth_error Γ j = Some sj ->
        is_response_of q (untag (sl_ev sj)) -> resolved_in Hl q;
      w_tr_in : forall i m, nth_error trp i = Some m ->
        (exists j sj, nth_error Γ j = Some sj /\ untag (sl_ev sj) = untag m) \/
        (exists h op ea, pending_at h op Hl /\ In ea Ha /\ fe_handle E ea = h /\
                         entry_res t ea = Some (untag m));
      w_edge : forall d j, dprec (evs Γ) d j ->
        exists i1 i2 a b sd sj, i1 < i2 /\
          nth_error trp i1 = Some a /\ nth_error trp i2 = Some b /\
          nth_error Γ d = Some sd /\ nth_error Γ j = Some sj /\
          untag a = untag (sl_ev sd) /\ untag b = untag (sl_ev sj) /\ must_precede a b;
      w_nodup : NoDup (map untag trp);
      w_slots_nodup : NoDup (map (fun s => untag (sl_ev s)) Γ);
      w_inv_store : forall i m h op, nth_error trp i = Some m -> te_ev E (untag m) = InvEv h op ->
        In h (map (fe_handle E) Ha);
      w_store_inv : forall e, In e Ha ->
        exists i m, nth_error trp i = Some m /\ untag m = entry_inv t e;
      w_res_store : forall i m, nth_error trp i = Some m -> is_response (untag m) ->
        exists ea, In ea Ha /\ entry_res t ea = Some (untag m);
      w_store_res : forall e ev, In e Ha -> entry_res t e = Some ev ->
        exists i m, nth_error trp i = Some m /\ untag m = ev;
      w_res_after_inv : forall i2 m2, nth_error trp i2 = Some m2 -> is_response (untag m2) ->
        exists i1 m1 op1, i1 < i2 /\ nth_error trp i1 = Some m1 /\
          te_ev E (untag m1) = InvEv (event_handle (te_ev E (untag m2))) op1;
      w_inv_unique : forall i i' m m' h op op',
        nth_error trp i = Some m -> nth_error trp i' = Some m' ->
        te_ev E (untag m) = InvEv h op -> te_ev E (untag m') = InvEv h op' -> i = i';
      (* invocations are placed at their actual position (only responses
         are lazy), so the invocation subsequences agree *)
      w_invs : inv_events (map untag trp) = inv_events (map untag (evs Γ))
    }.

    Lemma w_init : W [] empty_store empty_store [].
    Proof.
      constructor; try (intros; match goal with H : nth_error [] ?i = _ |- _ => destruct i; discriminate end).
      - constructor.
      - constructor.
      - apply ctxok_nil.
      - intros d j Hd. apply dprec_bound in Hd. cbn in Hd. lia.
      - constructor.
      - constructor.
      - intros e [].
      - intros e ev [].
      - reflexivity.
    Qed.

    (** Appending a slot whose event is appended to the trace. *)
    Lemma w_edge_snoc (Γ : list SlotT) (trp : list (TaggedEvent E)) (sl : SlotT) (m : TaggedEvent E) :
      (forall j sj, nth_error Γ j = Some sj ->
         exists i m, nth_error trp i = Some m /\ untag m = untag (sl_ev sj)) ->
      (forall d j, dprec (evs Γ) d j ->
        exists i1 i2 a b sd sj, i1 < i2 /\
          nth_error trp i1 = Some a /\ nth_error trp i2 = Some b /\
          nth_error Γ d = Some sd /\ nth_error Γ j = Some sj /\
          untag a = untag (sl_ev sd) /\ untag b = untag (sl_ev sj) /\ must_precede a b) ->
      untag m = untag (sl_ev sl) -> (forall q, tev_deps (sl_ev sl) q -> tev_deps m q) ->
      forall d j, dprec (evs (Γ ++ [sl])) d j ->
        exists i1 i2 a b sd sj, i1 < i2 /\
          nth_error (trp ++ [m]) i1 = Some a /\ nth_error (trp ++ [m]) i2 = Some b /\
          nth_error (Γ ++ [sl]) d = Some sd /\ nth_error (Γ ++ [sl]) j = Some sj /\
          untag a = untag (sl_ev sd) /\ untag b = untag (sl_ev sj) /\ must_precede a b.
    Proof.
      intros Hin Hedge Hm Htag d j Hd.
      pose proof (dprec_bound _ _ _ Hd) as Hjb. rewrite length_evs, length_app in Hjb. cbn in Hjb.
      destruct (Nat.lt_ge_cases j (length Γ)) as [Hlt | Hge].
      - rewrite evs_app in Hd. apply (dprec_app_iff (evs Γ) _ d j) in Hd; [| rewrite length_evs; exact Hlt].
        destruct (Hedge d j Hd) as (i1 & i2 & a & b & sd & sj & Hi & Ha & Hb & Hsd & Hsj & Hua & Hub & Hmp).
        exists i1, i2, a, b, sd, sj. split; [exact Hi |].
        split; [apply nth_error_snoc_old; exact Ha |]. split; [apply nth_error_snoc_old; exact Hb |].
        split; [apply nth_error_snoc_old; exact Hsd |]. split; [apply nth_error_snoc_old; exact Hsj |].
        auto.
      - assert (j = length Γ) by lia. subst j.
        inversion Hd as [d0 j0 x y Hlt Hx Hy Hmp]; subst.
        rewrite evs_app in Hx, Hy. rewrite nth_error_app1 in Hx by (rewrite length_evs; exact Hlt).
        rewrite <- (length_evs Γ) in Hy. rewrite nth_error_app2 in Hy by lia.
        rewrite Nat.sub_diag in Hy. cbn in Hy. injection Hy as <-.
        unfold evs in Hx. rewrite nth_error_map in Hx.
        destruct (nth_error Γ d) as [sd |] eqn:Hsd; cbn in Hx; [| discriminate]. injection Hx as <-.
        destruct (Hin d sd Hsd) as (i1 & a & Ha & Hua).
        exists i1, (length trp), a, m, sd, sl.
        split; [eapply nth_error_lt; eauto |].
        split; [apply nth_error_snoc_old; exact Ha |]. split; [apply nth_error_snoc_last |].
        split; [apply nth_error_snoc_old; exact Hsd |]. split; [apply nth_error_snoc_last |].
        split; [exact Hua |]. split; [exact Hm |].
        eapply must_precede_transfer; eauto.
    Qed.

    Ltac snoc_old := apply nth_error_snoc_old.

    (** *** Invocation step ([Future] / [FutureD]) *)
    Lemma w_invoke Γ Hl Ha trp (sl : SlotT) h op (tagA : RelaxedSig.handle E -> Prop) :
      W Γ Hl Ha trp -> handle_fresh h Ha -> NewSlotOK I R G k Pinit Γ sl ->
      untag (sl_ev sl) = Build_ThreadEvent t (InvEv h op) ->
      (forall q, tev_deps (sl_ev sl) q -> tagA q) ->
      W (Γ ++ [sl]) (add_pending h op Hl) (add_pending h op Ha)
        (trp ++ [Build_TaggedEvent (Build_ThreadEvent t (InvEv h op)) tagA]).
    Proof.
      intros HW Hfresh Hok Hev Htag.
      destruct HW as [Hlz Hwf Hctx Hsin Hsres Htrin Hedge Hnd Hsnd Hinvst Hstinv Hresst Hstres Hrai Hiu Hinvs].
      set (m := Build_TaggedEvent (Build_ThreadEvent t (InvEv h op)) tagA).
      assert (Hnot : forall i m' op', nth_error trp i = Some m' -> te_ev E (untag m') <> InvEv h op').
      { intros i m' op' Hi Hte. apply Hfresh. eapply Hinvst; eauto. }
      constructor.
      - apply lazier_add. exact Hlz.
      - apply add_pending_well_formed; assumption.
      - apply ctxok_snoc; assumption.
      - intros j sj Hj. destruct (nth_error_snoc_cases _ _ _ _ Hj) as [[Hlt Hj'] | [-> ->]].
        + destruct (Hsin j sj Hj') as (i & m' & Hi & Heq). exists i, m'.
          split; [snoc_old; exact Hi | exact Heq].
        + exists (length trp), m. split; [apply nth_error_snoc_last | rewrite Hev; reflexivity].
      - intros j sj q Hj Hq. destruct (nth_error_snoc_cases _ _ _ _ Hj) as [[Hlt Hj'] | [-> ->]].
        + destruct (Hsres j sj q Hj' Hq) as (op' & r' & Hin). exists op', r'. right. exact Hin.
        + rewrite Hev in Hq. destruct Hq.
      - intros i m' Hi. destruct (nth_error_snoc_cases _ _ _ _ Hi) as [[Hlt Hi'] | [-> ->]].
        + destruct (Htrin i m' Hi') as [(j & sj & Hj & Heq) | (h0 & op0 & ea & Hp & Hea & Hh & Hr)].
          * left. exists j, sj. split; [snoc_old; exact Hj | exact Heq].
          * right. exists h0, op0, ea. split; [right; exact Hp |]. split; [right; exact Hea |]. auto.
        + left. exists (length Γ), sl. split; [apply nth_error_snoc_last | rewrite Hev; reflexivity].
      - apply w_edge_snoc; [exact Hsin | exact Hedge | rewrite Hev; reflexivity | exact Htag].
      - rewrite map_app. apply nodup_snoc; [exact Hnd |]. intros Hin. apply in_map_iff in Hin.
        destruct Hin as (m' & Hm' & Hin). apply In_nth_error in Hin. destruct Hin as (i & Hi).
        apply (Hnot i m' op Hi). rewrite Hm'. reflexivity.
      - rewrite map_app. apply nodup_snoc; [exact Hsnd |]. intros Hin. apply in_map_iff in Hin.
        destruct Hin as (s & Hs & Hin). apply In_nth_error in Hin. destruct Hin as (j & Hj).
        destruct (Hsin j s Hj) as (i & m' & Hi & Heq). apply (Hnot i m' op Hi).
        rewrite Heq, Hs, Hev. reflexivity.
      - intros i m' h' op' Hi Hte. destruct (nth_error_snoc_cases _ _ _ _ Hi) as [[Hlt Hi'] | [-> ->]].
        + right. eapply Hinvst; eauto.
        + cbn in Hte. injection Hte as <- <-. left. reflexivity.
      - intros e He. destruct He as [<- | He].
        + exists (length trp), m. split; [apply nth_error_snoc_last | reflexivity].
        + destruct (Hstinv e He) as (i & m' & Hi & Heq). exists i, m'.
          split; [snoc_old; exact Hi | exact Heq].
      - intros i m' Hi Hr. destruct (nth_error_snoc_cases _ _ _ _ Hi) as [[Hlt Hi'] | [-> ->]].
        + destruct (Hresst i m' Hi' Hr) as (ea & Hea & Heq). exists ea. split; [right; exact Hea | exact Heq].
        + destruct Hr.
      - intros e ev He Hr. destruct He as [<- | He]; [discriminate |].
        destruct (Hstres e ev He Hr) as (i & m' & Hi & Heq). exists i, m'.
        split; [snoc_old; exact Hi | exact Heq].
      - intros i2 m2 Hi Hr. destruct (nth_error_snoc_cases _ _ _ _ Hi) as [[Hlt Hi'] | [-> ->]].
        + destruct (Hrai i2 m2 Hi' Hr) as (i1 & m1 & op1 & Hlt1 & Hi1 & Hte).
          exists i1, m1, op1. split; [exact Hlt1 |]. split; [snoc_old; exact Hi1 | exact Hte].
        + destruct Hr.
      - intros i i' m1 m2 h' op1 op2 Hi Hi' Hte Hte'.
        destruct (nth_error_snoc_cases _ _ _ _ Hi) as [[Hlt Hi0] | [-> ->]];
          destruct (nth_error_snoc_cases _ _ _ _ Hi') as [[Hlt' Hi0'] | [-> ->]].
        + eapply Hiu; eauto.
        + cbn in Hte'. injection Hte' as <- <-. exfalso. eapply Hnot; eauto.
        + cbn in Hte. injection Hte as <- <-. exfalso. eapply Hnot; eauto.
        + reflexivity.
      - rewrite evs_app, !map_app, !inv_events_app, Hinvs. f_equal.
        cbn [map evs]. rewrite Hev. reflexivity.
    Qed.

    (** Facts shared by the two steps that emit a response. *)
    Lemma resp_not_in (Γ : list SlotT) Hl Ha (trp : list (TaggedEvent E)) h op r :
      W Γ Hl Ha trp -> pending_at h op Ha ->
      forall i m', nth_error trp i = Some m' -> untag m' <> Build_ThreadEvent t (ResEv h op r).
    Proof.
      intros HW HpA i m' Hi Heq.
      destruct (w_res_store _ _ _ _ HW i m' Hi) as (ea & Hea & Hr); [rewrite Heq; exact Logic.I |].
      pose proof (entry_res_handle _ _ _ Hr) as Hh. rewrite Heq in Hh. cbn in Hh.
      pose proof (entry_res_resolved _ _ _ Hr) as Hc.
      assert (ea = Build_FutureEntry h (Pending op))
        by (eapply store_entry_unique; [apply (w_wf _ _ _ _ HW) | exact Hea | exact HpA | exact Hh]).
      subst ea. cbn in Hc. destruct Hc.
    Qed.

    Lemma store_after_resolve (Ha Ha' : FutureStore E) (trp : list (TaggedEvent E)) h op r
        (m : TaggedEvent E) :
      resolve_store h op r Ha Ha' ->
      pending_at h op Ha ->
      untag m = Build_ThreadEvent t (ResEv h op r) ->
      (forall e, In e Ha -> exists i m, nth_error trp i = Some m /\ untag m = entry_inv t e) ->
      (forall e ev, In e Ha -> entry_res t e = Some ev ->
         exists i m, nth_error trp i = Some m /\ untag m = ev) ->
      (forall e, In e Ha' -> exists i m', nth_error (trp ++ [m]) i = Some m' /\ untag m' = entry_inv t e) /\
      (forall e ev, In e Ha' -> entry_res t e = Some ev ->
         exists i m', nth_error (trp ++ [m]) i = Some m' /\ untag m' = ev).
    Proof.
      intros Hra HpA Hm Hstinv Hstres. split.
      - intros e He. destruct (resolve_store_back _ _ _ _ _ Hra e He) as [He0 | ->].
        + destruct (Hstinv e He0) as (i & m' & Hi & Heq). exists i, m'. split; [snoc_old; exact Hi | exact Heq].
        + destruct (Hstinv _ HpA) as (i & m' & Hi & Heq). exists i, m'. split; [snoc_old; exact Hi | exact Heq].
      - intros e ev He Hr. destruct (resolve_store_back _ _ _ _ _ Hra e He) as [He0 | ->].
        + destruct (Hstres e ev He0 Hr) as (i & m' & Hi & Heq). exists i, m'. split; [snoc_old; exact Hi | exact Heq].
        + cbn in Hr. injection Hr as <-. exists (length trp), m. split; [apply nth_error_snoc_last | exact Hm].
    Qed.

    (** *** Response step at a [Wait], with the response placed there *)
    Lemma w_respond Γ Hl Ha trp (sl : SlotT) h op r Hl' Ha' :
      W Γ Hl Ha trp -> resolve_store h op r Hl Hl' -> resolve_store h op r Ha Ha' ->
      NewSlotOK I R G k Pinit Γ sl ->
      untag (sl_ev sl) = Build_ThreadEvent t (ResEv h op r) ->
      (forall q, ~ tev_deps (sl_ev sl) q) ->
      W (Γ ++ [sl]) Hl' Ha' (trp ++ [Build_TaggedEvent (Build_ThreadEvent t (ResEv h op r)) no_deps]).
    Proof.
      intros HW Hrl Hra Hok Hev Htag.
      pose proof (resolve_store_pending _ _ _ _ _ Hra) as HpA.
      pose proof (resp_not_in _ _ _ _ h op r HW HpA) as Hnot.
      destruct HW as [Hlz Hwf Hctx Hsin Hsres Htrin Hedge Hnd Hsnd Hinvst Hstinv Hresst Hstres Hrai Hiu Hinvs].
      set (m := Build_TaggedEvent (Build_ThreadEvent t (ResEv h op r)) no_deps).
      destruct (store_after_resolve Ha Ha' trp h op r m Hra HpA eq_refl Hstinv Hstres) as [Hstinv' Hstres'].
      constructor.
      - eapply lazier_resolve_both; eauto.
      - eapply resolve_store_well_formed; eauto.
      - apply ctxok_snoc; assumption.
      - intros j sj Hj. destruct (nth_error_snoc_cases _ _ _ _ Hj) as [[Hlt Hj'] | [-> ->]].
        + destruct (Hsin j sj Hj') as (i & m' & Hi & Heq). exists i, m'.
          split; [snoc_old; exact Hi | exact Heq].
        + exists (length trp), m. split; [apply nth_error_snoc_last | rewrite Hev; reflexivity].
      - intros j sj q Hj Hq. destruct (nth_error_snoc_cases _ _ _ _ Hj) as [[Hlt Hj'] | [-> ->]].
        + eapply resolved_in_resolve_mono; [exact Hrl | eapply Hsres; eauto].
        + rewrite Hev in Hq. cbn in Hq. subst q. exists op, r. eapply resolve_store_resolved. exact Hrl.
      - intros i m' Hi. destruct (nth_error_snoc_cases _ _ _ _ Hi) as [[Hlt Hi'] | [-> ->]].
        + destruct (Htrin i m' Hi') as [(j & sj & Hj & Heq) | (h0 & op0 & ea & Hp & Hea & Hh & Hr)].
          * left. exists j, sj. split; [snoc_old; exact Hj | exact Heq].
          * destruct (resolve_store_fwd _ _ _ _ _ _ Hrl Hp) as [Hp' | Heq].
            -- right. exists h0, op0, ea. split; [exact Hp' |]. split; [| auto].
               eapply resolve_store_keep_resolved; [exact Hra | exact Hea | eapply entry_res_resolved; eauto].
            -- exfalso. apply (f_equal (fe_handle E)) in Heq. cbn in Heq. rewrite Heq in Hh.
               assert (ea = Build_FutureEntry h (Pending op))
                 by (eapply store_entry_unique; [exact Hwf | exact Hea | exact HpA | exact Hh]).
               subst ea. discriminate.
        + left. exists (length Γ), sl. split; [apply nth_error_snoc_last | rewrite Hev; reflexivity].
      - apply w_edge_snoc; [exact Hsin | exact Hedge | rewrite Hev; reflexivity |].
        intros q Hq. exfalso. exact (Htag q Hq).
      - rewrite map_app. apply nodup_snoc; [exact Hnd |]. intros Hin. apply in_map_iff in Hin.
        destruct Hin as (m' & Hm' & Hin). apply In_nth_error in Hin. destruct Hin as (i & Hi).
        exact (Hnot i m' Hi Hm').
      - rewrite map_app. apply nodup_snoc; [exact Hsnd |]. intros Hin. apply in_map_iff in Hin.
        destruct Hin as (s & Hs & Hin). apply In_nth_error in Hin. destruct Hin as (j & Hj).
        destruct (Hsin j s Hj) as (i & m' & Hi & Heq). apply (Hnot i m' Hi).
        rewrite Heq, Hs, Hev. reflexivity.
      - intros i m' h' op' Hi Hte. destruct (nth_error_snoc_cases _ _ _ _ Hi) as [[Hlt Hi'] | [-> ->]].
        + rewrite <- (resolve_store_handles _ _ _ _ _ Hra). eapply Hinvst; eauto.
        + discriminate.
      - exact Hstinv'.
      - intros i m' Hi Hr. destruct (nth_error_snoc_cases _ _ _ _ Hi) as [[Hlt Hi'] | [-> ->]].
        + destruct (Hresst i m' Hi' Hr) as (ea & Hea & Heq). exists ea. split; [| exact Heq].
          eapply resolve_store_keep_resolved; [exact Hra | exact Hea | eapply entry_res_resolved; eauto].
        + exists (Build_FutureEntry h (Resolved op r)). split; [eapply resolve_store_resolved; eauto | reflexivity].
      - exact Hstres'.
      - intros i2 m2 Hi Hr. destruct (nth_error_snoc_cases _ _ _ _ Hi) as [[Hlt Hi'] | [-> ->]].
        + destruct (Hrai i2 m2 Hi' Hr) as (i1 & m1 & op1 & Hlt1 & Hi1 & Hte).
          exists i1, m1, op1. split; [exact Hlt1 |]. split; [snoc_old; exact Hi1 | exact Hte].
        + destruct (Hstinv _ HpA) as (i1 & m1 & Hi1 & Heq).
          exists i1, m1, op. split; [eapply nth_error_lt; eauto |].
          split; [snoc_old; exact Hi1 | rewrite Heq; reflexivity].
      - intros i i' m1 m2 h' op1 op2 Hi Hi' Hte Hte'.
        destruct (nth_error_snoc_cases _ _ _ _ Hi) as [[Hlt Hi0] | [-> ->]];
          destruct (nth_error_snoc_cases _ _ _ _ Hi') as [[Hlt' Hi0'] | [-> ->]];
          try discriminate.
        eapply Hiu; eauto.
      - rewrite evs_app, !map_app, !inv_events_app, Hinvs. f_equal.
        cbn [map evs]. rewrite Hev. reflexivity.
    Qed.

    (** *** An early (asynchronous) response: the derivation does not move *)
    Lemma w_early (Γ : list SlotT) Hl Ha (trp : list (TaggedEvent E)) h op r Ha' :
      W Γ Hl Ha trp -> resolve_store h op r Ha Ha' ->
      W Γ Hl Ha' (trp ++ [Build_TaggedEvent (Build_ThreadEvent t (ResEv h op r)) no_deps]).
    Proof.
      intros HW Hra.
      pose proof (resolve_store_pending _ _ _ _ _ Hra) as HpA.
      pose proof (resp_not_in _ _ _ _ h op r HW HpA) as Hnot.
      destruct HW as [Hlz Hwf Hctx Hsin Hsres Htrin Hedge Hnd Hsnd Hinvst Hstinv Hresst Hstres Hrai Hiu Hinvs].
      set (m := Build_TaggedEvent (Build_ThreadEvent t (ResEv h op r)) no_deps).
      destruct (store_after_resolve Ha Ha' trp h op r m Hra HpA eq_refl Hstinv Hstres) as [Hstinv' Hstres'].
      constructor.
      - eapply lazier_resolve_actual; eauto.
      - eapply resolve_store_well_formed; eauto.
      - exact Hctx.
      - intros j sj Hj. destruct (Hsin j sj Hj) as (i & m' & Hi & Heq). exists i, m'.
        split; [snoc_old; exact Hi | exact Heq].
      - exact Hsres.
      - intros i m' Hi. destruct (nth_error_snoc_cases _ _ _ _ Hi) as [[Hlt Hi'] | [-> ->]].
        + destruct (Htrin i m' Hi') as [(j & sj & Hj & Heq) | (h0 & op0 & ea & Hp & Hea & Hh & Hr)].
          * left. exists j, sj. auto.
          * right. exists h0, op0, ea. split; [exact Hp |]. split; [| auto].
            eapply resolve_store_keep_resolved; [exact Hra | exact Hea | eapply entry_res_resolved; eauto].
        + right. exists h, op, (Build_FutureEntry h (Resolved op r)).
          split; [eapply lazier_pending; eauto |].
          split; [eapply resolve_store_resolved; eauto |]. split; reflexivity.
      - intros d j Hd. destruct (Hedge d j Hd)
          as (i1 & i2 & a & b & sd & sj & Hi & Ha1 & Hb & Hsd & Hsj & Hua & Hub & Hmp).
        exists i1, i2, a, b, sd, sj. split; [exact Hi |].
        split; [snoc_old; exact Ha1 |]. split; [snoc_old; exact Hb |]. auto.
      - rewrite map_app. apply nodup_snoc; [exact Hnd |]. intros Hin. apply in_map_iff in Hin.
        destruct Hin as (m' & Hm' & Hin). apply In_nth_error in Hin. destruct Hin as (i & Hi).
        exact (Hnot i m' Hi Hm').
      - exact Hsnd.
      - intros i m' h' op' Hi Hte. destruct (nth_error_snoc_cases _ _ _ _ Hi) as [[Hlt Hi'] | [-> ->]].
        + rewrite <- (resolve_store_handles _ _ _ _ _ Hra). eapply Hinvst; eauto.
        + discriminate.
      - exact Hstinv'.
      - intros i m' Hi Hr. destruct (nth_error_snoc_cases _ _ _ _ Hi) as [[Hlt Hi'] | [-> ->]].
        + destruct (Hresst i m' Hi' Hr) as (ea & Hea & Heq). exists ea. split; [| exact Heq].
          eapply resolve_store_keep_resolved; [exact Hra | exact Hea | eapply entry_res_resolved; eauto].
        + exists (Build_FutureEntry h (Resolved op r)). split; [eapply resolve_store_resolved; eauto | reflexivity].
      - exact Hstres'.
      - intros i2 m2 Hi Hr. destruct (nth_error_snoc_cases _ _ _ _ Hi) as [[Hlt Hi'] | [-> ->]].
        + destruct (Hrai i2 m2 Hi' Hr) as (i1 & m1 & op1 & Hlt1 & Hi1 & Hte).
          exists i1, m1, op1. split; [exact Hlt1 |]. split; [snoc_old; exact Hi1 | exact Hte].
        + destruct (Hstinv _ HpA) as (i1 & m1 & Hi1 & Heq).
          exists i1, m1, op. split; [eapply nth_error_lt; eauto |].
          split; [snoc_old; exact Hi1 | rewrite Heq; reflexivity].
      - intros i i' m1 m2 h' op1 op2 Hi Hi' Hte Hte'.
        destruct (nth_error_snoc_cases _ _ _ _ Hi) as [[Hlt Hi0] | [-> ->]];
          destruct (nth_error_snoc_cases _ _ _ _ Hi') as [[Hlt' Hi0'] | [-> ->]];
          try discriminate.
        eapply Hiu; eauto.
      - rewrite map_app, inv_events_app, Hinvs. cbn. apply app_nil_r.
    Qed.

    (** *** Lazy placement of an early response (at its [Wait] or at return) *)
    Lemma w_lazy_place Γ Hl Ha trp (sl : SlotT) h op r Hl' :
      W Γ Hl Ha trp -> resolve_store h op r Hl Hl' -> resolved_at h op r Ha ->
      NewSlotOK I R G k Pinit Γ sl ->
      untag (sl_ev sl) = Build_ThreadEvent t (ResEv h op r) ->
      (forall q, ~ tev_deps (sl_ev sl) q) ->
      W (Γ ++ [sl]) Hl' Ha trp.
    Proof.
      intros HW Hrl Hra Hok Hev Htag.
      pose proof (resolve_store_pending _ _ _ _ _ Hrl) as HpL.
      pose proof (lazier_wf _ _ (w_lazy _ _ _ _ HW) (w_wf _ _ _ _ HW)) as HwfL.
      destruct HW as [Hlz Hwf Hctx Hsin Hsres Htrin Hedge Hnd Hsnd Hinvst Hstinv Hresst Hstres Hrai Hiu Hinvs].
      destruct (Hstres _ (Build_ThreadEvent t (ResEv h op r)) Hra eq_refl) as (i2 & m2 & Hi2 & Hm2).
      constructor.
      - eapply lazier_resolve_lazy; eauto.
      - exact Hwf.
      - apply ctxok_snoc; assumption.
      - intros j sj Hj. destruct (nth_error_snoc_cases _ _ _ _ Hj) as [[Hlt Hj'] | [-> ->]].
        + exact (Hsin j sj Hj').
        + exists i2, m2. split; [exact Hi2 | rewrite Hev; exact Hm2].
      - intros j sj q Hj Hq. destruct (nth_error_snoc_cases _ _ _ _ Hj) as [[Hlt Hj'] | [-> ->]].
        + eapply resolved_in_resolve_mono; [exact Hrl | eapply Hsres; eauto].
        + rewrite Hev in Hq. cbn in Hq. subst q. exists op, r. eapply resolve_store_resolved. exact Hrl.
      - intros i m' Hi.
        destruct (Htrin i m' Hi) as [(j & sj & Hj & Heq) | (h0 & op0 & ea & Hp & Hea & Hh & Hr)].
        + left. exists j, sj. split; [snoc_old; exact Hj | exact Heq].
        + destruct (resolve_store_fwd _ _ _ _ _ _ Hrl Hp) as [Hp' | Heq].
          * right. exists h0, op0, ea. auto.
          * left. apply (f_equal (fe_handle E)) in Heq. cbn in Heq. rewrite Heq in Hh.
            assert (ea = Build_FutureEntry h (Resolved op r))
              by (eapply store_entry_unique; [exact Hwf | exact Hea | exact Hra | exact Hh]).
            subst ea. cbn in Hr. injection Hr as Hr.
            exists (length Γ), sl. split; [apply nth_error_snoc_last | rewrite Hev; exact Hr].
      - intros d j Hd.
        pose proof (dprec_bound _ _ _ Hd) as Hjb. rewrite length_evs, length_app in Hjb. cbn in Hjb.
        destruct (Nat.lt_ge_cases j (length Γ)) as [Hlt | Hge].
        + rewrite evs_app in Hd. apply (dprec_app_iff (evs Γ) _ d j) in Hd; [| rewrite length_evs; exact Hlt].
          destruct (Hedge d j Hd) as (i1 & i3 & a & b & sd & sj & Hi & Ha1 & Hb & Hsd & Hsj & Hua & Hub & Hmp).
          exists i1, i3, a, b, sd, sj. split; [exact Hi |]. split; [exact Ha1 |]. split; [exact Hb |].
          split; [snoc_old; exact Hsd |]. split; [snoc_old; exact Hsj |]. auto.
        + assert (j = length Γ) by lia. subst j.
          inversion Hd as [d0 j0 x y Hlt Hx Hy Hmp]; subst.
          rewrite evs_app in Hx, Hy. rewrite nth_error_app1 in Hx by (rewrite length_evs; exact Hlt).
          rewrite <- (length_evs Γ) in Hy. rewrite nth_error_app2 in Hy by lia.
          rewrite Nat.sub_diag in Hy. cbn in Hy. injection Hy as <-.
          unfold evs in Hx. rewrite nth_error_map in Hx.
          destruct (nth_error Γ d) as [sd |] eqn:Hsd; cbn in Hx; [| discriminate]. injection Hx as <-.
          destruct (Hsin d sd Hsd) as (i1 & a & Ha1 & Hua).
          (* the predecessor is the invocation of [h] *)
          unfold must_precede in Hmp. rewrite Hev in Hmp. cbn in Hmp.
          destruct (te_ev E (untag (sl_ev sd))) as [h1 op1 | h1 op1 r1] eqn:Hx; [| destruct Hmp].
          subst h1.
          assert (Hra2 : is_response (untag m2)) by (rewrite Hm2; exact Logic.I).
          destruct (Hrai i2 m2 Hi2 Hra2) as (i1' & m1' & op1' & Hlt1 & Hi1' & Hte1').
          rewrite Hm2 in Hte1'. cbn in Hte1'.
          assert (Hte1 : te_ev E (untag a) = InvEv h op1) by (rewrite Hua; exact Hx).
          assert (i1 = i1') by (eapply Hiu; [exact Ha1 | exact Hi1' | exact Hte1 | exact Hte1']).
          subst i1'.
          exists i1, i2, a, m2, sd, sl. split; [exact Hlt1 |]. split; [exact Ha1 |]. split; [exact Hi2 |].
          split; [snoc_old; exact Hsd |]. split; [apply nth_error_snoc_last |].
          split; [exact Hua |]. split; [rewrite Hev; exact Hm2 |].
          unfold must_precede. rewrite Hte1, Hm2. cbn. reflexivity.
      - exact Hnd.
      - rewrite map_app. apply nodup_snoc; [exact Hsnd |]. intros Hin. apply in_map_iff in Hin.
        destruct Hin as (s & Hs & Hin). apply In_nth_error in Hin. destruct Hin as (j & Hj).
        assert (Hq : is_response_of h (untag (sl_ev s))) by (rewrite Hs, Hev; reflexivity).
        destruct (Hsres j s h Hj Hq) as (op' & r' & Hin').
        assert (Build_FutureEntry h (Resolved op' r') = Build_FutureEntry h (Pending op))
          by (eapply store_entry_unique; [exact HwfL | exact Hin' | exact HpL | reflexivity]).
        discriminate.
      - exact Hinvst.
      - exact Hstinv.
      - exact Hresst.
      - exact Hstres.
      - exact Hrai.
      - exact Hiu.
      - rewrite evs_app, map_app, inv_events_app, <- Hinvs. cbn [map evs]. rewrite Hev. cbn.
        symmetry. apply app_nil_r.
    Qed.

    (** *** One program step *)

    Definition tlist (a : TAction E) : list (TaggedEvent E) :=
      match a with
      | TSilent => []
      | TEmit m => [m]
      end.

    Lemma step_sound {A : Type} (K : A -> list SlotT -> FutureStore E -> Prop) a c1 c2 :
      program_step_tagged t a c1 c2 ->
      forall Γ Hl trp, W Γ Hl (pc_futures c1) trp ->
        RProvable I R G k Pinit K Γ Hl (pc_prog c1) ->
        exists Γ' Hl', W Γ' Hl' (pc_futures c2) (trp ++ tlist a) /\
          RProvable I R G k Pinit K Γ' Hl' (pc_prog c2).
    Proof.
      intros Hstep.
      destruct Hstep as [op c h H Hfresh | op deps c h H Hfresh | op h r c H Hres
                        | op h r c H H' Hres | op h r p H H' Hres | p H];
        intros Γ Hl trp HW D; cbn [pc_futures pc_prog tlist] in *.
      - (* Future *)
        pose proof (rp_unfold I R G k Pinit K Γ Hl _ D) as V. cbn in V.
        destruct V as (sl & Hev & Hok & Hnext).
        assert (Hfl : handle_fresh h Hl) by (eapply lazier_fresh; [apply (w_lazy _ _ _ _ HW) | exact Hfresh]).
        exists (Γ ++ [sl h]), (add_pending h op Hl). split; [| apply Hnext; exact Hfl].
        apply w_invoke; [exact HW | exact Hfresh | apply Hok; exact Hfl | rewrite Hev; reflexivity |].
        rewrite Hev. cbn. intros q Hq. eapply lazier_resolved_in; [apply (w_lazy _ _ _ _ HW) | exact Hq].
      - (* FutureD *)
        pose proof (rp_unfold I R G k Pinit K Γ Hl _ D) as V. cbn in V.
        destruct V as (sl & Hev & Hok & Hnext).
        assert (Hfl : handle_fresh h Hl) by (eapply lazier_fresh; [apply (w_lazy _ _ _ _ HW) | exact Hfresh]).
        exists (Γ ++ [sl h]), (add_pending h op Hl). split; [| apply Hnext; exact Hfl].
        apply w_invoke; [exact HW | exact Hfresh | apply Hok; exact Hfl | rewrite Hev; reflexivity |].
        rewrite Hev. cbn. intros q [Hd Hq]. split; [exact Hd |].
        eapply lazier_resolved_in; [apply (w_lazy _ _ _ _ HW) | exact Hq].
      - (* Wait on an actually resolved handle *)
        pose proof (rp_unfold I R G k Pinit K Γ Hl _ D) as V. cbn in V.
        rewrite app_nil_r.
        destruct V as [[(r0 & Hr0) Hnext] | (sl & Hp & Hev & Hok & Hnext)].
        + exists Γ, Hl. split; [exact HW |]. apply Hnext.
          eapply lazier_resolved_back; [apply (w_lazy _ _ _ _ HW) | apply (w_wf _ _ _ _ HW) | exact Hr0 | exact Hres].
        + destruct (resolve_store_exists h op r Hl Hp) as (Hl' & Hrl).
          { eapply lazier_wf; [apply (w_lazy _ _ _ _ HW) | apply (w_wf _ _ _ _ HW)]. }
          exists (Γ ++ [sl r]), Hl'. split; [| eapply Hnext; exact Hrl].
          eapply w_lazy_place; [exact HW | exact Hrl | exact Hres | apply Hok | rewrite Hev; reflexivity |].
          rewrite Hev. cbn. intros q [].
      - (* Wait on an actually pending handle: the response is emitted now *)
        pose proof (rp_unfold I R G k Pinit K Γ Hl _ D) as V. cbn in V.
        destruct V as [[(r0 & Hr0) Hnext] | (sl & Hp & Hev & Hok & Hnext)].
        + exfalso.
          pose proof (lazier_resolved_entry _ _ _ _ _ (w_lazy _ _ _ _ HW) Hr0) as Ha0.
          pose proof (resolve_store_pending _ _ _ _ _ Hres) as HpA.
          assert (Build_FutureEntry h (Resolved op r0) = Build_FutureEntry h (Pending op))
            by (eapply store_entry_unique; [apply (w_wf _ _ _ _ HW) | exact Ha0 | exact HpA | reflexivity]).
          discriminate.
        + destruct (resolve_store_exists h op r Hl Hp) as (Hl' & Hrl).
          { eapply lazier_wf; [apply (w_lazy _ _ _ _ HW) | apply (w_wf _ _ _ _ HW)]. }
          exists (Γ ++ [sl r]), Hl'. split; [| eapply Hnext; exact Hrl].
          eapply w_respond; [exact HW | exact Hrl | exact Hres | apply Hok | rewrite Hev; reflexivity |].
          rewrite Hev. cbn. intros q [].
      - (* asynchronous response *)
        exists Γ, Hl. split; [| exact D]. eapply w_early; [exact HW | exact Hres].
      - (* Tau *)
        pose proof (rp_unfold I R G k Pinit K Γ Hl _ D) as V. cbn in V.
        exists Γ, Hl. rewrite app_nil_r. split; assumption.
    Qed.

    Lemma walk {A : Type} (K : A -> list SlotT -> FutureStore E -> Prop) c1 tr c3 :
      program_execution_tagged t c1 tr c3 ->
      forall Γ Hl trp, W Γ Hl (pc_futures c1) trp ->
        RProvable I R G k Pinit K Γ Hl (pc_prog c1) ->
        exists Γ' Hl', W Γ' Hl' (pc_futures c3) (trp ++ tr) /\
          RProvable I R G k Pinit K Γ' Hl' (pc_prog c3).
    Proof.
      intros Hexec. induction Hexec as [c | c1 c2 c3 tr Hstep Hexec IH | c1 c2 c3 m tr Hstep Hexec IH];
        intros Γ Hl trp HW D.
      - exists Γ, Hl. rewrite app_nil_r. auto.
      - destruct (step_sound K _ _ _ Hstep Γ Hl trp HW D) as (Γ1 & Hl1 & HW1 & D1).
        cbn [tlist] in HW1. rewrite app_nil_r in HW1. eapply IH; eauto.
      - destruct (step_sound K _ _ _ Hstep Γ Hl trp HW D) as (Γ1 & Hl1 & HW1 & D1).
        cbn [tlist] in HW1. destruct (IH Γ1 Hl1 (trp ++ [m]) HW1 D1) as (Γ2 & Hl2 & HW2 & D2).
        exists Γ2, Hl2. rewrite <- app_assoc in HW2. cbn in HW2. auto.
    Qed.

    (** *** Return: resolving the unwaited futures *)

    Lemma close_sound {A : Type} (Q : A -> Assn VE VF) (a : A) Γ Hl Ha tr :
      Close I R G k Pinit Q a Γ Hl -> W Γ Hl Ha tr -> all_resolved Ha ->
      exists Γ' fin fin0, CtxOK I R G k Pinit Γ' /\
        BarrierWith I R k Pinit Γ' fin fin0 (Q a) /\ Corr Γ' tr.
    Proof.
      intros HC. induction HC as [Γ Hl fin fin0 Hall Hbw | Γ Hl h op sl Hp Hev Hok Hnext IH];
        intros HW HallA.
      - exists Γ, fin, fin0. split; [exact (w_ctx _ _ _ _ HW) |]. split; [exact Hbw |].
        constructor.
        + exact (w_nodup _ _ _ _ HW).
        + exact (w_slots_nodup _ _ _ _ HW).
        + intros j sj Hj. destruct (w_slot_in _ _ _ _ HW j sj Hj) as (i & m & Hi & Heq).
          exists m. split; [eapply nth_error_In; eauto | exact Heq].
        + intros m Hm. apply In_nth_error in Hm. destruct Hm as (i & Hi).
          destruct (w_tr_in _ _ _ _ HW i m Hi) as [(j & sj & Hj & Heq) | (h0 & op0 & ea & Hp & _)].
          * exists j, sj. auto.
          * exfalso. unfold all_resolved in Hall. rewrite Forall_forall in Hall.
            exact (Hall _ Hp).
        + exact (w_edge _ _ _ _ HW).
      - destruct (lazier_in_l _ _ _ (w_lazy _ _ _ _ HW) Hp) as (ea & Hea & Hh & Hle).
        cbn in Hh, Hle.
        assert (Hres : exists r, resolved_at h op r Ha).
        { unfold all_resolved in HallA. rewrite Forall_forall in HallA.
          pose proof (HallA ea Hea) as Hc. destruct ea as [ha ca]. cbn in Hh, Hle, Hc. subst ha.
          destruct Hle as [-> | (r & ->)]; [destruct Hc | exists r; exact Hea]. }
        destruct Hres as (r & Hra).
        destruct (resolve_store_exists h op r Hl Hp) as (Hl' & Hrl).
        { eapply lazier_wf; [apply (w_lazy _ _ _ _ HW) | apply (w_wf _ _ _ _ HW)]. }
        apply (IH r Hl' Hrl); [| exact HallA].
        eapply w_lazy_place; [exact HW | exact Hrl | exact Hra | apply Hok | rewrite Hev; reflexivity |].
        rewrite Hev. cbn. intros q [].
    Qed.
  End Walk.

  (** ** Soundness *)

  Section Soundness.
    Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.
    Context (I : Assn VE VF) (R G : CallKey F -> PRel VE VF).
    Context (M : RelaxedModuleImpl E F).

    (** A4: every derivation implies the semantic per-call triple, for
        every overlay handle, produced tagged trace and result. *)
    Theorem method_sound t op Ω Q :
      MethodProvable I R G M t op Ω Q -> MethodSem I R G M t op.
    Proof.
      intros [HPI Hret Htriple] h tr ret (c' & Hexec & Hterm).
      pose proof (program_execution_tagged_trace_tid _ _ _ _ Hexec) as Htid.
      set (k := (t, h)). set (Pinit := PostInvoke I k op (Ω h)).
      destruct (walk I R G k Pinit
                  (fun a Γ H => Close I R G k Pinit (Q h) a Γ H /\ Ω h (own_invs Γ))
                  _ _ _ Hexec [] empty_store []
                  (w_init I R G k Pinit) (Htriple h)) as (Γ & Hl & HW & D).
      revert HW D. destruct Hterm as [Ha r Hall]. intros HW D. cbn [app pc_futures pc_prog] in HW, D.
      pose proof (rp_unfold I R G k Pinit _ Γ Hl _ D) as V. cbn in V. destruct V as [V HΩ].
      destruct (close_sound I R G k Pinit (Q h) r Γ Hl Ha tr V HW Hall)
        as (Γ' & fin & fin0 & Hctx & Hbw & Hco).
      destruct (ctx_triple I R G k Pinit Γ' fin fin0 (Q h r) op r tr Hctx Hbw
                  (fun s HQ HI Hno => Hret h r s HQ HI Hno) Hco) as [Htr Hinit].
      exists (Fam I Γ' fin fin0 tr). split; [exact Htr |].
      intros σ p γ p' HI Hinv.
      assert (HP : Pinit (σ, p', γ ++ ghost_new k tr)).
      { exists p, γ, (inv_events (map untag tr)). cbn [ps_mem ps_poss ps_ghost fst snd].
        split; [exact HI |]. split; [exact Hinv |]. split; [reflexivity |]. split.
        - unfold own_invs in HΩ. rewrite (w_invs _ _ _ _ _ _ _ _ _ HW). exact HΩ.
        - apply Forall_forall. intros ev Hev. destruct (inv_events_in _ _ Hev) as [Hin Hiv].
          split; [| exact Hiv]. apply in_map_iff in Hin. destruct Hin as (m & <- & Hm).
          rewrite Forall_forall in Htid. exact (Htid m Hm). }
      assert (HI' : I (σ, p', γ ++ ghost_new k tr)) by exact (HPI h _ HP).
      split; [exact HI' | apply Hinit; assumption].
    Qed.

    Corollary method_safe t op Ω Q :
      MethodProvable I R G M t op Ω Q -> MethodSafe I R G M t op.
    Proof. intros Hp. apply methodsem_safe. eapply method_sound. exact Hp. Qed.

    (** The blocking fragment (A5) is sound as well. *)
    Corollary chain_sound t op P Q :
      MethodProvableChain I R G M t op P Q -> MethodSem I R G M t op.
    Proof. intros Hc. eapply method_sound. exact (chain_provable I R G M t op P Q Hc). Qed.
  End Soundness.

End RelaxedHoareSound.
