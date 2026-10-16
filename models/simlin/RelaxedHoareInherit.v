(** * RLHL, part 9: readiness from semi-independence inheritance, and a
      generic renaming copy-cat instance (RLHL-3b, latest-review M-19)

    The RLHL instances over the decided layering interface
    ([RelaxedHoareCompLinSpec.EIhl]) were, before this file, all at
    semi-independence ∅ ([RelaxedHoareChecks.CounterEIhl],
    [CounterEIhlFrame]).  Their readiness lemma
    ([RelaxedHoareChecks.Counter.emit_ready]) concludes that the emitting
    call is the *oldest* [ls_inv] call of its thread, from "every
    same-thread ghost entry blocks", which holds only at SI = ∅.  This
    file replaces it by a lemma that works for any semi-independence
    relation that the overlay *inherits* from the underlay, and uses it
    for a generic instance.

    ** Part 1: readiness from inheritance ([emit_ready_SI])

    The invariant of the instances couples, per thread [t], the [ls_inv]
    calls of the abstract pool (oldest first) with the pending
    linearizing invocations of the ghost thread frontier (queue order):
    [inv_kops ρ t pool = gkops lz t ghost].  Both lists carry, besides
    the overlay call key, an underlay *operation*: [inv_kops] the image
    [ρ o] of the overlay operation [o] of the call, [gkops] the operation
    of the ghost entry.  [lz] selects the ghost entries that are
    linearizing (the others, e.g. an auxiliary access of a multi-future
    body, are not tracked by the coupling).

    [emit_ready_SI]: when the linearizing invocation [ρ o] of a call
    [k = (t, h)] is emitted with a ghost transition ([ghost_emit]: no
    older same-thread ghost entry [inv_blocks] it), the abstract
    invocation of [k] is enabled ([lin_invoke_update]), although [k] need
    not be the oldest [ls_inv] call of [t].  Reason: by the coupling, the
    older [ls_inv] calls of [t] are exactly the owners of the older
    linearizing ghost entries of [t], carrying [ρ o1]; such an entry does
    not block, so [~ ~ semi_independent E (ρ o1) (ρ o)]; the premise
    [Hsi] (inheritance, stable under double negation) gives
    [semi_independent F o1 o], which is what the directed
    [invocation_ready] asks of an older [ls_inv] entry.  The double
    negation carries no content (latest-review m-44): [Hsi] is
    equivalent to plain inheritance ([SI_E (ρ o1) (ρ o2) -> SI_F o1 o2])
    under [classic] ([ren_si_of_plain], [ren_si_plain_of_nn]), and
    follows from it without axioms whenever the underlay relation is
    stable under double negation ([ren_si_of_stable]), e.g. when it is
    decidable ([ren_si_of_dec]) or itself a negation ("different
    locations"); it holds for the empty relations.  [emit_ready_SI]
    uses no classical axiom.  The coupling is re-established after the
    step.

    ** Part 2: the renaming copy-cat ([ren_rlhl2]; the review's "Stronger
       approach 1")

    Data: underlay and overlay signatures [E], [F]; sequential
    specifications [δE] over [StE] and [δF] over [StF], with an
    abstraction [π : StE → StF]; an operation renaming
    [ρ : op F → op E] with a result map [back o : ar (ρ o) → ar o]; a
    filter [lz] of the linearizing underlay operations; a module [M]
    whose every body is the renaming call
    [Future (ρ o) (fun f => Wait f (fun r => Ret (back o r)))] ([HM],
    pointwise, so that modules defined by [match] qualify).

    Hypotheses (all discharged by the instances, see below):
    - [Hδ]: a [δE] step of [ρ o] with result [r] from [s] to [s'] is a
      [δF] step of [o] with result [back o r] from [π s] to [π s'];
    - [Hsi]: semi-independence inheritance, [~ ~ SI_E (ρ o1) (ρ o2) ->
      SI_F o1 o2];
    - [Hlz]: every [ρ o] is linearizing;
    - [Hinj]: [back o] is determined by the underlay record (equal
      records [Build_Op u (ρ o) r1 = Build_Op u (ρ o) r2] give [back o
      r1 = back o r2]).

    [Hinj] and the double negation in [Hsi] carry no content
    (latest-review m-44).  [Hinj] holds for every [E], [F], [ρ] and
    [back] under [eq_rect_eq] ([ren_inj_generic]), and without any axiom
    when [Sig.op E] has decidable equality ([ren_inj_of_dec]); it is a
    premise only so that [ren_rlhl2] itself is closed, and the instances
    discharge it without axioms ([cxy_inj]: the arity is the constant
    [nat]).  For [Hsi] see Part 1.  So the content of [ren_rlhl2] is
    [Hδ] (every [δE] step of [ρ o] is a [δF] step of [o] under [π] and
    [back], a total forward simulation of single steps) plus plain
    semi-independence inheritance; [HM] restricts it to single-future
    renaming bodies, with one linearizing ([lz]) invocation per call.

    Result: [ren_rlhl2 s0 : RLHL2Hyps Iren Rren Gren M ((s0, []), [])
    (π s0, [])] over [VE := EIhl δE] into [VF := EI δF], derived through
    [RelaxedHoareSound.method_sound] from a [MethodProvable] derivation
    ([ren_provable]).  The proof is [RelaxedHoareChecks.CounterEIhlFrame]
    made generic: the memory part of the rely and the guarantee is
    "any [EIhl δE] steps" ([eihl_steps]); the call's record is tracked by
    ownership ([eihl_mine], established by [eihl_mine_inv], kept by
    [eihl_mine_steps], read by [eihl_mine_res]); the invariant [Iren]
    contains the coupling [π (fst (fst σ)) = st] of the concrete and the
    abstract state, [eihl_rec_used], the readiness coupling of Part 1,
    and the bookkeeping of the abstract pending records.  The fields of
    [RLHL2Hyps] other than [h_sem] hold for every module
    ([ren_rlhl2_of_sem]); the per-event updates [inv_update] (readiness
    by [emit_ready_SI], abstract invocation by [Hδ]) and [res_update]
    (abstract response, by [eihl_mine_res] and [Hinj]) and the stability
    lemmas are stated for one call and reused by multi-future instances.
    Corollaries: [ren_complin_ei] (copy-cat inclusion over the plain
    [EI δE], [RelaxedHoareCompLinSpec.rlhl_complin_eihl]) and
    [ren_rel_lin] (every complete overlay trace of [M] over [EI δE] is
    relaxed-linearizable to [seq_legal δF (π s0)] under
    [semi_independent F], [RelaxedHoareCompLinSpec.complin_ei_rel_lin]).

    Instances (examples/Relaxed/RelaxedHoareCounterXY.v):
    - [cxy_rlhl2]: Counter_xy over the two-location SC memory, with
      semi-independence by location and by counter, both nonempty
      ([π := fun s => s], [lz := fun _ => true]);
    - [cxyb_rlhl2], [cxy00_rlhl2]: the same bodies and cell with other
      relations (choice (b): [si_mb], [si_cb]; and ∅ on both sides), the
      positive cells of the semi-independence table (latest-review
      m-46);
    - [CounterAsRename.counter_ren_rlhl2]: the SI = ∅ FAA→Inc counter of
      [RelaxedHoareChecks.CounterEIhl];
    - [CounterXYZ.cxyz_rlhl2]: a two-future variant (every operation
      also increments a private location [z]); not a renaming body, so
      it has its own derivation and uses [ren_rlhl2_of_sem],
      [inv_update], [res_update] with [π := fst] and [lz] excluding the
      [z] access.

    Scope and limitations.
    - [ren_provable] covers single-future bodies only: every [ns_if_*]
      premise of [ren_derivation] is vacuous, [Stable_true], or refuted
      by [before], exactly as in [CounterEIhlFrame].  Own-event
      interference discharged by stability is in
      [RelaxedHoareCounterXY.CounterXYZ].
    - The theorem is about the [EIhl] presentation of a sequential
      specification (the decided route, research-intent §8, M-20);
      nothing here mentions [memory/], and the identification of [M]
      over [EI δE] with ν_E;cc_E;⟦M⟧ needs the unproved absorption lemma
      (M-22).
    - Results go through [rlhl_complin_eihl] ([classic]) and
      [cc_rel_lin] ([eq_rect_eq], [classic]).

    Assumptions: [emit_ready_SI], the list and pool lemmas,
    [ren_rlhl2_of_sem] and [ren_rlhl2] are closed (no axiom);
    [ren_complin_ei] uses [Classical_Prop.classic] (through
    [RelaxedHoareCompLin.rinv_val]); [ren_rel_lin] uses [classic] and
    [Eqdep.Eq_rect_eq.eq_rect_eq] (through [RelaxedGSim.gsim_rel_lin]).
    Part 3 (the side conditions): [ren_inj_of_dec], [ren_si_of_stable],
    [ren_si_of_dec] and [ren_si_plain_of_nn] are closed;
    [ren_inj_generic] uses [eq_rect_eq] (through
    [Eqdep.EqdepTheory.inj_pair2]); [ren_si_of_plain] uses [classic]
    (through [Classical_Prop.NNPP]). *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Relations.Relation_Operators.
Require Import Stdlib.Logic.Eqdep_dec.
Require Stdlib.Logic.Eqdep.
Require Stdlib.Logic.Classical_Prop.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedPossibility.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.view.PrefixView.
Require Import models.simlin.RelaxedHoareBase.
Require Import models.simlin.RelaxedHoareDag.
Require Import models.simlin.RelaxedHoare.
Require Import models.simlin.RelaxedHoareSound.
Require Import models.simlin.RelaxedHoareSpec.
Require Import models.simlin.RelaxedHoareGSim.
Require Import models.simlin.RelaxedHoareCompLin.
Require Import models.simlin.RelaxedHoareCompLinSpec.

Import ListNotations.


Module RelaxedHoareInherit.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedPossibility.
  Import RelaxedHoareCompLin.
  Import RelaxedHoareCompLinSpec.
  Import RelaxedHoareBase.
  Import RelaxedHoareDag.
  Import RelaxedHoare.
  Import RelaxedHoareSound.

  (** ** List facts *)

  Section Lists.
    Context {A B : Type} (f : A -> B).

    (** Splitting a duplicate-free (under [f]) list at a given element is
        unique. *)
    Lemma split_unique (l1 l2 l1' l2' : list A) x :
      NoDup (map f (l1 ++ x :: l2)) -> l1 ++ x :: l2 = l1' ++ x :: l2' -> l1 = l1' /\ l2 = l2'.
    Proof.
      revert l1'. induction l1 as [| a l1 IH]; intros l1' Hnd Heq; destruct l1' as [| b l1']; cbn in *.
      - injection Heq as Heq. subst. auto.
      - injection Heq as Hb Heq. subst b. exfalso. apply NoDup_cons_iff in Hnd as [Hnin _].
        apply Hnin. apply in_map. rewrite Heq. apply in_or_app. right. left. reflexivity.
      - injection Heq as Ha Heq. subst a. exfalso. apply NoDup_cons_iff in Hnd as [Hnin _].
        apply Hnin. apply in_map. apply in_or_app. right. left. reflexivity.
      - injection Heq as Hab Heq. subst b. apply NoDup_cons_iff in Hnd as [_ Hnd'].
        destruct (IH l1' Hnd' Heq) as [-> ->]. auto.
    Qed.
  End Lists.

  Lemma lookup_unique_gen {F : RelaxedSig.t} (pool : LinPool F) k ls1 ls2 :
    lin_pool_well_formed pool -> lin_lookup k ls1 pool -> lin_lookup k ls2 pool -> ls1 = ls2.
  Proof.
    intros Hwf H1 H2.
    assert (Hk : lin_key (make_lin_entry k ls1) = lin_key (make_lin_entry k ls2))
      by (rewrite !lin_key_make_lin_entry; reflexivity).
    pose proof (nodup_map_in_inj lin_key pool _ _ Hwf H1 H2 Hk) as Heq.
    apply (f_equal (lin_state F)) in Heq. exact Heq.
  Qed.

  Lemma lin_update_exists_gen {F : RelaxedSig.t} (key : CallKey F) before after (pool : LinPool F) :
    lin_pool_well_formed pool -> lin_lookup key before pool ->
    exists pool', lin_update key before after pool pool'.
  Proof.
    induction pool as [| e pool IH]; intros Hwf Hl; [destruct Hl |].
    unfold lin_pool_well_formed, lin_domain in Hwf. cbn in Hwf.
    apply NoDup_cons_iff in Hwf as [Hnin Hwf].
    destruct Hl as [He | Hl].
    - subst e. eexists. apply lin_update_here.
    - destruct (IH Hwf Hl) as (pool' & Hu). exists (e :: pool').
      apply lin_update_next; [| exact Hu].
      intros Hk. apply Hnin. rewrite Hk. apply in_map_iff.
      exists (make_lin_entry key before). split; [apply lin_key_make_lin_entry | exact Hl].
  Qed.

  Lemma pinv_inv_gen {F : RelaxedSig.t} {VF : LTS F} t h op v pool p' :
    poss_invoke VF t h op (PossOk v pool) p' ->
    p' = PossOk v (make_lin_entry (t, h) (ls_inv op) :: pool) /\ lin_fresh (t, h) pool.
  Proof. intros Hi. inversion Hi as [v0 pool0 pool' Hins]; subst. inversion Hins; subst. auto. Qed.

  Lemma pret_inv_gen {F : RelaxedSig.t} {VF : LTS F} t h op r v pool p' :
    poss_return VF t h op r (PossOk v pool) p' ->
    exists pool', p' = PossOk v pool' /\ lin_remove (t, h) (ls_linr op r) pool pool'.
  Proof. intros Hr. inversion Hr; subst. eauto. Qed.

  (** ** Part 1: the readiness coupling and [emit_ready_SI] *)

  Section Ready.
    Context {E F : RelaxedSig.t}.
    Context (ρ : Sig.op (RelaxedSig.effect F) -> Sig.op (RelaxedSig.effect E)).
    Context (lz : Sig.op (RelaxedSig.effect E) -> bool).

    (** The contribution of one pool entry to the [ls_inv] list of thread
        [t]: its key and the underlay image of its operation. *)
    Definition ikop (t : tid) (e : LinEntry F) : list (CallKey F * Sig.op (RelaxedSig.effect E)) :=
      if Pos.eqb (lin_tid F e) t then
        match lin_state F e with ls_inv o => [(lin_key e, ρ o)] | _ => [] end
      else [].

    (** The [ls_inv] calls of thread [t], oldest first (pools are newest
        first), with the images of their operations. *)
    Fixpoint inv_kops (t : tid) (P : LinPool F) : list (CallKey F * Sig.op (RelaxedSig.effect E)) :=
      match P with
      | [] => []
      | e :: P' => inv_kops t P' ++ ikop t e
      end.

    (** The linearizing ghost entries of thread [t]. *)
    Definition gsel (t : tid) (e : ScheduledEvent E F) : bool :=
      Pos.eqb (fst (se_owner e)) t && lz (event_op (te_ev E (se_event e))).

    (** Their owners and operations, in queue order. *)
    Definition gkops (t : tid) (g : Ghost E F) : list (CallKey F * Sig.op (RelaxedSig.effect E)) :=
      map (fun e => (se_owner e, event_op (te_ev E (se_event e)))) (filter (gsel t) g).

    (** A ghost entry is an invocation of its owner's thread. *)
    Definition gwf (e : ScheduledEvent E F) : Prop :=
      te_tid E (se_event e) = fst (se_owner e) /\ is_invocation (se_event e).

    Lemma inv_kops_app t (P1 P2 : LinPool F) : inv_kops t (P1 ++ P2) = inv_kops t P2 ++ inv_kops t P1.
    Proof.
      induction P1 as [| e P1 IH]; cbn; [rewrite app_nil_r; reflexivity |].
      rewrite IH, app_assoc. reflexivity.
    Qed.

    Lemma gkops_app t (g1 g2 : Ghost E F) : gkops t (g1 ++ g2) = gkops t g1 ++ gkops t g2.
    Proof. unfold gkops. rewrite filter_app, map_app. reflexivity. Qed.

    Lemma gkops_one t (e : ScheduledEvent E F) :
      gkops t [e] = if gsel t e then [(se_owner e, event_op (te_ev E (se_event e)))] else [].
    Proof. unfold gkops. cbn. destruct (gsel t e); reflexivity. Qed.

    Lemma gkops_cons t (e : ScheduledEvent E F) g :
      gkops t (e :: g) = (if gsel t e then [(se_owner e, event_op (te_ev E (se_event e)))] else []) ++ gkops t g.
    Proof. unfold gkops. cbn. destruct (gsel t e); reflexivity. Qed.

    (** A non-linearizing ghost entry does not count. *)
    Lemma gkops_drop t (g1 g2 : Ghost E F) e :
      lz (event_op (te_ev E (se_event e))) = false -> gkops t (g1 ++ e :: g2) = gkops t (g1 ++ g2).
    Proof.
      intros Hlz. rewrite !gkops_app. f_equal. change (e :: g2) with ([e] ++ g2).
      rewrite gkops_app, gkops_one. unfold gsel. rewrite Hlz, andb_false_r. reflexivity.
    Qed.

    Lemma ikop_keys t e x : In x (ikop t e) -> fst x = lin_key e.
    Proof.
      unfold ikop. destruct (Pos.eqb (lin_tid F e) t); [| intros []].
      destruct (lin_state F e); [intros [<- | []]; reflexivity | intros [] | intros []].
    Qed.

    Lemma inv_kops_keys t (P : LinPool F) x : In x (inv_kops t P) -> In (fst x) (lin_domain P).
    Proof.
      induction P as [| e P IH]; cbn; [intros [] |]. intros Hin. apply in_app_or in Hin as [Hin | Hin].
      - right. exact (IH Hin).
      - left. symmetry. exact (ikop_keys t e x Hin).
    Qed.

    Lemma inv_kops_nodup t (P : LinPool F) : lin_pool_well_formed P -> NoDup (map fst (inv_kops t P)).
    Proof.
      induction P as [| e P IH]; cbn; [constructor |]. intros Hwf.
      unfold lin_pool_well_formed, lin_domain in Hwf. cbn in Hwf. apply NoDup_cons_iff in Hwf as [Hnin Hwf].
      rewrite map_app. apply NoDup_app; [exact (IH Hwf) | |].
      - unfold ikop. destruct (Pos.eqb (lin_tid F e) t); [| constructor].
        destruct (lin_state F e); cbn; repeat constructor. intros [].
      - intros a Ha Hb. apply in_map_iff in Ha as (x & <- & Hx). apply in_map_iff in Hb as (y & Hy & Hyin).
        apply Hnin. rewrite <- (ikop_keys t e y Hyin), Hy. exact (inv_kops_keys t P x Hx).
    Qed.

    Lemma inv_kops_in t (P : LinPool F) e o :
      In e P -> lin_tid F e = t -> lin_state F e = ls_inv o -> In (lin_key e, ρ o) (inv_kops t P).
    Proof.
      induction P as [| e0 P IH]; cbn; [intros [] |]. intros [<- | Hin] Ht Hs; apply in_or_app.
      - right. unfold ikop. rewrite Ht, Pos.eqb_refl, Hs. left. reflexivity.
      - left. exact (IH Hin Ht Hs).
    Qed.

    Lemma gkops_in t (g : Ghost E F) x :
      In x (gkops t g) ->
      exists e, In e g /\ fst (se_owner e) = t /\ se_owner e = fst x /\ event_op (te_ev E (se_event e)) = snd x.
    Proof.
      unfold gkops. intros Hin. apply in_map_iff in Hin as (e & <- & He).
      apply filter_In in He as [He Hsel]. unfold gsel in Hsel. apply andb_prop in Hsel as [Ht _].
      apply Pos.eqb_eq in Ht. exists e. auto.
    Qed.

    Lemma ikop_noninv t e : (forall o, lin_state F e <> ls_inv o) -> ikop t e = [].
    Proof.
      intros H. unfold ikop. destruct (Pos.eqb (lin_tid F e) t); [| reflexivity].
      destruct (lin_state F e) eqn:Hs; [exfalso; exact (H _ eq_refl) | reflexivity | reflexivity].
    Qed.

    (** Phase changes between non-[ls_inv] states, and removals of
        non-[ls_inv] entries, leave the coupling list unchanged. *)
    Lemma inv_kops_update key before after (P P' : LinPool F) t :
      (forall o, before <> ls_inv o) -> (forall o, after <> ls_inv o) ->
      lin_update key before after P P' -> inv_kops t P' = inv_kops t P.
    Proof.
      intros Hb Ha Hu. induction Hu as [tail | e P0 P0' Hne Hu IH]; cbn.
      - rewrite !ikop_noninv; [reflexivity | exact Hb | exact Ha].
      - rewrite IH. reflexivity.
    Qed.

    Lemma inv_kops_remove key st (P P' : LinPool F) t :
      (forall o, st <> ls_inv o) -> lin_remove key st P P' -> inv_kops t P' = inv_kops t P.
    Proof.
      intros Hst Hu. induction Hu as [tail | e P0 P0' Hne Hu IH]; cbn.
      - rewrite (ikop_noninv t (make_lin_entry key st)) by exact Hst. apply eq_sym, app_nil_r.
      - rewrite IH. reflexivity.
    Qed.

    (** Readiness from semi-independence inheritance (the review's
        [emit_ready_SI]).  The emitted linearizing invocation of [(t, h)]
        need not be the oldest of its thread; the older [ls_inv] calls of
        the thread are crossed because the overlay inherits the
        underlay's semi-independence. *)
    Lemma emit_ready_SI
        (Hsi : forall o1 o2, ~ ~ semi_independent E (ρ o1) (ρ o2) -> semi_independent F o1 o2)
        t h o hu (P : LinPool F) g1 g2 :
      lin_pool_well_formed P -> lin_lookup (t, h) (ls_inv o) P -> lz (ρ o) = true ->
      (forall t', inv_kops t' P =
                  gkops t' (g1 ++ Build_ScheduledEvent (t, h) (Build_ThreadEvent t (@InvEv E hu (ρ o))) :: g2)) ->
      Forall gwf g1 ->
      Forall (fun e => ~ inv_blocks (se_event e) (Build_ThreadEvent t (@InvEv E hu (ρ o)))) g1 ->
      exists P', lin_invoke_update t h o P P' /\ lin_pool_well_formed P' /\
                 forall t', inv_kops t' P' = gkops t' (g1 ++ g2).
    Proof.
      intros Hwf Hl Hlz HJ HJwf Hnb.
      destruct (in_split _ _ Hl) as (pre & older & HP).
      assert (Hwf0 := Hwf). unfold lin_pool_well_formed, lin_domain in Hwf0.
      rewrite HP, map_app in Hwf0. cbn in Hwf0.
      pose proof (NoDup_remove_2 _ _ _ Hwf0) as Hnin. rewrite lin_key_make_lin_entry in Hnin.
      assert (Hpre : forall y, In y pre -> lin_key y <> (t, h)).
      { intros y Hy Hk. apply Hnin. apply in_or_app. left. rewrite <- Hk. apply in_map. exact Hy. }
      assert (Hikx : forall t', ikop t' (make_lin_entry (t, h) (ls_inv o)) =
                                if Pos.eqb t t' then [((t, h), ρ o)] else []).
      { intros t'. unfold ikop. cbn. destruct (Pos.eqb t t'); reflexivity. }
      assert (Hikx' : forall t', ikop t' (make_lin_entry (t, h) (ls_lini o)) = []).
      { intros t'. apply ikop_noninv. intros o' Heq. discriminate Heq. }
      assert (Hgx : forall t', gsel t' (Build_ScheduledEvent (t, h) (Build_ThreadEvent t (@InvEv E hu (ρ o)))) =
                               Pos.eqb t t').
      { intros t'. unfold gsel. cbn. rewrite Hlz, andb_true_r. reflexivity. }
      assert (Hsplit : inv_kops t older = gkops t g1 /\ inv_kops t pre = gkops t g2).
      { pose proof (HJ t) as HJt. rewrite HP, inv_kops_app in HJt. cbn [inv_kops] in HJt.
        rewrite Hikx, Pos.eqb_refl in HJt.
        rewrite gkops_app, gkops_cons, Hgx, Pos.eqb_refl in HJt. rewrite <- app_assoc in HJt. cbn [app fst snd se_owner se_event te_ev event_op] in HJt.
        apply (split_unique fst) in HJt; [exact HJt |].
        pose proof (inv_kops_nodup t P Hwf) as Hnd. rewrite HP, inv_kops_app in Hnd. cbn [inv_kops] in Hnd.
        rewrite Hikx, Pos.eqb_refl, <- app_assoc in Hnd. exact Hnd. }
      destruct Hsplit as [Hold Hpre2].
      (* the older entries allow the invocation *)
      assert (Hready : invocation_ready t o older).
      { unfold invocation_ready. apply Forall_forall. intros e He.
        unfold older_entry_allows_invocation.
        destruct (Pos.eqb_spec (lin_tid F e) t) as [Ht | Ht]; [right | left; exact Ht].
        destruct (lin_state F e) as [o1 | o1 | o1 r1] eqn:Hs; [| exact Logic.I | exact Logic.I].
        pose proof (inv_kops_in t older e o1 He Ht Hs) as Hin. rewrite Hold in Hin.
        destruct (gkops_in t g1 _ Hin) as (e' & He' & Hte' & Hown & Hop). cbn [fst snd] in Hown, Hop.
        rewrite Forall_forall in HJwf, Hnb. destruct (HJwf e' He') as [Htid Hinv].
        pose proof (Hnb e' He') as Hnb'.
        apply Hsi. intros Hn. apply Hnb'. unfold inv_blocks.
        destruct (se_event e') as [te [hu' op' | hu' op' r']] eqn:Hev; cbn in Htid, Hinv, Hop |- *; [| destruct Hinv].
        split; [rewrite Htid; exact Hte' |]. rewrite Hop. exact Hn. }
      assert (Hu : lin_invoke_update t h o P (pre ++ make_lin_entry (t, h) (ls_lini o) :: older)).
      { rewrite HP. apply liu_app; [exact Hpre |]. apply lin_invoke_update_here. exact Hready. }
      exists (pre ++ make_lin_entry (t, h) (ls_lini o) :: older). split; [exact Hu | split].
      - eapply lin_invoke_update_well_formed; [exact Hu | exact Hwf].
      - intros t'. rewrite inv_kops_app. cbn [inv_kops]. rewrite Hikx', app_nil_r, gkops_app.
        destruct (Pos.eqb_spec t t') as [<- | Hne].
        + rewrite Hold, Hpre2. reflexivity.
        + pose proof (HJ t') as HJt'. rewrite HP, inv_kops_app in HJt'. cbn [inv_kops] in HJt'.
          rewrite Hikx in HJt'. apply Pos.eqb_neq in Hne. rewrite Hne, app_nil_r in HJt'.
          rewrite HJt', gkops_app, gkops_cons, Hgx, Hne. reflexivity.
    Qed.
  End Ready.

  (** ** Part 2: the renaming copy-cat over [EIhl δE] into [EI δF] *)

  Section Rename.
    Context {E F : RelaxedSig.t} {StE StF : Type}.
    Context (δE : StE -> forall o : Sig.op (RelaxedSig.effect E), Sig.ar o -> StE -> Prop).
    Context (δF : StF -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> StF -> Prop).
    (** The abstraction of the concrete state ([fun s => s] for the
        renaming copy-cat). *)
    Context (π : StE -> StF).
    Context (ρ : Sig.op (RelaxedSig.effect F) -> Sig.op (RelaxedSig.effect E)).
    (** The linearizing underlay operations ([fun _ => true] for the
        renaming copy-cat). *)
    Context (lz : Sig.op (RelaxedSig.effect E) -> bool).

    Local Abbreviation VE := (EIhl δE).
    Local Abbreviation VF := (RelaxedHoareSpec.EI δF).
    Local Abbreviation A := (Assn VE VF).
    Local Abbreviation POk v pool := (@PossOk F VF v pool).
    Local Abbreviation OpF := (RelaxedTraceLin.Op F).
    Local Abbreviation OpE := (RelaxedTraceLin.Op E).
    Local Abbreviation okey := (@RelaxedTraceLin.op_key F).
    Local Abbreviation oop := (@RelaxedTraceLin.op_op F).

    (** The invariant: the abstract state is the abstraction [π] of the
        concrete one; the readiness coupling of Part 1 (on the
        linearizing ghost entries, [lz]); the abstract pending records
        belong to [ls_lini] calls, one each; every pending concrete
        record has a used key. *)
    Definition Iren : A := fun s => exists st P pool,
      ps_poss s = POk (st, P) pool /\ π (fst (fst (ps_mem s))) = st /\ lin_pool_well_formed pool /\
      (forall t', inv_kops ρ t' pool = gkops lz t' (ps_ghost s)) /\ Forall gwf (ps_ghost s) /\
      (forall o : OpF, In o P -> lin_lookup (okey o) (ls_lini (oop o)) pool) /\
      NoDup (map okey P) /\
      eihl_rec_used δE (ps_mem s).

    (** Rely of [k]: memory moves by any [EIhl δE] steps; [k]'s pool
        entries and abstract records are kept. *)
    Definition Rren (k : CallKey F) : PRel VE VF := fun s s' =>
      eihl_steps δE (ps_mem s) (ps_mem s') /\
      exists v pool v' pool', ps_poss s = POk v pool /\ ps_poss s' = POk v' pool' /\
        (forall ls, lin_lookup k ls pool -> lin_lookup k ls pool') /\
        (forall o : OpF, okey o = k -> In o (snd v) -> In o (snd v')).

    (** Guarantee of [k]: memory moves by [EIhl δE] steps; the pool
        entries and abstract records of every other call are kept. *)
    Definition Gren (k : CallKey F) : PRel VE VF := fun s s' =>
      eihl_steps δE (ps_mem s) (ps_mem s') /\
      exists v pool v' pool', ps_poss s = POk v pool /\ ps_poss s' = POk v' pool' /\
        (forall k' ls, k' <> k -> lin_lookup k' ls pool -> lin_lookup k' ls pool') /\
        (forall o : OpF, okey o <> k -> In o (snd v) -> In o (snd v')).

    Lemma Gren_in_Rren k k' s s' : k' <> k -> Gren k' s s' -> Rren k s s'.
    Proof.
      intros Hne (Hm & v & pool & v' & pool' & Hp & Hp' & Hlk & HP). split; [exact Hm |].
      exists v, pool, v', pool'. split; [exact Hp |]. split; [exact Hp' |]. split.
      - intros ls Hl. apply Hlk; [intros Heq; apply Hne; symmetry; exact Heq | exact Hl].
      - intros o Hk. apply HP. rewrite Hk. intros Heq. apply Hne. symmetry. exact Heq.
    Qed.

    (** The rely admits every memory step, whatever the values. *)
    Lemma Rren_any_mem k σ σ' v pool γ γ' :
      eihl_steps δE σ σ' -> Rren k (σ, POk v pool, γ) (σ', POk v pool, γ').
    Proof. intros Hs. split; [exact Hs |]. exists v, pool, v, pool. repeat split; auto. Qed.

    Definition KInv (k : CallKey F) (o : Sig.op (RelaxedSig.effect F)) : A := fun s =>
      exists v pool, ps_poss s = POk v pool /\ lin_lookup k (ls_inv o) pool.

    Definition KLinr (k : CallKey F) (o : Sig.op (RelaxedSig.effect F)) (r : Sig.ar o) : A := fun s =>
      exists v pool, ps_poss s = POk v pool /\ lin_lookup k (ls_linr o r) pool.

    Lemma KInv_stable k o : Stable Iren (Rren k) (KInv k o).
    Proof.
      intros s s' (v & pool & Hp & Hl) (_ & v1 & pool1 & v1' & pool1' & Hp1 & Hp1' & Hlk & _) _.
      rewrite Hp in Hp1. injection Hp1 as <- <-. exists v1', pool1'. split; [exact Hp1' | apply Hlk; exact Hl].
    Qed.

    Lemma KLinr_stable k o r : Stable Iren (Rren k) (KLinr k o r).
    Proof.
      intros s s' (v & pool & Hp & Hl) (_ & v1 & pool1 & v1' & pool1' & Hp1 & Hp1' & Hlk & _) _.
      rewrite Hp in Hp1. injection Hp1 as <- <-. exists v1', pool1'. split; [exact Hp1' | apply Hlk; exact Hl].
    Qed.

    Context (back : forall o : Sig.op (RelaxedSig.effect F), Sig.ar (ρ o) -> Sig.ar o).

    (** After the underlay invocation of [k] on handle [hu]: [k] owns the
        record of its underlay call, with result [c] ([eihl_mine]); the
        abstract record of [k] has result [back o c]; [k] is at
        [ls_lini]. *)
    Definition KLini (k : CallKey F) (o : Sig.op (RelaxedSig.effect F)) (hu : RelaxedSig.handle E) : A := fun s =>
      exists c v pool, ps_poss s = POk v pool /\
        eihl_mine δE (fst k, hu) (@RelaxedTraceLin.Build_Op E (fst k, hu) (ρ o) c) (ps_mem s) /\
        In (@RelaxedTraceLin.Build_Op F k o (back o c)) (snd v) /\ lin_lookup k (ls_lini o) pool.

    Lemma KLini_stable k o hu : Stable Iren (Rren k) (KLini k o hu).
    Proof.
      intros s s' (c & v & pool & Hp & Hm & HP & Hl) (Hs & v1 & pool1 & v1' & pool1' & Hp1 & Hp1' & Hlk & HPk) _.
      rewrite Hp in Hp1. injection Hp1 as <- <-. exists c, v1', pool1'.
      split; [exact Hp1' |]. split; [exact (eihl_mine_steps δE _ _ _ _ Hs Hm) |].
      split; [apply HPk; [reflexivity | exact HP] | apply Hlk; exact Hl].
    Qed.

    Context (Hδ : forall s o r s', δE s (ρ o) r s' -> δF (π s) o (back o r) (π s')).
    (** The double negation carries no content: see Part 3
        ([ren_si_of_plain], [ren_si_of_stable], [ren_si_of_dec]). *)
    Context (Hsi : forall o1 o2, ~ ~ semi_independent E (ρ o1) (ρ o2) -> semi_independent F o1 o2).
    Context (Hlz : forall o, lz (ρ o) = true).
    (** No content either: it holds under [eq_rect_eq] for every [back]
        ([ren_inj_generic]), and without axioms for decidable [Sig.op E]
        ([ren_inj_of_dec]); see Part 3. *)
    Context (Hinj : forall u o (r1 r2 : Sig.ar (ρ o)),
                @RelaxedTraceLin.Build_Op E u (ρ o) r1 = @RelaxedTraceLin.Build_Op E u (ρ o) r2 ->
                back o r1 = back o r2).

    Section Call.
      Context (t : tid) (h : RelaxedSig.handle F) (o : Sig.op (RelaxedSig.effect F)).
      Local Abbreviation k := (@pair tid (RelaxedSig.handle F) t h).

      (** The own invocations of the call: one invocation of [ρ o]. *)
      Definition Ωren (evs : list (ThreadEvent E)) : Prop :=
        exists hu, evs = [Build_ThreadEvent t (@InvEv E hu (ρ o))].

      Local Abbreviation Pinit := (PostInvoke Iren k o Ωren).

      Lemma pinit_KInv : Impl Iren Pinit (KInv k o).
      Proof.
        intros [[σ p] γ] _ (p0 & γ0 & evs & (st & P & pool0 & Hp0 & _) & Hinv & _).
        cbn [ps_poss ps_mem ps_ghost fst snd] in Hp0, Hinv. rewrite Hp0 in Hinv.
        destruct (pinv_inv_gen _ _ _ _ _ _ Hinv) as [-> _].
        exists (st, P), (make_lin_entry k (ls_inv o) :: pool0). split; [reflexivity | left; reflexivity].
      Qed.

      (** The underlay invocation: readiness by [emit_ready_SI], the
          abstract invocation by [Hδ], ownership by [eihl_mine_inv]. *)
      Lemma inv_update hu :
        EvUpdate Iren (Gren k) k (Build_ThreadEvent t (@InvEv E hu (ρ o))) (KInv k o) (KLini k o hu).
      Proof.
        intros σ p γ γ' (v & pool & Hp & Hl)
          (st & P & pool1 & Hp1 & Hc & Hwf & HJ & HJwf & HPl & HPnd & Hru) Hge σ' Hstep.
        cbn [ps_poss ps_mem ps_ghost fst snd] in *. rewrite Hp in Hp1. injection Hp1 as -> <-. subst p.
        cbn in Hge. destruct Hge as (g1 & g2 & -> & -> & Hnb).
        pose proof (eihl_rec_used_step δE _ σ σ' Hstep Hru) as Hru'.
        destruct (eihl_mine_inv δE t hu (ρ o) σ σ' Hstep Hru) as (r & st' & Hd & Hσ' & Hm).
        pose proof (Hδ _ _ _ _ Hd) as HdF. rewrite Hc in HdF.
        apply Forall_app in HJwf as [HJwf1 HJwf2]. pose proof (Forall_inv_tail HJwf2) as HJwf2'.
        destruct (emit_ready_SI ρ lz Hsi t h o hu pool g1 g2 Hwf Hl (Hlz o) HJ HJwf1 Hnb)
          as (pool' & Hu & Hwf' & HJ').
        pose proof (lin_invoke_update_is_update _ _ _ _ _ Hu) as Hu2.
        assert (HPk : forall x : OpF, In x P -> okey x <> k).
        { intros x Hx Hk. pose proof (HPl x Hx) as Hlo. rewrite Hk in Hlo.
          pose proof (lookup_unique_gen pool k _ _ Hwf Hl Hlo) as Heq. discriminate Heq. }
        exists (POk (π st', @RelaxedTraceLin.Build_Op F k o (back o r) :: P) pool'). split; [| split; [| split]].
        - apply rt_step. exists k. apply (psa_inv VF t h o); [exact Hu |].
          cbn. exists (back o r), (π st'). split; [exact HdF | reflexivity].
        - exists r, (π st', @RelaxedTraceLin.Build_Op F k o (back o r) :: P), pool'. cbn [ps_poss ps_mem ps_ghost fst snd].
          split; [reflexivity |]. split; [exact Hm |]. split; [left; reflexivity |].
          exact (lin_update_target _ _ _ _ _ Hu2).
        - exists (π st'), (@RelaxedTraceLin.Build_Op F k o (back o r) :: P), pool'. cbn [ps_poss ps_mem ps_ghost fst snd].
          split; [reflexivity |]. split; [rewrite Hσ'; reflexivity |]. split; [exact Hwf' |].
          split; [exact HJ' |]. split; [apply Forall_app; split; assumption |]. split.
          + intros x [<- | Hx]; [exact (lin_update_target _ _ _ _ _ Hu2) |].
            eapply lin_update_other_lookup; [exact Hu2 | exact (HPk x Hx) | exact (HPl x Hx)].
          + split; [| exact Hru'].
            constructor; [| exact HPnd]; intros Hin; apply in_map_iff in Hin as (x & Hk & Hx); exact (HPk x Hx Hk).
        - split; [apply rt_step; exists (Build_ThreadEvent t (@InvEv E hu (ρ o))); exact Hstep |].
          exists (st, P), pool, (π st', @RelaxedTraceLin.Build_Op F k o (back o r) :: P), pool'.
          split; [reflexivity |]. split; [reflexivity |].
          split; [intros k' ls Hne Hlk; eapply lin_update_other_lookup; [exact Hu2 | exact Hne | exact Hlk] |].
          intros x _ Hx. right. exact Hx.
      Qed.

      (** The underlay response: by ownership ([eihl_mine_res]) and [Hinj]
          the response determines the abstract result. *)
      Lemma res_update hu (r : Sig.ar (ρ o)) :
        EvUpdate Iren (Gren k) k (Build_ThreadEvent t (@ResEv E hu (ρ o) r)) (KLini k o hu) (KLinr k o (back o r)).
      Proof.
        intros σ p γ γ' (c & v & pool & Hp & Hm & HP & Hl)
          (st & P & pool1 & Hp1 & Hc & Hwf & HJ & HJwf & HPl & HPnd & Hru) Hge σ' Hstep.
        cbn [ps_poss ps_mem ps_ghost fst snd] in *. cbn in Hge. subst γ'.
        pose proof (eihl_mine_res δE (t, hu) _ (ρ o) r σ σ' Hm Hstep) as Hxm.
        pose proof (Hinj (t, hu) o c r Hxm) as Hcr.
        pose proof (eihl_rec_used_step δE _ σ σ' Hstep Hru) as Hru'.
        assert (Hcnt : fst (fst σ') = fst (fst σ)).
        { destruct σ as [[n Pc] u], σ' as [[n' Pc'] u']. cbn in Hstep. destruct Hstep as ((P1 & P2 & _ & Hq') & _).
          injection Hq' as -> _. reflexivity. }
        rewrite Hp in Hp1. injection Hp1 as -> <-. subst p.
        cbn [snd] in HP. rewrite Hcr in HP. destruct (in_split _ _ HP) as (Pa1 & Pa2 & HPs).
        destruct (lin_update_exists_gen k (ls_lini o) (ls_linr o (back o r)) pool Hwf Hl) as (pool' & Hu).
        assert (HPk : forall x : OpF, In x (Pa1 ++ Pa2) -> okey x <> k).
        { intros x Hx Hk. rewrite HPs, map_app in HPnd. cbn [map] in HPnd.
          apply NoDup_remove_2 in HPnd. apply HPnd. rewrite <- map_app.
          apply in_map_iff. exists x. split; [exact Hk | exact Hx]. }
        assert (HPsub : forall x : OpF, In x (Pa1 ++ Pa2) -> In x P) by (intros x Hx; rewrite HPs; exact (in_remove_in _ _ _ _ Hx)).
        exists (POk (st, Pa1 ++ Pa2) pool'). split; [| split; [| split]].
        - apply rt_step. exists k. apply (psa_ret VF t h o (back o r) _ _ _ _ Hu). cbn. exists Pa1, Pa2.
          split; [exact HPs | reflexivity].
        - exists (st, Pa1 ++ Pa2), pool'. split; [reflexivity | eapply lin_update_target; exact Hu].
        - exists st, (Pa1 ++ Pa2), pool'. cbn [ps_poss ps_mem ps_ghost fst snd].
          split; [reflexivity |]. split; [rewrite Hcnt; exact Hc |].
          split; [eapply lin_update_well_formed; eauto |].
          split; [intros t'; rewrite (inv_kops_update ρ k (ls_lini o) (ls_linr o (back o r)) pool pool' t'
                    (fun o' (H : ls_lini o = ls_inv o') => ltac:(discriminate H))
                    (fun o' (H : ls_linr o (back o r) = ls_inv o') => ltac:(discriminate H)) Hu); apply HJ |].
          split; [exact HJwf |]. split.
          + intros x Hx. eapply lin_update_other_lookup; [exact Hu | exact (HPk x Hx) | exact (HPl x (HPsub x Hx))].
          + split; [rewrite HPs, map_app in HPnd; cbn [map] in HPnd; rewrite map_app; exact (NoDup_remove_1 _ _ _ HPnd) |].
            exact Hru'.
        - split; [apply rt_step; exists (Build_ThreadEvent t (@ResEv E hu (ρ o) r)); exact Hstep |].
          exists (st, P), pool, (st, Pa1 ++ Pa2), pool'. split; [reflexivity |]. split; [reflexivity |].
          split; [intros k' ls Hne Hlk; eapply lin_update_other_lookup; [exact Hu | exact Hne | exact Hlk] |].
          intros x Hk Hx. cbn in Hx |- *. rewrite HPs in Hx. apply (in_remove_ne _ _ _ _ Hx).
          intros ->. apply Hk. reflexivity.
      Qed.

      Definition sl_inv (hu : RelaxedSig.handle E) : Slot VE VF :=
        mkSlot (inv_tev (E := E) (F := F) k empty_store hu (ρ o)) (KInv k o) (fun _ _ => True)
          (KLini k o hu) (Gren k).

      Definition sl_res (hu : RelaxedSig.handle E) (r : Sig.ar (ρ o)) : Slot VE VF :=
        mkSlot (res_tev (E := E) (F := F) k hu (ρ o) r) (fun _ => True) (fun _ => KLini k o hu)
          (KLinr k o (back o r)) (Gren k).

      Lemma dprec_inv_res hu r :
        dprec [inv_tev (E := E) (F := F) k empty_store hu (ρ o); res_tev (E := E) (F := F) k hu (ρ o) r] 0 1.
      Proof. econstructor; [lia | reflexivity | reflexivity |]. unfold must_precede. cbn. reflexivity. Qed.

      Context (M : RelaxedModuleImpl E F).
      Context (HM : M o t = Future (ρ o) (fun f => Wait f (fun r => Ret (back o r)))).

      (** The derivation (as [RelaxedHoareChecks.CounterEIhlFrame.counter_derivationm]):
          a single future; every own-interference premise is vacuous,
          [Stable_true], or refuted by [before]. *)
      Lemma ren_derivation :
        RProvable Iren Rren Gren k Pinit
          (fun a Γ H => Close Iren Rren Gren k Pinit (KLinr k o) a Γ H /\ Ωren (own_invs Γ)) [] empty_store (M o t).
      Proof.
        rewrite HM.
        apply rp_future with (sl := sl_inv); [intros; reflexivity | |].
        { intros hu _. constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar sl_inv].
          - auto.
          - unfold pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar sl_inv].
            intros σ p γ γ' [HK _]. apply (inv_update hu σ p γ γ' HK).
          - exact pinit_KInv.
          - intros d sd _ Hd. destruct d; discriminate.
          - apply KInv_stable.
          - intros d _. apply Stable_true.
          - intros g sg Hg. destruct g; discriminate.
          - intros d g sg _ Hg. destruct g; discriminate.
          - intros y sy Hy. destruct y; discriminate.
          - intros y sy d Hy. destruct y; discriminate. }
        intros hu Hf. cbv beta.
        apply rp_wait_pending with (sl := sl_res hu); [left; reflexivity | intros; reflexivity | |].
        { intros r. constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar sl_res].
          - auto.
          - unfold pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar sl_res].
            intros σ p γ γ' [_ Hin]. apply (res_update hu r σ p γ γ'). apply (Hin 0).
            exact (dprec_inv_res hu r).
          - intros s _ _. exact Logic.I.
          - intros d sd _ Hd. destruct d as [| [|]]; try discriminate.
            cbn in Hd. injection Hd as <-. cbn. intros s _ Hs. exact Hs.
          - apply Stable_true.
          - intros d _. apply KLini_stable.
          - intros g sg _. apply Stable_true.
          - intros d g sg Hd Hg Hnb. exfalso. apply dprec_lt in Hd. cbn in Hd.
            destruct g as [| g]; [| destruct g; discriminate]. assert (d = 0) by lia. subst d.
            apply Hnb. apply before_refl.
          - intros y sy Hy Hnb. exfalso. destruct y as [| y]; [| destruct y; discriminate].
            apply Hnb. apply before_dprec. exact (dprec_inv_res hu r).
          - intros y sy d Hy _ Hd. exfalso. apply dprec_lt in Hd. destruct y as [| y]; [lia |].
            destruct y; discriminate. }
        intros r H2 Hres. cbv beta. apply rp_ret. split.
        - apply close_done with
            (fin := fun d => match d with 1 => KLinr k o (back o r) | _ => fun _ => True end)
            (fin0 := fun _ => True).
          + eapply resolve_fresh_all_resolved; [constructor | exact Hres].
          + constructor.
            * intros d sd Hd. destruct d as [| [| d]]; cbn in Hd; try (destruct d; discriminate).
              -- intros s _ _. exact Logic.I.
              -- injection Hd as <-. intros s _ Hs. exact Hs.
            * intros s _ _. exact Logic.I.
            * intros d g sg Hd Hg Hnb. destruct d as [| [| d]]; [apply Stable_true | | cbn in Hd; lia].
              exfalso. apply Hnb. destruct g as [| [| g]]; [| apply before_refl | destruct g; discriminate].
              apply before_dprec. exact (dprec_inv_res hu r).
            * intros g sg _. apply Stable_true.
            * intros [| [| d]]; [apply Stable_true | apply KLinr_stable | apply Stable_true].
            * apply Stable_true.
            * intros s _ _ Hfin. exact (Hfin 1 _ eq_refl Logic.I).
        - exists hu. reflexivity.
      Qed.

      (** LHL's [PI]: the post-invocation state satisfies the invariant. *)
      Lemma ren_PI : forall s, Pinit s -> Iren s.
      Proof.
        intros [[σ p] γ] (p0 & γ0 & evs & (st & P & pool0 & Hp0 & Hc & Hwf & HJ & HJwf & HPl & HPnd & Hru) & Hinv & Hg & (hu & ->) & _).
        cbn [ps_poss ps_mem ps_ghost fst snd] in *. subst γ. rewrite Hp0 in Hinv.
        destruct (pinv_inv_gen _ _ _ _ _ _ Hinv) as [-> Hfresh].
        exists st, P, (make_lin_entry k (ls_inv o) :: pool0). split; [reflexivity |]. split; [exact Hc |].
        split; [eapply lin_insert_well_formed; [constructor; exact Hfresh | exact Hwf] |]. split.
        - intros t'. cbn [inv_kops ps_ghost snd]. rewrite HJ, gkops_app. f_equal.
          cbn [map]. rewrite gkops_one. unfold ikop, gsel. cbn. rewrite (Hlz o), andb_true_r.
          destruct (Pos.eqb t t'); reflexivity.
        - split; [apply Forall_app; split; [exact HJwf | constructor; [split; [reflexivity | exact Logic.I] | constructor]] |].
          split; [intros x Hx; right; exact (HPl x Hx) |]. split; [exact HPnd | exact Hru].
      Qed.

      (** LHL's [Qlin] and [Qret]. *)
      Lemma ren_ret (r : Sig.ar o) s :
        KLinr k o r s -> Iren s -> NoOwn k (ps_ghost s) -> RetCond Iren Gren k o r s.
      Proof.
        intros (v & pool & Hp & Hl) HI _. destruct s as [[σ p] γ]. cbn [ps_poss ps_mem ps_ghost fst snd] in *.
        subst p. exists (POk v pool). split; [apply rt_refl |]. split; [exists v, pool; split; [reflexivity | exact Hl] |].
        split; [exact HI |]. split; [apply r_refl |].
        intros p2 Hret. destruct (pret_inv_gen _ _ _ _ _ _ _ Hret) as (pool2 & -> & Hrem).
        destruct HI as (st & P & pool3 & Hp3 & Hc & Hwf & HJ & HJwf & HPl & HPnd & Hru). cbn in Hp3.
        injection Hp3 as Hv Hpool. subst v pool3.
        exists st, P, pool2. cbn. split; [reflexivity |]. split; [exact Hc |].
        split; [eapply lin_remove_well_formed; eauto |].
        split; [intros t'; rewrite (inv_kops_remove ρ k (ls_linr o r) pool pool2 t'
                  (fun o' (H : ls_linr o r = ls_inv o') => ltac:(discriminate H)) Hrem); apply HJ |].
        split; [exact HJwf |]. split; [| split; [exact HPnd | exact Hru]].
        intros x Hx. eapply lin_remove_other_lookup; [exact Hrem | | exact (HPl x Hx)].
        intros Hk. pose proof (HPl x Hx) as Hlo. rewrite Hk in Hlo.
        pose proof (lookup_unique_gen pool k _ _ Hwf Hl Hlo) as Heq. discriminate Heq.
      Qed.

    End Call.

    (** The fields of [RLHL2Hyps] other than [h_sem] hold for every
        module: they only read the frame-style [Iren], [Rren], [Gren]. *)
    Lemma ren_init (s0 : StE) : Iren (((s0, []), []), POk (π s0, []) [], []).
    Proof.
      exists (π s0), [], []. cbn. split; [reflexivity |]. split; [reflexivity |].
      split; [constructor |]. split; [reflexivity |]. split; [constructor |].
      split; [intros x [] |]. split; [constructor |]. exact (eihl_rec_used_init δE s0).
    Qed.

    Theorem ren_rlhl2_of_sem (M : RelaxedModuleImpl E F) (s0 : StE) :
      (forall t o, MethodSem Iren Rren Gren M t o) ->
      RLHL2Hyps Iren Rren Gren M ((s0, []), []) (π s0, []).
    Proof.
      intros Hsem. constructor.
      - exact Hsem.
      - intros k k' s s' Hne HG. exact (Gren_in_Rren k' k s s' Hne HG).
      - intros k k' op tr ret s p' Hne _ HI Hinv. destruct s as [[σ p] γ].
        destruct HI as (st & P & pool & Hp & _). cbn [ps_poss ps_mem ps_ghost fst snd] in *. subst p.
        destruct k as [t h]. destruct (pinv_inv_gen _ _ _ _ _ _ Hinv) as [-> _].
        split; [apply rt_refl |].
        exists (st, P), pool, (st, P), (make_lin_entry (t, h) (ls_inv op) :: pool).
        split; [reflexivity |]. split; [reflexivity |]. split; [intros ls Hl; right; exact Hl | auto].
      - intros k k' op r s p2 Hne HI Hret _. destruct s as [[σ p] γ].
        destruct HI as (st & P & pool & Hp & _). cbn [ps_poss ps_mem ps_ghost fst snd] in *. subst p.
        destruct k as [t h]. destruct (pret_inv_gen _ _ _ _ _ _ _ Hret) as (pool2 & -> & Hrem).
        split; [apply rt_refl |].
        exists (st, P), pool, (st, P), pool2. split; [reflexivity |]. split; [reflexivity |].
        split; [| auto]. intros ls Hl. eapply lin_remove_other_lookup; [exact Hrem | | exact Hl].
        intros Heq. apply Hne. symmetry. exact Heq.
      - intros s (st & P & pool & Hp & _ & Hwf & _). exists (st, P), pool. auto.
      - exact (ren_init s0).
    Qed.

    Context (M : RelaxedModuleImpl E F).
    Context (HM : forall o t, M o t = Future (ρ o) (fun f => Wait f (fun r => Ret (back o r)))).

    Theorem ren_provable t o :
      MethodProvable Iren Rren Gren M t o (fun h => Ωren t o) (fun h => KLinr (t, h) o).
    Proof.
      constructor.
      - intros h s Hs. exact (ren_PI t h o s Hs).
      - intros h r s HQ HI Hno. exact (ren_ret t h o r s HQ HI Hno).
      - intros h. exact (ren_derivation t h o M (HM o t)).
    Qed.

    Theorem ren_methodsem t o : MethodSem Iren Rren Gren M t o.
    Proof. eapply method_sound. exact (ren_provable t o). Qed.

    (** Every field of [RLHL2Hyps], for the renaming copy-cat, over
        [EIhl δE] into [EI δF], from every initial concrete state [s0]
        (abstract state [π s0]). *)
    Theorem ren_rlhl2 (s0 : StE) : RLHL2Hyps Iren Rren Gren M ((s0, []), []) (π s0, []).
    Proof. exact (ren_rlhl2_of_sem M s0 ren_methodsem). Qed.

    (** Copy-cat inclusion over the plain [EI δE] ([classic], through
        [RelaxedHoareCompLin.rinv_val]). *)
    Corollary ren_complin_ei (s0 : StE) :
      RCompLin M (RelaxedHoareSpec.EI δE) (s0, []) (RelaxedHoareSpec.EI δF) (π s0, []).
    Proof. exact (rlhl_complin_eihl δE δF (π s0) Iren Rren Gren M (s0, []) (ren_rlhl2 s0)). Qed.

    (** Every complete overlay trace of [M] over [EI δE] is
        relaxed-linearizable to [seq_legal δF (π s0)] under the overlay's
        semi-independence ([classic], [eq_rect_eq]). *)
    Corollary ren_rel_lin (s0 : StE) s :
      MTraces (RelaxedHoareSpec.EI δE) M (s0, []) s -> PrefixView.complete s ->
      RelaxedTraceLin.rel_lin (@PrefixView.sel F) s (RelaxedSig.semi_independent F)
        (RelaxedHoareSpec.seq_legal δF (π s0)).
    Proof. exact (complin_ei_rel_lin δF (π s0) M (RelaxedHoareSpec.EI δE) (s0, []) (ren_complin_ei s0) s). Qed.
  End Rename.

  (** ** Part 3: the side conditions [Hinj] and [Hsi] carry no content
      (latest-review m-44) *)

  Section SideConditions.
    Context {E F : RelaxedSig.t}.
    Context (ρ : Sig.op (RelaxedSig.effect F) -> Sig.op (RelaxedSig.effect E)).
    Context (back : forall o : Sig.op (RelaxedSig.effect F), Sig.ar (ρ o) -> Sig.ar o).

    (** [Hinj] without axioms, when the underlay operations have
        decidable equality ([Eqdep_dec.inj_pair2_eq_dec]). *)
    Lemma ren_inj_of_dec :
      (forall o1 o2 : Sig.op (RelaxedSig.effect E), {o1 = o2} + {o1 <> o2}) ->
      forall u o (r1 r2 : Sig.ar (ρ o)),
        @RelaxedTraceLin.Build_Op E u (ρ o) r1 = @RelaxedTraceLin.Build_Op E u (ρ o) r2 ->
        back o r1 = back o r2.
    Proof.
      intros Hdec u o r1 r2 H. injection H as H.
      apply inj_pair2_eq_dec in H; [subst; reflexivity | exact Hdec].
    Qed.

    (** [Hinj] for every [E], [F], [ρ], [back], under [eq_rect_eq]
        ([Eqdep.EqdepTheory.inj_pair2], named explicitly: the homonym in
        [Classical_Prop] would use [classic] instead). *)
    Lemma ren_inj_generic :
      forall u o (r1 r2 : Sig.ar (ρ o)),
        @RelaxedTraceLin.Build_Op E u (ρ o) r1 = @RelaxedTraceLin.Build_Op E u (ρ o) r2 ->
        back o r1 = back o r2.
    Proof.
      intros u o r1 r2 H. injection H as H. apply Eqdep.EqdepTheory.inj_pair2 in H. subst. reflexivity.
    Qed.

    (** The double-negated [Hsi] from plain inheritance, without axioms,
        when the underlay relation is stable under double negation. *)
    Lemma ren_si_of_stable :
      (forall a b, ~ ~ semi_independent E a b -> semi_independent E a b) ->
      (forall o1 o2, semi_independent E (ρ o1) (ρ o2) -> semi_independent F o1 o2) ->
      forall o1 o2, ~ ~ semi_independent E (ρ o1) (ρ o2) -> semi_independent F o1 o2.
    Proof. intros Hst H o1 o2 Hnn. apply H, Hst, Hnn. Qed.

    (** The same for a decidable underlay relation (without axioms). *)
    Lemma ren_si_of_dec :
      (forall a b, semi_independent E a b \/ ~ semi_independent E a b) ->
      (forall o1 o2, semi_independent E (ρ o1) (ρ o2) -> semi_independent F o1 o2) ->
      forall o1 o2, ~ ~ semi_independent E (ρ o1) (ρ o2) -> semi_independent F o1 o2.
    Proof.
      intros Hdec. apply ren_si_of_stable. intros a b Hnn.
      destruct (Hdec a b) as [H | H]; [exact H | exfalso; exact (Hnn H)].
    Qed.

    (** The same for every relation.  [classic] is used (through
        [Classical_Prop.NNPP]) only to remove the double negation; this
        lemma is not used by any instance, which discharge [Hsi]
        constructively. *)
    Lemma ren_si_of_plain :
      (forall o1 o2, semi_independent E (ρ o1) (ρ o2) -> semi_independent F o1 o2) ->
      forall o1 o2, ~ ~ semi_independent E (ρ o1) (ρ o2) -> semi_independent F o1 o2.
    Proof. apply ren_si_of_stable. intros a b. apply Classical_Prop.NNPP. Qed.

    (** Conversely, the double-negated form implies plain inheritance
        (without axioms); with [ren_si_of_plain], the two are equivalent
        under [classic]. *)
    Lemma ren_si_plain_of_nn :
      (forall o1 o2, ~ ~ semi_independent E (ρ o1) (ρ o2) -> semi_independent F o1 o2) ->
      forall o1 o2, semi_independent E (ρ o1) (ρ o2) -> semi_independent F o1 o2.
    Proof. intros H o1 o2 Hs. apply H. intros Hn. exact (Hn Hs). Qed.
  End SideConditions.

End RelaxedHoareInherit.
