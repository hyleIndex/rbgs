(** * RLHL, part 13: readiness through semi-independence, direct
      blocks or recorded non-blocking ([RecNB]); stability of the
      record; ghost entries are never re-added (RLHL-seqlock .1) and
      persist under other calls' moves (RLHL-seqlock .B6, m-52)

    Plan: .rocq-review/tasks/RLHL-seqlock.md, §2.4 ("Readiness" table),
    §3 row .1 (and its Addendum: author decision RS-1 = WRd only), §7
    check 2 (script A, .rocq-review/scripts/RLHLsl_A_emit_ready_mixed.v);
    design A, .rocq-review/tasks/RLHL-seqlock-designs/A-object-proof.md
    §3.5 ("Records").  Generic in [E], [F]: no SeqLock definition is used.

    ** Purpose

    At the linearization point (LP) of a call [(t, h)] (the emission of
    one of its underlay invocations [ev]), the abstract invocation needs
    [invocation_ready]: every older [ls_inv] call [k1] of thread [t] must
    be semi-independent of [(t, h)] in the overlay [F].
    [RelaxedHoareRun.emit_ready_block_older] discharges an older call by a
    *direct* block (one of its pending ghost entries [inv_blocks ev], which
    the [ghost_emit] of [ev] excludes, by [GAge]).  The SeqLock readiness
    table needs two more ways:
    - overlay semi-independence (e.g. older write, younger read at
      [slRA]): [emit_ready_mixed];
    - a *recorded* block: the older call's pending entry blocks not [ev]
      but an earlier invocation [ev_r] of [(t, h)] that was emitted while
      that entry was already pending (WRd: older read, younger write; the
      read's pending [sRmb] blocks the write's [rd seq], not its LP
      [wr seq (v+1)]).  Since [ev_r] was emitted, no older entry blocked
      it then; [RecNB] records this, and it stays true because older
      entries are only removed, never re-added ([emit_ready_rec]).

    ** Contents
    - Part 1.  [emit_ready_mixed] (script A, verbatim proof): an older
      [ls_inv] call is either overlay-SI or directly blocking.
      [emit_ready_block_older_of_mixed]: the statement of
      [RelaxedHoareRun.emit_ready_block_older], re-derived as a corollary
      ([ebo_statement_matches] checks the two statements are identical).
      [emit_ready_si_older]: the all-SI special case.
    - Part 2.  [RecNB P k ev γ]: no entry of [γ] owned by a call older
      than [k] in [P] [inv_blocks ev].  [recnb_split] and
      [recnb_establish] (establish at the emission of [ev], from
      [ghost_emit] and [gage_before]); [recnb_contra] (use);
      [emit_ready_rec] (the three-way readiness lemma: SI, direct block,
      or recorded block).
    - Part 3.  Stability.  [OlderSub k P γ P' γ']: every entry of [γ']
      older than [k] in [P'] was in [γ] and older than [k] in [P].
      It holds for each transition of the RLHL proof state: an emission
      ([oldersub_ghost_emit]), a domain-preserving abstract update
      ([oldersub_same_domain]: [lin_update], [lin_invoke_update],
      [poss_steps]), an invocation of a fresh key [≠ k]
      ([oldersub_invoke], [oldersub_poss_invoke]), a return
      ([oldersub_lin_remove], [oldersub_poss_return]).  [recnb_oldersub]
      and its per-transition corollaries [recnb_ghost_emit],
      [recnb_ev_update], [recnb_lin_update], [recnb_lin_invoke_update],
      [recnb_poss_steps], [recnb_invoke], [recnb_poss_invoke],
      [recnb_lin_remove], [recnb_poss_return].
    - Part 4.  "A key's ghost entries are never re-added".  [GMove]: the
      four transitions of the (pool, ghost) part of the proof state
      (emission with a domain-preserving update; domain-preserving update
      alone; invocation of a fresh key with entries owned by it; return
      of a key with no ghost entry left), with [gmove_ev_update],
      [gmove_poss_steps], [gmove_poss_invoke], [gmove_poss_return]
      relating them to [EvUpdate]/[MethodSem]/[h_invoke_rely]/
      [h_return_rely].  [OwnSub k1 γ γ']: every entry of [γ'] owned by
      [k1] is in [γ].  [gmove_ownsub] (one step, [k1] in the pool),
      [ghost_never_readded] (any path along which [k1] stays in the pool
      at each step's source), [noown_persists]; [gmove_gage]/[gage_gmoves]
      ([GAge] is kept), [gmove_recnb]/[recnb_gmoves] ([RecNB] is kept
      while its owner is in the pool).
    - Part 5 (latest-review m-52).  Persistence, the dual of Part 4.
      [ghost_emit_keeps_other] (script S2 of latest-review: an emission
      by [k' <> k] keeps every entry of [k]); [ghost_emit_keeps_neq] (an
      emission removes at most the emitted entry).  [OwnKeep k γ γ']:
      every entry of [γ] owned by [k] is in [γ'] ([ownkeep_ownsub]: it is
      [OwnSub k γ' γ]); closure lemmas [ownkeep_refl], [ownkeep_trans],
      [ownkeep_incl], [ownkeep_ghost_emit_other],
      [ownkeep_ghost_emit_res], [ownkeep_app] (invocations);
      [ownkeep_exists], [ownkeep_not_noown], [not_noown_emit_other_entry]
      (uses); [ownframe_of]/[ownframe_to] ([OwnSub] and [OwnKeep] are
      the two-sided frame of [k]'s entries).  [GMoveBy k']: [GMove]
      tagged with the key that performs it ([gmoveby_gmove],
      [gmove_gmoveby]); [gmoveby_ownkeep], [gmoveby_ownsub] (a move by
      [k' <> k] keeps [k]'s entries both ways, with no pool condition);
      [GMovesOther k] (paths of such moves), [ghost_kept],
      [ghost_frame_other], [owned_persists]; [gmoveby_ev_update],
      [gmoveby_poss_steps], [gmoveby_poss_invoke], [gmoveby_poss_return]
      (the RLHL transitions as tagged moves).  [retcond_or_owned]: a
      postcondition that discharges [RetCond] may be weakened by
      "[k] still owns an entry", since [RetCond] is asked under [NoOwn]
      only (the generic form of the B-6 fix, reader-eval §1.3).

    ** How the prophetic read LP of the SeqLock uses both directions
    The read's LP is the emission of its last [rmb] ("last": after the
    emission [k] owns no [rmb], decided on the ghost).  The derivation
    needs, along the rest of the path,
    - never re-added (Part 4: [OwnSub], [ghost_never_readded],
      [noown_persists]): at the final [rmb], "[k] owns no [rmb]" stays
      true, so the read stays linearized (its coupling with the ghost);
    - persistence (Part 5: [OwnKeep], [ghost_kept], [owned_persists],
      [not_noown_emit_other_entry]): at a non-final [rmb], "[k] still owns
      an [rmb] of a later iteration" stays true under the moves of other
      calls and under [k]'s own emissions of other entries, up to a
      return that validates early; there it is the [¬ NoOwn] disjunct of
      the read postcondition, refuted at [mp_ret] by [NoOwn]
      ([retcond_or_owned]; [RelaxedHoareSL2Inv.Qrd], [qrd_ret]).
    In [RelaxedHoareSL2Inv] the rely [Rsl k] states the two-sided frame
    of [k]'s entries directly; the lemmas here are the generic form.

    ** K / S / P / R
    - K: all 72 [Theorem]/[Lemma]/[Corollary]/[Example] results are
      closed under the global context (Print Assumptions, Rocq 9.3.0);
      no [classic], no [eq_rect_eq], no other axiom.
    - S: facts about the abstract pool [LinPool F] and the ghost
      [Ghost E F] only; they hold for every underlay [E], overlay [F],
      [VF].  [emit_ready_mixed]/[emit_ready_rec] conclude the
      [lin_invoke_update] needed at an LP (as [emit_ready_block_older]).
      The stability lemmas are per transition; they become stability
      under a rely only once that rely constrains the pool and the ghost
      (e.g. by [GMove] steps).  None of the user relations [I], [R], [G]
      appears here, except in [retcond_or_owned], which is generic in
      [I] and [G].
    - P: no paper statement cites this file.  It is proof infrastructure
      for the planned RLHL SeqLock (plan §2.4).  The side condition it
      discharges is [RelaxedPossibility.invocation_ready], the existing
      mechanization of the abstract invocation steps ([TInvoke],
      Appendix/relaxedlin.tex:641); that correspondence is not
      re-examined here.
    - R: infrastructure for popl2027-reviews.md:215 ("No example verified
      on the COH model"), through the planned SeqLock; it does not by
      itself answer any reviewer concern.

    ** Limitations
    - [RecNB] is relative to the *current* pool order ([key_older] in
      [lin_domain P]).  Its stability under an invocation needs the
      invoked key to differ from the record's owner [k]
      ([recnb_invoke]); in the RLHL proof state an invoked key is fresh
      in the pool, so it suffices that [k] is in the pool ([gmove_recnb]).
      A key that has returned (left the pool) could be invoked again at
      the level of [poss_invoke] (freshness is pool freshness), so the
      "never re-added" statements are stated while the key is in the pool.
    - The recorded event [ev_r] of [emit_ready_rec] must be an event
      whose [RecNB] record the caller's invariant carries to the LP;
      transporting it along a call's own dependency edges (plan §2.7:
      "carried along the tag") is the object proof's job, not done here.
    - [GMove] is a description of the pool/ghost transitions, not part of
      [RLHL2Hyps]; nothing forces a user rely to be generated by it.  The
      same holds for [GMoveBy]/[GMovesOther].
    - Persistence under [k]'s own emissions is entry-wise only
      ([ghost_emit_keeps_neq]: an entry other than the emitted one); a
      derivation must know that the entry it carries is not the one its
      path emits.  For the SeqLock read the carried entry is an [rmb] of a
      later iteration of the footprint; showing that the path never emits
      it is the read derivation's obligation (task .5), not done here.

    ** Provenance and plan check (RLHL-seqlock.md §3 row .1)
    Written for RLHL-seqlock wave 1, task .1, on top of the generic
    RLHL-latch wave-1 file [RelaxedHoareRun] ([GAge], [key_older],
    [gage_before], [emit_ready_block_older]).  Script A's statement and
    proof of [emit_ready_mixed] are ported unchanged.  Plan items:
    [emit_ready_mixed] (present); [emit_ready_block_older] as a
    corollary (present, under the name [emit_ready_block_older_of_mixed]
    to avoid a clash with [RelaxedHoareRun.emit_ready_block_older] when
    both modules are imported); [RecNB] with establish-at-emission
    ([recnb_establish], [recnb_establish_ev_update]) and stability under
    [ghost_emit], invoke and lin updates ([recnb_ghost_emit],
    [recnb_ev_update], [recnb_invoke], [recnb_poss_invoke],
    [recnb_lin_update], [recnb_lin_invoke_update], [recnb_poss_steps];
    also return: [recnb_lin_remove], [recnb_poss_return]); "a key's ghost
    entries are never re-added" ([gmove_ownsub], [ghost_never_readded],
    [noown_persists]).  Additions beyond the plan: [emit_ready_rec] (the
    recorded case as a third disjunct), [GMove]/[GMovesIn] and their
    [GAge]/[RecNB] lemmas.  Part 5 was added for task .B6
    (latest-review m-52: [ghost_emit_keeps_other], [GMoveBy], [OwnKeep]
    closure lemmas, the note on the two directions above); everything
    before Part 5 is unchanged. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Relations.Relation_Operators.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedPossibility.
Require Import models.simlin.RelaxedHoareDag.
Require Import models.simlin.RelaxedHoareBase.
Require Import models.simlin.RelaxedHoareCompLinSpec.
Require Import models.simlin.RelaxedHoareInherit.
Require Import models.simlin.RelaxedHoareRun.

Import ListNotations.


Module RelaxedHoareReady.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedPossibility.
  Import RelaxedHoareDag.
  Import RelaxedHoareBase.
  Import RelaxedHoareRun.

  (** ** Part 1. Readiness: semi-independence or a direct block *)

  Section Mixed.
    Context {E F : RelaxedSig.t}.

    (** Script A (plan §7 check 2), proof unchanged.  For every older
        [ls_inv] call [k1] of thread [t]: either its operation is
        semi-independent of [o] in [F], or it owns a ghost entry that
        [inv_blocks ev]; the second case is impossible at the emission of
        [ev] ([gage_before] puts that entry in [g1]). *)
    Theorem emit_ready_mixed (P : LinPool F) (γ g1 g2 : Ghost E F) t h o (ev : ThreadEvent E) :
      lin_pool_well_formed P -> lin_lookup (t, h) (ls_inv o) P -> GAge P γ ->
      (forall k1 o1, fst k1 = t -> key_older (lin_domain P) k1 (t, h) -> lin_lookup k1 (ls_inv o1) P ->
         semi_independent F o1 o \/ exists e, In e γ /\ se_owner e = k1 /\ inv_blocks (se_event e) ev) ->
      γ = g1 ++ Build_ScheduledEvent (t, h) ev :: g2 -> Forall (fun e => ~ inv_blocks (se_event e) ev) g1 ->
      exists P', lin_invoke_update t h o P P' /\ lin_pool_well_formed P'.
    Proof.
      intros Hwf Hl Hage Hblk Hγ Hnb. destruct (in_split _ _ Hl) as (pre & older & HP).
      assert (Hwf0 := Hwf). unfold lin_pool_well_formed, lin_domain in Hwf0. rewrite HP, map_app in Hwf0. cbn in Hwf0.
      pose proof (NoDup_remove_2 _ _ _ Hwf0) as Hnin. rewrite lin_key_make_lin_entry in Hnin.
      assert (Hpre : forall y, In y pre -> lin_key y <> (t, h)).
      { intros y Hy Hk. apply Hnin. apply in_or_app. left. rewrite <- Hk. apply in_map. exact Hy. }
      assert (Hready : invocation_ready t o older).
      { unfold invocation_ready. apply Forall_forall. intros e He. unfold older_entry_allows_invocation.
        destruct (Pos.eqb_spec (lin_tid F e) t) as [Ht | Ht]; [right | left; exact Ht].
        destruct (lin_state F e) as [o1 | o1 | o1 r1] eqn:Hs; [| exact Logic.I | exact Logic.I].
        assert (He' : e = make_lin_entry (lin_key e) (ls_inv o1)) by (destruct e; cbn in *; subst; reflexivity).
        assert (Hold : key_older (lin_domain P) (lin_key e) (t, h)).
        { unfold key_older, lin_domain. rewrite HP, map_app. cbn [map]. rewrite lin_key_make_lin_entry.
          apply subseq_pair_split. apply in_map. exact He. }
        assert (Hle : lin_lookup (lin_key e) (ls_inv o1) P).
        { unfold lin_lookup. rewrite <- He', HP. apply in_or_app. right. right. exact He. }
        destruct (Hblk (lin_key e) o1 Ht Hold Hle) as [Hsi | (e' & He'γ & Hown & Hb)]; [exact Hsi | exfalso].
        assert (Hin1 : In e' g1).
        { apply (gage_before P γ g1 g2 (Build_ScheduledEvent (t, h) ev) e' Hage Hγ He'γ). rewrite Hown. exact Hold. }
        rewrite Forall_forall in Hnb. exact (Hnb e' Hin1 Hb). }
      assert (Hu : lin_invoke_update t h o P (pre ++ make_lin_entry (t, h) (ls_lini o) :: older)).
      { rewrite HP. apply RelaxedHoareCompLinSpec.liu_app; [exact Hpre |]. apply lin_invoke_update_here. exact Hready. }
      exists (pre ++ make_lin_entry (t, h) (ls_lini o) :: older). split; [exact Hu |].
      eapply lin_invoke_update_well_formed; [exact Hu | exact Hwf].
    Qed.

    (** [RelaxedHoareRun.emit_ready_block_older], re-derived: the
        blocking disjunct alone. *)
    Corollary emit_ready_block_older_of_mixed (P : LinPool F) (γ g1 g2 : Ghost E F) t h o (ev : ThreadEvent E) :
      lin_pool_well_formed P -> lin_lookup (t, h) (ls_inv o) P -> GAge P γ ->
      (forall k1 o1, fst k1 = t -> key_older (lin_domain P) k1 (t, h) -> lin_lookup k1 (ls_inv o1) P ->
         exists e, In e γ /\ se_owner e = k1 /\ inv_blocks (se_event e) ev) ->
      γ = g1 ++ Build_ScheduledEvent (t, h) ev :: g2 ->
      Forall (fun e => ~ inv_blocks (se_event e) ev) g1 ->
      exists P', lin_invoke_update t h o P P' /\ lin_pool_well_formed P'.
    Proof.
      intros Hwf Hl Hage Hblk. apply (emit_ready_mixed P γ g1 g2 t h o ev Hwf Hl Hage).
      intros k1 o1 Ht Ho Hl1. right. exact (Hblk k1 o1 Ht Ho Hl1).
    Qed.

    (** The semi-independent disjunct alone. *)
    Corollary emit_ready_si_older (P : LinPool F) (γ g1 g2 : Ghost E F) t h o (ev : ThreadEvent E) :
      lin_pool_well_formed P -> lin_lookup (t, h) (ls_inv o) P -> GAge P γ ->
      (forall k1 o1, fst k1 = t -> key_older (lin_domain P) k1 (t, h) -> lin_lookup k1 (ls_inv o1) P ->
         semi_independent F o1 o) ->
      γ = g1 ++ Build_ScheduledEvent (t, h) ev :: g2 ->
      Forall (fun e => ~ inv_blocks (se_event e) ev) g1 ->
      exists P', lin_invoke_update t h o P P' /\ lin_pool_well_formed P'.
    Proof.
      intros Hwf Hl Hage Hsi. apply (emit_ready_mixed P γ g1 g2 t h o ev Hwf Hl Hage).
      intros k1 o1 Ht Ho Hl1. left. exact (Hsi k1 o1 Ht Ho Hl1).
    Qed.
  End Mixed.

  (** The corollary has exactly the statement of
      [RelaxedHoareRun.emit_ready_block_older] (checked by the kernel). *)
  Example ebo_statement_matches : True.
  Proof.
    let T := type of (@emit_ready_block_older_of_mixed) in
    assert (Hsame : T) by exact (@RelaxedHoareRun.emit_ready_block_older).
    exact Logic.I.
  Qed.

  (** ** Part 2. Recorded non-blocking ([RecNB]) *)

  Section Records.
    Context {E F : RelaxedSig.t}.

    (** [RecNB P k ev γ]: no entry of [γ] whose owner is older than [k]
        (in the pool [P]) blocks [ev].  Established at the emission of an
        invocation [ev] of [k] (Part 2), kept by every transition (Part 3). *)
    Definition RecNB (P : LinPool F) (k : CallKey F) (ev : ThreadEvent E) (γ : Ghost E F) : Prop :=
      forall e, In e γ -> key_older (lin_domain P) (se_owner e) k -> ~ inv_blocks (se_event e) ev.

    Lemma recnb_contra P k ev γ e :
      RecNB P k ev γ -> In e γ -> key_older (lin_domain P) (se_owner e) k -> inv_blocks (se_event e) ev -> False.
    Proof. intros Hr He Ho Hb. exact (Hr e He Ho Hb). Qed.

    Lemma recnb_incl P k ev (γ γ' : Ghost E F) : incl γ' γ -> RecNB P k ev γ -> RecNB P k ev γ'.
    Proof. intros Hi Hr e He. exact (Hr e (Hi e He)). Qed.

    Lemma recnb_split P (γ g1 g2 : Ghost E F) k ev :
      GAge P γ -> γ = g1 ++ Build_ScheduledEvent k ev :: g2 ->
      Forall (fun e => ~ inv_blocks (se_event e) ev) g1 -> RecNB P k ev γ.
    Proof.
      intros Hage Hγ Hnb e He Ho.
      pose proof (gage_before P γ g1 g2 (Build_ScheduledEvent k ev) e Hage Hγ He Ho) as Hin.
      rewrite Forall_forall in Hnb. exact (Hnb e Hin).
    Qed.

    Lemma ghost_emit_incl k (ev : ThreadEvent E) (γ γ' : Ghost E F) : ghost_emit k ev γ γ' -> incl γ' γ.
    Proof.
      unfold ghost_emit. destruct (te_ev E ev).
      - intros (g1 & g2 & -> & -> & _) x Hx. apply in_app_or in Hx as [Hx | Hx]; apply in_or_app; [left | right; right]; exact Hx.
      - intros -> x Hx. exact Hx.
    Qed.

    (** Establish at emission: the [ghost_emit] of an invocation [ev] of
        [k] gives [RecNB] before and after the emission. *)
    Theorem recnb_establish P k (ev : ThreadEvent E) (γ γ' : Ghost E F) :
      GAge P γ -> is_invocation ev -> ghost_emit k ev γ γ' -> RecNB P k ev γ /\ RecNB P k ev γ'.
    Proof.
      intros Hage Hinv Hge. pose proof (ghost_emit_incl k ev γ γ' Hge) as Hincl.
      unfold ghost_emit in Hge. unfold is_invocation in Hinv. destruct (te_ev E ev); [| contradiction].
      destruct Hge as (g1 & g2 & Hγ & _ & Hnb).
      assert (Hr : RecNB P k ev γ) by exact (recnb_split P γ g1 g2 k ev Hage Hγ Hnb).
      split; [exact Hr | exact (recnb_incl P k ev γ γ' Hincl Hr)].
    Qed.

    (** Readiness, three ways: an older [ls_inv] call of thread [t] is
        semi-independent, or owns an entry that blocks the LP event [ev]
        (direct), or owns an entry that blocks an event [ev_r] recorded
        non-blocked for [(t, h)] (recorded; impossible). *)
    Theorem emit_ready_rec (P : LinPool F) (γ g1 g2 : Ghost E F) t h o (ev : ThreadEvent E) :
      lin_pool_well_formed P -> lin_lookup (t, h) (ls_inv o) P -> GAge P γ ->
      (forall k1 o1, fst k1 = t -> key_older (lin_domain P) k1 (t, h) -> lin_lookup k1 (ls_inv o1) P ->
         semi_independent F o1 o \/
         (exists e, In e γ /\ se_owner e = k1 /\ inv_blocks (se_event e) ev) \/
         (exists ev_r e, RecNB P (t, h) ev_r γ /\ In e γ /\ se_owner e = k1 /\ inv_blocks (se_event e) ev_r)) ->
      γ = g1 ++ Build_ScheduledEvent (t, h) ev :: g2 -> Forall (fun e => ~ inv_blocks (se_event e) ev) g1 ->
      exists P', lin_invoke_update t h o P P' /\ lin_pool_well_formed P'.
    Proof.
      intros Hwf Hl Hage Hblk. apply (emit_ready_mixed P γ g1 g2 t h o ev Hwf Hl Hage).
      intros k1 o1 Ht Ho Hl1.
      destruct (Hblk k1 o1 Ht Ho Hl1) as [Hsi | [Hd | (ev_r & e & Hr & He & Hown & Hb)]];
        [left; exact Hsi | right; exact Hd | exfalso].
      apply (recnb_contra P (t, h) ev_r γ e Hr He); [rewrite Hown; exact Ho | exact Hb].
    Qed.
  End Records.

  (** ** Part 3. Stability of [RecNB] *)

  Section Stability.
    Context {E F : RelaxedSig.t}.

    (** Every entry of [γ'] older than [k] in [P'] was in [γ] and older
        than [k] in [P]. *)
    Definition OlderSub (k : CallKey F) (P : LinPool F) (γ : Ghost E F) (P' : LinPool F) (γ' : Ghost E F) : Prop :=
      forall e, In e γ' -> key_older (lin_domain P') (se_owner e) k ->
        In e γ /\ key_older (lin_domain P) (se_owner e) k.

    Lemma recnb_oldersub k P γ P' γ' (ev : ThreadEvent E) :
      OlderSub k P γ P' γ' -> RecNB P k ev γ -> RecNB P' k ev γ'.
    Proof. intros Hs Hr e He Ho. destruct (Hs e He Ho) as [He0 Ho0]. exact (Hr e He0 Ho0). Qed.

    Lemma oldersub_refl k P γ : OlderSub k P γ P γ.
    Proof. intros e He Ho. auto. Qed.

    Lemma oldersub_trans k P1 γ1 P2 γ2 P3 γ3 :
      OlderSub k P1 γ1 P2 γ2 -> OlderSub k P2 γ2 P3 γ3 -> OlderSub k P1 γ1 P3 γ3.
    Proof. intros H12 H23 e He Ho. destruct (H23 e He Ho) as [He2 Ho2]. exact (H12 e He2 Ho2). Qed.

    (** Transitions that keep the pool domain and only remove ghost
        entries: emissions and abstract linearization steps. *)
    Lemma oldersub_same_domain k (P P' : LinPool F) (γ γ' : Ghost E F) :
      lin_domain P' = lin_domain P -> incl γ' γ -> OlderSub k P γ P' γ'.
    Proof. intros Hd Hi e He Ho. rewrite Hd in Ho. exact (conj (Hi e He) Ho). Qed.

    Lemma oldersub_ghost_emit k P k' (ev : ThreadEvent E) (γ γ' : Ghost E F) :
      ghost_emit k' ev γ γ' -> OlderSub k P γ P γ'.
    Proof. intros Hge. apply oldersub_same_domain; [reflexivity | exact (ghost_emit_incl k' ev γ γ' Hge)]. Qed.

    (** Invocation of a fresh key [key ≠ k], whose entries [γn] are
        appended: they are younger than [k]. *)
    Lemma oldersub_invoke k key st (P : LinPool F) (γ γn : Ghost E F) :
      lin_fresh key P -> k <> key -> (forall e, In e γn -> se_owner e = key) ->
      OlderSub k P γ (make_lin_entry key st :: P) (γ ++ γn).
    Proof.
      intros Hfr Hne Hown e He Ho. cbn [lin_domain map] in Ho. rewrite lin_key_make_lin_entry in Ho.
      destruct (key_older_cons _ _ _ _ Ho) as [(Hk & _) | Ho']; [contradiction (Hne Hk) |].
      split; [| exact Ho'].
      apply in_app_or in He as [He | He]; [exact He | exfalso].
      apply Hfr. rewrite <- (Hown e He). exact (proj1 (key_older_in _ _ _ Ho')).
    Qed.

    (** Return: the domain shrinks, the ghost is unchanged. *)
    Lemma oldersub_lin_remove k key st (P P' : LinPool F) (γ : Ghost E F) :
      lin_remove key st P P' -> OlderSub k P γ P' γ.
    Proof.
      intros Hr e He Ho. split; [exact He |].
      exact (key_older_mono _ _ _ _ (lin_remove_domain_subseq _ _ _ _ Hr) Ho).
    Qed.

    Section Poss.
      Context {VF : LTS F}.

      Lemma oldersub_poss_steps k v P v' P' (γ γ' : Ghost E F) :
        poss_steps VF (PossOk v P) (PossOk v' P') -> incl γ' γ -> OlderSub k P γ P' γ'.
      Proof.
        intros Hs. apply oldersub_same_domain. symmetry. exact (poss_steps_ok_domain VF _ _ _ _ Hs).
      Qed.

      Lemma oldersub_poss_invoke k t h op v P p' (γ : Ghost E F) tr :
        poss_invoke VF t h op (PossOk v P) p' -> k <> (t, h) ->
        exists P', p' = PossOk v P' /\ OlderSub k P γ P' (γ ++ ghost_new (t, h) tr).
      Proof.
        intros Hi Hne. destruct (RelaxedHoareInherit.pinv_inv_gen _ _ _ _ _ _ Hi) as [-> Hfr].
        eexists. split; [reflexivity |]. apply (oldersub_invoke k (t, h) _ P γ _ Hfr Hne).
        apply ghost_new_owner.
      Qed.

      Lemma oldersub_poss_return k t h op r v P p2 (γ : Ghost E F) :
        poss_return VF t h op r (PossOk v P) p2 -> exists P2, p2 = PossOk v P2 /\ OlderSub k P γ P2 γ.
      Proof.
        intros Hr. destruct (RelaxedHoareInherit.pret_inv_gen _ _ _ _ _ _ _ Hr) as (P2 & -> & Hrem).
        exists P2. split; [reflexivity | exact (oldersub_lin_remove k _ _ P P2 γ Hrem)].
      Qed.
    End Poss.

    (** Per-transition stability of [RecNB]. *)

    Corollary recnb_ghost_emit P k ev k' (ev' : ThreadEvent E) (γ γ' : Ghost E F) :
      ghost_emit k' ev' γ γ' -> RecNB P k ev γ -> RecNB P k ev γ'.
    Proof. intros Hge. apply recnb_oldersub. exact (oldersub_ghost_emit k P k' ev' γ γ' Hge). Qed.

    Corollary recnb_lin_update P P' k ev key b a (γ : Ghost E F) :
      lin_update key b a P P' -> RecNB P k ev γ -> RecNB P' k ev γ.
    Proof.
      intros Hu. apply recnb_oldersub. apply oldersub_same_domain; [| intros x Hx; exact Hx].
      symmetry. exact (lin_update_keys _ _ _ _ _ Hu).
    Qed.

    Corollary recnb_lin_invoke_update P P' k ev t h o (γ : Ghost E F) :
      lin_invoke_update t h o P P' -> RecNB P k ev γ -> RecNB P' k ev γ.
    Proof.
      intros Hu. apply recnb_oldersub. apply oldersub_same_domain; [| intros x Hx; exact Hx].
      symmetry. exact (lin_invoke_update_keys _ _ _ _ _ Hu).
    Qed.

    Corollary recnb_invoke P k ev key st (γ γn : Ghost E F) :
      lin_fresh key P -> k <> key -> (forall e, In e γn -> se_owner e = key) ->
      RecNB P k ev γ -> RecNB (make_lin_entry key st :: P) k ev (γ ++ γn).
    Proof. intros Hfr Hne Hown. apply recnb_oldersub. exact (oldersub_invoke k key st P γ γn Hfr Hne Hown). Qed.

    Corollary recnb_lin_remove P P' k ev key st (γ : Ghost E F) :
      lin_remove key st P P' -> RecNB P k ev γ -> RecNB P' k ev γ.
    Proof. intros Hr. apply recnb_oldersub. exact (oldersub_lin_remove k key st P P' γ Hr). Qed.

    Section PossRec.
      Context {VF : LTS F}.

      Corollary recnb_poss_steps v P v' P' k ev (γ : Ghost E F) :
        poss_steps VF (PossOk v P) (PossOk v' P') -> RecNB P k ev γ -> RecNB P' k ev γ.
      Proof. intros Hs. apply recnb_oldersub. apply (oldersub_poss_steps k v P v' P' γ γ Hs). intros x Hx; exact Hx. Qed.

      (** The [EvUpdate] shape: an emission by any call together with
          abstract linearization steps. *)
      Corollary recnb_ev_update v P v' P' k ev k' (ev' : ThreadEvent E) (γ γ' : Ghost E F) :
        poss_steps VF (PossOk v P) (PossOk v' P') -> ghost_emit k' ev' γ γ' ->
        RecNB P k ev γ -> RecNB P' k ev γ'.
      Proof.
        intros Hs Hge. apply recnb_oldersub.
        exact (oldersub_poss_steps k v P v' P' γ γ' Hs (ghost_emit_incl k' ev' γ γ' Hge)).
      Qed.

      (** Establish at an [EvUpdate] emission of [k]: the record holds in
          the post-state, at the post-state pool. *)
      Corollary recnb_establish_ev_update v P v' P' k (ev : ThreadEvent E) (γ γ' : Ghost E F) :
        GAge P γ -> is_invocation ev -> ghost_emit k ev γ γ' ->
        poss_steps VF (PossOk v P) (PossOk v' P') -> RecNB P' k ev γ'.
      Proof.
        intros Hage Hinv Hge Hs. apply (recnb_poss_steps v P v' P' k ev γ' Hs).
        exact (proj2 (recnb_establish P k ev γ γ' Hage Hinv Hge)).
      Qed.

      Corollary recnb_poss_invoke v P p' k ev t h op tr (γ : Ghost E F) :
        poss_invoke VF t h op (PossOk v P) p' -> k <> (t, h) -> RecNB P k ev γ ->
        exists P', p' = PossOk v P' /\ RecNB P' k ev (γ ++ ghost_new (t, h) tr).
      Proof.
        intros Hi Hne Hr. destruct (oldersub_poss_invoke k t h op v P p' γ tr Hi Hne) as (P' & -> & Hs).
        exists P'. split; [reflexivity | exact (recnb_oldersub k P γ P' _ ev Hs Hr)].
      Qed.

      Corollary recnb_poss_return v P p2 k ev t h op r (γ : Ghost E F) :
        poss_return VF t h op r (PossOk v P) p2 -> RecNB P k ev γ ->
        exists P2, p2 = PossOk v P2 /\ RecNB P2 k ev γ.
      Proof.
        intros Hr Hrec. destruct (oldersub_poss_return k t h op r v P p2 γ Hr) as (P2 & -> & Hs).
        exists P2. split; [reflexivity | exact (recnb_oldersub k P γ P2 γ ev Hs Hrec)].
      Qed.
    End PossRec.
  End Stability.

  (** ** Part 4. A key's ghost entries are never re-added *)

  Section Moves.
    Context {E F : RelaxedSig.t}.

    (** The transitions of the (pool, ghost) part of the RLHL proof state:
        an emission with a domain-preserving abstract update ([EvUpdate],
        [ct_emit]); a domain-preserving update alone ([poss_steps]); the
        invocation of a fresh key, whose entries are appended
        ([MethodSem], [PostInvoke], [h_invoke_rely]); the return of a key
        with no ghost entry left ([RetCond], [h_return_rely]). *)
    Inductive GMove : LinPool F * Ghost E F -> LinPool F * Ghost E F -> Prop :=
    | gm_emit k (ev : ThreadEvent E) (P P' : LinPool F) (γ γ' : Ghost E F) :
        ghost_emit k ev γ γ' -> lin_domain P' = lin_domain P -> GMove (P, γ) (P', γ')
    | gm_lin (P P' : LinPool F) (γ : Ghost E F) :
        lin_domain P' = lin_domain P -> GMove (P, γ) (P', γ)
    | gm_invoke key st (P : LinPool F) (γ γn : Ghost E F) :
        lin_fresh key P -> (forall e, In e γn -> se_owner e = key) ->
        GMove (P, γ) (make_lin_entry key st :: P, γ ++ γn)
    | gm_return key st (P P' : LinPool F) (γ : Ghost E F) :
        lin_remove key st P P' -> NoOwn key γ -> GMove (P, γ) (P', γ).

    (** [OwnSub k1 γ γ']: every entry of [γ'] owned by [k1] is in [γ]. *)
    Definition OwnSub (k1 : CallKey F) (γ γ' : Ghost E F) : Prop :=
      forall e, In e γ' -> se_owner e = k1 -> In e γ.

    Lemma ownsub_refl k1 γ : OwnSub k1 γ γ.
    Proof. intros e He _. exact He. Qed.

    Lemma ownsub_trans k1 γ1 γ2 γ3 : OwnSub k1 γ1 γ2 -> OwnSub k1 γ2 γ3 -> OwnSub k1 γ1 γ3.
    Proof. intros H12 H23 e He Ho. exact (H12 e (H23 e He Ho) Ho). Qed.

    Lemma noown_ownsub k1 γ γ' : NoOwn k1 γ -> OwnSub k1 γ γ' -> NoOwn k1 γ'.
    Proof. intros Hno Hs e He Ho. exact (Hno e (Hs e He Ho) Ho). Qed.

    Lemma ownsub_ghost_emit k1 k (ev : ThreadEvent E) (γ γ' : Ghost E F) : ghost_emit k ev γ γ' -> OwnSub k1 γ γ'.
    Proof. intros Hge e He _. exact (ghost_emit_incl k ev γ γ' Hge e He). Qed.

    Lemma ownsub_invoke k1 key (γ γn : Ghost E F) :
      k1 <> key -> (forall e, In e γn -> se_owner e = key) -> OwnSub k1 γ (γ ++ γn).
    Proof.
      intros Hne Hown e He Ho. apply in_app_or in He as [He | He]; [exact He |].
      exfalso. apply Hne. rewrite <- Ho. exact (Hown e He).
    Qed.

    (** One step: the entries of a key [k1] of the pool only shrink. *)
    Theorem gmove_ownsub k1 P γ P' γ' :
      GMove (P, γ) (P', γ') -> In k1 (lin_domain P) -> OwnSub k1 γ γ'.
    Proof.
      intros Hm. change (In k1 (lin_domain (fst (P, γ))) -> OwnSub k1 (snd (P, γ)) (snd (P', γ'))).
      destruct Hm as [k ev P0 P0' γ0 γ0' Hge Hd | P0 P0' γ0 Hd | key st P0 γ0 γn Hfr Hown
                     | key st P0 P0' γ0 Hr Hno]; cbn [fst snd]; intros Hk.
      - exact (ownsub_ghost_emit k1 k ev γ0 γ0' Hge).
      - apply ownsub_refl.
      - apply (ownsub_invoke k1 key γ0 γn); [| exact Hown]. intros ->. exact (Hfr Hk).
      - apply ownsub_refl.
    Qed.

    Lemma gmove_gage P γ P' γ' : GMove (P, γ) (P', γ') -> GAge P γ -> GAge P' γ'.
    Proof.
      intros Hm. change (GAge (fst (P, γ)) (snd (P, γ)) -> GAge (fst (P', γ')) (snd (P', γ'))).
      destruct Hm as [k ev P0 P0' γ0 γ0' Hge Hd | P0 P0' γ0 Hd | key st P0 γ0 γn Hfr Hown
                     | key st P0 P0' γ0 Hr Hno]; cbn [fst snd]; intros Hage.
      - exact (gage_domain P0 P0' γ0' Hd (gage_ghost_emit P0 k ev γ0 γ0' Hge Hage)).
      - exact (gage_domain P0 P0' γ0 Hd Hage).
      - exact (gage_invoke key st P0 γ0 γn Hfr Hown Hage).
      - exact (gage_lin_remove key st P0 P0' γ0 Hr Hno Hage).
    Qed.

    (** [RecNB] is kept by every move while its owner [k] is in the pool. *)
    Theorem gmove_recnb k (ev : ThreadEvent E) P γ P' γ' :
      GMove (P, γ) (P', γ') -> In k (lin_domain P) -> RecNB P k ev γ -> RecNB P' k ev γ'.
    Proof.
      intros Hm Hk. apply recnb_oldersub. revert Hk.
      change (In k (lin_domain (fst (P, γ))) -> OlderSub k (fst (P, γ)) (snd (P, γ)) (fst (P', γ')) (snd (P', γ'))).
      destruct Hm as [k0 ev0 P0 P0' γ0 γ0' Hge Hd | P0 P0' γ0 Hd | key st P0 γ0 γn Hfr Hown
                     | key st P0 P0' γ0 Hr Hno]; cbn [fst snd]; intros Hk.
      - exact (oldersub_same_domain k P0 P0' γ0 γ0' Hd (ghost_emit_incl k0 ev0 γ0 γ0' Hge)).
      - apply oldersub_same_domain; [exact Hd | intros x Hx; exact Hx].
      - apply (oldersub_invoke k key st P0 γ0 γn Hfr); [| exact Hown]. intros ->. exact (Hfr Hk).
      - exact (oldersub_lin_remove k key st P0 P0' γ0 Hr).
    Qed.

    (** Paths of moves along which [k] is in the pool at each step's
        source (e.g. the rely of [k]: other calls are invoked and return,
        [k] is not removed). *)
    Definition GMovesIn (k : CallKey F) : LinPool F * Ghost E F -> LinPool F * Ghost E F -> Prop :=
      clos_refl_trans _ (fun x y => GMove x y /\ In k (lin_domain (fst x))).

    Theorem ghost_never_readded k P γ P' γ' : GMovesIn k (P, γ) (P', γ') -> OwnSub k γ γ'.
    Proof.
      intros Hp. change (OwnSub k (snd (P, γ)) (snd (P', γ'))).
      induction Hp as [[P0 γ0] [P1 γ1] [Hm Hk] | x | x y z _ IH1 _ IH2].
      - exact (gmove_ownsub k P0 γ0 P1 γ1 Hm Hk).
      - apply ownsub_refl.
      - exact (ownsub_trans k _ _ _ IH1 IH2).
    Qed.

    Corollary noown_persists k P γ P' γ' : GMovesIn k (P, γ) (P', γ') -> NoOwn k γ -> NoOwn k γ'.
    Proof. intros Hp Hno. exact (noown_ownsub k γ γ' Hno (ghost_never_readded k P γ P' γ' Hp)). Qed.

    Theorem recnb_gmoves k (ev : ThreadEvent E) P γ P' γ' :
      GMovesIn k (P, γ) (P', γ') -> RecNB P k ev γ -> RecNB P' k ev γ'.
    Proof.
      intros Hp. change (RecNB (fst (P, γ)) k ev (snd (P, γ)) -> RecNB (fst (P', γ')) k ev (snd (P', γ'))).
      induction Hp as [[P0 γ0] [P1 γ1] [Hm Hk] | x | x y z _ IH1 _ IH2].
      - exact (gmove_recnb k ev P0 γ0 P1 γ1 Hm Hk).
      - exact (fun H => H).
      - intros H. exact (IH2 (IH1 H)).
    Qed.

    Theorem gage_gmoves x y : clos_refl_trans _ GMove x y -> GAge (fst x) (snd x) -> GAge (fst y) (snd y).
    Proof.
      induction 1 as [[P0 γ0] [P1 γ1] Hm | x | x y z _ IH1 _ IH2].
      - exact (gmove_gage P0 γ0 P1 γ1 Hm).
      - exact (fun H => H).
      - intros H. exact (IH2 (IH1 H)).
    Qed.

    (** The RLHL transitions are moves. *)
    Section PossMoves.
      Context {VF : LTS F}.

      Lemma gmove_ev_update v P v' P' k (ev : ThreadEvent E) (γ γ' : Ghost E F) :
        poss_steps VF (PossOk v P) (PossOk v' P') -> ghost_emit k ev γ γ' -> GMove (P, γ) (P', γ').
      Proof. intros Hs Hge. apply (gm_emit k ev); [exact Hge |]. symmetry. exact (poss_steps_ok_domain VF _ _ _ _ Hs). Qed.

      Lemma gmove_poss_steps v P v' P' (γ : Ghost E F) :
        poss_steps VF (PossOk v P) (PossOk v' P') -> GMove (P, γ) (P', γ).
      Proof. intros Hs. apply gm_lin. symmetry. exact (poss_steps_ok_domain VF _ _ _ _ Hs). Qed.

      Lemma gmove_poss_invoke t h op v P p' (γ : Ghost E F) tr :
        poss_invoke VF t h op (PossOk v P) p' ->
        exists P', p' = PossOk v P' /\ GMove (P, γ) (P', γ ++ ghost_new (t, h) tr).
      Proof.
        intros Hi. destruct (RelaxedHoareInherit.pinv_inv_gen _ _ _ _ _ _ Hi) as [-> Hfr].
        eexists. split; [reflexivity |]. apply (gm_invoke (t, h) _ P γ _ Hfr). apply ghost_new_owner.
      Qed.

      Lemma gmove_poss_return t h op r v P p2 (γ : Ghost E F) :
        poss_return VF t h op r (PossOk v P) p2 -> NoOwn (t, h) γ ->
        exists P2, p2 = PossOk v P2 /\ GMove (P, γ) (P2, γ).
      Proof.
        intros Hr Hno. destruct (RelaxedHoareInherit.pret_inv_gen _ _ _ _ _ _ _ Hr) as (P2 & -> & Hrem).
        exists P2. split; [reflexivity | exact (gm_return _ _ P P2 γ Hrem Hno)].
      Qed.
    End PossMoves.
  End Moves.

  (** ** Part 5. Persistence: a key's ghost entries are kept by the moves
      of other keys (latest-review m-52)

      Part 4 is one direction ("never re-added": [OwnSub]).  This part is
      the dual ([OwnKeep]): an entry of [k] leaves the ghost only when [k]
      itself emits it.  Together they give the two-sided frame of [k]'s
      entries ([ownframe_of], [ghost_frame_other]).  See the header for
      how the prophetic read LP of the SeqLock uses both. *)

  Section Keep.
    Context {E F : RelaxedSig.t}.

    (** Script S2 of latest-review (lens 1), statement and proof
        unchanged: an emission by [k' <> k] keeps every entry of [k]. *)
    Lemma ghost_emit_keeps_other (k k' : CallKey F) (ev : ThreadEvent E) (γ γ' : Ghost E F) :
      ghost_emit k' ev γ γ' -> k' <> k -> forall e, In e γ -> se_owner e = k -> In e γ'.
    Proof.
      unfold ghost_emit. destruct (te_ev E ev).
      - intros (g1 & g2 & -> & -> & _) Hne e He Ho. apply in_app_or in He as [He | [<- | He]];
          [apply in_or_app; left; exact He | cbn in Ho; contradiction (Hne Ho) | apply in_or_app; right; exact He].
      - intros -> _ e He _. exact He.
    Qed.

    (** Entry level: an emission removes at most the emitted entry
        [Build_ScheduledEvent k' ev]; every other entry is kept (also of
        [k'] itself). *)
    Lemma ghost_emit_keeps_neq (k' : CallKey F) (ev : ThreadEvent E) (γ γ' : Ghost E F) e :
      ghost_emit k' ev γ γ' -> e <> Build_ScheduledEvent k' ev -> In e γ -> In e γ'.
    Proof.
      unfold ghost_emit. destruct (te_ev E ev).
      - intros (g1 & g2 & -> & -> & _) Hne He. apply in_app_or in He as [He | [He | He]];
          [apply in_or_app; left; exact He | contradiction (Hne (eq_sym He)) | apply in_or_app; right; exact He].
      - intros -> _ He. exact He.
    Qed.

    (** [OwnKeep k γ γ']: every entry of [γ] owned by [k] is in [γ'] (the
        dual of [OwnSub]; [ownkeep_ownsub]). *)
    Definition OwnKeep (k : CallKey F) (γ γ' : Ghost E F) : Prop :=
      forall e, In e γ -> se_owner e = k -> In e γ'.

    Lemma ownkeep_ownsub k γ γ' : OwnKeep k γ γ' <-> OwnSub k γ' γ.
    Proof. split; intros H e He Ho; exact (H e He Ho). Qed.

    Lemma ownkeep_refl k γ : OwnKeep k γ γ.
    Proof. intros e He _. exact He. Qed.

    Lemma ownkeep_trans k γ1 γ2 γ3 : OwnKeep k γ1 γ2 -> OwnKeep k γ2 γ3 -> OwnKeep k γ1 γ3.
    Proof. intros H12 H23 e He Ho. exact (H23 e (H12 e He Ho) Ho). Qed.

    Lemma ownkeep_incl k (γ γ' : Ghost E F) : incl γ γ' -> OwnKeep k γ γ'.
    Proof. intros Hi e He _. exact (Hi e He). Qed.

    (** Closure under the transitions of the proof state. *)

    Lemma ownkeep_ghost_emit_other k k' (ev : ThreadEvent E) (γ γ' : Ghost E F) :
      ghost_emit k' ev γ γ' -> k' <> k -> OwnKeep k γ γ'.
    Proof. intros Hge Hne. exact (ghost_emit_keeps_other k k' ev γ γ' Hge Hne). Qed.

    Lemma ownkeep_ghost_emit_res k k' (ev : ThreadEvent E) (γ γ' : Ghost E F) :
      is_response ev -> ghost_emit k' ev γ γ' -> OwnKeep k γ γ'.
    Proof.
      unfold is_response, ghost_emit. destruct (te_ev E ev); [intros [] | intros _ -> ; apply ownkeep_refl].
    Qed.

    (** An invocation appends: every entry is kept, for every key. *)
    Lemma ownkeep_app k (γ γn : Ghost E F) : OwnKeep k γ (γ ++ γn).
    Proof. intros e He _. apply in_or_app. left. exact He. Qed.

    (** Uses: ownership of an entry with a property persists; in
        particular [~ NoOwn] persists (the B-6 escape at the return). *)
    Lemma ownkeep_exists k (γ γ' : Ghost E F) (Q : ScheduledEvent E F -> Prop) :
      OwnKeep k γ γ' -> (exists e, In e γ /\ se_owner e = k /\ Q e) -> exists e, In e γ' /\ se_owner e = k /\ Q e.
    Proof. intros Hk (e & He & Ho & Hq). exists e. split; [exact (Hk e He Ho) | auto]. Qed.

    Lemma ownkeep_not_noown k (γ γ' : Ghost E F) : OwnKeep k γ γ' -> ~ NoOwn k γ -> ~ NoOwn k γ'.
    Proof.
      intros Hk Hn Hno'. apply Hn. intros e He Ho. exact (Hno' e (Hk e He Ho) Ho).
    Qed.

    (** At [k]'s own emission of [ev], an entry of [k] other than the
        emitted one keeps [k] owning (a non-final step of a call). *)
    Lemma not_noown_emit_other_entry k (ev : ThreadEvent E) (γ γ' : Ghost E F) e :
      ghost_emit k ev γ γ' -> In e γ -> se_owner e = k -> e <> Build_ScheduledEvent k ev -> ~ NoOwn k γ'.
    Proof.
      intros Hge He Ho Hne Hno. exact (Hno e (ghost_emit_keeps_neq k ev γ γ' e Hge Hne He) Ho).
    Qed.

    (** Both directions: [k]'s entries are the same. *)
    Lemma ownframe_of k (γ γ' : Ghost E F) :
      OwnSub k γ γ' -> OwnKeep k γ γ' -> forall e, se_owner e = k -> (In e γ <-> In e γ').
    Proof. intros Hs Hk e Ho. split; [intros He; exact (Hk e He Ho) | intros He; exact (Hs e He Ho)]. Qed.

    Lemma ownframe_to k (γ γ' : Ghost E F) :
      (forall e, se_owner e = k -> (In e γ <-> In e γ')) -> OwnSub k γ γ' /\ OwnKeep k γ γ'.
    Proof. intros Hf. split; intros e He Ho; apply (Hf e Ho); exact He. Qed.

    (** Moves tagged with the key that performs them: an emission by [k'];
        a domain-preserving update (any tag); the invocation of the fresh
        key [k']; the return of [k'] with no entry left.  Every [GMove] is
        a [GMoveBy] of some key ([gmove_gmoveby]) and conversely
        ([gmoveby_gmove]). *)
    Inductive GMoveBy (k' : CallKey F) : LinPool F * Ghost E F -> LinPool F * Ghost E F -> Prop :=
    | gmb_emit (ev : ThreadEvent E) (P P' : LinPool F) (γ γ' : Ghost E F) :
        ghost_emit k' ev γ γ' -> lin_domain P' = lin_domain P -> GMoveBy k' (P, γ) (P', γ')
    | gmb_lin (P P' : LinPool F) (γ : Ghost E F) :
        lin_domain P' = lin_domain P -> GMoveBy k' (P, γ) (P', γ)
    | gmb_invoke st (P : LinPool F) (γ γn : Ghost E F) :
        lin_fresh k' P -> (forall e, In e γn -> se_owner e = k') ->
        GMoveBy k' (P, γ) (make_lin_entry k' st :: P, γ ++ γn)
    | gmb_return st (P P' : LinPool F) (γ : Ghost E F) :
        lin_remove k' st P P' -> NoOwn k' γ -> GMoveBy k' (P, γ) (P', γ).

    Lemma gmoveby_gmove k' x y : GMoveBy k' x y -> GMove x y.
    Proof.
      destruct 1 as [ev P P' γ γ' Hge Hd | P P' γ Hd | st P γ γn Hfr Hown | st P P' γ Hr Hno].
      - exact (gm_emit k' ev P P' γ γ' Hge Hd).
      - exact (gm_lin P P' γ Hd).
      - exact (gm_invoke k' st P γ γn Hfr Hown).
      - exact (gm_return k' st P P' γ Hr Hno).
    Qed.

    (** [k0] tags the domain-preserving updates, which have no mover. *)
    Lemma gmove_gmoveby (k0 : CallKey F) x y : GMove x y -> exists k', GMoveBy k' x y.
    Proof.
      destruct 1 as [k ev P P' γ γ' Hge Hd | P P' γ Hd | key st P γ γn Hfr Hown | key st P P' γ Hr Hno].
      - exists k. exact (gmb_emit k ev P P' γ γ' Hge Hd).
      - exists k0. exact (gmb_lin k0 P P' γ Hd).
      - exists key. exact (gmb_invoke key st P γ γn Hfr Hown).
      - exists key. exact (gmb_return key st P P' γ Hr Hno).
    Qed.

    (** One move by another key keeps [k]'s entries, both ways (no pool
        condition on [k] is needed). *)
    Theorem gmoveby_ownkeep k k' P γ P' γ' : GMoveBy k' (P, γ) (P', γ') -> k' <> k -> OwnKeep k γ γ'.
    Proof.
      intros Hm Hne. change (OwnKeep k (snd (P, γ)) (snd (P', γ'))).
      destruct Hm as [ev P0 P0' γ0 γ0' Hge Hd | P0 P0' γ0 Hd | st P0 γ0 γn Hfr Hown | st P0 P0' γ0 Hr Hno];
        cbn [fst snd].
      - exact (ownkeep_ghost_emit_other k k' ev γ0 γ0' Hge Hne).
      - apply ownkeep_refl.
      - apply ownkeep_app.
      - apply ownkeep_refl.
    Qed.

    Theorem gmoveby_ownsub k k' P γ P' γ' : GMoveBy k' (P, γ) (P', γ') -> k' <> k -> OwnSub k γ γ'.
    Proof.
      intros Hm Hne. change (OwnSub k (snd (P, γ)) (snd (P', γ'))).
      destruct Hm as [ev P0 P0' γ0 γ0' Hge Hd | P0 P0' γ0 Hd | st P0 γ0 γn Hfr Hown | st P0 P0' γ0 Hr Hno];
        cbn [fst snd].
      - exact (ownsub_ghost_emit k k' ev γ0 γ0' Hge).
      - apply ownsub_refl.
      - apply (ownsub_invoke k k' γ0 γn); [intros E'; apply Hne; symmetry; exact E' | exact Hown].
      - apply ownsub_refl.
    Qed.

    (** Paths of moves by keys other than [k] (e.g. the rely of [k]). *)
    Definition GMovesOther (k : CallKey F) : LinPool F * Ghost E F -> LinPool F * Ghost E F -> Prop :=
      clos_refl_trans _ (fun x y => exists k', k' <> k /\ GMoveBy k' x y).

    Theorem ghost_kept k P γ P' γ' : GMovesOther k (P, γ) (P', γ') -> OwnKeep k γ γ'.
    Proof.
      intros Hp. change (OwnKeep k (snd (P, γ)) (snd (P', γ'))).
      induction Hp as [[P0 γ0] [P1 γ1] (k' & Hne & Hm) | x | x y z _ IH1 _ IH2].
      - exact (gmoveby_ownkeep k k' P0 γ0 P1 γ1 Hm Hne).
      - apply ownkeep_refl.
      - exact (ownkeep_trans k _ _ _ IH1 IH2).
    Qed.

    Theorem ghost_frame_other k P γ P' γ' :
      GMovesOther k (P, γ) (P', γ') -> forall e, se_owner e = k -> (In e γ <-> In e γ').
    Proof.
      intros Hp. apply ownframe_of; [| exact (ghost_kept k P γ P' γ' Hp)].
      change (OwnSub k (snd (P, γ)) (snd (P', γ'))).
      induction Hp as [[P0 γ0] [P1 γ1] (k' & Hne & Hm) | x | x y z _ IH1 _ IH2].
      - exact (gmoveby_ownsub k k' P0 γ0 P1 γ1 Hm Hne).
      - apply ownsub_refl.
      - exact (ownsub_trans k _ _ _ IH1 IH2).
    Qed.

    Corollary owned_persists k P γ P' γ' : GMovesOther k (P, γ) (P', γ') -> ~ NoOwn k γ -> ~ NoOwn k γ'.
    Proof. intros Hp. exact (ownkeep_not_noown k γ γ' (ghost_kept k P γ P' γ' Hp)). Qed.

    (** The RLHL transitions as tagged moves. *)
    Section PossMovesBy.
      Context {VF : LTS F}.

      Lemma gmoveby_ev_update v P v' P' k (ev : ThreadEvent E) (γ γ' : Ghost E F) :
        poss_steps VF (PossOk v P) (PossOk v' P') -> ghost_emit k ev γ γ' -> GMoveBy k (P, γ) (P', γ').
      Proof. intros Hs Hge. apply (gmb_emit k ev); [exact Hge |]. symmetry. exact (poss_steps_ok_domain VF _ _ _ _ Hs). Qed.

      Lemma gmoveby_poss_steps k v P v' P' (γ : Ghost E F) :
        poss_steps VF (PossOk v P) (PossOk v' P') -> GMoveBy k (P, γ) (P', γ).
      Proof. intros Hs. apply gmb_lin. symmetry. exact (poss_steps_ok_domain VF _ _ _ _ Hs). Qed.

      Lemma gmoveby_poss_invoke t h op v P p' (γ : Ghost E F) tr :
        poss_invoke VF t h op (PossOk v P) p' ->
        exists P', p' = PossOk v P' /\ GMoveBy (t, h) (P, γ) (P', γ ++ ghost_new (t, h) tr).
      Proof.
        intros Hi. destruct (RelaxedHoareInherit.pinv_inv_gen _ _ _ _ _ _ Hi) as [-> Hfr].
        eexists. split; [reflexivity |]. apply (gmb_invoke (t, h) _ P γ _ Hfr). apply ghost_new_owner.
      Qed.

      Lemma gmoveby_poss_return t h op r v P p2 (γ : Ghost E F) :
        poss_return VF t h op r (PossOk v P) p2 -> NoOwn (t, h) γ ->
        exists P2, p2 = PossOk v P2 /\ GMoveBy (t, h) (P, γ) (P2, γ).
      Proof.
        intros Hr Hno. destruct (RelaxedHoareInherit.pret_inv_gen _ _ _ _ _ _ _ Hr) as (P2 & -> & Hrem).
        exists P2. split; [reflexivity | exact (gmb_return _ _ P P2 γ Hrem Hno)].
      Qed.
    End PossMovesBy.
  End Keep.

  (** The B-6 escape at the return, generically: a postcondition [Q] that
      discharges [RetCond] may be weakened by the disjunct "[k] still owns
      a ghost entry", because [RetCond] is asked only under [NoOwn k]
      ([MethodProvable.mp_ret], [CallTriple.ct_return]).  The persistence
      lemmas above are how a derivation establishes that disjunct on a
      path that returns early (reader-eval §1.3). *)
  Section RetOwned.
    Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.
    Context (I : Assn VE VF) (G : CallKey F -> PRel VE VF).

    Lemma retcond_or_owned k op (Q : Sig.ar op -> Assn VE VF) :
      (forall r s, Q r s -> I s -> NoOwn k (ps_ghost s) -> RetCond I G k op r s) ->
      forall r s, (Q r s \/ ~ NoOwn k (ps_ghost s)) -> I s -> NoOwn k (ps_ghost s) -> RetCond I G k op r s.
    Proof. intros Hq r s [Hs | Hn] HI Hno; [exact (Hq r s Hs HI Hno) | contradiction (Hn Hno)]. Qed.
  End RetOwned.

End RelaxedHoareReady.
