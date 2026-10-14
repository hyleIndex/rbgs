(** * TableBarrier: the buffered memory under a table-induced semi-independence relation, with ghost-location barriers

    Task F-1 of the buffered-cell redesign of the SeqLock running example
    (.rocq-review/buffered-cell-plan.md, Phase 1).  The SeqLock's
    categories and its table [WindowTable.dto] are in examples/, and
    memory/ must not depend on examples/, so the table is a parameter
    here.  This file imports only memory/ and models/RelaxedSignature.v,
    and changes no existing file.

    Definitions.
    - [I_tab to cat m m' := op_loc m <> op_loc m' /\ to (cat m) (cat m') = false].
      [C] is any configuration, [Cat] any category type, [to] any boolean
      table ([to c d = true]: an earlier [c] is ordered before a later [d]),
      and [cat] any categorization of the cell operations.  Two operations
      at one location are never semi-independent.  The fence modes of [C]
      are not consulted, so [I_tab] is not [Cell.mode_indep], and
      [Cell.CellRSig] over these configurations is not the table signature.
    - [tab_cfg dec MA]: the locations [gloc D] are data locations [Dat d]
      and two ghost locations [GBw] and [GBr]; [MA] is any mode assignment.
      [wmb v a := wrt GBw v a] and [rmb a := rd GBr a].
      [bcat catD cWmb cRmb] gives every wmb the category [cWmb], every rmb
      the category [cRmb], and every other operation its [catD] category.
      This includes ghost accesses that are not barriers (a read of Bw, a
      write of Br), which programs are not meant to issue; nothing here
      excludes them.
    - [relabel f s]: the block at position [i] of [s] gets handle [f i].

    Why two ghost locations, [Bw <> Br].  In the SeqLock underlay both
    barriers belong to object OB, and [SeqLockCOH.same_obj OB OB = false]
    (examples/Relaxed/SeqLockCOH.v:182-186).  So the same-object rule does
    not order rmb and wmb; only the table does, and it leaves them
    unordered.  [I_tab] orders every same-location pair, so with one
    barrier location an rmb and a wmb would be ordered in both directions,
    whatever the table says ([one_location_orders]).  With two locations
    they are unordered exactly when the table says so
    ([barriers_unordered]).  A second effect: programs never write Br and
    never read Bw.  So an rmb always reads the initial value 0 from memory
    and creates no rf or rb edge; on a single location an rmb could read
    another thread's wmb.
    Bw is one location shared by all threads, so [mo] totally orders the
    wmb writes of all threads.  Explanation, not a lemma: when no program
    reads Bw this adds no constraint.  The only coherence edges at Bw are
    then [mo] and same-thread [po_loc], and the latter is already in [ppo]
    (same location, hence not in [I_tab]).  If the other edges of [Dc] are
    acyclic, choosing [mo] at Bw along a linear extension of them keeps
    (D1) and (D2).  This is needed only on the declarative route to
    hardware (task G-1).  The x86 route of [memory/TableBarrierTSO.v] goes
    through the machine and [TSO.tso_traces] and does not use it.

    Results on [I_tab] (Part 3) and on the barriers (Part 6).
    - [I_tab_cross]: [I_tab m m' -> op_loc m <> op_loc m'], the hypothesis
      [HI] of [Equivalence.declarative_characterization].
    - [declarative_tab]: that theorem for [I_tab].  For a well-formed
      candidate [X] and an admissible [pre], [X] has a well-formed witness
      satisfying (D1) and (D2) iff some history of [ν_{I_tab}] presents [X]
      and respects [pre].
    - [pre0_of_to], [ppo_WW_of_to], [ppo_R_of_to]: a same-thread pair that
      the table orders is in [po \ I_tab].  Between two writes it is in
      [ppo] for every [pre]; from a read it is in [ppo] for every
      [pre ⊇ po \ I_tab].
    - [ppo_wmb_WW]: let [W →po wmb →po W'], with [W] and [W'] writes,
      [to (cat W) cWmb = true] and [to cWmb (cat W') = true].  Then both
      edges are in [ppo] for every [pre], and [(W, W')] is in [Dc⁺] for
      every witness.  The composite itself is in [ppo] only if the table
      also orders [cat W] before [cat W'].
    - [ppo_rmb_RR]: let [R →po rmb →po R'], with [R] a read,
      [to (cat R) cRmb = true], [to cRmb (cat R') = true] and
      [pre ⊇ po \ I_tab] (true of every admissible [pre]).  Then both edges
      and the composite [(R, R')] are in [ppo].
    - [contract_blocks]: the operational side.  In a trace that satisfies
      the contract, a flush cannot publish [m] while a pending write [m']
      of the same thread with a smaller handle has
      [to (cat m') (cat m) = true].

    Handle invariance (Parts 2 and 3).  The flush contract
    ([Cell.contract], Def. mem:def:contract) compares handles, so the
    handles carried by a trace are part of its meaning.
    - Equal handles are not a valid choice.  If all handles are equal, no
      pending write has a smaller handle than the one being published, so
      the contract holds vacuously and a wmb has no effect.
      [handle_invariance_needs_compare] is a kernel instance: under the
      constant assignment [f_tie] the contract holds, under [f_swap] it
      fails.  The existing SeqLock underlay encoding gives every operation
      index 0 ([SeqLockModule.uev], examples/Relaxed/SeqLockModule.v:511),
      so that index is not a valid handle for [V_{I_tab}].  The handles
      must be witness indices (positions in the sequential witness).
    - The declarative side assumes handles that increase in program order
      ([wf_cand.po_handles], memory/Declarative.v:59; Assumption
      mem:ass:handles).  The results below say when witness indices and
      such handles give the same contract.  Two pieces are still missing;
      they are carried into tasks D-2 and G-1:
      (i) [nu_handle_invariant]: the same invariance at the level of
      hidden histories ([hide]), whose positions differ from those of the
      trace with flushes by a monotone reindexing;
      (ii) [po_handles_vs_index]: for a well-formed candidate and a history
      that presents it and respects [po \ I_tab], under [write_symmetric],
      program-order handles and issue positions compare alike on dependent
      same-thread write pairs, so that [contract_witness_index] applies.
      On the x86 route neither is needed for soundness:
      [TableBarrierTSO.x86_trace_V_tab_index] gives every x86-TSO trace a
      witness with position handles, for every table.
    - [contract_handle_invariant_gen], for any [I] given as decidable
      ([I m m' \/ ~ I m m']).  The contracts of [relabel f1 s] and
      [relabel f2 s] coincide if [f1] and [f2] compare ([Nat.compare]) the
      positions of every pair of same-thread writes [(a, b)] with
      [~ I a b] in the same way.  Pairs are at distinct positions, in
      either order.  No symmetry is needed.
    - [contract_handle_invariant], the planned statement.  Take [I_tab],
      and assume [write_symmetric to cat]: the table is symmetric on the
      categories of write invocations.  Then it suffices that [f1] and [f2]
      agree on the pairs where [a] is issued before [b] (positions
      [i < j]) and [~ I_tab a b]; these are the pairs that rhb orders.
      [V_handle_invariant]: the same for [V I_tab].
      [contract_handle_invariant_self] and [contract_witness_index] compare
      a trace with its relabelling.  For the latter it is enough that the
      trace's handles and [f] both increase along issue order on those
      pairs.
    - Both features of the statement are needed; Part 7 checks this on
      examples.  [handle_invariance_needs_symmetry]: with an asymmetric
      table (everything is ordered before a "release" write of x), the
      issue-ordered hypothesis holds vacuously and the contracts differ.
      [handle_invariance_needs_compare]: agreeing on [<] alone is not
      enough when an assignment has ties, even with a symmetric table.
    - [relabel] overwrites the handles that the base trace [s] carries;
      only [f1] and [f2] matter.

    Scope of the table instance.  [I_tab] is defined for any table, but
    two kinds of table entries do not get their usual meaning here.
    - (a) An entry from a write category to a read category orders issue
      only, not publication.  The contract constrains only pairs of writes
      (Cell.v:603), and a read is served when it is issued.  So the entry
      places the read after the write's issue (in [pre] and in rhb), but the
      write may still be pending when the read executes.  No table entry
      and no ghost access makes a later read wait for an earlier write's
      publication: this model has no draining fence.  Examples from
      [WindowTable.dto]: rcsc's [L];po;[A] (DWrel→DRacq), acquire-like
      writes, and [DFence] used as mb.  By evaluation, DW→DR is unordered,
      so the SeqLock's cell categories have no ordered cross-location W→R
      entry and are not affected.
    - (b) Witness-index handles need [write_symmetric]
      ([contract_handle_invariant]; [handle_invariance_needs_symmetry] when
      it fails).  By evaluation in a scratch session (not in a file),
      [dto rc] is symmetric on {DW, Wmb, DRMW} for both [rc].  It is not
      symmetric once a release-like write category is buffered:
      [dto rc DWrel DW = false] but [dto rc DW DWrel = true].  The same
      holds for an acquire RMW category ([Acc KRW true false]) against DW.
      A generic TicketLock category set [K], or cells with rel/acq
      accesses, would therefore need program-order handles (Assumption
      mem:ass:handles).  This agrees with Mem.tex:196 and Ex. mem:ex:three
      for release/acquire memory.

    Non-vacuity (Part 7), on the abstract table [ato] over
    [ACat = {cR, cW, cRmb, cWmb}].  W→Wmb, Wmb→W, Wmb→Wmb, R→Rmb, Rmb→R and
    Rmb→Rmb are ordered, nothing else.  This is [WindowTable.dto rcsc]
    restricted to DR, DW, Rmb and Wmb, for both values of [rcsc].  That
    was checked in a scratch session (all 32 entries, by [reflexivity]),
    not in this file, because memory/ cannot import examples/.
    Configuration: data locations [nat] (x = [Dat 0], y = [Dat 1]) and
    unit modes; data reads have category [cR], all other data operations
    [cW].
    - MP+wmb/rmb is forbidden: T1: W x 1; wmb; W y 1 ‖ T2: R y = 1; rmb;
      R x = 0.
      [mp_wmb_rmb_inconsistent]: for every admissible [pre] and every
      well-formed witness, (D2) fails, by the [Dc] cycle
      W x 1 →ppo⁺ W y 1 →rfe R y = 1 →ppo R x = 0 →rb W x 1.  Its two
      [ppo] steps are [ppo_wmb_WW] and [ppo_rmb_RR].
      [mp_wmb_rmb_forbidden]: no history of [ν_{I_tab}] presents the
      candidate and respects an admissible [pre].
      [mp_wmb_rmb_forbidden_pre0]: in particular for [pre = po \ I_tab].
      These two go through [declarative_tab] (the extraction direction of
      the equivalence); there is no direct argument on [V].  The clause
      "respects [pre]" is essential.  [ν] is a set of histories with no
      issue order, and [mp_wmb_rmb_nu_unordered] shows a history of [ν]
      that presents the same candidate with T2's R x = 0 issued first.
      [mp_wmb_rmb_allowed_outcome] (positive control): the same program
      with the outcome R x = 1 is in [ν_{I_tab}], with a history that
      respects all of program order.  So the negative result comes from the
      outcome, not from the ghost encoding.
    - Controls: each barrier is needed.
      [mp_no_rmb_allowed]: without the rmb, the outcome is in [ν_{I_tab}]
      with a history that respects [po \ I_tab].  T2's two reads are
      unordered, so R x = 0 is issued first.
      [mp_no_wmb_allowed]: without the wmb, the outcome is in [ν_{I_tab}]
      with a history that respects all of program order; W y 1 is
      published before W x 1.
    - SB+rfi, Reviewer A's test (popl2027-reviews.md:69-81), is allowed:
      T1: W x 1; R x = 1; R y = 0 ‖ T2: W y 1; R y = 1; R x = 0, no
      barriers.  [sbrfi_tab_V], [sbrfi_tab_nu]; [sbrfi_tab_po]: the history
      respects all of program order; [sbrfi_tab_consistent]: (D1) and (D2)
      hold with [pre] the whole program order.
    - [ato_write_symmetric]: the symmetry premise holds for [ato].
      [mp_normb_witness_index]: an instance of [contract_witness_index] on
      a trace with two dependent same-thread write pairs and one
      independent pair.

    What this file does not give.
    - No atomic objects and no hybrid specification: the TicketLock and
      the atomic clause are task F-2.  memory/ has no read-modify-write.
    - No hardware model in this file.  The x86-TSO side (read/write
      fragment) is in [memory/TableBarrierTSO.v]: every trace of the x86
      machine, with ghost barriers inserted, is in [V_{I_tab}] for every
      table.  There is nothing on ARMv8 ([memory/ARM.v] has no fences and no
      RMWs); dmb ld/st and the RMW flavours are task G-3.  On x86, rmb and
      wmb are compiler barriers; in this model their effect comes from the
      table alone.
    - No link from [ν_{I_tab}] to relaxed linearizability or to the module
      semantics (task G-1).  [ppo_wmb_WW] and [ppo_rmb_RR] are about [ppo]
      and [Dc] on the declarative side.  The issue-order role of the
      barriers in [rel_lin], through [rhb], is not stated here.
    - [I_tab] may relate flush operations (through [cat]'s value on them).
      That is irrelevant here, because the contract applies [I] to pending
      writes only and candidates contain no flushes.  It is also why
      [I_tab] is not packaged as a [RelaxedSig.well_formed] signature.
    - Categories are a function of the invocation, as the plan requires.
      Categories that depend on the program point would need more.

    Trusted computation.  The finite checks ([tchk], [vchk], [pochk],
    [pre0chk], [idxchk]) are closed by [exact eq_refl], that is, by the
    kernel's conversion; there is no [vm_compute].  Proofs by [lia] carry
    a VM cast, as elsewhere in the development.

    Assumptions.  [declarative_tab], [mp_wmb_rmb_forbidden],
    [mp_wmb_rmb_forbidden_pre0] and [sbrfi_tab_consistent] use [classic],
    through [Equivalence.declarative_characterization].  Every other result
    is closed under the global context, including
    [mp_wmb_rmb_inconsistent] and all handle-invariance results. *)

From Stdlib Require Import List Arith PArith Bool micromega.Lia.
From Stdlib Require Import Relations.Relation_Definitions Relations.Relation_Operators Sorting.Permutation.
Require Import models.RelaxedSignature.
Require Import memory.Prelude.
Require Import memory.Cell.
Require Import memory.Declarative.
Require Import memory.Equivalence.

Import ListNotations.

Module TableBarrier.
  Import RelaxedSig Cell Decl.

  (** ** Part 1. Handles, relabelling, and pending writes over tagged lists *)

  Section Relabel.
    Context {C : Cfg}.

    Definition set_handle (b : block C) (h : nat) : block C :=
      match b with
      | BW t _ x v a => BW t h x v a
      | BR t _ x a v => BR t h x a v
      | BF t _ x => BF t h x
      end.

    Lemma set_handle_handle b h : b_handle (set_handle b h) = h.
    Proof. destruct b; reflexivity. Qed.
    Lemma set_handle_tid b h : b_tid (set_handle b h) = b_tid b.
    Proof. destruct b; reflexivity. Qed.
    Lemma set_handle_loc b h : b_loc (set_handle b h) = b_loc b.
    Proof. destruct b; reflexivity. Qed.
    Lemma set_handle_inv b h : b_inv (set_handle b h) = b_inv b.
    Proof. destruct b; reflexivity. Qed.
    Lemma set_handle_twice b h h' : set_handle (set_handle b h) h' = set_handle b h'.
    Proof. destruct b; reflexivity. Qed.
    Lemma set_handle_self b : set_handle b (b_handle b) = b.
    Proof. destruct b; reflexivity. Qed.

    (** [tagf n l] pairs each element of [l] with its position, counted
        from [n]. *)
    Fixpoint tagf {A : Type} (n : nat) (l : list A) : list (nat * A) :=
      match l with
      | [] => []
      | a :: l' => (n, a) :: tagf (S n) l'
      end.

    Lemma tagf_In {A : Type} n (l : list A) i a :
      In (i, a) (tagf n l) -> n <= i /\ nth_error l (i - n) = Some a.
    Proof.
      revert n. induction l as [| b l IH]; intros n H; cbn in H; [contradiction |].
      destruct H as [H | H].
      - inversion H; subst. rewrite Nat.sub_diag. split; [lia | reflexivity].
      - apply IH in H. destruct H as [Hle Hn]. split; [lia |].
        replace (i - n) with (S (i - S n)) by lia. exact Hn.
    Qed.

    Lemma map_snd_tagf {A : Type} n (l : list A) : map snd (tagf n l) = l.
    Proof. revert n. induction l as [| a l IH]; intros n; cbn; [reflexivity | f_equal; apply IH]. Qed.

    (** [relabel f s]: the block at position [i] of [s] gets handle [f i];
        nothing else changes. *)
    Definition relab (f : nat -> nat) (e : nat * block C) : block C :=
      set_handle (snd e) (f (fst e)).

    Definition relabel (f : nat -> nat) (s : trace C) : trace C :=
      map (relab f) (tagf 0 s).

    (** The handle assignment already present in [s]. *)
    Definition handles (s : trace C) (i : nat) : nat :=
      match nth_error s i with Some b => b_handle b | None => 0 end.

    Lemma relabel_handles s : relabel (handles s) s = s.
    Proof.
      unfold relabel. transitivity (map snd (tagf 0 s)); [| apply map_snd_tagf].
      apply map_ext_in. intros [i b] Hin. unfold relab. cbn [fst snd].
      apply tagf_In in Hin. destruct Hin as [_ Hn]. rewrite Nat.sub_0_r in Hn.
      unfold handles. rewrite Hn. apply set_handle_self.
    Qed.

    Lemma nth_error_relabel f s i :
      nth_error (relabel f s) i = option_map (fun b => set_handle b (f i)) (nth_error s i).
    Proof.
      unfold relabel.
      assert (H : forall n l i, nth_error (map (relab f) (tagf n l)) i =
                                option_map (fun b => set_handle b (f (n + i))) (nth_error l i)).
      { intros n l. revert n. induction l as [| b l IH]; intros n [| j]; cbn; try reflexivity.
        - unfold relab. cbn. rewrite Nat.add_0_r. reflexivity.
        - rewrite IH. replace (S n + j) with (n + S j) by lia. reflexivity. }
      apply H.
    Qed.

    (** The cell [Buf_x] ignores handles, so [VBuf] is unchanged by
        relabelling. *)
    Lemma enabled_set_handle b h st : enabled (set_handle b h) st <-> enabled b st.
    Proof. destruct b; reflexivity. Qed.

    Lemma step_at_set_handle x st b h : step_at x st (set_handle b h) = step_at x st b.
    Proof. destruct b; reflexivity. Qed.

    Lemma fold_step_relab x f (L : list (nat * block C)) st :
      fold_left (step_at x) (map (relab f) L) st = fold_left (step_at x) (map snd L) st.
    Proof.
      revert st. induction L as [| [i b] L IH]; intros st; [reflexivity |].
      cbn [map fold_left].
      rewrite (step_at_set_handle x st b (f i) : step_at x st (relab f (i, b)) = step_at x st b).
      apply IH.
    Qed.

    Lemma state_after_relabel_firstn x f s i :
      state_after x (firstn i (relabel f s)) = state_after x (firstn i s).
    Proof.
      unfold relabel, state_after. rewrite firstn_map, fold_step_relab, <- firstn_map, map_snd_tagf.
      reflexivity.
    Qed.

    Lemma VBuf_relabel f s x : VBuf x (proj x (relabel f s)) <-> VBuf x (proj x s).
    Proof.
      split; intros H; apply VBuf_proj_iff; apply VBuf_proj_iff in H; intros i b Hi Hloc.
      - specialize (H i (set_handle b (f i))). rewrite nth_error_relabel, Hi in H.
        rewrite state_after_relabel_firstn, set_handle_loc in H.
        apply (proj1 (enabled_set_handle b (f i) _)). apply H; auto.
      - rewrite nth_error_relabel in Hi.
        destruct (nth_error s i) as [b0 |] eqn:E; cbn in Hi; [| discriminate Hi].
        injection Hi as <-. rewrite set_handle_loc in Hloc.
        rewrite state_after_relabel_firstn. apply (proj2 (enabled_set_handle b0 (f i) _)).
        apply H; auto.
    Qed.

    (** *** [pend] over any list whose elements carry a block

        [pendG pr] is [Cell.pend] for a list of elements [a] read through
        [pr a].  With [pr := snd] on position-tagged blocks it remembers
        where each pending write was issued. *)
    Section PendG.
      Context {A : Type} (pr : A -> block C).

      Fixpoint rfaG (x : Loc C) (l : list A) : list A :=
        match l with
        | [] => []
        | a :: l' => if at_loc x (pr a) then l' else a :: rfaG x l'
        end.

      Definition pstepG (t : tid) (acc : list A) (a : A) : list A :=
        match pr a with
        | BW u _ _ _ _ => if Pos.eq_dec u t then acc ++ [a] else acc
        | BF u _ x => if Pos.eq_dec u t then rfaG x acc else acc
        | BR _ _ _ _ _ => acc
        end.

      Definition pendG (t : tid) (l : list A) : list A := fold_left (pstepG t) l [].

      Lemma rfaG_incl x l a : In a (rfaG x l) -> In a l.
      Proof.
        induction l as [| c l IH]; cbn; [tauto |].
        destruct (at_loc x (pr c)); cbn; [tauto |]. intros [-> | H]; [left | right]; auto.
      Qed.

      Lemma pendG_fold_In t l acc a :
        In a (fold_left (pstepG t) l acc) ->
        In a acc \/ (In a l /\ is_write (pr a) /\ b_tid (pr a) = t).
      Proof.
        revert acc. induction l as [| c l IH]; intros acc H; cbn in H; [left; exact H |].
        apply IH in H. destruct H as [H | (H1 & H2 & H3)];
          [| right; split; [right; exact H1 | auto]].
        unfold pstepG in H. destruct (pr c) as [u h x v m | u h x m v | u h x] eqn:E.
        - destruct (Pos.eq_dec u t) as [-> | Hne]; [| left; exact H].
          apply in_app_or in H. destruct H as [H | [<- | []]]; [left; exact H |].
          right. rewrite E. split; [left; reflexivity | split; [exact I | reflexivity]].
        - left; exact H.
        - destruct (Pos.eq_dec u t); [left; eapply rfaG_incl; eauto | left; exact H].
      Qed.

      Lemma pendG_In t l a :
        In a (pendG t l) -> In a l /\ is_write (pr a) /\ b_tid (pr a) = t.
      Proof. intros H. apply pendG_fold_In in H. destruct H as [[] | H]; exact H. Qed.
    End PendG.

    Lemma shape_loc (a b : block C) : set_handle a 0 = set_handle b 0 -> b_loc a = b_loc b.
    Proof. intros H. rewrite <- (set_handle_loc a 0), <- (set_handle_loc b 0), H. reflexivity. Qed.

    (** [pend], [proj] and [hd_error] commute with any map [g] that only
        changes handles. *)
    Section Natural.
      Context {A : Type} (pr g : A -> block C).
      Hypothesis Hg : forall a, set_handle (g a) 0 = set_handle (pr a) 0.

      Lemma at_loc_g x a : at_loc x (g a) = at_loc x (pr a).
      Proof. unfold at_loc. rewrite (shape_loc _ _ (Hg a)). reflexivity. Qed.

      Lemma rfa_map x l : remove_first_at x (map g l) = map g (rfaG pr x l).
      Proof.
        induction l as [| a l IH]; [reflexivity |].
        cbn [map rfaG]. rewrite remove_first_at_cons, at_loc_g.
        destruct (at_loc x (pr a)); [reflexivity | cbn [map]; rewrite IH; reflexivity].
      Qed.

      Lemma pend_step_map t acc a : pend_step t (map g acc) (g a) = map g (pstepG pr t acc a).
      Proof.
        unfold pstepG.
        destruct (g a) as [u h x v m | u h x m v | u h x] eqn:E1;
        destruct (pr a) as [u' h' x' v' m' | u' h' x' m' v' | u' h' x'] eqn:E2;
        pose proof (Hg a) as H; rewrite E1, E2 in H; cbn in H; try discriminate H;
        inversion H; subst; clear H; unfold pend_step.
        - destruct (Pos.eq_dec u' t); [| reflexivity].
          rewrite map_app. cbn [map]. rewrite E1. reflexivity.
        - reflexivity.
        - destruct (Pos.eq_dec u' t); [apply rfa_map | reflexivity].
      Qed.

      Lemma pend_map t l : pend t (map g l) = map g (pendG pr t l).
      Proof.
        unfold pend, pendG.
        assert (Hgen : forall acc, fold_left (pend_step t) (map g l) (map g acc) =
                                   map g (fold_left (pstepG pr t) l acc)).
        { induction l as [| a l IH]; intros acc; [reflexivity |].
          cbn [map fold_left]. rewrite pend_step_map. apply IH. }
        exact (Hgen []).
      Qed.

      Lemma proj_map x l : proj x (map g l) = map g (filter (fun a => at_loc x (pr a)) l).
      Proof.
        induction l as [| a l IH]; [reflexivity |].
        cbn [map filter]. rewrite proj_cons, at_loc_g.
        destruct (at_loc x (pr a)); cbn [map]; rewrite IH; reflexivity.
      Qed.
    End Natural.
  End Relabel.

  (** ** Part 2. Handle invariance of the contract, for any relation [I] *)

  Section Invariance.
    Context {C : Cfg} (I : cell_op C -> cell_op C -> Prop).
    Hypothesis Idec : forall m m', I m m' \/ ~ I m m'.

    Lemma contract_relabel_transfer (s : trace C) (f1 f2 : nat -> nat) :
      (forall i j a b, i <> j -> nth_error s i = Some a -> nth_error s j = Some b ->
         is_write a -> is_write b -> b_tid a = b_tid b -> ~ I (b_inv a) (b_inv b) ->
         Nat.compare (f1 i) (f1 j) = Nat.compare (f2 i) (f2 j)) ->
      contract I (relabel f2 s) -> contract I (relabel f1 s).
    Proof.
      intros Hag Hc2 p t h x q m Hdec Hm m' Hm' Hlt.
      assert (Hg1 : forall e : nat * block C, set_handle (relab f1 e) 0 = set_handle (snd e) 0)
        by (intros; apply set_handle_twice).
      assert (Hg2 : forall e : nat * block C, set_handle (relab f2 e) 0 = set_handle (snd e) 0)
        by (intros; apply set_handle_twice).
      unfold relabel in Hdec, Hc2.
      destruct (map_eq_app _ _ _ _ Hdec) as (T1 & T2 & HT & HT1 & HT2).
      destruct (map_eq_cons _ _ HT2) as (e & T3 & -> & He & _).
      assert (Hse : exists h0, snd e = BF t h0 x).
      { unfold relab in He. destruct (snd e) as [? ? ? ? ? | ? ? ? ? ? | u h0 y];
          cbn in He; try discriminate He.
        inversion He; subst. eauto. }
      destruct Hse as [h0 Hse].
      subst p. rewrite (pend_map snd (relab f1) Hg1) in Hm, Hm'.
      rewrite (proj_map snd (relab f1) Hg1) in Hm.
      destruct (filter (fun a => at_loc x (snd a)) (pendG snd t T1)) as [| em LX] eqn:ELX;
        [discriminate Hm |].
      cbn [map hd_error] in Hm. injection Hm as <-.
      apply in_map_iff in Hm'. destruct Hm' as (em' & <- & Hem').
      assert (HemL : In em (pendG snd t T1)).
      { assert (Hin : In em (filter (fun a => at_loc x (snd a)) (pendG snd t T1)))
          by (rewrite ELX; left; reflexivity).
        apply filter_In in Hin. tauto. }
      destruct (pendG_In snd t T1 em HemL) as (HemT & Hwm & Htm).
      destruct (pendG_In snd t T1 em' Hem') as (Hem'T & Hwm' & Htm').
      assert (HinT : forall e', In e' T1 -> nth_error s (fst e') = Some (snd e')).
      { intros [i b] Hi. cbn [fst snd].
        assert (Hi' : In (i, b) (tagf 0 s)) by (rewrite HT; apply in_or_app; left; exact Hi).
        apply tagf_In in Hi'. destruct Hi' as [_ Hn]. rewrite Nat.sub_0_r in Hn. exact Hn. }
      pose proof (HinT _ HemT) as Hj. pose proof (HinT _ Hem'T) as Hi.
      destruct em as [j bm], em' as [i bm']. cbn [fst snd] in *.
      unfold relab in Hlt |- *. cbn [fst snd] in Hlt |- *.
      rewrite !set_handle_handle in Hlt. rewrite !set_handle_inv.
      destruct (Idec (b_inv bm') (b_inv bm)) as [HI | HnI]; [exact HI | exfalso].
      assert (Hij : i <> j) by (intros ->; lia).
      pose proof (Hag i j bm' bm Hij Hi Hj Hwm' Hwm (eq_trans Htm' (eq_sym Htm)) HnI) as Hcmp.
      apply Nat.compare_lt_iff in Hlt. rewrite Hlt in Hcmp. symmetry in Hcmp.
      apply Nat.compare_lt_iff in Hcmp.
      apply HnI.
      rewrite HT, map_app in Hc2. cbn [map] in Hc2.
      assert (Hg2e : relab f2 e = BF t (f2 (fst e)) x) by (unfold relab; rewrite Hse; reflexivity).
      rewrite Hg2e in Hc2.
      specialize (Hc2 (map (relab f2) T1) t (f2 (fst e)) x (map (relab f2) T3)
                      (relab f2 (j, bm)) eq_refl).
      rewrite (pend_map snd (relab f2) Hg2), (proj_map snd (relab f2) Hg2), ELX in Hc2.
      specialize (Hc2 eq_refl (relab f2 (i, bm'))).
      unfold relab in Hc2. cbn [fst snd] in Hc2. rewrite !set_handle_inv, !set_handle_handle in Hc2.
      apply Hc2; [| exact Hcmp].
      apply in_map_iff. exists (i, bm'). split; [reflexivity | exact Hem'].
    Qed.

    (** The contract is the same under two handle assignments [f1], [f2]
        that order every pair of same-thread writes [(a, b)] with
        [~ I a b] (at distinct positions, in either position order) in
        the same way. *)
    Theorem contract_handle_invariant_gen (s : trace C) (f1 f2 : nat -> nat) :
      (forall i j a b, i <> j -> nth_error s i = Some a -> nth_error s j = Some b ->
         is_write a -> is_write b -> b_tid a = b_tid b -> ~ I (b_inv a) (b_inv b) ->
         Nat.compare (f1 i) (f1 j) = Nat.compare (f2 i) (f2 j)) ->
      contract I (relabel f1 s) <-> contract I (relabel f2 s).
    Proof.
      intros Hag. split; apply contract_relabel_transfer; auto.
      intros i j a b Hij Ha Hb Wa Wb Ht HnI. symmetry. eapply Hag; eauto.
    Qed.
  End Invariance.

  (** ** Part 3. The table-induced relation [I_tab] *)

  Section Table.
    Context {C : Cfg} {Cat : Type} (to : Cat -> Cat -> bool) (cat : cell_op C -> Cat).

    (** [m] (earlier) and [m'] (later) are semi-independent iff they are
        at different locations and the table does not order their
        categories. *)
    Definition I_tab (m m' : cell_op C) : Prop :=
      op_loc m <> op_loc m' /\ to (cat m) (cat m') = false.

    (** The hypothesis [HI] of [Equivalence.declarative_characterization]. *)
    Lemma I_tab_cross m m' : I_tab m m' -> op_loc m <> op_loc m'.
    Proof. intros [H _]. exact H. Qed.

    Lemma I_tab_same_loc m m' : op_loc m = op_loc m' -> ~ I_tab m m'.
    Proof. intros H [H' _]. exact (H' H). Qed.

    Lemma not_I_tab_of_to m m' : to (cat m) (cat m') = true -> ~ I_tab m m'.
    Proof. intros H [_ H']. rewrite H in H'. discriminate. Qed.

    Definition I_tabb (m m' : cell_op C) : bool :=
      negb (loc_eqb (op_loc m) (op_loc m')) && negb (to (cat m) (cat m')).

    Lemma I_tabb_spec m m' : I_tabb m m' = true <-> I_tab m m'.
    Proof.
      unfold I_tabb, I_tab. split.
      - intros H. apply andb_true_iff in H. destruct H as [H1 H2].
        apply negb_true_iff in H1, H2. split; [apply loc_eqb_false; exact H1 | exact H2].
      - intros [H1 H2]. apply andb_true_iff.
        split; apply negb_true_iff; [apply loc_eqb_false; exact H1 | exact H2].
    Qed.

    Lemma I_tab_dec m m' : I_tab m m' \/ ~ I_tab m m'.
    Proof.
      destruct (I_tabb m m') eqn:E.
      - left. apply I_tabb_spec. exact E.
      - right. intros H. apply I_tabb_spec in H. congruence.
    Qed.

    (** *** Declarative characterization for [I_tab] *)

    Theorem declarative_tab (X : cand C) (HX : wf_cand X)
        (pre : relation (block C)) (Hadm : admissible X I_tab pre) :
      (exists w, wf_witness X w /\ consistent X I_tab w pre) <->
      (exists s, nu I_tab s /\ presents s X /\ respects s pre).
    Proof. exact (Equivalence.declarative_characterization C I_tab I_tab_cross X HX pre Hadm). Qed.

    (** *** Preserved program order from table entries *)

    Lemma pre0_of_to (X : cand C) a b :
      po X a b -> to (cat (b_inv a)) (cat (b_inv b)) = true -> pre0 X I_tab a b.
    Proof.
      intros Hpo Hto. split; [exact Hpo |]. intros [_ H]. rewrite Hto in H. discriminate.
    Qed.

    (** A same-thread write--write pair ordered by the table is in [ppo]
        (second clause, [(po \ I) ∩ (W × W)]), whatever [pre] is. *)
    Lemma ppo_WW_of_to (X : cand C) (pre : relation (block C)) a b :
      po X a b -> is_write a -> is_write b ->
      to (cat (b_inv a)) (cat (b_inv b)) = true -> ppo X I_tab pre a b.
    Proof. intros Hpo Ha Hb Hto. right. split; [apply pre0_of_to; auto | split; auto]. Qed.

    (** A same-thread pair starting at a read and ordered by the table is in
        [pre] (as [pre ⊇ po \ I]), hence in [ppo] (first clause,
        [[rd]; pre⁺]). *)
    Lemma ppo_R_of_to (X : cand C) (pre : relation (block C)) a b :
      rel_incl (pre0 X I_tab) pre ->
      po X a b -> is_read a -> to (cat (b_inv a)) (cat (b_inv b)) = true -> ppo X I_tab pre a b.
    Proof.
      intros Hpre Hpo Ha Hto. left. split; [exact Ha |]. apply t_step. apply Hpre. apply pre0_of_to; auto.
    Qed.

    (** *** The operational side: the contract orders publications

        In a trace satisfying [contract I_tab], a flush cannot publish a
        write [m] while a pending write [m'] of the same thread with a
        smaller handle has [to (cat m') (cat m) = true]. *)
    Lemma contract_blocks (s : trace C) p t h x q m m' :
      contract I_tab s -> s = p ++ BF t h x :: q ->
      hd_error (proj x (pend t p)) = Some m ->
      In m' (pend t p) -> b_handle m' < b_handle m ->
      to (cat (b_inv m')) (cat (b_inv m)) = true -> False.
    Proof.
      intros Hc Hs Hm Hm' Hlt Hto. apply (not_I_tab_of_to _ _ Hto). eapply Hc; eauto.
    Qed.

    (** *** Handle invariance for [I_tab] *)

    (** The symmetry assumption: [to] is symmetric on the categories of
        write invocations (the buffered operations). *)
    Definition write_symmetric : Prop :=
      forall w w', op_is_write w -> op_is_write w' -> to (cat w) (cat w') = to (cat w') (cat w).

    Lemma is_write_inv (b : block C) : is_write b -> op_is_write (b_inv b).
    Proof. destruct b; cbn; tauto. Qed.

    Lemma I_tab_sym_writes (Hsym : write_symmetric) a b :
      is_write a -> is_write b -> I_tab (b_inv a) (b_inv b) -> I_tab (b_inv b) (b_inv a).
    Proof.
      intros Wa Wb [Hl Ht]. split; [congruence |].
      rewrite (Hsym (b_inv b) (b_inv a)); auto using is_write_inv.
    Qed.

    (** [contract_handle_invariant]: if [to] is symmetric on write
        categories, two handle assignments that order every same-thread
        write pair [(a, b)] with [a] issued before [b] and [~ I_tab a b] in
        the same way give the same contract. *)
    Theorem contract_handle_invariant (Hsym : write_symmetric) (s : trace C) (f1 f2 : nat -> nat) :
      (forall i j a b, i < j -> nth_error s i = Some a -> nth_error s j = Some b ->
         is_write a -> is_write b -> b_tid a = b_tid b -> ~ I_tab (b_inv a) (b_inv b) ->
         Nat.compare (f1 i) (f1 j) = Nat.compare (f2 i) (f2 j)) ->
      contract I_tab (relabel f1 s) <-> contract I_tab (relabel f2 s).
    Proof.
      intros Hag. apply contract_handle_invariant_gen; [exact I_tab_dec |].
      intros i j a b Hij Ha Hb Wa Wb Ht HnI.
      destruct (lt_eq_lt_dec i j) as [[Hlt | Heq] | Hgt]; [eapply Hag; eauto | contradiction |].
      assert (HnI' : ~ I_tab (b_inv b) (b_inv a)) by (intros H; apply HnI, I_tab_sym_writes; auto).
      pose proof (Hag j i b a Hgt Hb Ha Wb Wa (eq_sym Ht) HnI') as H.
      rewrite (Nat.compare_antisym (f1 j) (f1 i)), (Nat.compare_antisym (f2 j) (f2 i)), H.
      reflexivity.
    Qed.

    (** The same, comparing a trace with its relabelling. *)
    Corollary contract_handle_invariant_self (Hsym : write_symmetric) (s : trace C) (f : nat -> nat) :
      (forall i j a b, i < j -> nth_error s i = Some a -> nth_error s j = Some b ->
         is_write a -> is_write b -> b_tid a = b_tid b -> ~ I_tab (b_inv a) (b_inv b) ->
         Nat.compare (b_handle a) (b_handle b) = Nat.compare (f i) (f j)) ->
      contract I_tab s <-> contract I_tab (relabel f s).
    Proof.
      intros Hag. transitivity (contract I_tab (relabel (handles s) s)).
      - rewrite relabel_handles. reflexivity.
      - apply contract_handle_invariant; auto.
        intros i j a b Hij Ha Hb. unfold handles. rewrite Ha, Hb. apply Hag; auto.
    Qed.

    (** Witness indices.  If the handles of [s] and the assignment [f]
        (e.g. the position in the sequential witness) both increase along
        issue order on same-thread [I_tab]-dependent write pairs, the
        contract does not depend on which of the two is used. *)
    Corollary contract_witness_index (Hsym : write_symmetric) (s : trace C) (f : nat -> nat) :
      (forall i j a b, i < j -> nth_error s i = Some a -> nth_error s j = Some b ->
         is_write a -> is_write b -> b_tid a = b_tid b -> ~ I_tab (b_inv a) (b_inv b) ->
         b_handle a < b_handle b /\ f i < f j) ->
      contract I_tab s <-> contract I_tab (relabel f s).
    Proof.
      intros H. apply contract_handle_invariant_self; auto.
      intros i j a b Hij Ha Hb Wa Wb Ht HnI.
      destruct (H i j a b Hij Ha Hb Wa Wb Ht HnI) as [H1 H2].
      apply Nat.compare_lt_iff in H1, H2. congruence.
    Qed.

    (** The whole memory [V I_tab], not only its contract, is unchanged
        ([VBuf] ignores handles: [VBuf_relabel]). *)
    Theorem V_handle_invariant (Hsym : write_symmetric) (s : trace C) (f1 f2 : nat -> nat) :
      (forall i j a b, i < j -> nth_error s i = Some a -> nth_error s j = Some b ->
         is_write a -> is_write b -> b_tid a = b_tid b -> ~ I_tab (b_inv a) (b_inv b) ->
         Nat.compare (f1 i) (f1 j) = Nat.compare (f2 i) (f2 j)) ->
      V I_tab (relabel f1 s) <-> V I_tab (relabel f2 s).
    Proof.
      intros Hag. pose proof (contract_handle_invariant Hsym s f1 f2 Hag) as Hc.
      split; intros [H1 H2]; split.
      - apply Hc, H1.
      - intros x. apply (proj2 (VBuf_relabel f2 s x)), (proj1 (VBuf_relabel f1 s x)), H2.
      - apply Hc, H1.
      - intros x. apply (proj2 (VBuf_relabel f1 s x)), (proj1 (VBuf_relabel f2 s x)), H2.
    Qed.
  End Table.

  (** ** Part 4. Generic facts about candidates *)

  Section Candidates.
    Context {C : Cfg}.

    Lemma tc_po (X : cand C) (HX : wf_cand X) a b : tc (po X) a b -> po X a b.
    Proof.
      intros H. induction H as [a b H | a b c _ IH1 _ IH2]; [exact H | eapply (po_trans HX); eauto].
    Qed.

    Lemma po_admissible (X : cand C) (HX : wf_cand X) (I : cell_op C -> cell_op C -> Prop) :
      admissible X I (po X).
    Proof.
      split; [| split].
      - intros a b [H _]. exact H.
      - intros a Ha. apply (po_irrefl HX a). apply tc_po; auto.
      - intros a b H. apply (po_dom HX) in H. tauto.
    Qed.

    Lemma pre0_admissible (X : cand C) (HX : wf_cand X) (I : cell_op C -> cell_op C -> Prop) :
      admissible X I (pre0 X I).
    Proof.
      split; [| split].
      - intros a b H. exact H.
      - intros a Ha. apply (po_irrefl HX a). apply tc_po; auto.
        eapply tc_incl; [| exact Ha]. intros u v [H _]. exact H.
      - intros a b [H _]. apply (po_dom HX) in H. tauto.
    Qed.

    (** Program order as thread order by handle, as in [SeqLockQ6Mem]. *)
    Definition po_of (l : list (block C)) : relation (block C) :=
      fun a b => In a l /\ In b l /\ b_tid a = b_tid b /\ b_handle a < b_handle b.

    Definition cand_of (l : list (block C)) : cand C := {| ops := l; po := po_of l |}.
  End Candidates.

  (** ** Part 5. Boolean checkers with soundness lemmas *)

  Section Checkers.
    Context {C : Cfg}.

    Definition enabledb (b : block C) (st : cstate) : bool :=
      match b with
      | BW _ _ _ _ _ => true
      | BR t _ _ _ v => match cP st t with [] => Nat.eqb v (cg st) | l => Nat.eqb v (last l 0) end
      | BF t _ _ => match cP st t with [] => false | _ => true end
      end.

    Lemma enabledb_sound b st : enabledb b st = true -> enabled b st.
    Proof.
      destruct b as [t h x v a | t h x a v | t h x]; cbn; [auto | |].
      - destruct (cP st t) as [| n l] eqn:E; intros H; apply Nat.eqb_eq in H.
        + right. split; [reflexivity | exact H].
        + left. split; [discriminate | exact H].
      - destruct (cP st t); [discriminate | intros _; discriminate].
    Qed.

    Definition vchk (s : trace C) : bool :=
      forallb (fun i => match nth_error s i with
                        | Some b => enabledb b (state_after (b_loc b) (firstn i s))
                        | None => true
                        end) (seq 0 (length s)).

    Lemma VBuf_of_vchk s : vchk s = true -> forall x, VBuf x (proj x s).
    Proof.
      intros H x. apply VBuf_proj_iff. intros i b Hi Hloc. subst x. apply enabledb_sound.
      unfold vchk in H. rewrite forallb_forall in H.
      assert (Hin : In i (seq 0 (length s))) by (apply in_seq; split; [lia | apply nth_error_Some; congruence]).
      specialize (H i Hin). rewrite Hi in H. exact H.
    Qed.

    Definition pochk (l : list (block C)) : bool :=
      forallb (fun i => forallb (fun j => implb (Nat.leb j i)
         (match nth_error l i, nth_error l j with
          | Some a, Some b => negb (Pos.eqb (b_tid a) (b_tid b)) || Nat.leb (b_handle b) (b_handle a)
          | _, _ => true
          end))
         (seq 0 (length l))) (seq 0 (length l)).

    Lemma respects_po_of_chk l : pochk l = true -> respects l (po (cand_of l)).
    Proof.
      intros Hc a b (Ha & Hb & Ht & Hh). apply In_nth_error in Ha as [i Hi]. apply In_nth_error in Hb as [j Hj].
      destruct (Nat.lt_ge_cases i j) as [Hij | Hji]; [exists i, j; auto |].
      exfalso. unfold pochk in Hc. rewrite forallb_forall in Hc.
      assert (Hli : i < length l) by (apply nth_error_Some; congruence).
      assert (Hlj : j < length l) by (apply nth_error_Some; congruence).
      specialize (Hc i ltac:(apply in_seq; lia)). rewrite forallb_forall in Hc.
      specialize (Hc j ltac:(apply in_seq; lia)). rewrite Hi, Hj in Hc.
      apply Nat.leb_le in Hji. rewrite Hji in Hc. cbn in Hc. rewrite Ht, Pos.eqb_refl in Hc. cbn in Hc.
      apply Nat.leb_le in Hc. lia.
    Qed.

    Context {Cat : Type} (to : Cat -> Cat -> bool) (cat : cell_op C -> Cat).

    (** At every flush, every pending write of the thread with a smaller
        handle than the published one is [I_tab]-independent of it. *)
    Definition tchk (s : trace C) (k : nat) : bool :=
      match nth_error s k with
      | Some (BF t _ x) =>
          match hd_error (proj x (pend t (firstn k s))) with
          | Some m => forallb (fun m' => implb (Nat.ltb (b_handle m') (b_handle m))
                                               (I_tabb to cat (b_inv m') (b_inv m)))
                              (pend t (firstn k s))
          | None => true
          end
      | _ => true
      end.

    Lemma contract_of_tchk s : forallb (tchk s) (seq 0 (length s)) = true -> contract (I_tab to cat) s.
    Proof.
      intros H s1 t h x s2 m Hs Hm m' Hm' Hlt.
      assert (Hk : In (length s1) (seq 0 (length s))) by (apply in_seq; rewrite Hs, length_app; cbn; lia).
      rewrite forallb_forall in H. specialize (H _ Hk). unfold tchk in H.
      assert (E1 : nth_error s (length s1) = Some (BF t h x))
        by (rewrite Hs, nth_error_app2, Nat.sub_diag by lia; reflexivity).
      assert (E2 : firstn (length s1) s = s1)
        by (rewrite Hs, firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r; reflexivity).
      rewrite E1, E2 in H.
      change (match hd_error (proj x (pend t s1)) with
              | Some m => forallb (fun m' => implb (Nat.ltb (b_handle m') (b_handle m))
                                                   (I_tabb to cat (b_inv m') (b_inv m))) (pend t s1)
              | None => true end = true) in H.
      rewrite Hm in H. rewrite forallb_forall in H. specialize (H m' Hm').
      apply Nat.ltb_lt in Hlt. rewrite Hlt in H. cbn [implb] in H.
      apply I_tabb_spec. exact H.
    Qed.

    Lemma V_of_tchk s :
      forallb (tchk s) (seq 0 (length s)) = true -> vchk s = true -> V (I_tab to cat) s.
    Proof. intros H1 H2. split; [apply contract_of_tchk, H1 | apply VBuf_of_vchk, H2]. Qed.

    (** No pair of [pre0 = po \ I_tab] goes backwards in [l]. *)
    Definition pre0chk (l : list (block C)) : bool :=
      forallb (fun i => forallb (fun j => implb (Nat.leb j i)
         (match nth_error l i, nth_error l j with
          | Some a, Some b =>
              negb (Pos.eqb (b_tid a) (b_tid b) && Nat.ltb (b_handle a) (b_handle b)
                    && negb (I_tabb to cat (b_inv a) (b_inv b)))
          | _, _ => true
          end))
         (seq 0 (length l))) (seq 0 (length l)).

    Lemma respects_pre0_of_chk l : pre0chk l = true -> respects l (pre0 (cand_of l) (I_tab to cat)).
    Proof.
      intros Hc a b [(Ha & Hb & Ht & Hh) HnI].
      apply In_nth_error in Ha as [i Hi]. apply In_nth_error in Hb as [j Hj].
      destruct (Nat.lt_ge_cases i j) as [Hij | Hji]; [exists i, j; auto |].
      exfalso. unfold pre0chk in Hc. rewrite forallb_forall in Hc.
      assert (Hli : i < length l) by (apply nth_error_Some; congruence).
      assert (Hlj : j < length l) by (apply nth_error_Some; congruence).
      specialize (Hc i ltac:(apply in_seq; lia)). rewrite forallb_forall in Hc.
      specialize (Hc j ltac:(apply in_seq; lia)). rewrite Hi, Hj in Hc.
      apply Nat.leb_le in Hji. rewrite Hji in Hc. cbn [implb] in Hc.
      rewrite Ht, Pos.eqb_refl in Hc. apply Nat.ltb_lt in Hh. rewrite Hh in Hc.
      destruct (I_tabb to cat (b_inv a) (b_inv b)) eqn:E.
      - apply HnI. apply I_tabb_spec. exact E.
      - discriminate Hc.
    Qed.

    (** The hypothesis of [contract_witness_index]: on every same-thread
        [I_tab]-dependent write pair in issue order, both the handles of
        [s] and [f] increase. *)
    Definition idxchk (s : trace C) (f : nat -> nat) : bool :=
      forallb (fun i => forallb (fun j => implb (Nat.ltb i j)
         (match nth_error s i, nth_error s j with
          | Some a, Some b =>
              implb (is_writeb a && is_writeb b && Pos.eqb (b_tid a) (b_tid b)
                     && negb (I_tabb to cat (b_inv a) (b_inv b)))
                    (Nat.ltb (b_handle a) (b_handle b) && Nat.ltb (f i) (f j))
          | _, _ => true
          end))
         (seq 0 (length s))) (seq 0 (length s)).

    Lemma idx_of_chk s f : idxchk s f = true ->
      forall i j a b, i < j -> nth_error s i = Some a -> nth_error s j = Some b ->
        is_write a -> is_write b -> b_tid a = b_tid b -> ~ I_tab to cat (b_inv a) (b_inv b) ->
        b_handle a < b_handle b /\ f i < f j.
    Proof.
      intros Hc i j a b Hij Ha Hb Wa Wb Ht HnI.
      assert (Hli : i < length s) by (apply nth_error_Some; congruence).
      assert (Hlj : j < length s) by (apply nth_error_Some; congruence).
      unfold idxchk in Hc. rewrite forallb_forall in Hc.
      specialize (Hc i ltac:(apply in_seq; lia)). rewrite forallb_forall in Hc.
      specialize (Hc j ltac:(apply in_seq; lia)). rewrite Ha, Hb in Hc.
      apply Nat.ltb_lt in Hij. rewrite Hij in Hc. cbn [implb] in Hc.
      apply is_writeb_true in Wa, Wb. rewrite Wa, Wb, Ht, Pos.eqb_refl in Hc.
      destruct (I_tabb to cat (b_inv a) (b_inv b)) eqn:E.
      - exfalso. apply HnI. apply I_tabb_spec. exact E.
      - cbn in Hc. apply andb_true_iff in Hc. destruct Hc as [H1 H2].
        apply Nat.ltb_lt in H1, H2. auto.
    Qed.
  End Checkers.

  (** ** Part 6. Ghost-location barriers *)

  Inductive gloc (D : Type) : Type :=
  | Dat (d : D)
  | GBw
  | GBr.
  Arguments Dat {D} d.
  Arguments GBw {D}.
  Arguments GBr {D}.

  Definition gloc_eq_dec {D : Type} (dec : forall x y : D, {x = y} + {x <> y}) :
    forall x y : gloc D, {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  (** The configuration: data locations [D], two ghost locations, and any
      mode assignment (the modes are not consulted by [I_tab]). *)
  Definition tab_cfg {D : Type} (dec : forall x y : D, {x = y} + {x <> y}) (MA : ModeAssign) : Cfg :=
    {| Cell.Loc := gloc D; Cell.Loc_eq_dec := gloc_eq_dec dec; Cell.M := MA |}.

  Section Barriers.
    Context {D : Type} (dec : forall x y : D, {x = y} + {x <> y}) (MA : ModeAssign).
    Context {Cat : Type} (to : Cat -> Cat -> bool).
    Context (catD : cell_op (tab_cfg dec MA) -> Cat) (cWmb cRmb : Cat).

    Abbreviation BC := (tab_cfg dec MA).

    (** Categories: a write of [Bw] is a [wmb] and has category [cWmb]; a
        read of [Br] is an [rmb] and has category [cRmb]; every other
        operation has the category [catD] gives it. *)
    Definition bcat (m : cell_op BC) : Cat :=
      match m with
      | wrt GBw _ _ => cWmb
      | rd GBr _ => cRmb
      | _ => catD m
      end.

    Definition wmb (v : nat) (a : MW MA) : cell_op BC := @wrt BC GBw v a.
    Definition rmb (a : MR MA) : cell_op BC := @rd BC GBr a.

    Lemma bcat_wmb v a : bcat (wmb v a) = cWmb.
    Proof. reflexivity. Qed.

    Lemma bcat_rmb a : bcat (rmb a) = cRmb.
    Proof. reflexivity. Qed.

    Lemma ghost_distinct : @GBw D <> GBr /\ (forall d, @GBw D <> Dat d) /\ (forall d, @GBr D <> Dat d).
    Proof. repeat split; intros; discriminate. Qed.

    Abbreviation Ib := (I_tab to bcat).

    (** [rmb] and [wmb] are unordered, in either order, exactly when the
        table leaves them unordered.  This uses [Bw <> Br]. *)
    Lemma barriers_unordered v a a' :
      (Ib (rmb a') (wmb v a) <-> to cRmb cWmb = false) /\
      (Ib (wmb v a) (rmb a') <-> to cWmb cRmb = false).
    Proof.
      unfold I_tab. cbn. split; split.
      - intros [_ H]. exact H.
      - intros H. split; [discriminate | exact H].
      - intros [_ H]. exact H.
      - intros H. split; [discriminate | exact H].
    Qed.

    (** On a single location a barrier read and a barrier write could
        never be unordered, whatever the table says. *)
    Lemma one_location_orders (l : Loc BC) v a a' :
      ~ Ib (rd l a') (wrt l v a) /\ ~ Ib (wrt l v a) (rd l a').
    Proof. split; apply I_tab_same_loc; reflexivity. Qed.

    (** [ppo_wmb_WW]: for [W → wmb → W'] in program order, with [W] and
        [W'] writes, [to (cat W) Wmb] and [to Wmb (cat W')], both edges are
        in [ppo] for every [pre], and [W] precedes [W'] in [Dc⁺] for every
        witness. *)
    Lemma ppo_wmb_WW (X : cand BC) (pre : relation (block BC)) (W W' : block BC) t h v a :
      po X W (@BW BC t h GBw v a) -> po X (@BW BC t h GBw v a) W' ->
      is_write W -> is_write W' ->
      to (bcat (b_inv W)) cWmb = true -> to cWmb (bcat (b_inv W')) = true ->
      ppo X Ib pre W (@BW BC t h GBw v a) /\ ppo X Ib pre (@BW BC t h GBw v a) W' /\
      (forall w, tc (Dc X Ib w pre) W W').
    Proof.
      intros H1 H2 Hw Hw' Ht1 Ht2.
      assert (P1 : ppo X Ib pre W (@BW BC t h GBw v a)) by (apply ppo_WW_of_to; auto; exact I).
      assert (P2 : ppo X Ib pre (@BW BC t h GBw v a) W') by (apply ppo_WW_of_to; auto; exact I).
      split; [exact P1 | split; [exact P2 |]].
      intros w. eapply t_trans; apply t_step; left; left; left; eassumption.
    Qed.

    (** [ppo_rmb_RR]: for [R → rmb → R'] in program order, with [R] a read,
        [to (cat R) Rmb] and [to Rmb (cat R')], and any [pre ⊇ po \ I_tab]
        (in particular any admissible [pre]), both edges and the composite
        [R → R'] are in [ppo]. *)
    Lemma ppo_rmb_RR (X : cand BC) (pre : relation (block BC)) (R R' : block BC) t h a v :
      rel_incl (pre0 X Ib) pre ->
      po X R (@BR BC t h GBr a v) -> po X (@BR BC t h GBr a v) R' ->
      is_read R ->
      to (bcat (b_inv R)) cRmb = true -> to cRmb (bcat (b_inv R')) = true ->
      ppo X Ib pre R (@BR BC t h GBr a v) /\ ppo X Ib pre (@BR BC t h GBr a v) R' /\ ppo X Ib pre R R'.
    Proof.
      intros Hpre H1 H2 Hr Ht1 Ht2.
      assert (Q1 : pre R (@BR BC t h GBr a v)) by (apply Hpre, pre0_of_to; auto).
      assert (Q2 : pre (@BR BC t h GBr a v) R') by (apply Hpre, pre0_of_to; auto).
      split; [| split]; left; split.
      - exact Hr.
      - apply t_step. exact Q1.
      - exact I.
      - apply t_step. exact Q2.
      - exact Hr.
      - eapply t_trans; apply t_step; eassumption.
    Qed.
  End Barriers.

  (** ** Part 7. Non-vacuity on the abstract table *)

  Module NonVacuity.

    (** Plain reads and writes and the two barriers.  The ordered pairs
        are exactly W→Wmb, Wmb→W, Wmb→Wmb, R→Rmb, Rmb→R and Rmb→Rmb. *)
    Inductive ACat := cR | cW | cRmb | cWmb.

    Definition ato (c d : ACat) : bool :=
      match c, d with
      | cW, cWmb | cWmb, cW | cWmb, cWmb => true
      | cR, cRmb | cRmb, cR | cRmb, cRmb => true
      | _, _ => false
      end.

    (** Unit modes.  [I_tab] does not consult them. *)
    Definition umodes : ModeAssign :=
      {| MW := unit; MR := unit; accW := fun _ => Local; accR := fun _ => Local |}.

    Abbreviation AC := (tab_cfg Nat.eq_dec umodes).

    Definition adata (m : cell_op AC) : ACat :=
      match m with rd _ _ => cR | _ => cW end.

    Definition acat : cell_op AC -> ACat := bcat Nat.eq_dec umodes adata cWmb cRmb.

    Abbreviation AI := (I_tab ato acat).

    Lemma ato_write_symmetric : write_symmetric ato acat.
    Proof.
      intros [x v a | x a | x] [x' v' a' | x' a' | x'] Hw Hw'; cbn in Hw, Hw'; try contradiction.
      destruct x, x'; reflexivity.
    Qed.

    Local Ltac cand_wf :=
      constructor; cbn;
      [ intros b Hb; repeat (destruct Hb as [<- | Hb]; [cbn; tauto |]); destruct Hb
      | repeat constructor; cbn; intros H; repeat (destruct H as [H | H]; [discriminate H |]); exact H
      | intros a b (Ha & Hb & Ht & _); auto
      | intros a (_ & _ & _ & H); lia
      | intros a b c (Ha & Hb & Ht1 & H1) (_ & Hc & Ht2 & H2); repeat split; auto; [congruence | lia]
      | intros a b Ha Hb Ht Hne;
        assert (Hh : b_handle a <> b_handle b)
          by (intros Heq; repeat (destruct Ha as [<- | Ha]; [ repeat (destruct Hb as [<- | Hb];
                [ cbn in Ht, Heq; first [discriminate Ht | discriminate Heq | apply Hne; reflexivity] |]);
                destruct Hb |]); destruct Ha);
        destruct (lt_dec (b_handle a) (b_handle b)) as [Hlt | Hge];
          [left; repeat split; auto | right; repeat split; auto; lia]
      | intros a b (_ & _ & _ & H) _ _; exact H ].

    (** *** MP+wmb/rmb: forbidden *)

    (** T1: W x 1; wmb; W y 1  ‖  T2: R y = 1; rmb; R x = 0, with
        x = Dat 0, y = Dat 1; handles follow program order. *)
    Definition mp_ops : list (block AC) :=
      [ @BW AC 1%positive 0 (Dat 0) 1 tt;   (* T1: W x 1 *)
        @BW AC 1%positive 1 GBw 0 tt;       (* T1: wmb *)
        @BW AC 1%positive 2 (Dat 1) 1 tt;   (* T1: W y 1 *)
        @BR AC 2%positive 0 (Dat 1) tt 1;   (* T2: R y = 1 *)
        @BR AC 2%positive 1 GBr tt 0;       (* T2: rmb *)
        @BR AC 2%positive 2 (Dat 0) tt 0 ]. (* T2: R x = 0 *)

    Definition mp_cand : cand AC := cand_of mp_ops.

    Lemma mp_cand_wf : wf_cand mp_cand.
    Proof. cand_wf. Qed.

    Local Ltac po_tac := split; [cbn; tauto | split; [cbn; tauto | split; [reflexivity | cbn; lia]]].

    (** Declarative side: under every admissible [pre] and every
        well-formed witness, (D2) fails.  The [Dc] cycle is
        W x 1 →ppo⁺ W y 1 (through wmb, [ppo_wmb_WW]) →rfe R y = 1
        →ppo R x = 0 (through rmb, [ppo_rmb_RR]) →rb W x 1. *)
    Theorem mp_wmb_rmb_inconsistent (pre : relation (block AC)) (w : witness AC) :
      admissible mp_cand AI pre -> wf_witness mp_cand w -> ~ D2 mp_cand AI w pre.
    Proof.
      intros Hadm Hw HD2.
      assert (Hsrc : ~ ~ exists u, rf w u (@BR AC 2%positive 0 (Dat 1) tt 1)).
      { intros Hn.
        assert (H0 : b_val (@BR AC 2%positive 0 (Dat 1) tt 1) = 0).
        { apply (rf_init Hw); [cbn; tauto | exact I |]. intros u Hu. apply Hn. eauto. }
        discriminate H0. }
      apply Hsrc. intros (u & Hu).
      destruct (rf_dom Hw _ _ Hu) as (Hin & _ & Hwu & _ & Hloc & Hval).
      assert (Hu1 : u = @BW AC 1%positive 2 (Dat 1) 1 tt).
      { cbn in Hin. repeat (destruct Hin as [<- | Hin];
          [cbn in Hwu, Hloc, Hval; first [reflexivity | discriminate Hloc | discriminate Hval | contradiction Hwu] |]).
        destruct Hin. }
      subst u.
      destruct (ppo_wmb_WW Nat.eq_dec umodes ato adata cWmb cRmb mp_cand pre
                  (@BW AC 1%positive 0 (Dat 0) 1 tt) (@BW AC 1%positive 2 (Dat 1) 1 tt) 1%positive 1 0 tt)
        as (_ & _ & Hww); [po_tac | po_tac | exact I | exact I | reflexivity | reflexivity |].
      destruct (ppo_rmb_RR Nat.eq_dec umodes ato adata cWmb cRmb mp_cand pre
                  (@BR AC 2%positive 0 (Dat 1) tt 1) (@BR AC 2%positive 2 (Dat 0) tt 0) 2%positive 1 tt 0)
        as (_ & _ & Hrr); [exact (proj1 Hadm) | po_tac | po_tac | exact I | reflexivity | reflexivity |].
      apply (HD2 (@BW AC 1%positive 0 (Dat 0) 1 tt)).
      eapply t_trans; [exact (Hww w) |].
      eapply t_trans; [apply t_step; left; left; right; split; [exact Hu | discriminate] |].
      eapply t_trans; [apply t_step; left; left; left; exact Hrr |].
      apply t_step. right.
      split; [cbn; tauto | split; [cbn; tauto | split; [exact I | split; [exact I | split; [reflexivity |]]]]].
      intros u0 Hu0. exfalso.
      destruct (rf_dom Hw _ _ Hu0) as (Hin0 & _ & Hw0 & _ & Hl0 & Hv0).
      cbn in Hin0. repeat (destruct Hin0 as [<- | Hin0];
        [cbn in Hw0, Hl0, Hv0; first [discriminate Hl0 | discriminate Hv0 | contradiction Hw0] |]).
      destruct Hin0.
    Qed.

    (** The buffered memory itself: no history of [ν_{I_tab}] presents the
        MP candidate and respects an admissible [pre].  Proved through the
        declarative characterization ([declarative_tab]). *)
    Theorem mp_wmb_rmb_forbidden (pre : relation (block AC)) :
      admissible mp_cand AI pre -> ~ exists s, nu AI s /\ presents s mp_cand /\ respects s pre.
    Proof.
      intros Hadm Hs.
      apply (declarative_tab ato acat mp_cand mp_cand_wf pre Hadm) in Hs.
      destruct Hs as (w & Hw & _ & HD2).
      exact (mp_wmb_rmb_inconsistent pre w Hadm Hw HD2).
    Qed.

    (** In particular for the least admissible [pre], [po \ I_tab]: the
        issue order is constrained only by the table. *)
    Corollary mp_wmb_rmb_forbidden_pre0 :
      ~ exists s, nu AI s /\ presents s mp_cand /\ respects s (pre0 mp_cand AI).
    Proof. apply mp_wmb_rmb_forbidden, pre0_admissible, mp_cand_wf. Qed.

    (** Without "respects [pre]" the outcome is in [ν]: [ν] is a set of
        histories and imposes no issue order.  Here T2 issues R x = 0
        before its R y = 1 and its rmb, against [po \ I_tab]. *)
    Definition mp_unordered_trace : trace AC :=
      [ @BR AC 2%positive 2 (Dat 0) tt 0;
        @BW AC 1%positive 0 (Dat 0) 1 tt; @BF AC 1%positive 10 (Dat 0);
        @BW AC 1%positive 1 GBw 0 tt;     @BF AC 1%positive 11 GBw;
        @BW AC 1%positive 2 (Dat 1) 1 tt; @BF AC 1%positive 12 (Dat 1);
        @BR AC 2%positive 0 (Dat 1) tt 1;
        @BR AC 2%positive 1 GBr tt 0 ].

    Lemma mp_wmb_rmb_nu_unordered : exists s, nu AI s /\ presents s mp_cand.
    Proof.
      exists (hide mp_unordered_trace). split.
      - exists mp_unordered_trace. split; [apply V_of_tchk; exact eq_refl | reflexivity].
      - exact (Permutation_cons_append _ _).
    Qed.

    (** Positive control (review item m-38): the same program with the
        outcome R x = 1 is allowed, with a history that respects all of
        program order (hence [po \ I_tab]).  So [mp_wmb_rmb_forbidden] comes
        from the outcome R x = 0, not from the ghost encoding. *)
    Definition mp1_ops : list (block AC) :=
      [ @BW AC 1%positive 0 (Dat 0) 1 tt;   (* T1: W x 1 *)
        @BW AC 1%positive 1 GBw 0 tt;       (* T1: wmb *)
        @BW AC 1%positive 2 (Dat 1) 1 tt;   (* T1: W y 1 *)
        @BR AC 2%positive 0 (Dat 1) tt 1;   (* T2: R y = 1 *)
        @BR AC 2%positive 1 GBr tt 0;       (* T2: rmb *)
        @BR AC 2%positive 2 (Dat 0) tt 1 ]. (* T2: R x = 1 *)

    Definition mp1_trace : trace AC :=
      [ @BW AC 1%positive 0 (Dat 0) 1 tt; @BF AC 1%positive 10 (Dat 0);
        @BW AC 1%positive 1 GBw 0 tt;     @BF AC 1%positive 11 GBw;
        @BW AC 1%positive 2 (Dat 1) 1 tt; @BF AC 1%positive 12 (Dat 1);
        @BR AC 2%positive 0 (Dat 1) tt 1;
        @BR AC 2%positive 1 GBr tt 0;
        @BR AC 2%positive 2 (Dat 0) tt 1 ].

    Theorem mp_wmb_rmb_allowed_outcome :
      nu AI mp1_ops /\ presents mp1_ops (cand_of mp1_ops) /\
      respects mp1_ops (pre0 (cand_of mp1_ops) AI) /\ respects mp1_ops (po (cand_of mp1_ops)).
    Proof.
      split; [| split; [| split]].
      - exists mp1_trace. split; [apply V_of_tchk; exact eq_refl | reflexivity].
      - apply Permutation_refl.
      - apply respects_pre0_of_chk. exact eq_refl.
      - apply respects_po_of_chk. exact eq_refl.
    Qed.

    Lemma mp1_cand_wf : wf_cand (cand_of mp1_ops).
    Proof. cand_wf. Qed.

    (** *** Controls: each barrier is needed *)

    (** Without rmb, T2's reads are table-unordered, and [R x = 0] may be
        issued first. *)
    Definition mp_normb_hist : list (block AC) :=
      [ @BR AC 2%positive 1 (Dat 0) tt 0;   (* T2: R x = 0 (program-order second) *)
        @BW AC 1%positive 0 (Dat 0) 1 tt;   (* T1: W x 1 *)
        @BW AC 1%positive 1 GBw 0 tt;       (* T1: wmb *)
        @BW AC 1%positive 2 (Dat 1) 1 tt;   (* T1: W y 1 *)
        @BR AC 2%positive 0 (Dat 1) tt 1 ]. (* T2: R y = 1 (program-order first) *)

    Definition mp_normb_trace : trace AC :=
      [ @BR AC 2%positive 1 (Dat 0) tt 0;
        @BW AC 1%positive 0 (Dat 0) 1 tt; @BF AC 1%positive 10 (Dat 0);
        @BW AC 1%positive 1 GBw 0 tt;     @BF AC 1%positive 11 GBw;
        @BW AC 1%positive 2 (Dat 1) 1 tt; @BF AC 1%positive 12 (Dat 1);
        @BR AC 2%positive 0 (Dat 1) tt 1 ].

    Theorem mp_no_rmb_allowed :
      nu AI mp_normb_hist /\ presents mp_normb_hist (cand_of mp_normb_hist) /\
      respects mp_normb_hist (pre0 (cand_of mp_normb_hist) AI).
    Proof.
      split; [| split].
      - exists mp_normb_trace. split; [apply V_of_tchk; exact eq_refl | reflexivity].
      - apply Permutation_refl.
      - apply respects_pre0_of_chk. exact eq_refl.
    Qed.

    (** Without wmb, T1's writes are table-unordered, and W y 1 may be
        published first; the history respects all of program order. *)
    Definition mp_nowmb_hist : list (block AC) :=
      [ @BW AC 1%positive 0 (Dat 0) 1 tt;   (* T1: W x 1 *)
        @BW AC 1%positive 1 (Dat 1) 1 tt;   (* T1: W y 1 *)
        @BR AC 2%positive 0 (Dat 1) tt 1;   (* T2: R y = 1 *)
        @BR AC 2%positive 1 GBr tt 0;       (* T2: rmb *)
        @BR AC 2%positive 2 (Dat 0) tt 0 ]. (* T2: R x = 0 *)

    Definition mp_nowmb_trace : trace AC :=
      [ @BW AC 1%positive 0 (Dat 0) 1 tt;
        @BW AC 1%positive 1 (Dat 1) 1 tt; @BF AC 1%positive 10 (Dat 1);
        @BR AC 2%positive 0 (Dat 1) tt 1;
        @BR AC 2%positive 1 GBr tt 0;
        @BR AC 2%positive 2 (Dat 0) tt 0; @BF AC 1%positive 11 (Dat 0) ].

    Theorem mp_no_wmb_allowed :
      nu AI mp_nowmb_hist /\ presents mp_nowmb_hist (cand_of mp_nowmb_hist) /\
      respects mp_nowmb_hist (po (cand_of mp_nowmb_hist)).
    Proof.
      split; [| split].
      - exists mp_nowmb_trace. split; [apply V_of_tchk; exact eq_refl | reflexivity].
      - apply Permutation_refl.
      - apply respects_po_of_chk. exact eq_refl.
    Qed.

    (** *** SB+rfi (Reviewer A's test): allowed *)

    (** T1: W x 1; R x = 1; R y = 0  ‖  T2: W y 1; R y = 1; R x = 0, no
        barriers.  Both own reads are forwarded; both flushes come last. *)
    Definition sb_hist : list (block AC) :=
      [ @BW AC 1%positive 0 (Dat 0) 1 tt;   (* T1: W x 1 *)
        @BR AC 1%positive 1 (Dat 0) tt 1;   (* T1: R x = 1, forwarded *)
        @BR AC 1%positive 2 (Dat 1) tt 0;   (* T1: R y = 0, from memory *)
        @BW AC 2%positive 0 (Dat 1) 1 tt;   (* T2: W y 1 *)
        @BR AC 2%positive 1 (Dat 1) tt 1;   (* T2: R y = 1, forwarded *)
        @BR AC 2%positive 2 (Dat 0) tt 0 ]. (* T2: R x = 0, from memory *)

    Definition sb_trace : trace AC :=
      sb_hist ++ [@BF AC 1%positive 10 (Dat 0); @BF AC 2%positive 11 (Dat 1)].

    Theorem sbrfi_tab_V : V AI sb_trace.
    Proof. apply V_of_tchk; exact eq_refl. Qed.

    Theorem sbrfi_tab_nu : nu AI sb_hist.
    Proof. exists sb_trace. split; [exact sbrfi_tab_V | reflexivity]. Qed.

    (** The history is issued in full program order. *)
    Theorem sbrfi_tab_po :
      nu AI sb_hist /\ presents sb_hist (cand_of sb_hist) /\ respects sb_hist (po (cand_of sb_hist)).
    Proof.
      split; [exact sbrfi_tab_nu | split; [apply Permutation_refl |]].
      apply respects_po_of_chk. exact eq_refl.
    Qed.

    Lemma sb_cand_wf : wf_cand (cand_of sb_hist).
    Proof. cand_wf. Qed.

    (** Declaratively: (D1) and (D2) hold with [pre] the whole program
        order. *)
    Theorem sbrfi_tab_consistent :
      exists w, wf_witness (cand_of sb_hist) w /\ consistent (cand_of sb_hist) AI w (po (cand_of sb_hist)).
    Proof.
      apply (proj2 (declarative_tab ato acat _ sb_cand_wf _ (po_admissible _ sb_cand_wf _))).
      exists sb_hist. exact sbrfi_tab_po.
    Qed.

    (** *** The symmetry assumption of [contract_handle_invariant] is needed *)

    (** An asymmetric table: every operation is ordered before a write of
        [x] (a "release" write), and nothing else is ordered. *)
    Definition rcat (m : cell_op AC) : bool :=
      match m with wrt (Dat 0) _ _ => true | _ => false end.

    Definition rto (c d : bool) : bool := d.

    (** T1 issues W x (release) then W y, and publishes W x first. *)
    Definition asym_s : trace AC :=
      [ @BW AC 1%positive 0 (Dat 0) 1 tt; @BW AC 1%positive 0 (Dat 1) 1 tt; @BF AC 1%positive 0 (Dat 0) ].

    Definition f_id (i : nat) : nat := i.
    Definition f_swap (i : nat) : nat := match i with 0 => 1 | 1 => 0 | n => n end.

    (** Both handle assignments satisfy the hypothesis of
        [contract_handle_invariant] (vacuously: the only same-thread write
        pair in issue order is [I_tab]-independent), [to] is not symmetric
        on writes, and the two contracts differ. *)
    Theorem handle_invariance_needs_symmetry :
      ~ write_symmetric rto rcat /\
      (forall i j a b, i < j -> nth_error asym_s i = Some a -> nth_error asym_s j = Some b ->
         is_write a -> is_write b -> b_tid a = b_tid b -> ~ I_tab rto rcat (b_inv a) (b_inv b) ->
         Nat.compare (f_id i) (f_id j) = Nat.compare (f_swap i) (f_swap j)) /\
      contract (I_tab rto rcat) (relabel f_id asym_s) /\
      ~ contract (I_tab rto rcat) (relabel f_swap asym_s).
    Proof.
      split; [| split; [| split]].
      - intros Hs. specialize (Hs (@wrt AC (Dat 0) 1 tt) (@wrt AC (Dat 1) 1 tt) I I). discriminate Hs.
      - intros i j a b Hij Ha Hb Wa Wb Ht HnI.
        assert (Hj3 : j < 3) by (change 3 with (length asym_s); apply nth_error_Some; congruence).
        destruct i as [| [| i]]; destruct j as [| [| [| j]]]; try lia; cbn in Ha, Hb;
          injection Ha as <-; injection Hb as <-; cbn in Wa, Wb; try contradiction.
        exfalso. apply HnI. split; [discriminate | reflexivity].
      - apply contract_of_tchk. exact eq_refl.
      - intros Hc.
        specialize (Hc [@BW AC 1%positive 1 (Dat 0) 1 tt; @BW AC 1%positive 0 (Dat 1) 1 tt]
                       1%positive 2 (Dat 0) [] (@BW AC 1%positive 1 (Dat 0) 1 tt) eq_refl eq_refl
                       (@BW AC 1%positive 0 (Dat 1) 1 tt) ltac:(cbn; tauto) ltac:(cbn; lia)).
        destruct Hc as [_ H]. discriminate H.
    Qed.

    (** *** Agreement must be on [Nat.compare], ties included *)

    (** T1 issues W x then wmb (a dependent pair under [ato]) and
        publishes W x.  [f_tie] gives both handle 5; [f_swap] gives W x
        handle 1 and wmb handle 0.  The two agree on [<] for the pair
        (neither puts W x strictly first), the table is symmetric on writes,
        and still the contracts differ: under [f_swap] the pending wmb has
        the smaller handle and blocks the flush of W x. *)
    Definition tie_s : trace AC :=
      [ @BW AC 1%positive 0 (Dat 0) 1 tt; @BW AC 1%positive 0 GBw 0 tt; @BF AC 1%positive 0 (Dat 0) ].

    Definition f_tie (i : nat) : nat := 5.

    Theorem handle_invariance_needs_compare :
      write_symmetric ato acat /\
      (forall i j a b, i < j -> nth_error tie_s i = Some a -> nth_error tie_s j = Some b ->
         is_write a -> is_write b -> b_tid a = b_tid b -> ~ AI (b_inv a) (b_inv b) ->
         (f_tie i < f_tie j <-> f_swap i < f_swap j)) /\
      Nat.compare (f_tie 0) (f_tie 1) <> Nat.compare (f_swap 0) (f_swap 1) /\
      contract AI (relabel f_tie tie_s) /\
      ~ contract AI (relabel f_swap tie_s).
    Proof.
      split; [exact ato_write_symmetric | split; [| split; [| split]]].
      - intros i j a b Hij Ha Hb Wa Wb Ht HnI.
        assert (Hj3 : j < 3) by (change 3 with (length tie_s); apply nth_error_Some; congruence).
        destruct i as [| [| i]]; destruct j as [| [| [| j]]]; try lia; cbn in Ha, Hb;
          injection Ha as <-; injection Hb as <-; cbn in Wa, Wb; try contradiction.
        unfold f_tie. cbn. split; intros; lia.
      - unfold f_tie. cbn. discriminate.
      - apply contract_of_tchk. exact eq_refl.
      - intros Hc.
        specialize (Hc [@BW AC 1%positive 1 (Dat 0) 1 tt; @BW AC 1%positive 0 GBw 0 tt]
                       1%positive 2 (Dat 0) [] (@BW AC 1%positive 1 (Dat 0) 1 tt) eq_refl eq_refl
                       (@BW AC 1%positive 0 GBw 0 tt) ltac:(cbn; tauto) ltac:(cbn; lia)).
        destruct Hc as [_ H]. discriminate H.
    Qed.

    (** *** A non-trivial instance of [contract_witness_index]

        In [mp_normb_trace], T1's pairs (W x 1, wmb) and (wmb, W y 1) are
        dependent and (W x 1, W y 1) is not.  Handles (program order) and
        positions (issue order) both increase on the dependent pairs, so
        the contract with positions as handles follows from the contract of
        the trace by [contract_witness_index] (not by recomputation). *)
    Lemma mp_normb_index_hyp :
      forall i j a b, i < j -> nth_error mp_normb_trace i = Some a -> nth_error mp_normb_trace j = Some b ->
        is_write a -> is_write b -> b_tid a = b_tid b -> ~ AI (b_inv a) (b_inv b) ->
        b_handle a < b_handle b /\ (fun k : nat => k) i < (fun k : nat => k) j.
    Proof. apply idx_of_chk. exact eq_refl. Qed.

    Theorem mp_normb_witness_index : contract AI (relabel (fun k => k) mp_normb_trace).
    Proof.
      apply (proj1 (contract_witness_index ato acat ato_write_symmetric mp_normb_trace (fun k => k)
                      mp_normb_index_hyp)).
      apply contract_of_tchk. exact eq_refl.
    Qed.

  End NonVacuity.

End TableBarrier.
