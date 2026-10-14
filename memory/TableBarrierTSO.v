(** * TableBarrierTSO: x86-TSO machine traces, with ghost barriers, are in the table-induced buffered memory

    Addendum to [memory/TableBarrier.v] (task F-1.2; alternative 1 of the
    F-1 review, .rocq-review/latest-review.md).  It grounds the cell level
    of the table-induced memory [V_{I_tab}] in the x86-TSO machine of
    [memory/TSO.v]: the read/write fragment of Owens, Sarkar and Sewell,
    without locked instructions or fences.  It imports only memory/ and
    models/RelaxedSignature.v, and changes no existing file.

    Results.
    - Part 1.  [contract_mono], [V_mono], [nu_mono]: the contract, [V] and
      [ν] are monotone in the semi-independence relation.
    - Part 2.  [contract_TSO_strongest]: the TSO contract implies the
      contract of every relation [J].  [mode_indep] of [TSO_cfg] relates no
      two writes ([TSO.TSO_no_WW]), so at a flush it forbids every pending
      same-thread write with a smaller handle: publication is FIFO in
      handle order.  [J]'s condition is then vacuous.  This is not an
      instance of [contract_mono], because [mode_indep] need not be
      contained in [J].
    - Part 3.  [tab_cfg_TSO]: [tab_cfg decD TSO_modes] is
      [TSO_cfg (gloc_eq_dec decD)], by [reflexivity].
      [x86_trace_V_tab]: for every table [to] and categorization [cat],
      every trace [l] of the x86-TSO machine over the locations [gloc D]
      (data and ghost) is [TSO.erase s] for some [s] in [V_{I_tab}].  The
      witness issues each thread's writes in increasing handle order.
      [x86_history_nu_tab]: the flush-free history [hide s] is in
      [ν_{I_tab}].  The proof is [TSO.tso_traces] (the machine traces are
      the erasures of [V↑_TSO]), then [contract_TSO_strongest].
      [x86_trace_V_tab_index]: the same with witness indices as handles
      (position [i] gets handle [i]), for every table and without
      [write_symmetric].  The machine publishes each thread's writes in
      issue order, and the [V↑_TSO] witness issues them in handle order,
      so handles and positions compare alike ([contract_handle_invariant_gen]
      with [I = mode_indep]).
    - Part 4: the ghost barriers on the machine.
      [Tr_insert_rmb]: a load [ER t GBr 0] can be inserted at any point of a
      machine trace before which no store to [GBr] occurs.
      [Tr_insert_wmb]: a store [EW t GBw v] can be inserted after [l1], and
      its flush [EF t GBw] after [l2], if [l2] contains exactly as many
      flushes of [t] as [t] has pending stores after [l1] (stores minus
      flushes of [t] in [l1]), and no load of [GBw] follows the insertion
      point.  The ghost entry is then at the head of [t]'s buffer, where
      x86's FIFO buffer puts it.
      [Tr_insert_wmb_pending]: if fewer flushes of [t] follow, the store
      alone can be inserted; it stays pending.
      [Tr_insert_wmb_exists]: one of the two always applies.
      [no_read_GBw_rmb] and [no_write_GBr_wmb]: an inserted ghost keeps the
      hypotheses of further insertions, so any number of barriers can be
      added one at a time.
    - Part 5.  [x86_wmb_V_tab] and [x86_rmb_V_tab]: Parts 3 and 4
      composed.  A machine trace with a ghost barrier inserted is the
      erasure of a trace of [V_{I_tab}] with position handles, for every
      table.

    What this gives.  Take an x86 execution of a program in which rmb and
    wmb are compiler barriers (no instruction), as a trace of the machine
    over [gloc D] that touches only data locations.  Insert a ghost load of
    [GBr] at each rmb, and a ghost store to [GBw] at each wmb, with its
    flush where Part 4 places it.  The result is again a machine trace, and
    hence, for every table, the erasure of a trace of [V_{I_tab}] whose
    handles are witness indices.  This is x86 grounding of the cell level
    of the table-induced memory.  It goes through the operational
    equivalence [TSO.tso_traces], not through the declarative
    characterization, so it does not need the lemma about [mo] at [Bw]
    (review item m-35).

    What this does not give.
    - Program points.  memory/ has no program semantics, so placing the
      ghosts at the program points of rmb and wmb is not formalized; the
      lemmas take the insertion points as given.  The execution is taken
      directly as a machine trace over [gloc D]; a renaming lemma from the
      machine over [D] is not stated.
    - RMW.  The machine of [TSO.v] has no locked instructions, so the
      TicketLock's RMWs are not covered (task F-2 and the hybrid's atomic
      clause).
    - ARMv8 (task G-3).
    - Relaxed linearizability.  There is no link from [V_{I_tab}] or
      [ν_{I_tab}] to [rel_lin] or to the module semantics (task G-1).
    - The converse.  Only "x86 traces ⊆ V_{I_tab}" is shown.  [V_{I_tab}]
      is in general much larger: for example
      [TableBarrier.NonVacuity.mp_no_wmb_allowed] publishes W y 1 before
      W x 1, which x86 never does.

    Assumptions.  Every result is closed under the global context.
    [TSO.tso_traces] is closed as well. *)

From Stdlib Require Import List Arith PArith Bool micromega.Lia.
Require Import models.RelaxedSignature.
Require Import memory.Prelude.
Require Import memory.Cell.
Require Import memory.TSO.
Require Import memory.TableBarrier.

Import ListNotations.

Module TableBarrierTSO.
  Import RelaxedSig Cell Cell.Instances TableBarrier.

  (** ** Part 1. The contract, [V] and [ν] are monotone in [I] *)

  Section Mono.
    Context {C : Cfg}.

    Lemma contract_mono (I J : cell_op C -> cell_op C -> Prop) (s : trace C) :
      (forall m m', I m m' -> J m m') -> contract I s -> contract J s.
    Proof. intros HIJ Hc p t h x q m Hs Hm m' Hm' Hlt. apply HIJ. eapply Hc; eauto. Qed.

    Lemma V_mono (I J : cell_op C -> cell_op C -> Prop) (s : trace C) :
      (forall m m', I m m' -> J m m') -> V I s -> V J s.
    Proof. intros HIJ [Hc Hb]. split; [eapply contract_mono; eauto | exact Hb]. Qed.

    Lemma nu_mono (I J : cell_op C -> cell_op C -> Prop) (s : trace C) :
      (forall m m', I m m' -> J m m') -> nu I s -> nu J s.
    Proof. intros HIJ (s' & HV & Hh). exists s'. split; [eapply V_mono; eauto | exact Hh]. Qed.
  End Mono.

  (** ** Part 2. The TSO contract implies every contract *)

  Section Strongest.
    Context {Loc : Type} (dec : forall x y : Loc, {x = y} + {x <> y}).

    (** [TSO.I] relates no two writes ([TSO.TSO_no_WW]), so at every flush
        the TSO contract forbids any pending same-thread write with a
        smaller handle; the condition of any other contract is then
        vacuous. *)
    Lemma contract_TSO_strongest (J : cell_op (TSO_cfg dec) -> cell_op (TSO_cfg dec) -> Prop)
        (s : trace (TSO_cfg dec)) :
      contract (mode_indep (C := TSO_cfg dec)) s -> contract J s.
    Proof.
      intros Hc p t h x q m Hs Hm m' Hm' Hlt. exfalso.
      pose proof (Hc p t h x q m Hs Hm m' Hm' Hlt) as HI.
      assert (Hin : In m (pend t p)).
      { destruct (proj x (pend t p)) as [| b l] eqn:E; cbn in Hm; [discriminate Hm |].
        injection Hm as ->. assert (H : In m (proj x (pend t p))) by (rewrite E; left; reflexivity).
        unfold proj in H. apply filter_In in H. tauto. }
      apply pend_In in Hin. apply pend_In in Hm'.
      exact (TSO.TSO_no_WW Loc dec m' m (proj1 (proj2 Hm')) (proj1 (proj2 Hin)) HI).
    Qed.

    Lemma mode_indep_TSO_dec (m m' : cell_op (TSO_cfg dec)) : mode_indep m m' \/ ~ mode_indep m m'.
    Proof.
      destruct m as [x v a | x a | x]; destruct m' as [y v' a' | y a' | y];
        try (right; intros H; apply TSO_indep_iff in H; destruct H as (_ & H1 & H2);
             cbn in H1, H2; contradiction).
      destruct (dec x y) as [-> | Hne].
      - right. intros H. apply TSO_indep_iff in H. destruct H as (H & _). apply H. reflexivity.
      - left. apply TSO_indep_iff. split; [exact Hne | split; exact I].
    Qed.
  End Strongest.

  (** ** Part 3. x86-TSO traces over data and ghost locations are in [V_{I_tab}] *)

  Section X86.
    Context {D : Type} (decD : forall x y : D, {x = y} + {x <> y}).

    Abbreviation GL := (gloc D).
    Abbreviation gdec := (gloc_eq_dec decD).

    (** The table configuration with TSO modes is the TSO configuration on
        [gloc D], definitionally. *)
    Lemma tab_cfg_TSO : tab_cfg decD TSO_modes = TSO_cfg gdec.
    Proof. reflexivity. Qed.

    Lemma erase_relabel (f : nat -> nat) (s : trace (TSO_cfg gdec)) :
      TSO.erase GL gdec (relabel f s) = TSO.erase GL gdec s.
    Proof.
      unfold TSO.erase, relabel.
      transitivity (map (TSO.erase_block GL gdec) (map snd (tagf 0 s))).
      - rewrite !map_map. apply map_ext. intros [i b]. destruct b; reflexivity.
      - rewrite map_snd_tagf. reflexivity.
    Qed.

    Context {Cat : Type} (to : Cat -> Cat -> bool) (cat : cell_op (tab_cfg decD TSO_modes) -> Cat).

    (** Every trace of the x86-TSO machine (read/write fragment, Owens,
        Sarkar and Sewell; [TSO.Tr]) over the locations [gloc D] is the
        handle erasure of a trace of [V_{I_tab}], for every table [to] and
        categorization [cat].  The witness issues the writes of each thread
        in increasing handle order. *)
    Theorem x86_trace_V_tab (l : list (TSO.elabel GL)) :
      TSO.Tr GL gdec l ->
      exists s : trace (tab_cfg decD TSO_modes),
        V (I_tab to cat) s /\ TSO.erase GL gdec s = l /\ TSO.wr_handle_order GL gdec s.
    Proof.
      intros Hl. apply (proj2 (TSO.tso_traces GL gdec l)) in Hl.
      destruct Hl as (s & [[Hc Hb] Hho] & He).
      exists s. split; [| split; assumption].
      split; [| exact Hb]. exact (contract_TSO_strongest gdec (I_tab to cat) s Hc).
    Qed.

    Corollary x86_history_nu_tab (l : list (TSO.elabel GL)) :
      TSO.Tr GL gdec l ->
      exists s : trace (tab_cfg decD TSO_modes),
        TSO.erase GL gdec s = l /\ nu (I_tab to cat) (hide s).
    Proof.
      intros Hl. destruct (x86_trace_V_tab l Hl) as (s & HV & He & _).
      exists s. split; [exact He | exists s; split; [exact HV | reflexivity]].
    Qed.

    (** The same with witness indices as handles: the block at position [i]
        gets handle [i].  On this route no symmetry of [to] is needed,
        because the x86 machine publishes each thread's writes in issue
        order (the TSO contract is FIFO). *)
    Theorem x86_trace_V_tab_index (l : list (TSO.elabel GL)) :
      TSO.Tr GL gdec l ->
      exists s : trace (tab_cfg decD TSO_modes),
        V (I_tab to cat) (relabel (fun i => i) s) /\
        TSO.erase GL gdec (relabel (fun i => i) s) = l.
    Proof.
      intros Hl. apply (proj2 (TSO.tso_traces GL gdec l)) in Hl.
      destruct Hl as (s & [[Hc Hb] Hho] & He).
      exists s. split; [| rewrite erase_relabel; exact He].
      (* The handles of [s] increase along issue order on every same-thread
         write pair ([wr_handle_order]), so they compare like positions. *)
      assert (Hag : forall i j (a b : block (TSO_cfg gdec)), i <> j ->
                nth_error s i = Some a -> nth_error s j = Some b ->
                is_write a -> is_write b -> b_tid a = b_tid b ->
                ~ mode_indep (b_inv a) (b_inv b) ->
                Nat.compare (handles s i) (handles s j) = Nat.compare i j).
      { intros i j a b Hij Ha Hb' Wa Wb Ht _. unfold handles. rewrite Ha, Hb'.
        destruct (lt_eq_lt_dec i j) as [[Hlt | Heq] | Hgt]; [| contradiction |].
        - pose proof (Hho i j a b Hlt Ha Hb' Wa Wb Ht) as H.
          apply Nat.compare_lt_iff in H, Hlt. congruence.
        - pose proof (Hho j i b a Hgt Hb' Ha Wb Wa (eq_sym Ht)) as H.
          apply Nat.compare_gt_iff in Hgt. rewrite Hgt. apply Nat.compare_gt_iff. exact H. }
      pose proof (proj1 (contract_handle_invariant_gen (mode_indep (C := TSO_cfg gdec))
                           (mode_indep_TSO_dec gdec) s (handles s) (fun i => i) Hag)) as Hinv.
      rewrite relabel_handles in Hinv.
      pose proof (Hinv Hc) as Hc'.
      split.
      - exact (contract_TSO_strongest gdec (I_tab to cat) _ Hc').
      - intros x. apply (proj2 (VBuf_relabel (fun i => i) s x)). exact (Hb x).
    Qed.
  End X86.

  (** ** Part 4. Inserting the ghost barriers into an x86-TSO machine trace *)

  Section Insert.
    Context {D : Type} (decD : forall x y : D, {x = y} + {x <> y}).

    Abbreviation GL := (gloc D).
    Abbreviation gdec := (gloc_eq_dec decD).
    Abbreviation tstate := (TSO.tstate GL).
    Abbreviation tm := (TSO.tm GL).
    Abbreviation tB := (TSO.tB GL).
    Abbreviation tstep := (TSO.tstep GL gdec).
    Abbreviation tpath := (TSO.tpath GL gdec).
    Abbreviation last_entry := (TSO.last_entry GL gdec).
    Abbreviation Tr := (TSO.Tr GL gdec).
    Abbreviation elabel := (TSO.elabel GL).

    (** Counting the writes and the flushes of a thread. *)
    Fixpoint nwrite (t : tid) (l : list elabel) : nat :=
      match l with
      | [] => 0
      | TSO.EW _ u _ _ :: l' => (if Pos.eq_dec u t then 1 else 0) + nwrite t l'
      | _ :: l' => nwrite t l'
      end.

    Fixpoint nflush (t : tid) (l : list elabel) : nat :=
      match l with
      | [] => 0
      | TSO.EF _ u _ :: l' => (if Pos.eq_dec u t then 1 else 0) + nflush t l'
      | _ :: l' => nflush t l'
      end.

    Lemma nflush_app t l1 l2 : nflush t (l1 ++ l2) = nflush t l1 + nflush t l2.
    Proof. induction l1 as [| [u x w | u x w | u x] l1 IH]; cbn; try rewrite IH; lia. Qed.

    (** No read of location [y], no write of location [y]. *)
    Definition no_read (y : GL) (l : list elabel) : Prop :=
      forall u x w, In (TSO.ER GL u x w) l -> x <> y.
    Definition no_write (y : GL) (l : list elabel) : Prop :=
      forall u x w, In (TSO.EW GL u x w) l -> x <> y.

    Lemma tpath_app_iff st l1 l2 st'' :
      tpath st (l1 ++ l2) st'' <-> exists st', tpath st l1 st' /\ tpath st' l2 st''.
    Proof.
      revert st. induction l1 as [| e l1 IH]; intros st; cbn.
      - split.
        + intros H. exists st. split; [constructor | exact H].
        + intros (st' & H1 & H2). inversion H1; subst. exact H2.
      - split.
        + intros H. inversion H as [| ? ? st1 ? ? Hs Hp]; subst.
          apply IH in Hp. destruct Hp as (st2 & H1 & H2).
          exists st2. split; [econstructor; eauto | exact H2].
        + intros (st' & H1 & H2). inversion H1 as [| ? ? st1 ? ? Hs Hp]; subst.
          econstructor; [exact Hs |]. apply IH. eauto.
    Qed.

    (** The length of a thread's buffer is its writes minus its flushes. *)
    Lemma tpath_buffer_length st l st' t :
      tpath st l st' -> length (tB st' t) + nflush t l = length (tB st t) + nwrite t l.
    Proof.
      induction 1 as [st | st e sta l st'' Hs Hp IH]; [cbn; lia |].
      destruct Hs as [u x w st0 sta0 Htm HtB | u x w st0 sta0 Hle [Htm HtB]
                     | u x w st0 sta0 Hle Hv [Htm HtB] | u x w B' st0 sta0 HB Htm HtB]; cbn.
      - rewrite HtB in IH. destruct (Pos.eq_dec t u) as [<- | Hne].
        + destruct (Pos.eq_dec t t) as [_ | Hc]; [| congruence].
          rewrite length_app in IH. cbn in IH. lia.
        + destruct (Pos.eq_dec u t) as [Heq | _]; [congruence |]. lia.
      - rewrite HtB in IH. lia.
      - rewrite HtB in IH. lia.
      - rewrite HtB in IH. destruct (Pos.eq_dec t u) as [<- | Hne].
        + destruct (Pos.eq_dec t t) as [_ | Hc]; [| congruence].
          rewrite HB. cbn. lia.
        + destruct (Pos.eq_dec u t) as [Heq | _]; [congruence |]. lia.
    Qed.

    Lemma last_entry_insert x y w (A B : list (GL * nat)) :
      y <> x -> last_entry x (A ++ (y, w) :: B) = last_entry x (A ++ B).
    Proof.
      intros Hyx. induction A as [| [z u] A IH]; cbn.
      - destruct (TSO.last_entry GL gdec x B); [reflexivity |].
        destruct (gdec y x); [contradiction | reflexivity].
      - rewrite IH. reflexivity.
    Qed.

    (** *** wmb: a store to [GBw] and its flush *)

    (** The original state [st] and the state [st'] of the run with the
        ghost store [(GBw, v)] of thread [t]: memory agrees off [GBw], the
        other buffers agree, and [t]'s buffer has the ghost entry after the
        entries [A] that were pending when it was issued. *)
    Definition Rg (t : tid) (v : nat) (A : list (GL * nat)) (st st' : tstate) : Prop :=
      (forall y, y <> GBw -> tm st' y = tm st y) /\
      (forall u, u <> t -> tB st' u = tB st u) /\
      exists B, tB st t = A ++ B /\ tB st' t = A ++ (GBw, v) :: B.

    (** After the ghost entry is flushed: memory agrees off [GBw] and all
        buffers agree. *)
    Definition R0 (st st' : tstate) : Prop :=
      (forall y, y <> GBw -> tm st' y = tm st y) /\ (forall u, tB st' u = tB st u).

    Lemma path_Rg t v l st st2 :
      tpath st l st2 -> forall A st', Rg t v A st st' -> no_read GBw l -> nflush t l <= length A ->
      exists A' st2', tpath st' l st2' /\ Rg t v A' st2 st2' /\ length A' + nflush t l = length A.
    Proof.
      induction 1 as [st | st e sta l st2 Hs Hp IH]; intros A st' HR Hnr Hcnt.
      { exists A, st'. split; [constructor | split; [exact HR | cbn; lia]]. }
      destruct HR as (Htm & HtB & B & HB & HB').
      assert (Hnr' : no_read GBw l) by (intros u x w Hin; apply (Hnr u x w); right; exact Hin).
      destruct Hs as [u x w st0 sta0 Htma HtBa | u x w st0 sta0 Hle [Htma HtBa]
                     | u x w st0 sta0 Hle Hv [Htma HtBa] | u x w B' st0 sta0 HBu Htma HtBa].
      - (* write *)
        set (st'a := {| TSO.tm := tm st';
                        TSO.tB := fun u' => if Pos.eq_dec u' u then tB st' u ++ [(x, w)] else tB st' u' |}).
        assert (HRa : Rg t v A sta0 st'a).
        { split; [| split].
          - intros y Hy. cbn. rewrite Htma. auto.
          - intros u' Hu'. cbn. rewrite HtBa. destruct (Pos.eq_dec u' u) as [-> | Hne]; auto.
            rewrite HtB; auto.
          - cbn. rewrite HtBa. destruct (Pos.eq_dec t u) as [-> | Hne].
            + exists (B ++ [(x, w)]). rewrite HB, HB', <- !app_assoc. split; reflexivity.
            + exists B. rewrite HB'. auto. }
        cbn in Hcnt. destruct (IH A st'a HRa Hnr' Hcnt) as (A' & st2' & Hp' & HR' & Hlen).
        exists A', st2'. split; [| split; [exact HR' | cbn; exact Hlen]].
        econstructor; [| exact Hp']. constructor; intros; reflexivity.
      - (* read, from the buffer *)
        assert (Hx : x <> GBw) by (apply (Hnr u x w); left; reflexivity).
        assert (HRa : Rg t v A sta0 st').
        { split; [| split].
          - intros y Hy. rewrite Htma. auto.
          - intros u' Hu'. rewrite HtBa. auto.
          - exists B. rewrite HtBa. auto. }
        cbn in Hcnt. destruct (IH A st' HRa Hnr' Hcnt) as (A' & st2' & Hp' & HR' & Hlen).
        exists A', st2'. split; [| split; [exact HR' | cbn; exact Hlen]].
        econstructor; [| exact Hp']. apply TSO.TRdB; [| apply TSO.steq_refl].
        destruct (Pos.eq_dec u t) as [-> | Hne].
        + rewrite HB', last_entry_insert by congruence. rewrite <- HB. exact Hle.
        + rewrite HtB; auto.
      - (* read, from memory *)
        assert (Hx : x <> GBw) by (apply (Hnr u x w); left; reflexivity).
        assert (HRa : Rg t v A sta0 st').
        { split; [| split].
          - intros y Hy. rewrite Htma. auto.
          - intros u' Hu'. rewrite HtBa. auto.
          - exists B. rewrite HtBa. auto. }
        cbn in Hcnt. destruct (IH A st' HRa Hnr' Hcnt) as (A' & st2' & Hp' & HR' & Hlen).
        exists A', st2'. split; [| split; [exact HR' | cbn; exact Hlen]].
        econstructor; [| exact Hp']. apply TSO.TRdM; [| rewrite Htm; auto | apply TSO.steq_refl].
        destruct (Pos.eq_dec u t) as [-> | Hne].
        + rewrite HB', last_entry_insert by congruence. rewrite <- HB. exact Hle.
        + rewrite HtB; auto.
      - (* flush *)
        destruct (Pos.eq_dec u t) as [-> | Hne].
        + (* a flush of [t]: it publishes the head of [A] *)
          cbn in Hcnt. destruct (Pos.eq_dec t t) as [_ | Hc]; [| congruence].
          destruct A as [| a0 A0]; [cbn in Hcnt; lia |].
          rewrite HB in HBu. cbn in HBu. injection HBu as Ha0 HB'0. subst a0.
          set (st'a := {| TSO.tm := fun y => if gdec y x then w else tm st' y;
                          TSO.tB := fun u' => if Pos.eq_dec u' t then A0 ++ (GBw, v) :: B else tB st' u' |}).
          assert (HRa : Rg t v A0 sta0 st'a).
          { split; [| split].
            - intros y Hy. cbn. rewrite Htma. destruct (gdec y x); auto.
            - intros u' Hu'. cbn. rewrite HtBa. destruct (Pos.eq_dec u' t); [contradiction | auto].
            - exists B. cbn. rewrite HtBa. destruct (Pos.eq_dec t t); [| congruence]. auto. }
          destruct (IH A0 st'a HRa Hnr' ltac:(cbn in Hcnt; lia)) as (A' & st2' & Hp' & HR' & Hlen).
          exists A', st2'. split; [| split; [exact HR' | cbn; destruct (Pos.eq_dec t t); [lia | congruence]]].
          econstructor; [| exact Hp']. eapply TSO.TFl; [rewrite HB'; reflexivity | |]; intros; reflexivity.
        + (* a flush of another thread *)
          set (st'a := {| TSO.tm := fun y => if gdec y x then w else tm st' y;
                          TSO.tB := fun u' => if Pos.eq_dec u' u then B' else tB st' u' |}).
          assert (HRa : Rg t v A sta0 st'a).
          { split; [| split].
            - intros y Hy. cbn. rewrite Htma. destruct (gdec y x); auto.
            - intros u' Hu'. cbn. rewrite HtBa. destruct (Pos.eq_dec u' u); auto.
            - exists B. cbn. rewrite HtBa. destruct (Pos.eq_dec t u) as [-> | _]; [congruence |]. auto. }
          cbn in Hcnt. destruct (Pos.eq_dec u t) as [Hc | _]; [contradiction |]. cbn in Hcnt.
          destruct (IH A st'a HRa Hnr' Hcnt) as (A' & st2' & Hp' & HR' & Hlen).
          exists A', st2'. split; [| split; [exact HR' | cbn; destruct (Pos.eq_dec u t); [contradiction | cbn; exact Hlen]]].
          econstructor; [| exact Hp']. eapply TSO.TFl; [rewrite HtB; [exact HBu | exact Hne] | |];
            intros; reflexivity.
    Qed.

    Lemma path_R0 l st st2 :
      tpath st l st2 -> forall st', R0 st st' -> no_read GBw l ->
      exists st2', tpath st' l st2' /\ R0 st2 st2'.
    Proof.
      induction 1 as [st | st e sta l st2 Hs Hp IH]; intros st' HR Hnr.
      { exists st'. split; [constructor | exact HR]. }
      destruct HR as (Htm & HtB).
      assert (Hnr' : no_read GBw l) by (intros u x w Hin; apply (Hnr u x w); right; exact Hin).
      destruct Hs as [u x w st0 sta0 Htma HtBa | u x w st0 sta0 Hle [Htma HtBa]
                     | u x w st0 sta0 Hle Hv [Htma HtBa] | u x w B' st0 sta0 HBu Htma HtBa].
      - set (st'a := {| TSO.tm := tm st';
                        TSO.tB := fun u' => if Pos.eq_dec u' u then tB st' u ++ [(x, w)] else tB st' u' |}).
        destruct (IH st'a) as (st2' & Hp' & HR'); [| exact Hnr' |].
        { split.
          - intros y Hy. cbn. rewrite Htma. auto.
          - intros u'. cbn. rewrite HtBa, !HtB. reflexivity. }
        exists st2'. split; [| exact HR'].
        econstructor; [| exact Hp']. constructor; intros; reflexivity.
      - destruct (IH st') as (st2' & Hp' & HR'); [| exact Hnr' |].
        { split; [intros y Hy; rewrite Htma; auto | intros u'; rewrite HtBa; auto]. }
        exists st2'. split; [| exact HR'].
        econstructor; [| exact Hp']. apply TSO.TRdB; [rewrite HtB; exact Hle | apply TSO.steq_refl].
      - assert (Hx : x <> GBw) by (apply (Hnr u x w); left; reflexivity).
        destruct (IH st') as (st2' & Hp' & HR'); [| exact Hnr' |].
        { split; [intros y Hy; rewrite Htma; auto | intros u'; rewrite HtBa; auto]. }
        exists st2'. split; [| exact HR'].
        econstructor; [| exact Hp']. apply TSO.TRdM; [rewrite HtB; exact Hle | rewrite Htm; auto | apply TSO.steq_refl].
      - set (st'a := {| TSO.tm := fun y => if gdec y x then w else tm st' y;
                        TSO.tB := fun u' => if Pos.eq_dec u' u then B' else tB st' u' |}).
        destruct (IH st'a) as (st2' & Hp' & HR'); [| exact Hnr' |].
        { split.
          - intros y Hy. cbn. rewrite Htma. destruct (gdec y x); auto.
          - intros u'. cbn. rewrite HtBa, HtB. reflexivity. }
        exists st2'. split; [| exact HR'].
        econstructor; [| exact Hp']. eapply TSO.TFl; [rewrite HtB; exact HBu | |]; intros; reflexivity.
    Qed.

    (** [Tr_insert_wmb]: insert a ghost store [EW t GBw v] after [l1], and
        its flush [EF t GBw] after [l2], where [l2] contains exactly as many
        flushes of [t] as [t] had pending writes after [l1] (writes minus
        flushes of [t] in [l1]).  The ghost entry is then at the head of
        [t]'s buffer, so the flush is a machine step.  No read of [GBw] may
        follow the insertion point. *)
    Theorem Tr_insert_wmb (t : tid) (v : nat) (l1 l2 l3 : list elabel) :
      Tr (l1 ++ l2 ++ l3) ->
      no_read GBw (l2 ++ l3) ->
      nflush t l2 + nflush t l1 = nwrite t l1 ->
      Tr (l1 ++ TSO.EW GL t GBw v :: l2 ++ TSO.EF GL t GBw :: l3).
    Proof.
      intros (st3 & Hp) Hnr Hcnt.
      apply tpath_app_iff in Hp. destruct Hp as (st1 & Hp1 & Hp).
      apply tpath_app_iff in Hp. destruct Hp as (st2 & Hp2 & Hp3).
      assert (Hnr2 : no_read GBw l2) by (intros u x w Hin; apply (Hnr u x w); apply in_or_app; left; exact Hin).
      assert (Hnr3 : no_read GBw l3) by (intros u x w Hin; apply (Hnr u x w); apply in_or_app; right; exact Hin).
      pose proof (tpath_buffer_length _ _ _ t Hp1) as Hlen1. cbn in Hlen1.
      set (st1' := {| TSO.tm := tm st1;
                      TSO.tB := fun u => if Pos.eq_dec u t then tB st1 t ++ [(GBw, v)] else tB st1 u |}).
      assert (HR1 : Rg t v (tB st1 t) st1 st1').
      { split; [| split].
        - intros y _. reflexivity.
        - intros u Hu. cbn. destruct (Pos.eq_dec u t); [contradiction | reflexivity].
        - exists []. cbn. destruct (Pos.eq_dec t t); [| congruence]. rewrite app_nil_r. split; reflexivity. }
      destruct (path_Rg t v l2 st1 st2 Hp2 (tB st1 t) st1' HR1 Hnr2 ltac:(lia))
        as (A' & st2' & Hp2' & (Htm2 & HtB2 & B & HB & HB') & Hlen2).
      destruct A' as [| a A']; [| cbn in Hlen2; lia]. cbn in HB, HB'.
      set (st2'' := {| TSO.tm := fun y => if gdec y GBw then v else tm st2' y;
                       TSO.tB := fun u => if Pos.eq_dec u t then B else tB st2' u |}).
      assert (HR2 : R0 st2 st2'').
      { split.
        - intros y Hy. cbn. destruct (gdec y GBw); [contradiction | auto].
        - intros u. cbn. destruct (Pos.eq_dec u t) as [-> | Hne]; [auto | auto]. }
      destruct (path_R0 l3 st2 st3 Hp3 st2'' HR2 Hnr3) as (st3' & Hp3' & _).
      exists st3'. apply tpath_app_iff. exists st1. split; [exact Hp1 |].
      apply (TSO.tp_cons GL gdec st1 _ st1'); [constructor; intros; reflexivity |].
      apply tpath_app_iff. exists st2'. split; [exact Hp2' |].
      econstructor; [| exact Hp3'].
      eapply TSO.TFl; [exact HB' | |]; intros; reflexivity.
    Qed.

    (** If fewer flushes of [t] follow than [t] had pending writes, the
        ghost store stays pending to the end. *)
    Theorem Tr_insert_wmb_pending (t : tid) (v : nat) (l1 l2 : list elabel) :
      Tr (l1 ++ l2) ->
      no_read GBw l2 ->
      nflush t l2 + nflush t l1 <= nwrite t l1 ->
      Tr (l1 ++ TSO.EW GL t GBw v :: l2).
    Proof.
      intros (st2 & Hp) Hnr Hcnt.
      apply tpath_app_iff in Hp. destruct Hp as (st1 & Hp1 & Hp2).
      pose proof (tpath_buffer_length _ _ _ t Hp1) as Hlen1. cbn in Hlen1.
      set (st1' := {| TSO.tm := tm st1;
                      TSO.tB := fun u => if Pos.eq_dec u t then tB st1 t ++ [(GBw, v)] else tB st1 u |}).
      assert (HR1 : Rg t v (tB st1 t) st1 st1').
      { split; [| split].
        - intros y _. reflexivity.
        - intros u Hu. cbn. destruct (Pos.eq_dec u t); [contradiction | reflexivity].
        - exists []. cbn. destruct (Pos.eq_dec t t); [| congruence]. rewrite app_nil_r. split; reflexivity. }
      destruct (path_Rg t v l2 st1 st2 Hp2 (tB st1 t) st1' HR1 Hnr ltac:(lia))
        as (A' & st2' & Hp2' & _ & _).
      exists st2'. apply tpath_app_iff. exists st1. split; [exact Hp1 |].
      apply (TSO.tp_cons GL gdec st1 _ st1'); [constructor; intros; reflexivity | exact Hp2'].
    Qed.

    Lemma split_nflush t (l : list elabel) n :
      n <= nflush t l -> exists la lb, l = la ++ lb /\ nflush t la = n.
    Proof.
      revert n. induction l as [| e l IH]; intros n Hn.
      - exists [], []. cbn in *. split; [reflexivity | lia].
      - destruct n as [| n]; [exists [], (e :: l); split; reflexivity |].
        destruct e as [u x w | u x w | u x]; cbn in Hn.
        + destruct (IH (S n) Hn) as (la & lb & -> & Hla). exists (TSO.EW GL u x w :: la), lb. auto.
        + destruct (IH (S n) Hn) as (la & lb & -> & Hla). exists (TSO.ER GL u x w :: la), lb. auto.
        + destruct (Pos.eq_dec u t) as [Heq | Hne]; cbn in Hn.
          * destruct (IH n ltac:(lia)) as (la & lb & -> & Hla). exists (TSO.EF GL u x :: la), lb.
            split; [reflexivity | cbn; destruct (Pos.eq_dec u t); [lia | contradiction]].
          * destruct (IH (S n) Hn) as (la & lb & -> & Hla). exists (TSO.EF GL u x :: la), lb.
            split; [reflexivity | cbn; destruct (Pos.eq_dec u t); [contradiction | exact Hla]].
    Qed.

    (** A ghost wmb can be inserted at every point of every trace that does
        not read [GBw] afterwards: with its flush placed right after the
        flushes of [t]'s pending writes, or, if they do not all occur,
        without a flush. *)
    Corollary Tr_insert_wmb_exists (t : tid) (v : nat) (l1 l2 : list elabel) :
      Tr (l1 ++ l2) -> no_read GBw l2 ->
      (exists l2a l2b, l2 = l2a ++ l2b /\
         Tr (l1 ++ TSO.EW GL t GBw v :: l2a ++ TSO.EF GL t GBw :: l2b)) \/
      Tr (l1 ++ TSO.EW GL t GBw v :: l2).
    Proof.
      intros HT Hnr.
      assert (Hle : nflush t l1 <= nwrite t l1).
      { destruct HT as (st & Hp). apply tpath_app_iff in Hp. destruct Hp as (st1 & Hp1 & _).
        pose proof (tpath_buffer_length _ _ _ t Hp1) as H. cbn in H. lia. }
      destruct (le_lt_dec (nflush t l2) (nwrite t l1 - nflush t l1)) as [Hfew | Hmany].
      - right. apply Tr_insert_wmb_pending; auto. lia.
      - left. destruct (split_nflush t l2 (nwrite t l1 - nflush t l1) ltac:(lia)) as (la & lb & -> & Hla).
        exists la, lb. split; [reflexivity |]. apply Tr_insert_wmb; auto. lia.
    Qed.

    (** *** rmb: a load of [GBr] *)

    Lemma path_no_GBr st l st' :
      tpath st l st' -> no_write GBr l ->
      (forall u, last_entry GBr (tB st u) = None) -> tm st GBr = 0 ->
      (forall u, last_entry GBr (tB st' u) = None) /\ tm st' GBr = 0.
    Proof.
      induction 1 as [st | st e sta l st'' Hs Hp IH]; intros Hnw Hle Hm; [auto |].
      assert (Hnw' : no_write GBr l) by (intros u x w Hin; apply (Hnw u x w); right; exact Hin).
      apply IH; [exact Hnw' | |];
        destruct Hs as [u x w st0 sta0 Htma HtBa | u x w st0 sta0 Hle' [Htma HtBa]
                       | u x w st0 sta0 Hle' Hv [Htma HtBa] | u x w B' st0 sta0 HBu Htma HtBa].
      - assert (Hx : x <> GBr) by (apply (Hnw u x w); left; reflexivity).
        intros u'. rewrite HtBa. destruct (Pos.eq_dec u' u); [| auto].
        rewrite last_entry_insert by congruence. rewrite app_nil_r. apply Hle.
      - intros u'. rewrite HtBa. auto.
      - intros u'. rewrite HtBa. auto.
      - intros u'. rewrite HtBa. destruct (Pos.eq_dec u' u) as [-> | _]; [| auto].
        specialize (Hle u). rewrite HBu in Hle. cbn in Hle.
        destruct (TSO.last_entry GL gdec GBr B'); [discriminate | reflexivity].
      - rewrite Htma. exact Hm.
      - rewrite Htma. exact Hm.
      - rewrite Htma. exact Hm.
      - rewrite Htma. destruct (gdec GBr x) as [<- | _]; [| exact Hm].
        specialize (Hle u). rewrite HBu in Hle. cbn in Hle.
        destruct (TSO.last_entry GL gdec GBr B'); [discriminate |].
        destruct (gdec GBr GBr); [discriminate | congruence].
    Qed.

    (** [Tr_insert_rmb]: a load [ER t GBr 0] can be inserted at every point
        before which no write of [GBr] occurs. *)
    Theorem Tr_insert_rmb (t : tid) (l1 l2 : list elabel) :
      Tr (l1 ++ l2) -> no_write GBr l1 -> Tr (l1 ++ TSO.ER GL t GBr 0 :: l2).
    Proof.
      intros (st2 & Hp) Hnw.
      apply tpath_app_iff in Hp. destruct Hp as (st1 & Hp1 & Hp2).
      destruct (path_no_GBr _ _ _ Hp1 Hnw (fun _ => eq_refl) eq_refl) as [Hle Hm].
      exists st2. apply tpath_app_iff. exists st1. split; [exact Hp1 |].
      econstructor; [| exact Hp2]. apply TSO.TRdM; [apply Hle | symmetry; exact Hm | apply TSO.steq_refl].
    Qed.

    (** Inserting ghost operations preserves the hypotheses of further
        insertions: a wmb writes [GBw] and reads nothing, an rmb reads [GBr]
        and writes nothing. *)
    Lemma no_read_GBw_rmb l1 l2 t :
      no_read GBw (l1 ++ l2) -> no_read GBw (l1 ++ TSO.ER GL t GBr 0 :: l2).
    Proof.
      intros H u x w Hin. apply in_app_or in Hin. destruct Hin as [Hin | [Heq | Hin]].
      - apply (H u x w). apply in_or_app. auto.
      - injection Heq as _ <- _. discriminate.
      - apply (H u x w). apply in_or_app. auto.
    Qed.

    Lemma no_write_GBr_wmb l1 l2 t v :
      no_write GBr (l1 ++ l2) -> no_write GBr (l1 ++ TSO.EW GL t GBw v :: l2).
    Proof.
      intros H u x w Hin. apply in_app_or in Hin. destruct Hin as [Hin | [Heq | Hin]].
      - apply (H u x w). apply in_or_app. auto.
      - injection Heq as _ <- _. discriminate.
      - apply (H u x w). apply in_or_app. auto.
    Qed.
  End Insert.

  (** ** Part 5. Composition: x86 traces with ghost barriers are in [V_{I_tab}] *)

  Section Composed.
    Context {D : Type} (decD : forall x y : D, {x = y} + {x <> y}).
    Context {Cat : Type} (to : Cat -> Cat -> bool) (cat : cell_op (tab_cfg decD TSO_modes) -> Cat).

    Abbreviation GL := (gloc D).
    Abbreviation gdec := (gloc_eq_dec decD).

    Corollary x86_wmb_V_tab (t : tid) (v : nat) (l1 l2 l3 : list (TSO.elabel GL)) :
      TSO.Tr GL gdec (l1 ++ l2 ++ l3) ->
      no_read GBw (l2 ++ l3) ->
      nflush t l2 + nflush t l1 = nwrite t l1 ->
      exists s : trace (tab_cfg decD TSO_modes),
        V (I_tab to cat) (relabel (fun i => i) s) /\
        TSO.erase GL gdec (relabel (fun i => i) s) =
          l1 ++ TSO.EW GL t GBw v :: l2 ++ TSO.EF GL t GBw :: l3.
    Proof.
      intros HT Hnr Hcnt. apply x86_trace_V_tab_index. apply Tr_insert_wmb; assumption.
    Qed.

    Corollary x86_rmb_V_tab (t : tid) (l1 l2 : list (TSO.elabel GL)) :
      TSO.Tr GL gdec (l1 ++ l2) ->
      no_write GBr l1 ->
      exists s : trace (tab_cfg decD TSO_modes),
        V (I_tab to cat) (relabel (fun i => i) s) /\
        TSO.erase GL gdec (relabel (fun i => i) s) = l1 ++ TSO.ER GL t GBr 0 :: l2.
    Proof.
      intros HT Hnw. apply x86_trace_V_tab_index. apply Tr_insert_rmb; assumption.
    Qed.
  End Composed.

End TableBarrierTSO.
