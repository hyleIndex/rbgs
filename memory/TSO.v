(** * The x86-TSO machine (Prop. mem:prop:tso)

    The read/write fragment of the x86-TSO machine of Owens, Sarkar and
    Sewell (Def. mem:def:tsomachine): states are a memory [m : Loc -> nat]
    and per-thread FIFO store buffers [B : tid -> list (Loc * nat)], with
    the transitions

      [TWr]  (m, B) --wrt(x,v)@t--> (m, B[t ↦ B(t)·(x,v)])
      [TRd]  (m, B) --rd(x)=v@t---> (m, B)      if v is the last x-entry of
                                                B(t), or v = m(x) if none
      [TFl]  (m, B) --flush(x)@t--> (m[x ↦ v], B[t ↦ B'])  if B(t) = (x,v)·B'

    The machine carries no handles and publishes each thread's writes in
    issue order, whereas the contract of the [TSO] instance publishes them
    in handle order.  The two agree on the traces in which the two orders
    coincide: [V↑_TSO] is the set of [s ∈ V_TSO] in which every thread
    issues its writes in increasing handle order, and [erase] deletes the
    handles.  Prop. mem:prop:tso: [erase(V↑_TSO[Locs]) = Tr(TSO_Locs)].

    The proof is the simulation of the paper, with
    [μ(s) = (λx. g_x, λt. (loc, val) of pend_t(s))]: by the bookkeeping
    lemma the pending values of [Buf_x] for [t] are the values of the
    [x]-entries of [B(t)], in order.

    Successor states of the machine are specified pointwise (the memory
    and the buffers are functions), so that the simulation needs no
    functional extensionality; the set of traces is unaffected. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Sorting.Sorted.
Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.

Require Import models.RelaxedSignature.
Require Import memory.Prelude.
Require Import memory.Cell.

Import ListNotations.

Module TSO.

  Import Cell Cell.Instances.

  Section TSO.
    Context (Loc : Type) (dec : forall x y : Loc, {x = y} + {x <> y}).
    Abbreviation C := (TSO_cfg dec).
    Abbreviation block := (block C).
    Abbreviation trace := (trace C).
    Abbreviation I := (mode_indep (C := C)).

    (** The configuration is fixed, so the block functions are used at [C]
        throughout (the location type of the section is [Loc], not
        [Cell.Loc C], which the elaborator cannot invert). *)
    Abbreviation at_loc := (at_loc (C := C)).
    Abbreviation proj := (proj (C := C)).
    Abbreviation pend := (pend (C := C)).
    Abbreviation remove_first_at := (remove_first_at (C := C)).
    Abbreviation state_after := (state_after (C := C)).
    Abbreviation enabled := (enabled (C := C)).
    Abbreviation next := (next (C := C)).
    Abbreviation VBuf := (VBuf (C := C)).
    Abbreviation contract := (contract (C := C)).
    Abbreviation V := (V (C := C)).

    (** ** Erasing handles *)

    Inductive elabel : Type :=
    | EW (t : tid) (x : Loc) (v : nat)
    | ER (t : tid) (x : Loc) (v : nat)
    | EF (t : tid) (x : Loc).

    Definition erase_block (b : block) : elabel :=
      match b with
      | BW t _ x v _ => EW t x v
      | BR t _ x _ v => ER t x v
      | BF t _ x => EF t x
      end.

    Definition erase (s : trace) : list elabel := map erase_block s.

    (** ** The machine *)

    Record tstate : Type := {
      tm : Loc -> nat;
      tB : tid -> list (Loc * nat);
    }.

    Definition tinit : tstate := {| tm := fun _ => 0; tB := fun _ => [] |}.

    (** The value of the last [x]-entry of a buffer, if any. *)
    Fixpoint last_entry (x : Loc) (l : list (Loc * nat)) : option nat :=
      match l with
      | [] => None
      | (y, v) :: l' =>
          match last_entry x l' with
          | Some v' => Some v'
          | None => if dec y x then Some v else None
          end
      end.

    (** Extensional equality of states. *)
    Definition steq (st st' : tstate) : Prop :=
      (forall y, tm st y = tm st' y) /\ (forall u, tB st u = tB st' u).

    Lemma steq_refl st : steq st st.
    Proof. split; reflexivity. Qed.

    Lemma steq_sym st st' : steq st st' -> steq st' st.
    Proof. intros [H1 H2]. split; auto. Qed.

    Inductive tstep : tstate -> elabel -> tstate -> Prop :=
    | TWr t x v st st' :
        (forall y, tm st' y = tm st y) ->
        (forall u, tB st' u = if Pos.eq_dec u t then tB st t ++ [(x, v)] else tB st u) ->
        tstep st (EW t x v) st'
    | TRdB t x v st st' :
        last_entry x (tB st t) = Some v ->
        steq st' st ->
        tstep st (ER t x v) st'
    | TRdM t x v st st' :
        last_entry x (tB st t) = None ->
        v = tm st x ->
        steq st' st ->
        tstep st (ER t x v) st'
    | TFl t x v B' st st' :
        tB st t = (x, v) :: B' ->
        (forall y, tm st' y = if dec y x then v else tm st y) ->
        (forall u, tB st' u = if Pos.eq_dec u t then B' else tB st u) ->
        tstep st (EF t x) st'.

    Inductive tpath : tstate -> list elabel -> tstate -> Prop :=
    | tp_nil st : tpath st [] st
    | tp_cons st e st' l st'' :
        tstep st e st' -> tpath st' l st'' -> tpath st (e :: l) st''.

    (** [Tr(TSO_Locs)]: the label sequences of paths from the initial
        state. *)
    Definition Tr (l : list elabel) : Prop := exists st, tpath tinit l st.

    (** The machine is deterministic up to extensional equality. *)
    Lemma tstep_det st e st1 st2 :
      tstep st e st1 -> tstep st e st2 -> steq st1 st2.
    Proof.
      intros H1 H2.
      inversion H1 as [t x v ? ? Htm1 HtB1 | t x v ? ? Hle1 Heq1
                      | t x v ? ? Hle1 Hv1 Heq1 | t x v B1 ? ? HB1 Htm1 HtB1]; subst;
        inversion H2 as [? ? ? ? ? Htm2 HtB2 | ? ? ? ? ? Hle2 Heq2
                        | ? ? ? ? ? Hle2 Hv2 Heq2 | ? ? ? B2 ? ? HB2 Htm2 HtB2]; subst.
      - split; intros z; [rewrite Htm1, Htm2 | rewrite HtB1, HtB2]; reflexivity.
      - destruct Heq1 as [A1 B1]; destruct Heq2 as [A2 B2]. split; intros z; congruence.
      - congruence.
      - congruence.
      - destruct Heq1 as [A1 B1]; destruct Heq2 as [A2 B2]. split; intros z; congruence.
      - rewrite HB1 in HB2. injection HB2 as <- <-.
        split; intros z; [rewrite Htm1, Htm2 | rewrite HtB1, HtB2]; reflexivity.
    Qed.

    Lemma tpath_app st l e st'' :
      tpath st (l ++ [e]) st'' <-> exists st', tpath st l st' /\ tstep st' e st''.
    Proof.
      revert st. induction l as [| e0 l IH]; intros st; cbn.
      - split.
        + intros H. inversion H as [| ? ? st1 ? ? Hs Hp]; subst.
          inversion Hp; subst. exists st. split; [constructor | auto].
        + intros (st' & H1 & H2). inversion H1; subst. econstructor; eauto. constructor.
      - split.
        + intros H. inversion H as [| ? ? st1 ? ? Hs Hp]; subst.
          apply IH in Hp. destruct Hp as (st2 & H1 & H2).
          exists st2. split; [econstructor; eauto | auto].
        + intros (st' & H1 & H2). inversion H1 as [| ? ? st1 ? ? Hs Hp]; subst.
          econstructor; eauto. apply IH. eauto.
    Qed.

    (** ** [V↑_TSO]: witnesses issuing writes in handle order *)

    Definition wr_handle_order (s : trace) : Prop :=
      forall i j a b,
        i < j -> nth_error s i = Some a -> nth_error s j = Some b ->
        is_write a -> is_write b -> b_tid a = b_tid b -> b_handle a < b_handle b.

    Definition V_up (s : trace) : Prop := V I s /\ wr_handle_order s.

    Lemma wr_handle_order_prefix s s' : wr_handle_order (s ++ s') -> wr_handle_order s.
    Proof.
      intros H i j a b Hij Hi Hj Ha Hb Ht.
      assert (Hi' : i < length s) by (apply nth_error_Some; congruence).
      assert (Hj' : j < length s) by (apply nth_error_Some; congruence).
      apply (H i j a b Hij); auto; rewrite nth_error_app1; auto.
    Qed.

    Lemma wr_handle_order_snoc s b :
      wr_handle_order s ->
      (forall a, In a s -> is_write a -> is_write b -> b_tid a = b_tid b -> b_handle a < b_handle b) ->
      wr_handle_order (s ++ [b]).
    Proof.
      intros H Hb i j a c Hij Hi Hj Ha Hc Ht.
      destruct (lt_dec j (length s)) as [Hjs | Hjs].
      - rewrite nth_error_app1 in Hi by lia. rewrite nth_error_app1 in Hj by lia.
        apply (H i j a c Hij); auto.
      - rewrite nth_error_app2 in Hj by lia.
        destruct (j - length s) as [| k] eqn:Hk; [| destruct k; discriminate].
        cbn in Hj. injection Hj as <-.
        rewrite nth_error_app1 in Hi by lia.
        apply Hb; auto. eapply nth_error_In; eauto.
    Qed.

    Lemma wr_handle_order_last s b a :
      wr_handle_order (s ++ [b]) -> In a s ->
      is_write a -> is_write b -> b_tid a = b_tid b -> b_handle a < b_handle b.
    Proof.
      intros H Ha Hwa Hwb Ht. apply In_nth_error in Ha. destruct Ha as (i & Hi).
      assert (Hi' : i < length s) by (apply nth_error_Some; congruence).
      eapply (H i (length s)); eauto.
      - rewrite nth_error_app1; auto.
      - rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
    Qed.

    Lemma V_up_prefix s b : V_up (s ++ [b]) -> V_up s.
    Proof.
      intros [HV Hho]. split.
      - apply V_prefix in HV. exact HV.
      - eapply wr_handle_order_prefix; eauto.
    Qed.

    (** *** The pending writes of a thread are sorted by handle *)

    Definition hlt (a b : block) : Prop := b_handle a < b_handle b.

    Lemma In_remove_first_at x (l : list block) b :
      In b (remove_first_at x l) -> In b l.
    Proof.
      induction l as [| c l IH]; cbn; auto.
      destruct (at_loc x c); cbn; auto. intros [-> | H]; auto.
    Qed.

    Lemma StronglySorted_remove_first_at x (l : list block) :
      StronglySorted hlt l -> StronglySorted hlt (remove_first_at x l).
    Proof.
      induction l as [| a l IH]; intros H; [constructor |].
      apply StronglySorted_inv in H. destruct H as [Hl Hall].
      rewrite remove_first_at_cons. destruct (at_loc x a); auto.
      constructor; auto. rewrite Forall_forall in *.
      intros b Hb. apply Hall. eapply In_remove_first_at; eauto.
    Qed.

    Lemma StronglySorted_snoc (l : list block) b :
      StronglySorted hlt l -> Forall (fun a => hlt a b) l -> StronglySorted hlt (l ++ [b]).
    Proof.
      induction l as [| a l IH]; intros H Hall; cbn.
      - constructor; constructor.
      - apply StronglySorted_inv in H. destruct H as [Hl Ha].
        inversion Hall; subst. constructor; auto.
        apply Forall_app. split; auto.
    Qed.

    Lemma pend_sorted s t : wr_handle_order s -> StronglySorted hlt (pend t s).
    Proof.
      induction s as [| b s IH] using rev_ind; intros H.
      - constructor.
      - rewrite pend_snoc. pose proof (wr_handle_order_prefix _ _ H) as Hs.
        specialize (IH Hs). unfold pend_step.
        destruct b as [u h y v a | u h y a v | u h y].
        + destruct (Pos.eq_dec u t) as [-> | Hne]; auto.
          apply StronglySorted_snoc; auto.
          rewrite Forall_forall. intros m Hm.
          pose proof (pend_In _ _ _ Hm) as (Hin & Hw & Ht).
          unfold hlt. eapply wr_handle_order_last; eauto. exact Logic.I.
        + auto.
        + destruct (Pos.eq_dec u t); auto. apply StronglySorted_remove_first_at; auto.
    Qed.

    (** *** The contract under [TSO]

        No two writes are semi-independent under [TSO], so the contract at
        a flush block says that the published write has the least handle
        among the thread's pending writes.  Since the pending writes are
        sorted by handle, that is the head of the buffer. *)

    Lemma TSO_no_WW (a b : block) : is_write a -> is_write b -> ~ I (b_inv a) (b_inv b).
    Proof.
      intros Ha Hb H. apply TSO_indep_iff in H. destruct H as (_ & _ & Hr).
      destruct b; cbn in *; auto.
    Qed.

    Lemma contract_snoc_nonflush s b : ~ is_flush b -> contract I s -> contract I (s ++ [b]).
    Proof.
      intros Hb Hc s1 t h x s2 m Hs Hm m' Hm' Hlt.
      apply snoc_split in Hs. destruct Hs as [(-> & -> & Heq) | (s2' & -> & Hs)].
      - subst b. destruct Hb. exact Logic.I.
      - eapply Hc; eauto.
    Qed.

    Lemma contract_snoc_flush s t h x :
      contract I s ->
      (forall m m', hd_error (proj x (pend t s)) = Some m -> In m' (pend t s) ->
                    b_handle m' < b_handle m -> False) ->
      contract I (s ++ [BF t h x]).
    Proof.
      intros Hc Hvac s1 t' h' x' s2 m Hs Hm m' Hm' Hlt.
      apply snoc_split in Hs. destruct Hs as [(-> & -> & Heq) | (s2' & -> & Hs)].
      - injection Heq as Ht Hh Hx. subst t' h' x'. exfalso. eapply Hvac; eauto.
      - eapply Hc; eauto.
    Qed.

    (** In a trace of [V↑_TSO], a flush block of [t] at [x] publishes the
        head of [pend_t]. *)
    Lemma flush_head s t h x :
      wr_handle_order s -> contract I (s ++ [BF t h x]) -> proj x (pend t s) <> [] ->
      exists b0 rest, pend t s = b0 :: rest /\ b_loc b0 = x.
    Proof.
      intros Hho Hc Hne.
      destruct (pend t s) as [| b0 rest] eqn:Hp; [exfalso; apply Hne; reflexivity |].
      exists b0, rest. split; auto.
      destruct (proj x (b0 :: rest)) as [| m l'] eqn:Hpx; [congruence |].
      assert (Hm : In m (b0 :: rest)).
      { assert (Hin : In m (proj x (b0 :: rest))) by (rewrite Hpx; left; auto).
        unfold proj in Hin. apply filter_In in Hin. tauto. }
      assert (Hcon : forall m', In m' (pend t s) -> b_handle m' < b_handle m -> I (b_inv m') (b_inv m)).
      { intros m' Hm' Hlt. eapply (Hc s t h x [] m); eauto. rewrite Hp, Hpx. reflexivity. }
      destruct (at_loc x b0) eqn:Hb0; [apply at_loc_true in Hb0; exact Hb0 |].
      exfalso.
      (* [m] is a later pending write than [b0] with a larger handle *)
      rewrite proj_cons, Hb0 in Hpx.
      assert (Hm' : In m rest).
      { assert (Hin : In m (proj x rest)) by (rewrite Hpx; left; auto).
        unfold proj in Hin. apply filter_In in Hin. tauto. }
      pose proof (pend_sorted s t Hho) as Hsorted. rewrite Hp in Hsorted.
      apply StronglySorted_inv in Hsorted. destruct Hsorted as [_ Hall].
      rewrite Forall_forall in Hall. specialize (Hall m Hm'). unfold hlt in Hall.
      assert (Hb0in : In b0 (pend t s)) by (rewrite Hp; left; auto).
      assert (Hmin : In m (pend t s)) by (rewrite Hp; auto).
      pose proof (pend_In _ _ _ Hb0in) as (_ & Hwb0 & _).
      pose proof (pend_In _ _ _ Hmin) as (_ & Hwm & _).
      apply (TSO_no_WW b0 m Hwb0 Hwm). apply Hcon; auto.
    Qed.

    (** *** Enabledness of the last block *)

    Lemma V_last_enabled s b :
      (forall y, VBuf y (proj y (s ++ [b]))) -> enabled b (state_after (b_loc b) s).
    Proof.
      intros H. specialize (H (b_loc b)). rewrite proj_app in H.
      destruct H as (st & Hp). apply cell_path_app in Hp. destruct Hp as (st1 & H1 & H2).
      apply cell_path_proj_state in H1. subst st1.
      assert (Hb : at_loc (b_loc b) b = true) by (apply at_loc_true; reflexivity).
      cbn in H2. rewrite Hb in H2.
      inversion H2 as [| ? ? st2 ? ? Hs Hp']; subst. apply cell_step_iff in Hs. tauto.
    Qed.

    Lemma V_snoc_VBuf s b :
      (forall y, VBuf y (proj y s)) -> enabled b (state_after (b_loc b) s) ->
      forall y, VBuf y (proj y (s ++ [b])).
    Proof.
      intros Hall Hen y. rewrite proj_app.
      destruct (Hall y) as (st & Hp).
      assert (Hst := Hp). apply cell_path_proj_state in Hst. subst st.
      cbn. destruct (at_loc y b) eqn:Hy.
      - apply at_loc_true in Hy. exists (next b (state_after y s)).
        apply cell_path_app. exists (state_after y s). split; auto.
        econstructor; [| constructor]. apply cell_step_iff.
        split; auto. split; [rewrite Hy in Hen; exact Hen | reflexivity].
      - exists (state_after y s). rewrite app_nil_r. exact Hp.
    Qed.

    (** ** The simulation map [μ] *)

    Definition entry (b : block) : Loc * nat := (b_loc b, b_val b).

    Definition mu (s : trace) : tstate :=
      {| tm := fun x => cg (state_after x s);
         tB := fun t => map entry (pend t s) |}.

    (** The last [x]-entry of [B(t)] is the last pending value of [Buf_x]
        for [t] (Lemma mem:lem:book). *)
    Lemma last_entry_map x (l : list block) :
      last_entry x (map entry l) =
      match proj x l with [] => None | l' => Some (last (map b_val l') 0) end.
    Proof.
      induction l as [| b l IH]; [reflexivity |].
      cbn [map last_entry entry]. rewrite IH. rewrite proj_cons.
      destruct (at_loc x b) eqn:Hb.
      - apply at_loc_true in Hb. destruct (proj x l) as [| c l'].
        + cbn. destruct (dec (b_loc b) x); congruence.
        + reflexivity.
      - apply at_loc_false in Hb. destruct (proj x l) as [| c l'].
        + cbn. destruct (dec (b_loc b) x); congruence.
        + reflexivity.
    Qed.

    Lemma read_enabled_iff s t h x a v :
      enabled (BR t h x a v) (state_after x s) <->
      (last_entry x (tB (mu s) t) = Some v \/
       (last_entry x (tB (mu s) t) = None /\ v = tm (mu s) x)).
    Proof.
      cbn. rewrite bookkeeping. rewrite last_entry_map.
      destruct (proj x (pend t s)) as [| c l'] eqn:Hp.
      - cbn. split.
        + intros [[H _] | [_ H]]; [congruence | right; auto].
        + intros [H | [_ H]]; [discriminate | right; auto].
      - split.
        + intros [[_ H] | [H _]]; [left; congruence | discriminate].
        + intros [H | [H _]]; [left; split; [discriminate | congruence] | discriminate].
    Qed.

    Lemma mu_tm_nonflush s b y : ~ is_flush b -> tm (mu (s ++ [b])) y = tm (mu s) y.
    Proof.
      intros Hb. unfold mu. cbn [tm]. rewrite state_after_snoc. unfold step_at.
      destruct (at_loc y b); [| reflexivity].
      destruct b as [t h x v a | t h x a v | t h x]; cbn; auto. destruct Hb. exact Logic.I.
    Qed.

    Lemma mu_tB_write s t h x v a u :
      tB (mu (s ++ [BW t h x v a])) u =
      if Pos.eq_dec u t then tB (mu s) t ++ [(x, v)] else tB (mu s) u.
    Proof.
      unfold mu. cbn [tB]. rewrite pend_snoc. unfold pend_step.
      destruct (Pos.eq_dec t u), (Pos.eq_dec u t); try congruence.
      subst. rewrite map_app. reflexivity.
    Qed.

    Lemma mu_tB_read s t h x a v u :
      tB (mu (s ++ [BR t h x a v])) u = tB (mu s) u.
    Proof.
      unfold mu. cbn [tB]. rewrite pend_snoc. reflexivity.
    Qed.

    Lemma mu_tm_flush s t h x b0 rest y :
      pend t s = b0 :: rest -> b_loc b0 = x ->
      tm (mu (s ++ [BF t h x])) y = if dec y x then b_val b0 else tm (mu s) y.
    Proof.
      intros Hp Hl. unfold mu. cbn [tm]. rewrite state_after_snoc. unfold step_at.
      destruct (at_loc y (BF t h x)) eqn:Hy.
      - apply at_loc_true in Hy. cbn in Hy. subst y.
        destruct (dec x x) as [_ | Hne]; [| congruence].
        cbn [next]. rewrite bookkeeping, Hp, proj_cons.
        replace (at_loc x b0) with true by (symmetry; apply at_loc_true; auto).
        reflexivity.
      - apply at_loc_false in Hy. cbn in Hy.
        destruct (dec y x) as [Heq | _]; [congruence | reflexivity].
    Qed.

    Lemma mu_tB_flush s t h x b0 rest u :
      pend t s = b0 :: rest -> b_loc b0 = x ->
      tB (mu (s ++ [BF t h x])) u = if Pos.eq_dec u t then map entry rest else tB (mu s) u.
    Proof.
      intros Hp Hl. unfold mu. cbn [tB]. rewrite pend_snoc. unfold pend_step.
      destruct (Pos.eq_dec t u) as [Htu | Htu], (Pos.eq_dec u t) as [Hut | Hut]; try congruence.
      subst u. rewrite Hp, remove_first_at_cons.
      replace (at_loc x b0) with true by (symmetry; apply at_loc_true; auto).
      reflexivity.
    Qed.

    (** ** Forward simulation: [erase(V↑_TSO) ⊆ Tr] *)

    Lemma step_forward s b :
      V_up (s ++ [b]) -> tstep (mu s) (erase_block b) (mu (s ++ [b])).
    Proof.
      intros HVb. pose proof (V_up_prefix _ _ HVb) as HVs.
      destruct HVb as [[Hc Hbuf] Hho]. destruct HVs as [[Hcs Hbufs] Hhos].
      assert (Hen : enabled b (state_after (b_loc b) s)) by (apply V_last_enabled; auto).
      destruct b as [t h x v a | t h x a v | t h x]; cbn [erase_block].
      - (* write *)
        apply TWr.
        + intros y. apply mu_tm_nonflush. cbn. tauto.
        + intros u. apply mu_tB_write.
      - (* read *)
        cbn [b_loc] in Hen. apply read_enabled_iff in Hen.
        destruct Hen as [Hbuf' | [Hnone Hv]].
        + apply TRdB with (v := v); auto.
          split; [intros y; apply mu_tm_nonflush; cbn; tauto | intros u; apply mu_tB_read].
        + apply TRdM; auto.
          split; [intros y; apply mu_tm_nonflush; cbn; tauto | intros u; apply mu_tB_read].
      - (* flush *)
        cbn [b_loc] in Hen. apply flush_enabled_iff in Hen.
        destruct (flush_head s t h x Hhos Hc Hen) as (b0 & rest & Hp & Hl).
        apply TFl with (v := b_val b0) (B' := map entry rest).
        + unfold mu. cbn [tB]. rewrite Hp. cbn [map]. unfold entry at 1. rewrite Hl. reflexivity.
        + intros y. eapply mu_tm_flush; eauto.
        + intros u. eapply mu_tB_flush; eauto.
    Qed.

    Lemma mu_nil : mu [] = tinit.
    Proof. reflexivity. Qed.

    Lemma traces_forward s : V_up s -> tpath tinit (erase s) (mu s).
    Proof.
      induction s as [| b s IH] using rev_ind; intros HV.
      - rewrite mu_nil. constructor.
      - unfold erase. rewrite map_app. apply tpath_app.
        exists (mu s). split.
        + apply IH. eapply V_up_prefix; eauto.
        + apply step_forward; auto.
    Qed.

    (** ** Backward simulation: [Tr ⊆ erase(V↑_TSO)] *)

    (** A handle larger than every handle of the trace. *)
    Definition fresh_handle (s : trace) : nat :=
      S (fold_right (fun b n => Nat.max (b_handle b) n) 0 s).

    Lemma fresh_handle_gt s a : In a s -> b_handle a < fresh_handle s.
    Proof.
      unfold fresh_handle. induction s as [| b s IH]; intros H; [inversion H |].
      cbn. destruct H as [<- | H]; [lia |]. specialize (IH H). lia.
    Qed.

    Lemma V_up_nil : V_up [].
    Proof.
      split; [split |].
      - apply contract_nil.
      - intros y. exists init_state. constructor.
      - intros i j a b _ Hi. destruct i; discriminate.
    Qed.

    Lemma step_backward s st st' e :
      V_up s -> steq st (mu s) -> tstep st e st' ->
      exists b, V_up (s ++ [b]) /\ erase_block b = e /\ steq st' (mu (s ++ [b])).
    Proof.
      intros [[Hc Hbuf] Hho] [Htm HtB] Hstep.
      inversion Hstep; subst.
      - (* [TWr]: give the write a fresh handle *)
        pose (b := @BW C t (fresh_handle s) x v tt).
        exists b. unfold b. split; [| split].
        + split; [split |].
          * apply contract_snoc_nonflush; [cbn; tauto | exact Hc].
          * apply V_snoc_VBuf; auto. exact Logic.I.
          * apply wr_handle_order_snoc; auto.
            intros a Ha _ _ _. cbn. apply fresh_handle_gt. exact Ha.
        + reflexivity.
        + split.
          * intros y. rewrite mu_tm_nonflush by (cbn; tauto). rewrite <- Htm. auto.
          * intros u. rewrite mu_tB_write. rewrite <- !HtB. auto.
      - (* [TRd], buffered *)
        pose (b := @BR C t 0 x tt v).
        assert (Hen : enabled b (state_after x s)).
        { apply read_enabled_iff. left. rewrite <- HtB. auto. }
        exists b. unfold b. split; [| split].
        + split; [split |].
          * apply contract_snoc_nonflush; [cbn; tauto | exact Hc].
          * apply V_snoc_VBuf; auto.
          * apply wr_handle_order_snoc; auto. intros a _ _ Hb. destruct Hb.
        + reflexivity.
        + destruct H0 as [Htm' HtB']. split.
          * intros y. rewrite mu_tm_nonflush by (cbn; tauto). rewrite Htm'. auto.
          * intros u. rewrite mu_tB_read. rewrite HtB'. auto.
      - (* [TRd], from memory *)
        pose (b := @BR C t 0 x tt (tm st x)).
        assert (Hen : enabled b (state_after x s)).
        { apply read_enabled_iff. right. split; [rewrite <- HtB; auto | auto]. }
        exists b. unfold b. split; [| split].
        + split; [split |].
          * apply contract_snoc_nonflush; [cbn; tauto | exact Hc].
          * apply V_snoc_VBuf; auto.
          * apply wr_handle_order_snoc; auto. intros a _ _ Hb. destruct Hb.
        + reflexivity.
        + destruct H1 as [Htm' HtB']. split.
          * intros y. rewrite mu_tm_nonflush by (cbn; tauto). rewrite Htm'. auto.
          * intros u. rewrite mu_tB_read. rewrite HtB'. auto.
      - (* [TFl]: the head of the buffer is the head of [pend_t] *)
        rewrite HtB in H. cbn [mu tB] in H.
        destruct (pend t s) as [| b0 rest] eqn:Hp; [discriminate |].
        cbn [map] in H. unfold entry in H. injection H as Hl Hv Hrest.
        pose (b := @BF C t 0 x).
        assert (Hne : proj x (pend t s) <> []).
        { rewrite Hp, proj_cons.
          replace (at_loc x b0) with true by (symmetry; apply at_loc_true; auto). discriminate. }
        exists b. unfold b. split; [| split].
        + split; [split |].
          * apply contract_snoc_flush; auto.
            intros m m' Hm Hm' Hlt.
            rewrite Hp, proj_cons in Hm.
            replace (at_loc x b0) with true in Hm by (symmetry; apply at_loc_true; auto).
            cbn in Hm. injection Hm as <-.
            rewrite Hp in Hm'. destruct Hm' as [<- | Hm']; [lia |].
            pose proof (pend_sorted s t Hho) as Hsorted. rewrite Hp in Hsorted.
            apply StronglySorted_inv in Hsorted. destruct Hsorted as [_ Hall].
            rewrite Forall_forall in Hall. specialize (Hall m' Hm'). unfold hlt in Hall. lia.
          * apply V_snoc_VBuf; auto. apply flush_enabled_iff. exact Hne.
          * apply wr_handle_order_snoc; auto. intros a _ _ Hb. destruct Hb.
        + reflexivity.
        + split.
          * intros y. rewrite (mu_tm_flush s t 0 x b0 rest y Hp Hl). rewrite H0.
            destruct (dec y x); auto.
          * intros u. rewrite (mu_tB_flush s t 0 x b0 rest u Hp Hl). rewrite H1.
            destruct (Pos.eq_dec u t); auto.
    Qed.

    Lemma traces_backward l st :
      tpath tinit l st -> exists s, V_up s /\ erase s = l /\ steq st (mu s).
    Proof.
      revert st. induction l as [| e l IH] using rev_ind; intros st H.
      - inversion H; subst. exists []. split; [apply V_up_nil | split; [reflexivity | apply steq_refl]].
      - apply tpath_app in H. destruct H as (st1 & H1 & H2).
        destruct (IH st1 H1) as (s & HV & Herase & Heq).
        destruct (step_backward s st1 st e HV Heq H2) as (b & HVb & Hb & Heq').
        exists (s ++ [b]). split; [exact HVb | split; [| exact Heq']].
        unfold erase in *. rewrite map_app. cbn [map]. rewrite Hb, Herase. reflexivity.
    Qed.

    (** ** Prop. mem:prop:tso *)

    Theorem tso_traces l : (exists s, V_up s /\ erase s = l) <-> Tr l.
    Proof.
      split.
      - intros (s & HV & <-). exists (mu s). apply traces_forward. exact HV.
      - intros (st & H). destruct (traces_backward l st H) as (s & HV & Herase & _). eauto.
    Qed.

  End TSO.

End TSO.
