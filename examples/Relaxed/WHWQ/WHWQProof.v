(** * WHWQProof: the RLHL derivation of the enqueue of the weak
      Herlihy–Wing queue

    Task WHWQ (.rocq-review/tasks/WHWQ.md), phase P7.  The invariant,
    rely, guarantee, footprints and postcondition are those of
    [WHWQInv]; nothing there is changed.  The method is derived through
    [RelaxedHoareRun.run_method_provable] (hence [rp_run] and
    [RProvable_coind]), as a [MethodProvable] derivation
    ([enq_provable]).  The dequeue and T4 are in [WHWQDeq].

    ** The enqueue ([enext v]: [i <- FAA; store i v [dix 0]])

    Positions: [0] the [FAA] invocation, [1] its response, [2] the store
    invocation, [3] its response.  The own dag is the chain [0 → 1 → 2 →
    3] ((F1), the tag [dix [0]], (F1)), plus [0 → 2] ((F2): the store
    releases).  So the four events are totally ordered and every
    own-interference premise ([ns_if_*], [bw_if]) is refuted by the
    order; only the stability under [Rq k] is a real obligation.
    Assertions:
    - [EStart] (start of position 0): [k] at [ls_inv], its pending
      invocations are its footprint [[FAA; store]];
    - [EA0 hu0] (after the [FAA]): [k] owns the record of the [FAA] with
      value [n], is the pending enqueue of its thread with vertex [n]
      ([KPend]), and its pending invocation is a store;
    - [EA1 i] (after the response [i]): [KPend k i v] (the record gave
      [i = n]) and a pending store;
    - [EA2] (after the store): [k] at [ls_linr].
    Updates: [upd_e0] ([iq_faa_lp]: [AInv]), [upd_e1] ([iq_response] and
    the record), [upd_e2] ([iq_store_lp]: [ARet]; the pending store is
    the one emitted, so its slot is [i]), [upd_e3] ([iq_response]).

    ** Scope and dependencies

    - Over [EIhl δRC], with the overlay presentation [POQueueRD] (see the
      scope of [WHWQInv]).
    - The derivation uses the hand-written address tag of the store: the
      edge [1 → 2], from the [FAA]'s response to the store, carries [EA1]
      and with it the slot [i] (tag policy in [WHWQProg]; review gate 4,
      WHWQ-g4-2).

    No axiom is used: [enq_provable] is closed under the global context
    ([Print Assumptions]; task log). *)

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

Import ListNotations.

Module WHWQProof.
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

  Local Abbreviation ES := ERC.
  Local Abbreviation FP := (FQ positive).
  Local Abbreviation VE := (EIhl (E := ERC) δRC).
  Local Abbreviation VF := (POQueueRD.POQueueRD positive).
  Local Abbreviation POk c P := (@PossOk FP VF c P).
  Local Abbreviation QSt := (@POQueueState positive).

  (** ** Generic pieces *)

  Lemma IE_inj t1 t2 h1 h2 o1 o2 : IE t1 h1 o1 = IE t2 h2 o2 -> t1 = t2 /\ h1 = h2 /\ o1 = o2.
  Proof. unfold IE. intros E. injection E as E1 E2 E3. auto. Qed.

  Lemma evupdate_conseq (I : Assn VE VF) (g : PRel VE VF) k ev (P P' Q : Assn VE VF) :
    (forall s, P' s -> P s) -> EvUpdate I g k ev P Q -> EvUpdate I g k ev P' Q.
  Proof. intros HP HU σ p γ γ' Hpre. apply HU. exact (HP _ Hpre). Qed.

  Lemma before_chain {E : RelaxedSig.t} (L : list (TaggedEvent E)) a b :
    (forall j, a <= j -> j < b -> dprec L j (S j)) -> a <= b -> before L a b.
  Proof.
    intros Hch Hab. induction b as [| b IH]; [replace a with 0 by lia; apply before_refl |].
    destruct (Nat.eq_dec a (S b)) as [-> | Hne]; [apply before_refl |].
    apply (before_step _ _ b); [apply IH; [intros j H1 H2; apply Hch; lia | lia] | apply Hch; lia].
  Qed.

  Section Enq.
    Context (t : tid) (v : positive).
    Local Abbreviation w := (Pos.to_nat v).

    (** ** Part 1. The calls of the enqueue *)

    Definition eop (i j : nat) : RCOp := match j with 0 => op_faa | _ => op_store i w end.
    Definition edix (j : nat) : list nat := match j with 0 => [] | _ => [0] end.

    Definition ECalls (i : nat) (cs : list (RCall ES)) : Prop :=
      length cs <= 2 /\ forall j c, nth_error cs j = Some c -> rc_op c = eop i j /\ rc_dix c = edix j.

    Section Call.
      Context (h : nat).
      Local Abbreviation k := (@pair tid (handle FP) t h).
      Local Abbreviation Pinit := (PostInvoke Iq k (enq v) (Oq t (enq v) h)).

      (** ** Part 2. The slot assertions *)

      Definition EStart : Assn VE VF := fun s =>
        KLk k (@ls_inv FP (enq v)) s /\ exists evs, EnqShape t v evs /\ KG k evs s.

      Definition KSt : Assn VE VF := fun s => exists h1 i', KG k [IE t h1 (op_store i' w)] s.

      Definition EA0 (hu0 : nat) : Assn VE VF := fun s =>
        exists n, KMine (t, hu0) (@RelaxedTraceLin.Build_Op ES (t, hu0) op_faa n) s /\ KPend k n v s /\ KSt s.

      Definition EA1 (i : nat) : Assn VE VF := fun s => KPend k i v s /\ KSt s.

      Definition EA2 : Assn VE VF := KLk k (@ls_linr FP (enq v) tt).

      Lemma kst_stable_r : Stable Iq (Rq k) KSt.
      Proof. intros s s' (h1 & i' & Hg) Hr HI. exists h1, i'. exact (kg_stable_r k _ s s' Hg Hr HI). Qed.

      Lemma estart_stable_r : Stable Iq (Rq k) EStart.
      Proof.
        intros s s' (Hl & evs & HΩ & Hg) Hr HI. split; [exact (klk_stable_r k _ s s' Hl Hr HI) |].
        exists evs. split; [exact HΩ | exact (kg_stable_r k evs s s' Hg Hr HI)].
      Qed.

      Lemma ea0_stable_r hu0 : Stable Iq (Rq k) (EA0 hu0).
      Proof.
        intros s s' (n & Hm & Hp & Hk) Hr HI. exists n.
        split; [exact (kmine_stable_r k _ _ s s' Hm Hr HI) |].
        split; [exact (kpend_stable_r k n v s s' Hp Hr HI) | exact (kst_stable_r s s' Hk Hr HI)].
      Qed.

      Lemma ea1_stable_r i : Stable Iq (Rq k) (EA1 i).
      Proof.
        intros s s' (Hp & Hk) Hr HI.
        split; [exact (kpend_stable_r k i v s s' Hp Hr HI) | exact (kst_stable_r s s' Hk Hr HI)].
      Qed.

      Lemma ea2_stable_r : Stable Iq (Rq k) EA2.
      Proof. apply klk_stable_r. Qed.

      (** ** Part 3. The own dag: a chain *)

      Lemma edp_chain (Γ : list (Slot VE VF)) (H : FutureStore ES) (cs : list (RCall ES)) i j :
        RunCtx k Γ H cs -> ECalls i cs -> S j < length Γ -> dprec (evs Γ) j (S j).
      Proof.
        intros Hc [Hl Hw] Hj. pose proof (runctx_len k Γ H cs Hc) as HlΓ.
        destruct (Nat.Even_or_Odd j) as [[c Hc2] | [c Hc2]].
        - subst j. destruct (nth_error cs c) as [x |] eqn:Ex; [| apply nth_error_None in Ex; lia].
          apply (proj2 (dprec_run k Γ H cs (2 * c) (S (2 * c)) Hc)). exists c, x. split; [exact Ex |]. right. split; reflexivity.
        - subst j. assert (Hc1 : c = 0) by lia. subst c.
          destruct (nth_error cs 1) as [x |] eqn:Ex; [| apply nth_error_None in Ex; lia].
          destruct (nth_error cs 0) as [x0 |] eqn:Ex0; [| apply nth_error_None in Ex0; lia].
          apply (proj2 (dprec_run k Γ H cs (S (2 * 0)) (2 * 1) Hc)). exists 1, x. split; [exact Ex |]. left.
          split; [reflexivity |]. exists 0, x0. split; [exact Ex0 |]. split; [lia |]. right. split; [reflexivity |].
          rewrite (proj2 (Hw 1 x Ex)). cbn. left. reflexivity.
      Qed.

      Lemma ebefore (Γ : list (Slot VE VF)) (H : FutureStore ES) (cs : list (RCall ES)) i a b :
        RunCtx k Γ H cs -> ECalls i cs -> a <= b -> b < length Γ -> before (evs Γ) a b.
      Proof.
        intros Hc Hw Hab Hb. apply before_chain; [| exact Hab].
        intros j _ Hj. exact (edp_chain Γ H cs i j Hc Hw ltac:(lia)).
      Qed.

      (** ** Part 4. The slots, and one lemma for every [NewSlotOK] *)

      Definition estart (j : nat) : Assn VE VF := match j with 0 => EStart | _ => fun _ => True end.

      Definition ein (hu0 i j d : nat) : Assn VE VF :=
        match j, d with
        | 1, 0 => EA0 hu0
        | 2, 1 => EA1 i
        | 3, 2 => EA2
        | _, _ => fun _ => True
        end.

      Definition epost (hu0 i j : nat) : Assn VE VF :=
        match j with 0 => EA0 hu0 | 1 => EA1 i | _ => EA2 end.

      Definition eguar (j : nat) : PRel VE VF := match j with 0 | 2 => Gq k | _ => GRes k end.

      Definition eslot (hu0 i j : nat) (ev : TaggedEvent ES) : Slot VE VF :=
        mkSlot ev (estart j) (ein hu0 i j) (epost hu0 i j) (eguar j).

      Definition SlotsOK (hu0 i : nat) (Γ : list (Slot VE VF)) : Prop :=
        forall j sj, nth_error Γ j = Some sj -> sj = eslot hu0 i j (sl_ev sj).

      Lemma ein_cases hu0 i j d : ein hu0 i j d = (fun _ => True) \/ (j = S d /\ ein hu0 i j d = epost hu0 i d).
      Proof.
        destruct j as [| [| [| [| j]]]]; cbn; try (left; reflexivity);
          destruct d as [| [| [| d]]]; cbn; try (left; reflexivity); right; split; reflexivity.
      Qed.

      Lemma ein_stable_r hu0 i j d : Stable Iq (Rq k) (ein hu0 i j d).
      Proof.
        destruct j as [| [| [| [| j]]]]; cbn; try apply Stable_true;
          destruct d as [| [| [| d]]]; cbn; try apply Stable_true;
          [apply ea0_stable_r | apply ea1_stable_r | apply ea2_stable_r].
      Qed.

      Lemma estart_est j : Impl Iq Pinit (estart j).
      Proof.
        destruct j as [| j]; [| intros s _ _; exact Logic.I].
        intros s HI (p0 & γ0 & evs & (st & P0 & Hp0 & _ & HC) & Hinv & Hg & HΩ & _).
        cbn [ps_poss ps_mem ps_ghost fst snd] in Hp0, HC, Hinv. subst p0.
        destruct (RelaxedHoareInherit.pinv_inv_gen _ _ _ _ _ _ Hinv) as [Hp Hfr].
        split; [exists st, (make_lin_entry k (@ls_inv FP (enq v)) :: P0); split; [exact Hp | left; reflexivity] |].
        exists evs. split; [exact HΩ |]. unfold KG. rewrite Hg, kg_app, kg_new.
        rewrite (kg_none k γ0); [reflexivity |]. intros e He Ho. apply Hfr. rewrite <- Ho. exact (proj1 (iq_age _ _ _ _ HC) e He).
      Qed.

      Lemma estart_stable j : Stable Iq (Rq k) (estart j).
      Proof. destruct j as [| j]; [exact estart_stable_r | apply Stable_true]. Qed.

      Lemma eguar_gq j s s' : eguar j s s' -> Gq k s s'.
      Proof. destruct j as [| [| [| j]]]; cbn; [exact (fun H => H) | exact (fun H => proj1 H) | exact (fun H => H) | exact (fun H => proj1 H)]. Qed.

      (** The generic slot lemma: every own-interference premise is refuted
          by the order ([ebefore]); the rest is the update and the
          stability under the rely. *)
      Lemma enew hu0 i (Γ : list (Slot VE VF)) p (ev : TaggedEvent ES) (Γx : list (Slot VE VF)) (Hx : FutureStore ES)
          (csx : list (RCall ES)) (rest : list (Slot VE VF)) :
        p = length Γ ->
        RunCtx k Γx Hx csx -> ECalls i csx -> Γx = (Γ ++ [eslot hu0 i p ev]) ++ rest -> SlotsOK hu0 i Γ ->
        EvUpdate Iq (eguar p) k (untag ev) (fun s => estart p s /\ forall d, ein hu0 i p d s) (epost hu0 i p) ->
        NewSlotOK Iq Rq Gq k Pinit Γ (eslot hu0 i p ev).
      Proof.
        intros -> Hc Hw HΓx Hok Hupd.
        assert (Hlx : length Γ < length Γx) by (rewrite HΓx, !length_app; cbn; lia).
        assert (Hbx : forall a b, a <= b -> b <= length Γ -> before (evs (Γ ++ [eslot hu0 i (length Γ) ev])) a b).
        { intros a b Hab Hb. pose proof (ebefore Γx Hx csx i a b Hc Hw Hab ltac:(lia)) as Hbf. rewrite HΓx, evs_app in Hbf.
          apply (before_app_iff (evs (Γ ++ [eslot hu0 i (length Γ) ev])) (evs rest) a b) in Hbf;
            [exact Hbf | rewrite length_evs, length_app; cbn; lia]. }
        assert (Hbo : forall a b, a <= b -> b < length Γ -> before (evs Γ) a b).
        { intros a b Hab Hb. pose proof (Hbx a b Hab ltac:(lia)) as Hbf. rewrite evs_app in Hbf.
          apply (before_app_iff (evs Γ) (evs [eslot hu0 i (length Γ) ev]) a b) in Hbf; [exact Hbf | rewrite length_evs; exact Hb]. }
        assert (Hslot : forall j sj, nth_error Γ j = Some sj ->
                          sl_start sj = estart j /\ sl_in sj = ein hu0 i j /\ sl_post sj = epost hu0 i j /\ sl_guar sj = eguar j).
        { intros j sj Hj. rewrite (Hok j sj Hj). cbn. auto. }
        assert (Hjn : forall j sj, nth_error Γ j = Some sj -> j < length Γ)
          by (intros j sj Hj; apply nth_error_Some; rewrite Hj; discriminate).
        constructor; cbn [eslot sl_ev sl_start sl_in sl_post sl_guar].
        - intros s s' Hg. exact (eguar_gq _ s s' Hg).
        - intros σ p γ γ' [Hst Hin] HI Hge σ' Hs. apply (Hupd σ p γ γ'); [| exact HI | exact Hge | exact Hs].
          split; [exact Hst |]. intros d. destruct (ein_cases hu0 i (length Γ) d) as [E | (Hd & E)]; [rewrite E; exact Logic.I |].
          apply Hin.
          assert (Hdp : dprec (evs Γx) d (S d)) by (apply (edp_chain Γx Hx csx i d Hc Hw); lia).
          rewrite <- Hd in Hdp. rewrite HΓx, evs_app in Hdp.
          apply (dprec_app_iff (evs (Γ ++ [eslot hu0 i (length Γ) ev])) (evs rest) d (length Γ)) in Hdp;
            [exact Hdp | rewrite length_evs, length_app; cbn; lia].
        - apply estart_est.
        - intros d sd _ Hsd s _ Hp. destruct (Hslot d sd Hsd) as (_ & _ & Hpo & _). rewrite Hpo in Hp.
          destruct (ein_cases hu0 i (length Γ) d) as [E | (_ & E)]; rewrite E; [exact Logic.I | exact Hp].
        - apply estart_stable.
        - intros d _. apply ein_stable_r.
        - intros g sg Hg. destruct Γ as [| x Γ']; [destruct g; discriminate Hg |]. apply Stable_true.
        - intros d g sg Hd Hg Hnb. destruct (ein_cases hu0 i (length Γ) d) as [E | (Hdj & E)]; [rewrite E; apply Stable_true |].
          exfalso. apply Hnb. pose proof (Hjn g sg Hg) as Hgn. apply Hbo; lia.
        - intros y sy Hy Hnb. exfalso. apply Hnb. apply Hbx; [pose proof (Hjn y sy Hy); lia | lia].
        - intros y sy d Hy Hnb Hd. exfalso. apply Hnb. apply Hbx; [pose proof (Hjn y sy Hy); lia | lia].
      Qed.

      (** ** Part 5. The event updates *)

      (** Position 0, the [FAA]: [AInv]. *)
      Lemma upd_e0 hu0 (P : Assn VE VF) :
        (forall s, P s -> EStart s) -> EvUpdate Iq (Gq k) k (IE t hu0 op_faa) P (EA0 hu0).
      Proof.
        intros HP σ p γ γ' Hpre HI Hge σ' Hs.
        destruct (HP _ Hpre) as ((st & P0 & Hp & Hl) & evs & (h0 & h1 & i' & Hne & ->) & Hg).
        cbn [ps_poss ps_ghost ps_mem fst snd] in Hp, Hg. subst p. unfold KG in Hg. cbn [ps_ghost snd] in Hg.
        pose proof HI as (st1 & P1 & Hp1 & Hru & HC). cbn in Hp1. injection Hp1 as <- <-.
        unfold regs, ps_mem, ps_ghost in HC. cbn [fst snd] in HC.
        destruct (kg_head k γ γ' (IE t h0 op_faa) [IE t h1 (op_store i' w)] (IE t hu0 op_faa) (iq_gnd _ _ _ _ HC) Hg Hge Logic.I)
          as [E Hg'].
        { destruct (Nat.eq_dec h0 hu0) as [-> | Hh]; [left; reflexivity | right].
          split; [reflexivity |]. cbn. exact (proj1 (rc_si_not_before_rel op_faa)). }
        apply IE_inj in E as (_ & -> & _).
        assert (Hst : Owns k isSt γ').
        { apply owns_kg. exists (IE t h1 (op_store i' w)). rewrite Hg'. split; [left; reflexivity | exists i', w; reflexivity]. }
        destruct (iq_faa_lp t h v h0 σ σ' st P0 γ γ' HI Hl Hs Hge Hst) as (P' & Hinv & Hk' & Hps & HI' & HG & Hn).
        destruct (inv_mine σ σ' t h0 op_faa Hru Hs) as (r & Hm & HU).
        destruct (step_faa σ σ' t h0 Hs) as [_ HU']. rewrite HU in HU'.
        apply (f_equal (fun l : list (RelaxedTraceLin.Op ES) => match l with a :: _ => rec_nat a | [] => 0 end)) in HU'.
        cbn in HU'. subst r.
        exists (POk (POQReady (poq_start_enq t v st)) P'). split; [exact Hps |]. split; [| split; [exact HI' | exact HG]].
        exists (poq_next st). split; [rewrite Hn; exact Hm |]. split.
        - exists (poq_start_enq t v st), P'. split; [reflexivity |]. split; [exact Hk' |].
          split; [cbn; apply TMap.gss | exact (poq_start_enq_vertex_new t v st)].
        - exists h1, i'. unfold KG. cbn [ps_ghost snd]. exact Hg'.
      Qed.

      (** Position 1, the response [i] of the [FAA]: the record gives the
          vertex. *)
      Lemma upd_e1 hu0 i (P : Assn VE VF) :
        (forall s, P s -> EA0 hu0 s) ->
        EvUpdate Iq (GRes k) k (Build_ThreadEvent t (@ResEv ES hu0 op_faa i)) P (EA1 i).
      Proof.
        intros HP σ p γ γ' Hpre HI Hge σ' Hs. cbn in Hge. subst γ'.
        destruct (HP _ Hpre) as (n & Hm & Hpend & Hk).
        pose proof (mine_res_val (t, hu0) op_faa i _ σ σ' Hm Hs) as E. apply faa_rec_inj in E. subst n.
        destruct (iq_response k t hu0 op_faa i σ σ' p γ HI Hs) as [HI' HG].
        exists p. split; [apply rt_refl |]. split; [| split; [exact HI' | split; [exact HG | split; reflexivity]]].
        split.
        - destruct Hpend as (st & P0 & Hp & H). exists st, P0. split; [exact Hp | exact H].
        - destruct Hk as (h1 & i' & Hg). exists h1, i'. exact Hg.
      Qed.

      (** Position 2, the store: [ARet]. *)
      Lemma upd_e2 i hu (P : Assn VE VF) :
        (forall s, P s -> EA1 i s) -> EvUpdate Iq (Gq k) k (IE t hu (op_store i w)) P EA2.
      Proof.
        intros HP σ p γ γ' Hpre HI Hge σ' Hs.
        destruct (HP _ Hpre) as ((st & P0 & Hp & Hl & Hf & Hv) & h1 & i' & Hg).
        cbn [ps_poss ps_ghost ps_mem fst snd] in Hp, Hg. subst p. unfold KG in Hg. cbn [ps_ghost snd] in Hg.
        pose proof HI as (st1 & P1 & Hp1 & Hru & HC). cbn in Hp1. injection Hp1 as <- <-.
        unfold regs, ps_mem, ps_ghost in HC. cbn [fst snd] in HC.
        destruct (kg_head k γ γ' (IE t h1 (op_store i' w)) [] (IE t hu (op_store i w)) (iq_gnd _ _ _ _ HC) Hg Hge Logic.I)
          as [E _].
        { destruct (Nat.eq_dec h1 hu) as [-> | Hh]; [destruct (Nat.eq_dec i' i) as [-> | Hi]; [left; reflexivity |] |].
          - right. split; [reflexivity |]. cbn. exact (proj2 (rc_si_not_before_rel _) i w).
          - right. split; [reflexivity |]. cbn. exact (proj2 (rc_si_not_before_rel _) i w). }
        destruct (iq_store_lp t h v hu i σ σ' st P0 γ γ' HI Hl Hf Hs Hge) as (P' & Hu & Hps & HI' & HG).
        exists (POk (POQReady (poq_finish_enq t st)) P'). split; [exact Hps |]. split; [| split; [exact HI' | exact HG]].
        exists (poq_finish_enq t st), P'. split; [reflexivity | exact (lin_update_target _ _ _ _ _ Hu)].
      Qed.

      (** Position 3, the response of the store. *)
      Lemma upd_e3 i hu (r : unit) (P : Assn VE VF) :
        (forall s, P s -> EA2 s) ->
        EvUpdate Iq (GRes k) k (Build_ThreadEvent t (@ResEv ES hu (op_store i w) r)) P EA2.
      Proof.
        intros HP σ p γ γ' Hpre HI Hge σ' Hs. cbn in Hge. subst γ'.
        destruct (iq_response k t hu (op_store i w) r σ σ' p γ HI Hs) as [HI' HG].
        exists p. split; [apply rt_refl |]. split; [| split; [exact HI' | split; [exact HG | split; reflexivity]]].
        destruct (HP _ Hpre) as (st & P0 & Hp & H). exists st, P0. split; [exact Hp | exact H].
      Qed.
      (** ** Part 6. The calls, the machine invariant, the return *)

      Definition einv (st : ESt) (cs : list (RCall ES)) (Γ : list (Slot VE VF)) (H : FutureStore ES) : Prop :=
        match st with
        | E0 => cs = [] /\ Γ = []
        | E1 i => length cs = 1 /\ ECalls i cs /\ exists hu0, SlotsOK hu0 i Γ
        | ED => exists i, length cs = 2 /\ ECalls i cs /\ exists hu0, SlotsOK hu0 i Γ
        end.

      Lemma slotsok_snoc hu0 i (Γ : list (Slot VE VF)) p ev :
        SlotsOK hu0 i Γ -> p = length Γ -> SlotsOK hu0 i (Γ ++ [eslot hu0 i p ev]).
      Proof.
        intros Hok -> j sj Hj. destruct (nth_error_snoc_cases _ _ _ _ Hj) as [(_ & Hj') | (-> & ->)];
          [exact (Hok j sj Hj') | reflexivity].
      Qed.

      Lemma ecalls_snoc i n (cs : list (RCall ES)) (hu : nat) :
        length cs = n -> n <= 1 -> ECalls i cs -> ECalls i (cs ++ [@mkRCall ES hu (eop i n) (edix n)]).
      Proof.
        intros Hl Hn [_ Hw]. split; [rewrite length_app; cbn; lia |].
        intros j c Hj. destruct (nth_error_snoc_cases _ _ _ _ Hj) as [(_ & Hj') | (-> & ->)]; [exact (Hw j c Hj') |].
        rewrite Hl. split; reflexivity.
      Qed.

      (** Call 0, the [FAA]: its response [r] becomes the slot index of the
          machine state, its handle the [hu0] of the slots. *)
      Definition esi0 (H : FutureStore ES) (cs : list (RCall ES)) (hu : nat) : Slot VE VF :=
        eslot hu 0 0 (invD_tev (E := ES) k H (dep_of (map rc_h cs) []) hu op_faa).

      Definition esr0 (hu : nat) (r : nat) : Slot VE VF :=
        eslot hu r 1 (res_tev (E := ES) k hu op_faa r).

      Lemma ecall0 cs Γ H :
        RunCtx k Γ H cs -> cs = [] -> Γ = [] ->
        RunCallOK Iq Rq Gq k Pinit einv cs Γ H op_faa [] (fun r => E1 r) (esi0 H cs) esr0.
      Proof.
        intros Hc -> ->.
        assert (Hctx : forall hu (r : nat), handle_fresh hu H ->
                  RunCtx k (([] ++ [esi0 H [] hu]) ++ [esr0 hu r]) (Build_FutureEntry hu (@Resolved ES op_faa r) :: H)
                    ([] ++ [@mkRCall ES hu op_faa []])).
        { intros hu r Hf. apply (runctx_snoc k [] H [] _ _ hu op_faa [] r _ Hc Hf); [reflexivity | reflexivity |].
          apply resolve_here. }
        assert (Hw : forall r hu, ECalls r ([] ++ [@mkRCall ES hu op_faa []]))
          by (intros r hu; apply (ecalls_snoc r 0 [] hu); [reflexivity | lia | split; [cbn; lia | intros j c Hj; destruct j; discriminate Hj]]).
        assert (Hok : forall r hu, SlotsOK hu r [esi0 H [] hu]).
        { intros r hu j sj Hj. destruct j as [| j]; [| destruct j; discriminate Hj]. injection Hj as <-. reflexivity. }
        split; [| split; [| split; [| split]]].
        - intros hu. reflexivity.
        - intros hu Hf. unfold esi0.
          apply (enew hu 0 [] 0 _ _ _ _ [esr0 hu 0] eq_refl (Hctx hu 0 Hf) (Hw 0 hu) eq_refl
                   (fun j sj Hj => ltac:(destruct j; discriminate Hj))).
          apply (upd_e0 hu). intros s Hs. exact (proj1 Hs).
        - intros hu r. reflexivity.
        - intros hu r Hf. unfold esr0.
          apply (enew hu r [esi0 H [] hu] 1 _ _ _ _ [] eq_refl (Hctx hu r Hf) (Hw r hu) eq_refl (Hok r hu)).
          apply (upd_e1 hu r). intros s Hs. exact (proj2 Hs 0).
        - intros hu r H' _ _ _. cbn [einv]. split; [reflexivity |]. split; [exact (Hw r hu) |].
          exists hu. apply slotsok_snoc; [exact (Hok r hu) | reflexivity].
      Qed.

      (** Call 1, the store into slot [i]. *)
      Definition esi1 (hu0 i : nat) (H : FutureStore ES) (cs : list (RCall ES)) (hu : nat) : Slot VE VF :=
        eslot hu0 i 2 (invD_tev (E := ES) k H (dep_of (map rc_h cs) [0]) hu (op_store i w)).

      Definition esr1 (hu0 i hu : nat) (r : unit) : Slot VE VF :=
        eslot hu0 i 3 (res_tev (E := ES) k hu (op_store i w) r).

      Lemma ecall1 hu0 i cs Γ H :
        RunCtx k Γ H cs -> length cs = 1 -> ECalls i cs -> SlotsOK hu0 i Γ ->
        RunCallOK Iq Rq Gq k Pinit einv cs Γ H (op_store i w) [0] (fun _ => ED) (esi1 hu0 i H cs) (esr1 hu0 i).
      Proof.
        intros Hc Hl Hw Hok. pose proof (runctx_len k Γ H cs Hc) as HlΓ.
        assert (Hctx : forall hu (r : unit), handle_fresh hu H ->
                  RunCtx k ((Γ ++ [esi1 hu0 i H cs hu]) ++ [esr1 hu0 i hu r]) (Build_FutureEntry hu (@Resolved ES (op_store i w) r) :: H)
                    (cs ++ [@mkRCall ES hu (op_store i w) [0]])).
        { intros hu r Hf. apply (runctx_snoc k Γ H cs _ _ hu (op_store i w) [0] r _ Hc Hf); [reflexivity | reflexivity |].
          apply resolve_here. }
        assert (Hw' : forall hu, ECalls i (cs ++ [@mkRCall ES hu (op_store i w) [0]]))
          by (intros hu; exact (ecalls_snoc i 1 cs hu Hl ltac:(lia) Hw)).
        assert (Hok' : forall hu, SlotsOK hu0 i (Γ ++ [esi1 hu0 i H cs hu])) by (intros hu; apply slotsok_snoc; [exact Hok | lia]).
        split; [| split; [| split; [| split]]].
        - intros hu. reflexivity.
        - intros hu Hf. unfold esi1.
          apply (enew hu0 i Γ 2 _ _ _ _ [esr1 hu0 i hu tt] ltac:(lia) (Hctx hu tt Hf) (Hw' hu) eq_refl Hok).
          apply (upd_e2 i hu). intros s Hs. exact (proj2 Hs 1).
        - intros hu r. reflexivity.
        - intros hu r Hf. unfold esr1.
          apply (enew hu0 i (Γ ++ [esi1 hu0 i H cs hu]) 3 _ _ _ _ [] ltac:(rewrite length_app; cbn; lia)
                   (Hctx hu r Hf) (Hw' hu) ltac:(rewrite app_nil_r; reflexivity) (Hok' hu)).
          apply (upd_e3 i hu r). intros s Hs. exact (proj2 Hs 2).
        - intros hu r H' _ _ _. cbn [einv]. exists i. split; [rewrite length_app, Hl; reflexivity |].
          split; [exact (Hw' hu) |]. exists hu0. apply slotsok_snoc; [exact (Hok' hu) | rewrite length_app; cbn; lia].
      Qed.

      (** The return: the store's response carries [EA2], hence [Qq]; the
          footprint is the two invocations. *)
      Lemma eclose i hu0 cs Γ H :
        RunCtx k Γ H cs -> length cs = 2 -> ECalls i cs -> SlotsOK hu0 i Γ ->
        Close Iq Rq Gq k Pinit (fun r => Qq k (enq v) r) tt Γ H /\ Oq t (enq v) h (own_invs Γ).
      Proof.
        intros Hc Hl Hw Hok. pose proof (runctx_len k Γ H cs Hc) as HlΓ.
        destruct (runctx_store k Γ H cs Hc) as (_ & Hall & Hnd).
        split.
        - apply (close_done Iq Rq Gq k Pinit (fun r => Qq k (enq v) r) tt Γ H
                   (fun d => if Nat.eqb d 3 then EA2 else fun _ => True) (fun _ => True) Hall).
          constructor.
          + intros d sd Hd s _ Hp. rewrite (Hok d sd Hd) in Hp. cbn [eslot sl_post] in Hp.
            destruct (Nat.eqb_spec d 3) as [-> | _]; [exact Hp | exact Logic.I].
          + intros s _ _. exact Logic.I.
          + intros d g sg Hd Hg Hnb. destruct (Nat.eqb_spec d 3) as [-> | _]; [| apply Stable_true].
            exfalso. apply Hnb. assert (Hgn : g < length Γ) by (apply nth_error_Some; rewrite Hg; discriminate).
            apply (ebefore Γ H cs i g 3 Hc Hw); lia.
          + intros g sg _. apply Stable_true.
          + intros d. destruct (Nat.eqb d 3); [exact ea2_stable_r | apply Stable_true].
          + apply Stable_true.
          + intros s _ _ Hfin.
            destruct (nth_error cs 1) as [c1 |] eqn:E1; [| apply nth_error_None in E1; lia].
            destruct (runctx_res_at k Γ H cs 1 c1 Hc E1) as (sr & r & Hsr & Hev).
            pose proof (Hfin 3 sr Hsr ltac:(unfold is_response; rewrite Hev; exact Logic.I)) as Hk. cbn in Hk. exact Hk.
        - rewrite (own_invs_run k Γ H cs Hc). destruct Hw as [_ Hw].
          destruct cs as [| c0 [| c1 [| c2 cs]]]; cbn in Hl; try lia.
          cbn [map] in Hnd |- *. rewrite (proj1 (Hw 0 c0 eq_refl)), (proj1 (Hw 1 c1 eq_refl)).
          exists (rc_h c0), (rc_h c1), i. split; [| reflexivity].
          intros E. inversion Hnd as [| ? ? Hn _]. apply Hn. rewrite E. left. reflexivity.
      Qed.

      Lemma estep_ok st cs Γ H :
        RunCtx k Γ H cs -> einv st cs Γ H ->
        RunStepOK Iq Rq Gq k Pinit einv
          (fun a Γ' H' => Close Iq Rq Gq k Pinit (fun r => Qq k (enq v) r) a Γ' H' /\ Oq t (enq v) h (own_invs Γ'))
          cs Γ H (enext v st).
      Proof.
        intros Hc Hi. destruct st as [| i |]; cbn [einv] in Hi; cbn [enext RunStepOK].
        - destruct Hi as [-> ->]. exists (esi0 H []), esr0. exact (ecall0 [] [] H Hc eq_refl eq_refl).
        - destruct Hi as (Hl & Hw & hu0 & Hok). exists (esi1 hu0 i H cs), (esr1 hu0 i). exact (ecall1 hu0 i cs Γ H Hc Hl Hw Hok).
        - destruct Hi as (i & Hl & Hw & hu0 & Hok). exact (eclose i hu0 cs Γ H Hc Hl Hw Hok).
      Qed.
    End Call.

    (** ** Part 7. The enqueue derivation *)

    Theorem enq_provable :
      MethodProvable Iq Rq Gq Mwhw t (enq v) (fun h => Oq t (enq v) h) (fun h r => Qq (t, h) (enq v) r).
    Proof.
      apply (run_method_provable Iq Rq Gq Mwhw t (enq v) _ _ (enext v) E0 (fun h => einv h)).
      - reflexivity.
      - intros h s Hs. exact (iq_postinvoke t h (enq v) s Hs).
      - intros h r s Hq HI Hno. exact (qq_ret t h (enq v) r s Hq HI Hno).
      - intros h. cbn. split; reflexivity.
      - intros h st cs Γ H Hc Hi. exact (estep_ok h st cs Γ H Hc Hi).
    Qed.

  End Enq.

End WHWQProof.
