(** * RLHL, part 5: underlay and overlay presentations for the end-to-end theorems

    Two library facts for the end-to-end theorems of RLHL-2/3
    ([RelaxedHoareGSim]), decided by the author on the iteration-2 review
    (research-intent §8, M-16 and M-17).  Nothing here changes the
    triple or [RLHL2Hyps].

    ** Part 1: handle-linear underlays ([RelaxedHoareBase.HandleLinear])

    - [hl_path_inv_unique]: along every path of a handle-linear LTS, each
      key [(thread, handle)] is invoked at most once, and never a key
      that is already used at the start of the path.  This is the
      invocation half of [PrefixView.wf] and of Appendix/gamemodel.tex:19
      ("no two moves with the same polarity and the same future handle").
    - [vt_handle_linear]: the LTS of view traces [ViewLHL.VT nu], the
      complete underlay presentation of [ViewLHL.vlhl_sound], is
      handle-linear, with [used] = "the key is invoked in the view trace".
      The reason is [PrefixView.wf] (first clause), which every state of
      [VT] satisfies.

    ** Part 2: effect-at-invocation specifications (M-17)

    The author decided (M-17) that RLHL-2 specifications take effect at
    the abstract invocation (the style of [RelaxedHoareChecks.Counter]);
    the same-thread order is then discharged through the ghost thread
    frontier, not by helping.  For the over-every-underlay route this is
    superseded (author decision on latest-review M-18, research-intent
    §8): the intended RLHL-3 instance of
    [RelaxedHoareGSim.rlhl_rel_lin_pres] is [VE := ViewLHL.VT nuE] with
    the stamp-based overlay [VF := ViewLHL.VT nuF] and [Hsound :=
    ViewLHL.vt_sound] (not done).  [EI] and [ei_hvf] stay valid, and
    [RelaxedHoareGSim.rlhl_rel_lin_ei] uses them, but they apply to
    invocation-ordered underlays (such as
    [RelaxedHoareChecks.CounterHL.HVE]): over [ViewLHL.VT] an
    effect-at-invocation overlay is not expected to have a [GSimRel] when
    same-thread operations are ordered, because [VT] accepts dead-end
    prefixes in which a younger same-thread call responds first
    ([RelaxedHoareChecks.CounterRelLin.vt_junk],
    [vt_junk_not_rl_prefix]).  For the counter the impossibility is
    mechanized ([RelaxedHoareChecks.CounterRelLin.counter_vt_no_rlhl2]:
    no [RLHL2Hyps] over [VT] with [EI]); in general it is the review's
    prose argument (latest-review M-18).

    [EI δ] builds an effect-at-invocation specification LTS from a
    sequential specification given as a relation
    [δ : St -> forall op, ar op -> St -> Prop] ("from [s], [op] may return
    [r] and move to [s']"; a function is a special case):

    - state [(s, P)]: the sequential state and the list [P] of pending
      results, one [Op] record (key, operation, result) per call that has
      taken its abstract invocation but not its abstract response;
    - [InvEv (t, h) op]: apply [δ] now, [(s, P) --> (s', Build_Op (t, h)
      op r :: P)];
    - [ResEv (t, h) op r]: return the value computed at the invocation:
      [Build_Op (t, h) op r] must be in [P]; it is removed, [s] is kept.

    [seq_legal δ s0] is the sequential specification [ν]: the witnesses
    with a [δ]-run from [s0].  [ei_hvf] is the hypothesis [HVF] of
    [RelaxedGSim.gsim_rel_lin] for [VF := EI δ], [v0 := (s0, [])] and
    [nu := seq_legal δ s0]: every complete well-formed trace of [EI δ] is
    relaxed-linearizable.  It holds for *every* semi-independence relation
    ([ei_hvf_indep]), because the witness orders the operations by
    invocation, which respects both kinds of [rhb] edges.  [ei_sound_pres]
    is the same fact in the vocabulary of [ViewLHL] ([sound_pres]), so
    [EI δ] is a sound overlay presentation for
    [ViewLHL.presentation_choice].  [HVF] stays an explicit hypothesis of
    the RLHL-2 theorem; this lemma discharges it for every
    effect-at-invocation specification.

    Limitations.  [EI δ] needs no decidable equality on handles or
    operations; the response matches the pending record by [In], so a
    trace that invokes one key twice may match the older record (this
    cannot happen on the well-formed traces [HVF] is about).  The
    specification is total in the sense of [δ]: an invocation whose [δ]
    has no successor blocks (no error transition, [Error := False]).
    Specifications whose effect is at the response, with a no-op
    invocation and helping, are not covered and in general do not satisfy
    [HVF] under their natural [ν], even when their same-thread pairs
    commute: [RelaxedHoareChecks.tas_not_hvf] (TAS, non-commuting) and
    [RelaxedHoareChecks.pair_not_hvf] (two commuting reads of one thread
    with another thread's write in between).

    Assumptions: everything in this file is closed. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Relations.Relation_Definitions.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedGSim.
Require Import models.view.PrefixView.
Require Import models.view.ViewLHL.
Require Import models.simlin.RelaxedHoareBase.

Import ListNotations.


Module RelaxedHoareSpec.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedTraceLin.
  Import RelaxedGSim.
  Import ViewLHL.
  Import RelaxedHoareBase.

  (** ** Index facts for traces with [PrefixView.sel] *)

  Section Index.
    Context {E : RelaxedSig.t}.

    Abbreviation inv L := (inv_at (@PrefixView.sel E) L).
    Abbreviation res L := (res_at (@PrefixView.sel E) L).

    Lemma inv_cons_inv (ev : ThreadEvent E) L i k op :
      inv (ev :: L) i k op ->
      (i = 0 /\ ev = Build_ThreadEvent (fst k) (InvEv (snd k) op)) \/
      (exists i', i = S i' /\ inv L i' k op).
    Proof.
      intros (x & Hx & Hs). unfold PrefixView.sel in Hs. injection Hs as ->.
      destruct i as [| i']; cbn in Hx.
      - left. injection Hx as ->. auto.
      - right. exists i'. split; [reflexivity |]. exists (Build_ThreadEvent (fst k) (InvEv (snd k) op)).
        split; [exact Hx | reflexivity].
    Qed.

    Lemma inv_cons_S (ev : ThreadEvent E) L i k op : inv L i k op -> inv (ev :: L) (S i) k op.
    Proof. intros (x & Hx & Hs). exists x. split; [exact Hx | exact Hs]. Qed.

    Lemma inv_cons_0 L k op :
      inv (Build_ThreadEvent (fst k) (InvEv (snd k) op) :: L) 0 k op.
    Proof. eexists. split; reflexivity. Qed.

    Lemma inv_lt L i k op : inv L i k op -> i < length L.
    Proof. intros (x & Hx & _). apply nth_error_Some. congruence. Qed.

    Lemma res_lt L i k op (r : Sig.ar op) : res L i k op r -> i < length L.
    Proof. intros (x & Hx & _). apply nth_error_Some. congruence. Qed.

    Lemma inv_app_l L L' i k op : inv L i k op -> inv (L ++ L') i k op.
    Proof.
      intros (x & Hx & Hs). exists x. split; [| exact Hs].
      rewrite nth_error_app1; [exact Hx | apply nth_error_Some; congruence].
    Qed.

    Lemma res_app_l L L' i k op (r : Sig.ar op) : res L i k op r -> res (L ++ L') i k op r.
    Proof.
      intros (x & Hx & Hs). exists x. split; [| exact Hs].
      rewrite nth_error_app1; [exact Hx | apply nth_error_Some; congruence].
    Qed.

    Lemma inv_app_lt L L' i k op : i < length L -> inv (L ++ L') i k op -> inv L i k op.
    Proof.
      intros Hlt (x & Hx & Hs). exists x. split; [| exact Hs].
      rewrite nth_error_app1 in Hx; [exact Hx | exact Hlt].
    Qed.

    Lemma res_app_lt L L' i k op (r : Sig.ar op) : i < length L -> res (L ++ L') i k op r -> res L i k op r.
    Proof.
      intros Hlt (x & Hx & Hs). exists x. split; [| exact Hs].
      rewrite nth_error_app1 in Hx; [exact Hx | exact Hlt].
    Qed.

    Lemma nth_snoc_last {A : Type} (L : list A) x : nth_error (L ++ [x]) (length L) = Some x.
    Proof. rewrite nth_error_app2, Nat.sub_diag; reflexivity. Qed.

    Lemma nth_snoc_inv {A : Type} (L : list A) x i y :
      nth_error (L ++ [x]) i = Some y -> (i < length L /\ nth_error L i = Some y) \/ (i = length L /\ y = x).
    Proof.
      intros Hy. destruct (Nat.lt_ge_cases i (length L)) as [Hlt | Hge].
      - left. split; [exact Hlt |]. rewrite nth_error_app1 in Hy; [exact Hy | exact Hlt].
      - right. rewrite nth_error_app2 in Hy by exact Hge.
        destruct (i - length L) as [| n] eqn:Hn; cbn in Hy.
        + split; [lia | injection Hy as <-; reflexivity].
        + destruct n; discriminate.
    Qed.

    Lemma inv_snoc_inv L (ev : ThreadEvent E) i k op :
      inv (L ++ [ev]) i k op ->
      inv L i k op \/ (i = length L /\ ev = Build_ThreadEvent (fst k) (InvEv (snd k) op)).
    Proof.
      intros (x & Hx & Hs). unfold PrefixView.sel in Hs. injection Hs as ->.
      destruct (nth_snoc_inv _ _ _ _ Hx) as [[Hlt Hx'] | [-> <-]].
      - left. eexists. split; [exact Hx' | reflexivity].
      - right. auto.
    Qed.

    Lemma res_snoc_inv L (ev : ThreadEvent E) i k op (r : Sig.ar op) :
      res (L ++ [ev]) i k op r ->
      res L i k op r \/ (i = length L /\ ev = Build_ThreadEvent (fst k) (ResEv (snd k) op r)).
    Proof.
      intros (x & Hx & Hs). unfold PrefixView.sel in Hs. injection Hs as ->.
      destruct (nth_snoc_inv _ _ _ _ Hx) as [[Hlt Hx'] | [-> <-]].
      - left. eexists. split; [exact Hx' | reflexivity].
      - right. auto.
    Qed.

    Lemma inv_snoc_last L t h op :
      inv (L ++ [Build_ThreadEvent t (InvEv h op)]) (length L) (t, h) op.
    Proof. eexists. split; [apply nth_snoc_last | reflexivity]. Qed.

    Lemma res_snoc_last L t h op (r : Sig.ar op) :
      res (L ++ [Build_ThreadEvent t (ResEv h op r)]) (length L) (t, h) op r.
    Proof. eexists. split; [apply nth_snoc_last | reflexivity]. Qed.

    Lemma inv_not_res_ev L t h op' (r : Sig.ar op') i k op :
      inv (L ++ [Build_ThreadEvent t (ResEv h op' r)]) i k op -> inv L i k op.
    Proof.
      intros Hi. destruct (inv_snoc_inv _ _ _ _ _ Hi) as [H | [_ Heq]]; [exact H |].
      apply (f_equal (te_ev E)) in Heq. discriminate Heq.
    Qed.

    Lemma res_not_inv_ev L t h op' i k op (r : Sig.ar op) :
      res (L ++ [Build_ThreadEvent t (InvEv h op')]) i k op r -> res L i k op r.
    Proof.
      intros Hi. destruct (res_snoc_inv _ _ _ _ _ _ Hi) as [H | [_ Heq]]; [exact H |].
      apply (f_equal (te_ev E)) in Heq. discriminate Heq.
    Qed.

    Lemma wf_app_l (L L' : list (ThreadEvent E)) : PrefixView.wf (L ++ L') -> PrefixView.wf L.
    Proof.
      intros (H1 & H2 & H3). split; [| split].
      - intros i j k op op' Hi Hj. exact (H1 _ _ _ _ _ (inv_app_l _ L' _ _ _ Hi) (inv_app_l _ L' _ _ _ Hj)).
      - intros i j k op op' r r' Hi Hj. exact (H2 _ _ _ _ _ _ _ (res_app_l _ L' _ _ _ _ Hi) (res_app_l _ L' _ _ _ _ Hj)).
      - intros j k op r Hj. destruct (H3 _ _ _ _ (res_app_l _ L' _ _ _ _ Hj)) as (i & Hij & Hi).
        exists i. split; [exact Hij |]. apply (inv_app_lt _ L'); [pose proof (res_lt _ _ _ _ _ Hj); lia | exact Hi].
    Qed.
  End Index.

  (** ** Part 1: handle-linear underlays *)

  Section HLPath.
    Context {E : RelaxedSig.t}.

    Abbreviation inv L := (inv_at (@PrefixView.sel E) L).

    (** Along a path of a handle-linear LTS each key is invoked at most
        once, and no invoked key was used at the start of the path. *)
    Theorem hl_path_inv_unique (VE : LTS E) used :
      HandleLinear VE used ->
      forall σ T σ', vf_path VE σ T σ' ->
        (forall i k op, inv T i k op -> ~ used σ k) /\
        (forall i j k op op', inv T i k op -> inv T j k op' -> i = j).
    Proof.
      intros Hhl σ T σ' Hp.
      induction Hp as [σ | σ ev σ1 T σ2 Hs Hp IH]; [split; intros i; [intros k op (x & Hx & _) | intros j k op op' (x & Hx & _)]; destruct i; discriminate |].
      destruct IH as [IHu IHd]. split.
      - intros i k op Hi Hu. destruct (inv_cons_inv _ _ _ _ _ Hi) as [[_ ->] | (i' & _ & Hi')].
        + destruct k as [t h]. exact (hl_fresh _ _ Hhl t h op σ σ1 Hs Hu).
        + exact (IHu i' k op Hi' (hl_mono _ _ Hhl ev σ σ1 k Hs Hu)).
      - intros i j k op op' Hi Hj.
        destruct (inv_cons_inv _ _ _ _ _ Hi) as [[-> ->] | (i' & -> & Hi')];
          destruct (inv_cons_inv _ _ _ _ _ Hj) as [[-> Hev] | (j' & -> & Hj')].
        + reflexivity.
        + exfalso. destruct k as [t h]. apply (IHu j' (t, h) op' Hj'). exact (hl_inv_used _ _ Hhl t h op σ σ1 Hs).
        + exfalso. subst ev. destruct k as [t h]. apply (IHu i' (t, h) op Hi'). exact (hl_inv_used _ _ Hhl t h op' σ σ1 Hs).
        + f_equal. exact (IHd i' j' k op op' Hi' Hj').
    Qed.
  End HLPath.

  Section VTHL.
    Context {E : RelaxedSig.t} (nu : list (Op E) -> Prop).

    (** A key is used in a [VT] state when it is invoked in its trace. *)
    Definition vt_used (v : State (VT nu)) (k : CallKey E) : Prop :=
      exists i op, inv_at (@PrefixView.sel E) (v_trace (E := E) v) i k op.

    Theorem vt_handle_linear : HandleLinear (VT nu) vt_used.
    Proof.
      constructor.
      - intros t h op σ σ' Hs. cbn in Hs. inversion Hs as [ev L H H' Hst Hv]; subst.
        exists (length L), op. cbn. apply inv_snoc_last.
      - intros ev σ σ' k Hs (i & op & Hi). cbn in Hs. inversion Hs as [ev0 L H H' Hst Hv]; subst.
        exists i, op. cbn in Hi |- *. apply inv_app_l. exact Hi.
      - intros t h op σ σ' Hs (i & op' & Hi). cbn in Hs. inversion Hs as [ev L H H' Hst Hv]; subst.
        cbn in Hi. destruct Hv as (((Hw1 & _ & _) & _ & _) & _).
        pose proof (Hw1 i (length L) (t, h) op' op (inv_app_l _ _ _ _ _ Hi) (inv_snoc_last L t h op)) as Heq.
        pose proof (inv_lt _ _ _ _ Hi). lia.
    Qed.
  End VTHL.

  (** ** Part 2: effect-at-invocation specifications (M-17) *)

  Section EI.
    Context {F : RelaxedSig.t} {St : Type}.
    Context (δ : St -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> St -> Prop).

    Abbreviation inv L := (inv_at (@PrefixView.sel F) L).
    Abbreviation res L := (res_at (@PrefixView.sel F) L).

    Definition ei_step (ev : ThreadEvent F) (s s' : St * list (Op F)) : Prop :=
      match te_ev F ev with
      | InvEv h o =>
          exists r st', δ (fst s) o r st' /\ s' = (st', Build_Op (te_tid F ev, h) o r :: snd s)
      | ResEv h o r =>
          exists P1 P2, snd s = P1 ++ Build_Op (te_tid F ev, h) o r :: P2 /\ s' = (fst s, P1 ++ P2)
      end.

    Definition EI : LTS F :=
      {| State := (St * list (Op F))%type; Step := ei_step; Error := fun _ _ => False |}.

    (** The sequential specification: runs of [δ]. *)
    Inductive seq_run : St -> list (Op F) -> St -> Prop :=
    | seq_nil s : seq_run s [] s
    | seq_cons s o s1 W s2 :
        δ s (op_op o) (op_ret o) s1 -> seq_run s1 W s2 -> seq_run s (o :: W) s2.

    Definition seq_legal (s0 : St) (W : list (Op F)) : Prop := exists s, seq_run s0 W s.

    Lemma seq_run_snoc s0 W s o s' :
      seq_run s0 W s -> δ s (op_op o) (op_ret o) s' -> seq_run s0 (W ++ [o]) s'.
    Proof.
      induction 1 as [s | s o0 s1 W s2 Hd Hr IH]; intros Hd'; cbn.
      - econstructor; [exact Hd' | constructor].
      - econstructor; [exact Hd | apply IH; exact Hd'].
    Qed.

    Lemma before_snoc {A : Type} (W : list A) a b x : before W a b -> before (W ++ [x]) a b.
    Proof.
      intros (l1 & l2 & -> & Hb). exists l1, (l2 ++ [x]). rewrite <- app_assoc. cbn.
      split; [reflexivity | apply in_or_app; left; exact Hb].
    Qed.

    Lemma before_last {A : Type} (W : list A) a x : In a W -> before (W ++ [x]) a x.
    Proof.
      intros Ha. destruct (in_split _ _ Ha) as (l1 & l2 & ->). exists l1, (l2 ++ [x]).
      rewrite <- app_assoc. cbn. split; [reflexivity | apply in_or_app; right; left; reflexivity].
    Qed.

    Lemma vf_path_app_inv {G : RelaxedSig.t} (V : LTS G) v T1 T2 v'' :
      vf_path V v (T1 ++ T2) v'' -> exists v', vf_path V v T1 v' /\ vf_path V v' T2 v''.
    Proof.
      revert v. induction T1 as [| x T1 IH]; intros v Hp; cbn in Hp.
      - exists v. split; [constructor | exact Hp].
      - inversion Hp as [| ? ? v1 ? ? Hs Hp']; subst.
        destruct (IH v1 Hp') as (v' & H1 & H2). exists v'. split; [econstructor; eauto | exact H2].
    Qed.

    Lemma some_eq {A : Type} (x y : A) : Some x = Some y -> x = y.
    Proof. intros H. injection H. auto. Qed.

    Lemma nodup_key_eq (W : list (Op F)) o o' :
      NoDup (map op_key W) -> In o W -> In o' W -> op_key o = op_key o' -> o = o'.
    Proof.
      induction W as [| x W IH]; intros Hnd Ho Ho' Hk; [destruct Ho |].
      cbn in Hnd. inversion Hnd as [| ? ? Hnin Hnd']; subst.
      destruct Ho as [<- | Ho], Ho' as [<- | Ho'].
      - reflexivity.
      - exfalso. apply Hnin. rewrite Hk. apply in_map. exact Ho'.
      - exfalso. apply Hnin. rewrite <- Hk. apply in_map. exact Ho.
      - apply IH; assumption.
    Qed.

    Section Inv.
      Context (indep : relation (Sig.op (RelaxedSig.effect F))) (s0 : St).

      (** The invariant along a prefix [T] that ends in [(s, P)], with the
          witness [W] built so far: the operations invoked in [T], in
          invocation order, with the results computed at invocation. *)
      Record EInv (T : list (ThreadEvent F)) (s : St) (P : list (Op F)) (W : list (Op F)) : Prop := {
        ei_run : seq_run s0 W s;
        ei_nd : NoDup (map op_key W);
        ei_inv : forall o, In o W -> exists i, inv T i (op_key o) (op_op o);
        ei_cov : forall i k op, inv T i k op -> exists o, In o W /\ op_key o = k;
        ei_pend : forall x, In x P -> In x W /\ forall j op (r : Sig.ar op), ~ res T j (op_key x) op r;
        ei_ndP : NoDup (map op_key P);
        ei_res : forall j k op (r : Sig.ar op), res T j k op r -> In (Build_Op k op r) W;
        ei_ord : forall o o', In o W -> In o' W -> rhb (@PrefixView.sel F) T indep o o' -> before W o o'
      }.

      Lemma einv_nil : EInv [] s0 [] [].
      Proof.
        constructor.
        - constructor.
        - constructor.
        - intros o [].
        - intros i k op (x & Hx & _). destruct i; discriminate.
        - intros x [].
        - constructor.
        - intros j k op r (x & Hx & _). destruct j; discriminate.
        - intros o o' [].
      Qed.

      (** An invocation step. *)
      Lemma einv_inv T s P W t h op r s' :
        EInv T s P W -> PrefixView.wf (T ++ [Build_ThreadEvent t (InvEv h op)]) -> δ s op r s' ->
        EInv (T ++ [Build_ThreadEvent t (InvEv h op)]) s' (Build_Op (t, h) op r :: P) (W ++ [Build_Op (t, h) op r]).
      Proof.
        intros [Hrun Hnd Hinv Hcov Hpend HndP Hres Hord] Hwf Hd.
        set (T' := T ++ [Build_ThreadEvent t (InvEv h op)]).
        set (onew := Build_Op (t, h) op r).
        destruct Hwf as (Hw1 & Hw2 & Hw3).
        (* the new key is not invoked in [T] *)
        assert (Hfresh : forall i op', ~ inv T i (t, h) op').
        { intros i op' Hi. pose proof (Hw1 i (length T) (t, h) op' op (inv_app_l _ _ _ _ _ Hi) (inv_snoc_last T t h op)) as ->.
          pose proof (inv_lt _ _ _ _ Hi). lia. }
        assert (HnotW : forall o, In o W -> op_key o <> (t, h)).
        { intros o Ho Hk. destruct (Hinv o Ho) as (i & Hi). rewrite Hk in Hi. exact (Hfresh _ _ Hi). }
        (* the new key has no response in [T'] *)
        assert (Hnores : forall j op' (r' : Sig.ar op'), ~ res T' j (t, h) op' r').
        { intros j op' r' Hj. destruct (Hw3 _ _ _ _ Hj) as (i & Hij & Hi).
          pose proof (Hw1 i (length T) (t, h) op' op Hi (inv_snoc_last T t h op)) as ->.
          pose proof (res_lt _ _ _ _ _ Hj) as Hlt. unfold T' in Hlt. rewrite length_app in Hlt. cbn in Hlt. lia. }
        constructor.
        - exact (seq_run_snoc _ _ _ onew _ Hrun Hd).
        - rewrite map_app. apply NoDup_app; [exact Hnd | repeat constructor; intros [] |].
          intros k Hk [Hk' | []]. apply in_map_iff in Hk as (o & Hko & Ho). subst k.
          exact (HnotW o Ho (eq_sym Hk')).
        - intros o Ho. apply in_app_or in Ho. destruct Ho as [Ho | [<- | []]].
          + destruct (Hinv o Ho) as (i & Hi). exists i. apply inv_app_l. exact Hi.
          + exists (length T). apply inv_snoc_last.
        - intros i k op' Hi. destruct (inv_snoc_inv _ _ _ _ _ Hi) as [Hi' | [_ Heq]].
          + destruct (Hcov _ _ _ Hi') as (o & Ho & Hk). exists o. split; [apply in_or_app; left; exact Ho | exact Hk].
          + exists onew. split; [apply in_or_app; right; left; reflexivity |].
            cbn. destruct k as [tk hk]. cbn in Heq. injection Heq as -> -> _. reflexivity.
        - intros x [<- | Hx].
          + split; [apply in_or_app; right; left; reflexivity | exact Hnores].
          + destruct (Hpend x Hx) as [HxW Hxn]. split; [apply in_or_app; left; exact HxW |].
            intros j op' r' Hj. exact (Hxn j op' r' (res_not_inv_ev _ _ _ _ _ _ _ _ Hj)).
        - cbn. constructor; [| exact HndP]. intros Hin. apply in_map_iff in Hin as (x & Hxk & Hx).
          destruct (Hpend x Hx) as [HxW _]. exact (HnotW x HxW Hxk).
        - intros j k op' r' Hj. apply in_or_app. left. exact (Hres _ _ _ _ (res_not_inv_ev _ _ _ _ _ _ _ _ Hj)).
        - intros o o' Ho Ho' Hr.
          apply in_app_or in Ho, Ho'.
          destruct Ho' as [Ho' | [<- | []]].
          + (* [o'] is old, so its invocation is in [T] *)
            destruct Ho as [Ho | [<- | []]].
            * apply before_snoc. apply Hord; [exact Ho | exact Ho' |].
              destruct Hr as [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & Hn)].
              -- left. exists i, j.
                 destruct (inv_snoc_inv _ _ _ _ _ Hj) as [Hj' | [-> Heq]].
                 ++ split; [| split; [exact Hj' | exact Hij]].
                    apply (res_app_lt _ [Build_ThreadEvent t (InvEv h op)]); [pose proof (inv_lt _ _ _ _ Hj'); lia | exact Hi].
                 ++ exfalso. apply (HnotW o' Ho'). destruct (op_key o') as [tk hk]. cbn in Heq. injection Heq as -> -> _. reflexivity.
              -- right. split; [exact Ht |]. exists i, j.
                 destruct (inv_snoc_inv _ _ _ _ _ Hj) as [Hj' | [-> Heq]].
                 ++ split; [| split; [exact Hj' | split; [exact Hij | exact Hn]]].
                    apply (inv_app_lt _ [Build_ThreadEvent t (InvEv h op)]); [pose proof (inv_lt _ _ _ _ Hj'); lia | exact Hi].
                 ++ exfalso. apply (HnotW o' Ho'). destruct (op_key o') as [tk hk]. cbn in Heq. injection Heq as -> -> _. reflexivity.
            * (* [o] is the new operation: it has no [rhb] successor *)
              exfalso. destruct Hr as [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & Hn)].
              -- exact (Hnores _ _ _ Hi).
              -- pose proof (Hw1 i (length T) (t, h) op op Hi (inv_snoc_last T t h op)) as ->.
                 pose proof (inv_lt _ _ _ _ Hj) as Hlt. unfold T' in Hlt. rewrite length_app in Hlt. cbn in Hlt. lia.
          + destruct Ho as [Ho | [<- | []]].
            * apply before_last. exact Ho.
            * exfalso. destruct Hr as [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & Hn)].
              -- exact (Hnores _ _ _ Hi).
              -- pose proof (Hw1 i j (t, h) op op Hi Hj). lia.
      Qed.

      (** A response step. *)
      Lemma einv_res T s P1 P2 W t h op (r : Sig.ar op) :
        EInv T s (P1 ++ Build_Op (t, h) op r :: P2) W ->
        PrefixView.wf (T ++ [Build_ThreadEvent t (ResEv h op r)]) ->
        EInv (T ++ [Build_ThreadEvent t (ResEv h op r)]) s (P1 ++ P2) W.
      Proof.
        intros [Hrun Hnd Hinv Hcov Hpend HndP Hres Hord] Hwf.
        assert (HxP : In (Build_Op (t, h) op r) (P1 ++ Build_Op (t, h) op r :: P2))
          by (apply in_or_app; right; left; reflexivity).
        assert (Hkeys : forall x, In x (P1 ++ P2) -> op_key x <> (t, h)).
        { intros x Hx Hk. rewrite map_app in HndP. cbn in HndP.
          apply NoDup_remove_2 in HndP. apply HndP. rewrite <- map_app. rewrite <- Hk. apply in_map. exact Hx. }
        constructor.
        - exact Hrun.
        - exact Hnd.
        - intros o Ho. destruct (Hinv o Ho) as (i & Hi). exists i. apply inv_app_l. exact Hi.
        - intros i k op' Hi. exact (Hcov _ _ _ (inv_not_res_ev _ _ _ _ _ _ _ _ Hi)).
        - intros x Hx. assert (Hx' : In x (P1 ++ Build_Op (t, h) op r :: P2)).
          { apply in_app_or in Hx. apply in_or_app. destruct Hx; [left | right; right]; assumption. }
          destruct (Hpend x Hx') as [HxW Hxn]. split; [exact HxW |].
          intros j op' r' Hj. destruct (res_snoc_inv _ _ _ _ _ _ Hj) as [Hj' | [_ Heq]].
          + exact (Hxn _ _ _ Hj').
          + apply (Hkeys x Hx). destruct (op_key x) as [tk hk]. cbn in Heq. injection Heq as -> -> _. reflexivity.
        - rewrite map_app in HndP |- *. cbn in HndP. exact (NoDup_remove_1 _ _ _ HndP).
        - intros j k op' r' Hj. destruct (res_snoc_inv _ _ _ _ _ _ Hj) as [Hj' | [_ Heq]].
          + exact (Hres _ _ _ _ Hj').
          + destruct (Hpend _ HxP) as [HW _].
            assert (Hev : Build_ThreadEvent (fst k) (ResEv (snd k) op' r') = Build_ThreadEvent t (ResEv h op r))
              by exact (eq_sym Heq).
            pose (sel_op := fun ev : ThreadEvent F => match te_ev F ev with
                              | ResEv h0 o0 r0 => Some (Build_Op (te_tid F ev, h0) o0 r0)
                              | InvEv _ _ => None end).
            apply (f_equal sel_op) in Hev. cbn in Hev. apply some_eq in Hev.
            destruct k as [tk hk]. cbn in Hev. rewrite Hev. exact HW.
        - intros o o' Ho Ho' Hr. apply Hord; [exact Ho | exact Ho' |].
          destruct Hr as [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & Hn)].
          + left. exists i, j. pose proof (inv_not_res_ev _ _ _ _ _ _ _ _ Hj) as Hj'.
            split; [| split; [exact Hj' | exact Hij]].
            apply (res_app_lt _ [Build_ThreadEvent t (ResEv h op r)]); [pose proof (inv_lt _ _ _ _ Hj'); lia | exact Hi].
          + right. split; [exact Ht |]. exists i, j.
            split; [exact (inv_not_res_ev _ _ _ _ _ _ _ _ Hi) |].
            split; [exact (inv_not_res_ev _ _ _ _ _ _ _ _ Hj) |]. auto.
      Qed.

      Lemma einv_path T v :
        vf_path EI (s0, []) T v -> PrefixView.wf T -> exists W, EInv T (fst v) (snd v) W.
      Proof.
        revert v. induction T as [| ev T IH] using rev_ind; intros v Hp Hwf.
        - inversion Hp; subst. exists []. exact einv_nil.
        - destruct (vf_path_app_inv _ _ _ _ _ Hp) as (v1 & Hp1 & Hp2).
          inversion Hp2 as [| ? ? v2 ? ? Hs Hp3]; subst. inversion Hp3; subst.
          destruct (IH v1 Hp1 (wf_app_l _ _ Hwf)) as (W & HW).
          destruct v1 as [s P]. cbn in HW, Hs. destruct ev as [t [h op | h op r]]; cbn in Hs.
          + destruct Hs as (r & s' & Hd & ->). exists (W ++ [Build_Op (t, h) op r]).
            exact (einv_inv _ _ _ _ t h op r s' HW Hwf Hd).
          + destruct Hs as (P1 & P2 & -> & ->). exists W. exact (einv_res _ _ _ _ _ t h op r HW Hwf).
      Qed.

      Theorem ei_hvf_indep T v :
        vf_path EI (s0, []) T v -> PrefixView.wf T -> PrefixView.complete T ->
        rel_lin (@PrefixView.sel F) T indep (seq_legal s0).
      Proof.
        intros Hp Hwf Hc. destruct (einv_path T v Hp Hwf) as (W & [Hrun Hnd Hinv Hcov _ _ Hres Hord]).
        exists W. split; [exists (fst v); exact Hrun |]. split; [exact Hnd |]. split; [| split].
        - intros o Ho. destruct (Hinv o Ho) as (i & Hi). split; [exists i; exact Hi |].
          destruct (Hc _ _ _ Hi) as (j & r & Hj).
          pose proof (Hres _ _ _ _ Hj) as HW.
          assert (Heq : Build_Op (op_key o) (op_op o) r = o)
            by (apply (nodup_key_eq W); [exact Hnd | exact HW | exact Ho | reflexivity]).
          rewrite <- Heq. cbn. exists j. exact Hj.
        - exact Hcov.
        - exact Hord.
      Qed.
    End Inv.

    (** [HVF] of [RelaxedGSim.gsim_rel_lin] for [VF := EI δ]. *)
    Corollary ei_hvf (s0 : St) :
      forall T v, vf_path EI (s0, []) T v -> PrefixView.wf T -> PrefixView.complete T ->
        rel_lin (@PrefixView.sel F) T (semi_independent F) (seq_legal s0).
    Proof. intros T v. exact (ei_hvf_indep (semi_independent F) s0 T v). Qed.

    Corollary ei_sound_pres (s0 : St) : sound_pres (seq_legal s0) EI (s0, []).
    Proof. exact (ei_hvf s0). Qed.
  End EI.

  Arguments EI {F St} δ.
  Arguments seq_legal {F St} δ s0 W.
  Arguments seq_run {F St} δ _ _ _.

End RelaxedHoareSpec.
