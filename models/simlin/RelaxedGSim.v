(** * S1: a global forward simulation for RLHL, and its soundness

    Part 1 ([Transfer]): relaxed linearizability transfers from an abstract
    trace to a concrete trace along a possibility run.  A run
    ([ViewPossibility.PStep]) interleaves concrete events ([CEv]) with
    abstract invocations ([AInv]) and responses ([ARet]).  [TValid] asks,
    for every step, the order facts that RLHL possibilities maintain:

    - an abstract invocation follows the concrete one;
    - an abstract invocation follows the abstract invocation of every
      concretely earlier, dependent call of the same thread;
    - an abstract response follows its abstract invocation;
    - a concrete response follows the abstract one, with the same value.

    [transfer]: if the concrete trace is well formed and complete and the
    abstract responses are unique per key, every witness of the abstract
    trace is a witness of the concrete trace.  The reason is that every
    [rhb] edge of the concrete trace is an [rhb] edge of the abstract
    trace.

    Part 2 ([GSim]): a global forward simulation [GSimRel S] between the
    tagged module semantics ([module_step_tagged]) and the two-phase
    possibilities of [RelaxedPossibility].  The relation must match each
    overlay invocation by [poss_invoke], each underlay step by
    [poss_steps], and each overlay return by [poss_steps] followed by
    [poss_return] with the same result.  The record [RInv] is the
    invariant that links an execution to a [TValid] run whose abstract
    part is a path of the abstract LTS [VF].  [gsim_rel_lin] (and
    [GSim_rel_lin]) state the soundness result: a complete overlay trace
    of a simulated execution is relaxed-linearizable under one hypothesis
    on [VF], namely that every complete well-formed trace [VF] produces is
    relaxed-linearizable.

    Assumptions: none beyond [Eqdep.Eq_rect_eq.eq_rect_eq], which is
    inherited from [ResEvInversion] in the base library. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Relations.Relation_Definitions.
Require Import Stdlib.Relations.Relation_Operators.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedPossibility.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.view.PrefixView.
Require Import models.view.ViewPossibility.

Import ListNotations.

Module RelaxedGSim.
  Import LinCCALBase RelaxedSig RelaxedLTSSpec RelaxedTraceLin.
  Import ViewPossibility.
  Import RelaxedPossibility RelaxedModuleSemantics.

  (** ** List facts *)

  Lemma prefix_le {A : Type} (l r1 q1 a b : list A) :
    l = r1 ++ a -> l = q1 ++ b -> length q1 <= length r1 -> exists s, r1 = q1 ++ s.
  Proof.
    revert r1 q1 a b. induction l as [|x l IH]; intros r1 q1 a b H1 H2 Hle.
    - destruct q1; [exists r1; reflexivity | destruct q1; discriminate].
    - destruct q1 as [|y q1]; [exists r1; reflexivity|].
      destruct r1 as [|z r1]; [simpl in Hle; lia|].
      simpl in H1, H2. injection H1 as -> H1. injection H2 as <- H2.
      destruct (IH r1 q1 a b H1 H2 ltac:(simpl in Hle; lia)) as (s & ->). exists s. reflexivity.
  Qed.

  (** ** Part 1: transfer *)

  Section Transfer.
    Context {F : RelaxedSig.t}.
    Context (indep : relation (Sig.op (RelaxedSig.effect F))).

    Abbreviation inv L := (inv_at (@PrefixView.sel F) L).
    Abbreviation res L := (res_at (@PrefixView.sel F) L).
    Abbreviation run_t := (list (PStep F)).

    Definition tok (r1 : run_t) (st : PStep F) : Prop :=
      match st with
      | CEv e =>
          forall k m (r : Sig.ar m), e = Build_ThreadEvent (fst k) (ResEv (snd k) m r) ->
            exists b, res (abs r1) b k m r
      | AInv k m =>
          (exists i, inv (conc r1) i k m) /\
          (forall i j k' m', inv (conc r1) i k m -> inv (conc r1) j k' m' -> j < i ->
             fst k' = fst k -> ~ indep m' m -> exists a, inv (abs r1) a k' m')
      | ARet k m r => exists a, inv (abs r1) a k m
      end.

    Definition TValid (run : run_t) : Prop :=
      forall r1 st r2, run = r1 ++ st :: r2 -> tok r1 st.

    Definition AUniq (run : run_t) : Prop :=
      forall b b' k m m' (r : Sig.ar m) (r' : Sig.ar m'),
        res (abs run) b k m r -> res (abs run) b' k m' r' -> b = b'.

    Lemma conc_length_lt (run r1 q1 r2 q2 : run_t) x y :
      run = r1 ++ x :: r2 -> run = q1 ++ y :: q2 ->
      length (conc r1) < length (conc q1) -> exists s, q1 = r1 ++ x :: s.
    Proof.
      intros H1 H2 Hlt. destruct (Nat.le_gt_cases (length q1) (length r1)) as [Hle | Hgt].
      - exfalso. destruct (prefix_le run r1 q1 _ _ H1 H2 Hle) as (s & ->).
        rewrite conc_app, length_app in Hlt. lia.
      - destruct (prefix_le run q1 (r1 ++ [x]) (y :: q2) r2)
          as (s & Hs); [exact H2 | rewrite <- app_assoc; exact H1 | rewrite length_app; simpl; lia|].
        exists s. rewrite Hs, <- app_assoc. reflexivity.
    Qed.

    Lemma res_index (run r1 r2 : run_t) i k m (r : Sig.ar m) :
      PrefixView.wf (conc run) -> res (conc run) i k m r ->
      run = r1 ++ CEv (Build_ThreadEvent (fst k) (ResEv (snd k) m r)) :: r2 ->
      i = length (conc r1).
    Proof.
      intros Hwf Hi Hrun.
      assert (Hr : res (conc run) (length (conc r1)) k m r).
      { rewrite Hrun, conc_app. simpl. eexists. split; [|reflexivity].
        rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
      exact (proj1 (proj2 Hwf) _ _ _ _ _ _ _ Hi Hr).
    Qed.

    Lemma abs_inv_index (q1 q2 : run_t) k m :
      inv (abs (q1 ++ AInv k m :: q2)) (length (abs q1)) k m.
    Proof.
      rewrite abs_app. simpl. eexists. split; [|reflexivity].
      rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
    Qed.

    Theorem transfer (nu : list (Op F) -> Prop) run :
      TValid run -> PrefixView.wf (conc run) -> PrefixView.complete (conc run) -> AUniq run ->
      rel_lin (@PrefixView.sel F) (abs run) indep nu -> rel_lin (@PrefixView.sel F) (conc run) indep nu.
    Proof.
      intros HV Hwf Hc Hu (W & Hnu & Hnd & Hocc & Hcov & Hord).
      (* The abstract invocation of [k] follows its concrete invocation. *)
      assert (Hainv : forall a k m, inv (abs run) a k m ->
                exists q1 q2 i0, run = q1 ++ AInv k m :: q2 /\ inv (conc q1) i0 k m /\ tok q1 (AInv k m)).
      { intros a k m Ha. destruct (abs_inv_step _ _ _ _ Ha) as (q1 & q2 & Hrun).
        pose proof (HV q1 _ q2 Hrun) as Hok. destruct Hok as ((i0 & Hi0) & Hpo).
        exists q1, q2, i0. split; [exact Hrun|]. split; [exact Hi0|]. split; [exists i0; exact Hi0 | exact Hpo]. }
      (* A concrete response has the abstract response before it. *)
      assert (Hcres : forall j k m (r : Sig.ar m), res (conc run) j k m r ->
                exists r1 r2 b, run = r1 ++ CEv (Build_ThreadEvent (fst k) (ResEv (snd k) m r)) :: r2 /\
                                res (abs r1) b k m r).
      { intros j k m r Hj. destruct (conc_res_step _ _ _ _ _ Hj) as (r1 & r2 & Hrun).
        destruct (HV r1 _ r2 Hrun k m r eq_refl) as (b & Hb). exists r1, r2, b. auto. }
      exists W. split; [exact Hnu|]. split; [exact Hnd|]. split; [|split].
      - intros o Ho. destruct (Hocc o Ho) as [(a & Ha) (b & Hb)].
        destruct (Hainv _ _ _ Ha) as (q1 & q2 & i0 & Hrun & Hi0 & _).
        assert (Hi : inv (conc run) i0 (op_key o) (op_op o)) by (rewrite Hrun, conc_app; exact (inv_app_l _ _ _ _ _ Hi0)).
        split; [exists i0; exact Hi|].
        destruct (Hc _ _ _ Hi) as (j & r' & Hj).
        destruct (Hcres _ _ _ _ Hj) as (r1 & r2 & b' & Hrun' & Hb').
        assert (Hb'' : res (abs run) b' (op_key o) (op_op o) r') by (rewrite Hrun', abs_app; exact (res_app_l _ _ _ _ _ _ Hb')).
        pose proof (Hu _ _ _ _ _ _ _ Hb'' Hb) as ->.
        pose proof (PrefixView.res_ret _ _ _ _ _ _ Hb'' Hb) as ->. exists j. exact Hj.
      - intros i k m Hi. destruct (Hc _ _ _ Hi) as (j & r & Hj).
        destruct (Hcres _ _ _ _ Hj) as (r1 & r2 & b & Hrun & Hb).
        assert (Hb' : res (abs run) b k m r) by (rewrite Hrun, abs_app; exact (res_app_l _ _ _ _ _ _ Hb)).
        destruct (abs_res_step _ _ _ _ _ Hb') as (s1 & s2 & Hrun2).
        destruct (HV s1 _ s2 Hrun2) as (a & Ha).
        apply (Hcov a k m). rewrite Hrun2, abs_app. exact (inv_app_l _ _ _ _ _ Ha).
      - intros o o' Ho Ho' Hr. apply Hord; [exact Ho | exact Ho'|].
        destruct (Hocc o' Ho') as [(a' & Ha') _].
        destruct (Hainv _ _ _ Ha') as (q1 & q2 & i0 & Hrun & Hi0 & _ & Hpo).
        assert (Hi0' : inv (conc run) i0 (op_key o') (op_op o')) by (rewrite Hrun, conc_app; exact (inv_app_l _ _ _ _ _ Hi0)).
        pose proof (abs_inv_index q1 q2 (op_key o') (op_op o')) as Hai. rewrite <- Hrun in Hai.
        destruct Hr as [(i & j & Hi & Hj & Hij) | (Hth & i & j & Hi & Hj & Hij & Hn)].
        + (* real time *)
          pose proof (proj1 Hwf _ _ _ _ _ Hj Hi0') as ->.
          destruct (Hcres _ _ _ _ Hi) as (r1 & r2 & b & Hrun1 & Hb).
          pose proof (res_index _ _ _ _ _ _ _ Hwf Hi Hrun1) as ->.
          pose proof (inv_lt _ _ _ _ Hi0) as Hlt.
          destruct (conc_length_lt run r1 q1 r2 q2 _ _ Hrun1 Hrun ltac:(lia)) as (s & Hs).
          left. exists b, (length (abs q1)). split; [rewrite Hrun1, abs_app; exact (res_app_l _ _ _ _ _ _ Hb)|].
          split; [exact Hai|]. pose proof (res_lt _ _ _ _ _ Hb) as Hblt.
          rewrite Hs, abs_app, length_app. lia.
        + (* same thread, dependent *)
          pose proof (proj1 Hwf _ _ _ _ _ Hj Hi0') as ->.
          assert (Hiq : inv (conc q1) i (op_key o) (op_op o)).
          { apply (inv_app_lt _ (conc (AInv (op_key o') (op_op o') :: q2))).
            - pose proof (inv_lt _ _ _ _ Hi0). lia.
            - rewrite <- conc_app, <- Hrun. exact Hi. }
          destruct (Hpo _ _ _ _ Hi0 Hiq Hij Hth Hn) as (a & Ha).
          right. split; [exact Hth|]. exists a, (length (abs q1)).
          split; [rewrite Hrun, abs_app; exact (inv_app_l _ _ _ _ _ Ha)|].
          split; [exact Hai|]. split; [exact (inv_lt _ _ _ _ Ha) | exact Hn].
    Qed.
  End Transfer.

  (** ** Generic facts about events in lists *)

  Section Events.
    Context {F : RelaxedSig.t}.

    Abbreviation inv L := (inv_at (@PrefixView.sel F) L).
    Abbreviation res L := (res_at (@PrefixView.sel F) L).
    Abbreviation iev k m := (Build_ThreadEvent (fst k) (InvEv (snd k) m)).
    Abbreviation rev_ k m r := (Build_ThreadEvent (fst k) (ResEv (snd k) m r)).

    Lemma nth_snoc_cases {A : Type} (l : list A) a i x :
      nth_error (l ++ [a]) i = Some x -> nth_error l i = Some x \/ (i = length l /\ x = a).
    Proof.
      intros H. destruct (Nat.lt_ge_cases i (length l)) as [Hlt | Hge].
      - left. rewrite nth_error_app1 in H by exact Hlt. exact H.
      - right. rewrite nth_error_app2 in H by exact Hge.
        destruct (i - length l) as [|n] eqn:Hn; simpl in H.
        + injection H as <-. split; [lia | reflexivity].
        + destruct n; discriminate.
    Qed.

    Lemma inv_snoc (L : list (ThreadEvent F)) x i k m :
      inv (L ++ [x]) i k m -> inv L i k m \/ (i = length L /\ x = iev k m).
    Proof.
      intros (y & Hy & Hs). unfold PrefixView.sel in Hs. injection Hs as ->.
      apply nth_snoc_cases in Hy as [Hy | [-> ->]]; [left; eexists; split; [exact Hy | reflexivity] | right; auto].
    Qed.

    Lemma res_snoc (L : list (ThreadEvent F)) x j k m (r : Sig.ar m) :
      res (L ++ [x]) j k m r -> res L j k m r \/ (j = length L /\ x = rev_ k m r).
    Proof.
      intros (y & Hy & Hs). unfold PrefixView.sel in Hs. injection Hs as ->.
      apply nth_snoc_cases in Hy as [Hy | [-> ->]]; [left; eexists; split; [exact Hy | reflexivity] | right; auto].
    Qed.

    Lemma inv_snoc_new (L : list (ThreadEvent F)) k m : inv (L ++ [iev k m]) (length L) k m.
    Proof.
      eexists. split; [|reflexivity]. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
    Qed.

    Lemma res_snoc_new (L : list (ThreadEvent F)) k m r : res (L ++ [rev_ k m r]) (length L) k m r.
    Proof.
      eexists. split; [|reflexivity]. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
    Qed.

    Lemma inv_not_res (k k' : CallKey F) m m' (r : Sig.ar m') : iev k m <> rev_ k' m' r.
    Proof. intros H. apply (f_equal (te_ev F)) in H. discriminate. Qed.

    Lemma wf_snoc_inv (L : list (ThreadEvent F)) k m :
      PrefixView.wf L -> (forall i m', ~ inv L i k m') -> PrefixView.wf (L ++ [iev k m]).
    Proof.
      intros (H1 & H2 & H3) Hfresh. split; [|split].
      - intros i j k0 op op' Hi Hj.
        apply inv_snoc in Hi as [Hi | (-> & Hx)]; apply inv_snoc in Hj as [Hj | (-> & Hy)].
        + exact (H1 _ _ _ _ _ Hi Hj).
        + apply inv_ev_inj in Hy as [<- _]. exfalso. exact (Hfresh _ _ Hi).
        + apply inv_ev_inj in Hx as [<- _]. exfalso. exact (Hfresh _ _ Hj).
        + reflexivity.
      - intros i j k0 op op' r r' Hi Hj.
        apply res_snoc in Hi as [Hi | (_ & Hx)]; [|exfalso; exact (inv_not_res _ _ _ _ _ Hx)].
        apply res_snoc in Hj as [Hj | (_ & Hy)]; [|exfalso; exact (inv_not_res _ _ _ _ _ Hy)].
        exact (H2 _ _ _ _ _ _ _ Hi Hj).
      - intros j k0 op r Hj. apply res_snoc in Hj as [Hj | (_ & Hx)]; [|exfalso; exact (inv_not_res _ _ _ _ _ Hx)].
        destruct (H3 _ _ _ _ Hj) as (i & Hij & Hi). exists i. split; [exact Hij | exact (inv_app_l _ _ _ _ _ Hi)].
    Qed.

    Lemma wf_snoc_res (L : list (ThreadEvent F)) k m r :
      PrefixView.wf L -> (exists i, inv L i k m) -> (forall j m' (r' : Sig.ar m'), ~ res L j k m' r') ->
      PrefixView.wf (L ++ [rev_ k m r]).
    Proof.
      intros (H1 & H2 & H3) (i0 & Hi0) Hfresh. split; [|split].
      - intros i j k0 op op' Hi Hj.
        apply inv_snoc in Hi as [Hi | (_ & Hx)]; [|exfalso; exact (inv_not_res _ _ _ _ _ (eq_sym Hx))].
        apply inv_snoc in Hj as [Hj | (_ & Hy)]; [|exfalso; exact (inv_not_res _ _ _ _ _ (eq_sym Hy))].
        exact (H1 _ _ _ _ _ Hi Hj).
      - intros i j k0 op op' r1 r2 Hi Hj.
        apply res_snoc in Hi as [Hi | (-> & Hx)]; apply res_snoc in Hj as [Hj | (-> & Hy)].
        + exact (H2 _ _ _ _ _ _ _ Hi Hj).
        + apply res_ev_inj in Hy as [<- _]. exfalso. exact (Hfresh _ _ _ Hi).
        + apply res_ev_inj in Hx as [<- _]. exfalso. exact (Hfresh _ _ _ Hj).
        + reflexivity.
      - intros j k0 op r0 Hj. apply res_snoc in Hj as [Hj | (-> & Hx)].
        + destruct (H3 _ _ _ _ Hj) as (i & Hij & Hi). exists i. split; [lia | exact (inv_app_l _ _ _ _ _ Hi)].
        + pose proof (res_ev_inj _ _ _ _ _ _ Hx) as [<- <-]. exists i0.
          split; [exact (inv_lt _ _ _ _ Hi0) | exact (inv_app_l _ _ _ _ _ Hi0)].
    Qed.
  End Events.

  (** Removing an element other than [a] and [b] keeps [a] before [b]. *)
  Lemma before_remove {A : Type} (l1 l2 : list A) x a b :
    before (l1 ++ x :: l2) a b -> a <> x -> b <> x -> before (l1 ++ l2) a b.
  Proof.
    intros (pre & post & Heq & Hb) Hax Hbx.
    destruct (Nat.lt_total (length l1) (length pre)) as [Hlt | [Heq' | Hgt]].
    - destruct (prefix_le _ pre l1 (a :: post) (x :: l2) Heq eq_refl ltac:(lia)) as (s & Hs).
      destruct s as [|y s]; [rewrite app_nil_r in Hs; subst; lia|].
      subst pre. rewrite <- app_assoc in Heq. apply app_inv_head in Heq. simpl in Heq. injection Heq as <- Heq.
      exists (l1 ++ s), post. split; [rewrite Heq, <- app_assoc; reflexivity | exact Hb].
    - assert (l1 = pre).
      { destruct (prefix_le _ pre l1 (a :: post) (x :: l2) Heq eq_refl ltac:(lia)) as (s & Hs).
        destruct s; [rewrite app_nil_r in Hs; exact (eq_sym Hs) | subst; rewrite length_app in Heq'; simpl in Heq'; lia]. }
      subst. apply app_inv_head in Heq. injection Heq as <-. contradiction.
    - destruct (prefix_le _ l1 pre (x :: l2) (a :: post) eq_refl Heq ltac:(lia)) as (s & Hs).
      destruct s as [|y s]; [rewrite app_nil_r in Hs; subst; lia|].
      subst l1. rewrite <- app_assoc in Heq. apply app_inv_head in Heq. simpl in Heq. injection Heq as <- Heq.
      subst post. exists pre, (s ++ l2). split; [rewrite <- app_assoc; reflexivity|].
      apply in_app_or in Hb as [Hb | [Hb | Hb]]; [apply in_or_app; left; exact Hb | congruence | apply in_or_app; right; exact Hb].
  Qed.

  (** In a list without duplicate keys, a key occurs at one position. *)
  Lemma key_position {A K : Type} (f : A -> K) (l pre post pre' post' : list A) e e' :
    NoDup (map f l) -> l = pre ++ e :: post -> l = pre' ++ e' :: post' -> f e = f e' ->
    pre = pre' /\ e = e' /\ post = post'.
  Proof.
    intros Hnd H1 H2 Hk. subst l. revert pre' Hnd H2. induction pre as [|x pre IH]; intros pre' Hnd H2.
    - destruct pre' as [|y pre']; simpl in H2.
      + injection H2 as -> ->. auto.
      + injection H2 as -> H2. simpl in Hnd. apply NoDup_cons_iff in Hnd as [Hn _]. exfalso. apply Hn.
        rewrite Hk, H2, map_app. apply in_or_app. right. left. reflexivity.
    - destruct pre' as [|y pre']; simpl in H2.
      + injection H2 as -> H2. simpl in Hnd. apply NoDup_cons_iff in Hnd as [Hn _]. exfalso. apply Hn.
        rewrite <- Hk, map_app. apply in_or_app. right. left. reflexivity.
      + injection H2 as -> H2. simpl in Hnd. apply NoDup_cons_iff in Hnd as [_ Hnd].
        destruct (IH pre' Hnd H2) as (-> & -> & ->). auto.
  Qed.

  (** ** Part 2: the global simulation and its soundness *)

  Section GSim.
    Context {E F : RelaxedSig.t}.
    Context (VE : RelaxedLTSSpec.LTS E) (VF : RelaxedLTSSpec.LTS F).
    Context (M : RelaxedLang.RelaxedModuleImpl E F).

    Abbreviation inv L := (inv_at (@PrefixView.sel F) L).
    Abbreviation res L := (res_at (@PrefixView.sel F) L).
    Abbreviation Cfg := (@TaggedModuleConfig E F VE).
    Abbreviation iev k m := (Build_ThreadEvent (fst k) (InvEv (snd k) m)).
    Abbreviation rev_ k m r := (Build_ThreadEvent (fst k) (ResEv (snd k) m r)).

    (** The global simulation: every overlay invocation is matched by the
        abstract bookkeeping insertion; every underlay step by abstract
        linearization steps; every overlay return by abstract
        linearization steps followed by the abstract removal of the call in
        its linearized-return phase, with the same result. *)
    Definition gsim_step (S : Cfg -> Poss VF -> Prop) (c : Cfg) (p : Poss VF) : Prop :=
      (exists v pool, p = PossOk v pool) /\
      (forall t h op c',
         module_step_tagged VE M (OverlayEvent (Build_ThreadEvent t (@InvEv F h op))) c c' ->
         exists p', poss_invoke VF t h op p p' /\ S c' p') /\
      (forall ev c',
         module_step_tagged VE M (UnderlayEvent ev) c c' ->
         exists p', poss_steps VF p p' /\ S c' p') /\
      (forall t h op (ret : Sig.ar op) c',
         module_step_tagged VE M (OverlayEvent (Build_ThreadEvent t (@ResEv F h op ret))) c c' ->
         exists p' p'', poss_steps VF p p' /\ poss_return VF t h op ret p' p'' /\ S c' p'').

    Definition GSimRel (S : Cfg -> Poss VF -> Prop) : Prop :=
      forall c p, S c p -> gsim_step S c p.

    Definition GSim (c : Cfg) (p : Poss VF) : Prop := exists S, GSimRel S /\ S c p.

    (** *** Abstract runs *)

    Inductive prun : Poss VF -> list (PStep F) -> Poss VF -> Prop :=
    | prun_nil p : prun p [] p
    | prun_inv t h op v v' pool pool' rest p'' :
        lin_invoke_update t h op pool pool' ->
        RelaxedLTSSpec.Step VF (Build_ThreadEvent t (@InvEv F h op)) v v' ->
        prun (PossOk v' pool') rest p'' ->
        prun (PossOk v pool) (AInv (t, h) op :: rest) p''
    | prun_ret t h op (ret : Sig.ar op) v v' pool pool' rest p'' :
        lin_update (t, h) (ls_lini op) (ls_linr op ret) pool pool' ->
        RelaxedLTSSpec.Step VF (Build_ThreadEvent t (@ResEv F h op ret)) v v' ->
        prun (PossOk v' pool') rest p'' ->
        prun (PossOk v pool) (ARet (t, h) op ret :: rest) p''.

    Lemma prun_app p q r a b : prun p a q -> prun q b r -> prun p (a ++ b) r.
    Proof.
      induction 1; intros Hb; simpl; [exact Hb | eapply prun_inv; eauto | eapply prun_ret; eauto].
    Qed.

    Lemma poss_steps_prun p p' : poss_steps VF p p' -> p' <> PossError -> exists evs, prun p evs p'.
    Proof.
      induction 1 as [p p' Hs | p | p1 p2 p3 H12 IH12 H23 IH23]; intros Hne.
      - destruct Hs as (owner & Hs). destruct Hs as [t h op v v' pool pool' Hlin Hlts | t h op ret v v' pool pool' Hlin Hlts | | ];
          [| | contradiction | contradiction].
        + exists [AInv (t, h) op]. eapply prun_inv; [exact Hlin | exact Hlts | constructor].
        + exists [ARet (t, h) op ret]. eapply prun_ret; [exact Hlin | exact Hlts | constructor].
      - exists []. constructor.
      - destruct p2 as [v2 pool2 |]; [| apply poss_steps_from_error in H23; contradiction].
        destruct (IH12 ltac:(discriminate)) as (a & Ha). destruct (IH23 Hne) as (b & Hb).
        exists (a ++ b). exact (prun_app _ _ _ _ _ Ha Hb).
    Qed.

    Inductive vf_path : RelaxedLTSSpec.State VF -> list (ThreadEvent F) -> RelaxedLTSSpec.State VF -> Prop :=
    | vf_nil v : vf_path v [] v
    | vf_cons v ev v' evs v'' : RelaxedLTSSpec.Step VF ev v v' -> vf_path v' evs v'' -> vf_path v (ev :: evs) v''.

    Lemma vf_path_snoc v evs v' ev v'' :
      vf_path v evs v' -> RelaxedLTSSpec.Step VF ev v' v'' -> vf_path v (evs ++ [ev]) v''.
    Proof.
      induction 1; intros Hs; simpl; [econstructor; [exact Hs | constructor] | econstructor; eauto].
    Qed.

    Definition overlay_events (evs : list (ModuleEvent E F)) : list (ThreadEvent F) :=
      flat_map (fun ev => match ev with OverlayEvent e => [e] | UnderlayEvent _ => [] end) evs.

    (** *** Pools *)

    Lemma liu_split t h op (pool pool' : LinPool F) :
      lin_invoke_update t h op pool pool' ->
      exists pre older, pool = pre ++ make_lin_entry (t, h) (ls_inv op) :: older /\
        pool' = pre ++ make_lin_entry (t, h) (ls_lini op) :: older /\ invocation_ready t op older.
    Proof.
      induction 1 as [older Hready | entry pool pool' Hneq Hupd IH].
      - exists [], older. auto.
      - destruct IH as (pre & older & -> & -> & Hr). exists (entry :: pre), older. auto.
    Qed.

    Lemma lu_split k b a (pool pool' : LinPool F) :
      lin_update k b a pool pool' ->
      exists pre post, pool = pre ++ make_lin_entry k b :: post /\ pool' = pre ++ make_lin_entry k a :: post.
    Proof.
      induction 1 as [tail | entry pool pool' Hneq Hupd IH].
      - exists [], tail. auto.
      - destruct IH as (pre & post & -> & ->). exists (entry :: pre), post. auto.
    Qed.

    Lemma lr_split k st (pool pool' : LinPool F) :
      lin_remove k st pool pool' -> exists pre post, pool = pre ++ make_lin_entry k st :: post /\ pool' = pre ++ post.
    Proof.
      induction 1 as [tail | entry pool pool' Hneq Hrem IH].
      - exists [], tail. auto.
      - destruct IH as (pre & post & -> & ->). exists (entry :: pre), post. auto.
    Qed.

    Lemma split_in (pre post : LinPool F) (e x : LinEntry F) :
      NoDup (map (lin_key (F := F)) (pre ++ e :: post)) -> In x (pre ++ post) -> lin_key x <> lin_key e.
    Proof.
      intros Hnd Hin Hk. rewrite map_app in Hnd. simpl in Hnd.
      apply NoDup_remove_2 in Hnd. apply Hnd. rewrite <- Hk, <- map_app. apply in_map. exact Hin.
    Qed.

    Lemma in_swap (pre post : LinPool F) (e' x : LinEntry F) : In x (pre ++ e' :: post) -> x = e' \/ In x (pre ++ post).
    Proof.
      intros Hin. apply in_app_or in Hin as [Hin | [<- | Hin]]; [right; apply in_or_app; auto | left; reflexivity | right; apply in_or_app; auto].
    Qed.

    Lemma in_unswap (pre post : LinPool F) (e x : LinEntry F) : In x (pre ++ post) -> In x (pre ++ e :: post).
    Proof. intros Hin. apply in_app_or in Hin as [Hin | Hin]; apply in_or_app; [left | right; right]; exact Hin. Qed.

    Lemma entry_key (x : LinEntry F) : x = make_lin_entry (lin_key x) (lin_state F x).
    Proof. destruct x. reflexivity. Qed.

    Lemma make_entry_inj (k k' : CallKey F) s s' : make_lin_entry k s = make_lin_entry k' s' -> k = k' /\ s = s'.
    Proof.
      intros H. pose proof (f_equal (lin_key (F := F)) H) as Hk. rewrite !lin_key_make_lin_entry in Hk.
      split; [exact Hk|]. apply (f_equal (lin_state F)) in H. exact H.
    Qed.

    Lemma domain_split (pre post : LinPool F) (e : LinEntry F) : lin_domain (pre ++ e :: post) = lin_domain pre ++ lin_key e :: lin_domain post.
    Proof. unfold lin_domain. rewrite map_app. reflexivity. Qed.

    (** *** The invariant of a simulated execution *)

    Context (v0 : RelaxedLTSSpec.State VF).

    Lemma inv_op_unique (L : list (ThreadEvent F)) i i' k m m' :
      PrefixView.wf L -> inv L i k m -> inv L i' k m' -> m = m'.
    Proof.
      intros Hwf Hi Hi'. pose proof (proj1 Hwf _ _ _ _ _ Hi Hi') as <-.
      exact (proj2 (PrefixView.inv_det _ _ _ _ _ _ Hi Hi')).
    Qed.

    Lemma res_op_inv (L : list (ThreadEvent F)) j k m (r : Sig.ar m) i m' :
      PrefixView.wf L -> res L j k m r -> inv L i k m' -> m = m'.
    Proof.
      intros Hwf Hj Hi. destruct (proj2 (proj2 Hwf) _ _ _ _ Hj) as (i0 & _ & Hi0).
      exact (inv_op_unique _ _ _ _ _ _ Hwf Hi0 Hi).
    Qed.

    Record RInv (run : list (PStep F)) (calls : CallPool F) (v : RelaxedLTSSpec.State VF) (pool : LinPool F) : Prop := {
      ri_path : vf_path v0 (abs run) v;
      ri_pwf : lin_pool_well_formed pool;
      ri_linv : forall k m, lin_lookup k (ls_inv m) pool ->
        (exists i, inv (conc run) i k m) /\ (forall a m', ~ inv (abs run) a k m');
      ri_llini : forall k m, lin_lookup k (ls_lini m) pool ->
        (exists i, inv (conc run) i k m) /\ (exists a, inv (abs run) a k m) /\
        (forall b m' (r' : Sig.ar m'), ~ res (abs run) b k m' r');
      ri_llinr : forall k m (r : Sig.ar m), lin_lookup k (ls_linr m r) pool ->
        (exists i, inv (conc run) i k m) /\ (exists a, inv (abs run) a k m) /\ (exists b, res (abs run) b k m r);
      ri_status : forall i k m, inv (conc run) i k m ->
        In k (lin_domain pool) \/ exists j m' (r' : Sig.ar m'), res (conc run) j k m' r';
      ri_dead : forall j k m (r : Sig.ar m), res (conc run) j k m r ->
        ~ In k (lin_domain pool) /\ exists b, res (abs run) b k m r;
      ri_order : forall i1 i2 k1 k2 m1 m2, inv (conc run) i1 k1 m1 -> inv (conc run) i2 k2 m2 -> i1 < i2 ->
        In k1 (lin_domain pool) -> In k2 (lin_domain pool) -> before (lin_domain pool) k2 k1;
      ri_ainv : forall a k m, inv (abs run) a k m -> exists i, inv (conc run) i k m;
      ri_ares : forall b k m (r : Sig.ar m), res (abs run) b k m r -> exists a, a < b /\ inv (abs run) a k m;
      ri_auinv : forall a a' k m m', inv (abs run) a k m -> inv (abs run) a' k m' -> a = a';
      ri_aures : AUniq run;
      ri_valid : TValid (RelaxedSig.semi_independent F) run;
      ri_cwf : call_pool_well_formed calls;
      ri_cin : forall i k m, inv (conc run) i k m -> In k (map call_key calls);
      ri_cact : forall t h op (ret : Sig.ar op), In (Build_CallEntry t h (ActiveCall op ret)) calls ->
        (exists i, inv (conc run) i (t, h) op) /\ (forall j m' (r' : Sig.ar m'), ~ res (conc run) j (t, h) m' r');
      ri_cdead : forall t h, In (@Build_CallEntry F t h DeadCall) calls ->
        exists j m (r : Sig.ar m), res (conc run) j (t, h) m r;
      ri_lwf : PrefixView.wf (conc run);
    }.

    Lemma inv_nil i k m : ~ inv (@nil (ThreadEvent F)) i k m.
    Proof. intros (x & Hx & _). destruct i; discriminate. Qed.

    Lemma res_nil j k m (r : Sig.ar m) : ~ res (@nil (ThreadEvent F)) j k m r.
    Proof. intros (x & Hx & _). destruct j; discriminate. Qed.

    Lemma RInv_init : RInv [] [] v0 [].
    Proof.
      constructor; simpl.
      - constructor.
      - constructor.
      - intros k m [].
      - intros k m [].
      - intros k m r [].
      - intros i k m Hi. exfalso. exact (inv_nil _ _ _ Hi).
      - intros j k m r Hj. exfalso. exact (res_nil _ _ _ _ Hj).
      - intros i1 i2 k1 k2 m1 m2 Hi. exfalso. exact (inv_nil _ _ _ Hi).
      - intros a k m Ha. exfalso. exact (inv_nil _ _ _ Ha).
      - intros b k m r Hb. exfalso. exact (res_nil _ _ _ _ Hb).
      - intros a a' k m m' Ha. exfalso. exact (inv_nil _ _ _ Ha).
      - intros b b' k m m' r r' Hb. exfalso. exact (res_nil _ _ _ _ Hb).
      - intros r1 st r2 Heq. destruct r1; discriminate.
      - constructor.
      - intros i k m Hi. exfalso. exact (inv_nil _ _ _ Hi).
      - intros t h op ret [].
      - intros t h [].
      - split; [|split].
        + intros i j k op op' Hi. exfalso. exact (inv_nil _ _ _ Hi).
        + intros i j k op op' r r' Hi. exfalso. exact (res_nil _ _ _ _ Hi).
        + intros j k op r Hj. exfalso. exact (res_nil _ _ _ _ Hj).
    Qed.

    (** Entries of an updated pool. *)
    Lemma pool_other (pre post : LinPool F) e e' x :
      lin_pool_well_formed (pre ++ e :: post) -> In x (pre ++ e' :: post) ->
      x = e' \/ (In x (pre ++ e :: post) /\ lin_key x <> lin_key e).
    Proof.
      intros Hwf Hx. destruct (in_swap _ _ _ _ Hx) as [-> | Hx']; [left; reflexivity|].
      right. split; [exact (in_unswap _ _ _ _ Hx') | exact (split_in _ _ _ _ Hwf Hx')].
    Qed.

    Lemma TValid_snoc indep (run : list (PStep F)) st :
      TValid indep run -> tok indep run st -> TValid indep (run ++ [st]).
    Proof.
      intros HV Hok r1 st' r2 Heq. destruct r2 as [|x r2 _] using rev_ind.
      - apply app_inj_tail in Heq as [-> ->]. exact Hok.
      - apply (HV r1 st' r2). rewrite app_comm_cons, app_assoc in Heq.
        apply app_inj_tail in Heq as [-> _]. reflexivity.
    Qed.

    (** *** Preservation: an abstract invocation *)

    Lemma rinv_ainv run calls v pool t h op pool' v' :
      RInv run calls v pool -> lin_invoke_update t h op pool pool' ->
      RelaxedLTSSpec.Step VF (Build_ThreadEvent t (@InvEv F h op)) v v' ->
      RInv (run ++ [AInv (t, h) op]) calls v' pool'.
    Proof.
      intros HI Hupd Hst.
      destruct (liu_split _ _ _ _ _ Hupd) as (pre & older & Hp & Hp' & Hready).
      assert (HL : conc (run ++ [AInv (t, h) op]) = conc run) by (rewrite conc_app; simpl; apply app_nil_r).
      assert (HT : abs (run ++ [AInv (t, h) op]) = abs run ++ [iev (t, h) op]) by (rewrite abs_app; reflexivity).
      pose proof (ri_pwf _ _ _ _ HI) as Hpwf.
      assert (Hold : lin_lookup (t, h) (ls_inv op) pool) by (rewrite Hp; apply in_or_app; right; left; reflexivity).
      destruct (ri_linv _ _ _ _ HI _ _ Hold) as ((i0 & Hi0) & Hnoabs).
      assert (Hnores : forall b m' (r' : Sig.ar m'), ~ res (abs run) b (t, h) m' r').
      { intros b m' r' Hb. destruct (ri_ares _ _ _ _ HI _ _ _ _ Hb) as (a & _ & Ha). exact (Hnoabs _ _ Ha). }
      assert (Hdom : lin_domain pool' = lin_domain pool) by (rewrite Hp, Hp', !domain_split; reflexivity).
      assert (Hother : forall x, In x pool' -> x = make_lin_entry (t, h) (ls_lini op) \/
                (In x pool /\ lin_key x <> (t, h))).
      { intros x Hx. rewrite Hp' in Hx. rewrite Hp in Hpwf |- *.
        destruct (pool_other _ _ _ _ _ Hpwf Hx) as [-> | (Hx' & Hk)]; [left; reflexivity|].
        right. rewrite lin_key_make_lin_entry in Hk. auto. }
      assert (Hwf := ri_lwf _ _ _ _ HI).
      constructor; rewrite ?HL, ?HT.
      - exact (vf_path_snoc _ _ _ _ _ (ri_path _ _ _ _ HI) Hst).
      - exact (lin_invoke_update_well_formed _ _ _ _ _ Hupd Hpwf).
      - intros k m Hk. destruct (Hother _ Hk) as [Heq | (Hk' & Hne)].
        + apply make_entry_inj in Heq as [_ Heq]. discriminate.
        + rewrite lin_key_make_lin_entry in Hne.
          destruct (ri_linv _ _ _ _ HI _ _ Hk') as (Hc & Ha). split; [exact Hc|].
          intros a m' Ha'. apply inv_snoc in Ha' as [Ha' | (_ & Hx)]; [exact (Ha _ _ Ha')|].
          apply inv_ev_inj in Hx as [Hkk _]. exact (Hne (eq_sym Hkk)).
      - intros k m Hk. destruct (Hother _ Hk) as [Heq | (Hk' & Hne)].
        + apply make_entry_inj in Heq as [-> Heq]. injection Heq as ->.
          split; [exists i0; exact Hi0|]. split; [exists (length (abs run)); apply inv_snoc_new|].
          intros b m' r' Hb. apply res_snoc in Hb as [Hb | (_ & Hx)]; [exact (Hnores _ _ _ Hb)|].
          exact (inv_not_res _ _ _ _ _ Hx).
        + rewrite lin_key_make_lin_entry in Hne.
          destruct (ri_llini _ _ _ _ HI _ _ Hk') as (Hc & (a & Ha) & Hr). split; [exact Hc|].
          split; [exists a; exact (inv_app_l _ _ _ _ _ Ha)|].
          intros b m' r' Hb. apply res_snoc in Hb as [Hb | (_ & Hx)]; [exact (Hr _ _ _ Hb)|].
          exact (inv_not_res _ _ _ _ _ Hx).
      - intros k m r Hk. destruct (Hother _ Hk) as [Heq | (Hk' & Hne)].
        + apply make_entry_inj in Heq as [_ Heq]. discriminate.
        + destruct (ri_llinr _ _ _ _ HI _ _ _ Hk') as (Hc & (a & Ha) & (b & Hb)).
          split; [exact Hc|]. split; [exists a; exact (inv_app_l _ _ _ _ _ Ha)|].
          exists b. exact (res_app_l _ _ _ _ _ _ Hb).
      - intros i k m Hi. rewrite Hdom. exact (ri_status _ _ _ _ HI _ _ _ Hi).
      - intros j k m r Hj. rewrite Hdom. destruct (ri_dead _ _ _ _ HI _ _ _ _ Hj) as (Hn & b & Hb).
        split; [exact Hn|]. exists b. exact (res_app_l _ _ _ _ _ _ Hb).
      - intros i1 i2 k1 k2 m1 m2 H1 H2 H12. rewrite Hdom. exact (ri_order _ _ _ _ HI _ _ _ _ _ _ H1 H2 H12).
      - intros a k m Ha. apply inv_snoc in Ha as [Ha | (_ & Hx)]; [exact (ri_ainv _ _ _ _ HI _ _ _ Ha)|].
        apply inv_ev_inj in Hx as [<- <-]. exists i0. exact Hi0.
      - intros b k m r Hb. apply res_snoc in Hb as [Hb | (_ & Hx)]; [|exfalso; exact (inv_not_res _ _ _ _ _ Hx)].
        destruct (ri_ares _ _ _ _ HI _ _ _ _ Hb) as (a & Hab & Ha). exists a. split; [exact Hab | exact (inv_app_l _ _ _ _ _ Ha)].
      - intros a a' k m m' Ha Ha'.
        apply inv_snoc in Ha as [Ha | (-> & Hx)]; apply inv_snoc in Ha' as [Ha' | (-> & Hy)].
        + exact (ri_auinv _ _ _ _ HI _ _ _ _ _ Ha Ha').
        + apply inv_ev_inj in Hy as [<- _]. exfalso. exact (Hnoabs _ _ Ha).
        + apply inv_ev_inj in Hx as [<- _]. exfalso. exact (Hnoabs _ _ Ha').
        + reflexivity.
      - intros b b' k m m' r r' Hb Hb'. rewrite HT in Hb, Hb'.
        apply res_snoc in Hb as [Hb | (_ & Hx)]; [|exfalso; exact (inv_not_res _ _ _ _ _ Hx)].
        apply res_snoc in Hb' as [Hb' | (_ & Hy)]; [|exfalso; exact (inv_not_res _ _ _ _ _ Hy)].
        exact (ri_aures _ _ _ _ HI _ _ _ _ _ _ _ Hb Hb').
      - apply TValid_snoc; [exact (ri_valid _ _ _ _ HI)|]. split; [exists i0; exact Hi0|].
        intros i j k' m' Hi Hj Hji Hth Hn.
        pose proof (inv_op_unique _ _ _ _ _ _ Hwf Hi Hi0) as _.
        pose proof (proj1 Hwf _ _ _ _ _ Hi Hi0) as ->.
        destruct (ri_status _ _ _ _ HI _ _ _ Hj) as [Hlive | (j' & m'' & r'' & Hres)].
        + (* [k'] is live: it is older than [(t, h)] in the pool *)
          assert (Hin0 : In (t, h) (lin_domain pool)) by (rewrite Hp, domain_split; apply in_or_app; right; left; reflexivity).
          pose proof (ri_order _ _ _ _ HI _ _ _ _ _ _ Hj Hi0 Hji Hlive Hin0) as (l1 & l2 & Hl & Hk2).
          rewrite Hp, domain_split in Hl. rewrite lin_key_make_lin_entry in Hl.
          assert (Hnd : NoDup (lin_domain pool)) by exact Hpwf.
          rewrite Hp, domain_split in Hnd. rewrite lin_key_make_lin_entry in Hnd.
          assert (Hnd' : NoDup (map (fun x : CallKey F => x) (lin_domain pre ++ (t, h) :: lin_domain older)))
            by (rewrite map_id; exact Hnd).
          destruct (key_position (fun x => x) _ _ _ _ _ _ _ Hnd' eq_refl Hl eq_refl) as (_ & _ & Hpost).
          rewrite <- Hpost in Hk2. unfold lin_domain in Hk2. apply in_map_iff in Hk2 as (e' & Hke & He').
          unfold invocation_ready in Hready. rewrite Forall_forall in Hready. specialize (Hready e' He').
          assert (He'p : In e' pool) by (rewrite Hp; apply in_or_app; right; right; exact He').
          rewrite (entry_key e') in He'p. rewrite Hke in He'p.
          destruct Hready as [Htid | Hst'].
          * exfalso. apply Htid. rewrite <- Hke in Hth. unfold lin_key in Hth. simpl in Hth. exact Hth.
          * destruct (lin_state F e') as [om | om | om orr] eqn:Hs.
            -- exfalso. destruct (ri_linv _ _ _ _ HI _ _ He'p) as ((i' & Hi') & _).
               pose proof (inv_op_unique _ _ _ _ _ _ Hwf Hi' Hj) as ->. exact (Hn Hst').
            -- destruct (ri_llini _ _ _ _ HI _ _ He'p) as ((i' & Hi') & (a & Ha) & _).
               pose proof (inv_op_unique _ _ _ _ _ _ Hwf Hi' Hj) as ->. exists a. exact Ha.
            -- destruct (ri_llinr _ _ _ _ HI _ _ _ He'p) as ((i' & Hi') & (a & Ha) & _).
               pose proof (inv_op_unique _ _ _ _ _ _ Hwf Hi' Hj) as ->. exists a. exact Ha.
        + (* [k'] has responded: its abstract response, hence its abstract invocation, exists *)
          destruct (ri_dead _ _ _ _ HI _ _ _ _ Hres) as (_ & b & Hb).
          destruct (ri_ares _ _ _ _ HI _ _ _ _ Hb) as (a & _ & Ha).
          pose proof (res_op_inv _ _ _ _ _ _ _ Hwf Hres Hj) as ->. exists a. exact Ha.
      - exact (ri_cwf _ _ _ _ HI).
      - exact (ri_cin _ _ _ _ HI).
      - exact (ri_cact _ _ _ _ HI).
      - exact (ri_cdead _ _ _ _ HI).
      - exact Hwf.
    Qed.

    (** *** Preservation: an abstract response *)

    Lemma linr_event (k : CallKey F) m (r : Sig.ar m) m' (r' : Sig.ar m') :
      ls_linr m r = ls_linr m' r' -> m = m' /\ rev_ k m r = rev_ k m' r'.
    Proof.
      intros Heq. split.
      - apply (f_equal (fun s : LinState F => match s with ls_linr m0 _ => Some m0 | _ => None end)) in Heq.
        injection Heq as ->. reflexivity.
      - apply (f_equal (fun s : LinState F => match s with
                                             | ls_linr m0 r0 => rev_ k m0 r0
                                             | _ => rev_ k m r end)) in Heq.
        exact Heq.
    Qed.

    Lemma rinv_aret run calls v pool t h op (ret : Sig.ar op) pool' v' :
      RInv run calls v pool -> lin_update (t, h) (ls_lini op) (ls_linr op ret) pool pool' ->
      RelaxedLTSSpec.Step VF (Build_ThreadEvent t (@ResEv F h op ret)) v v' ->
      RInv (run ++ [ARet (t, h) op ret]) calls v' pool'.
    Proof.
      intros HI Hupd Hst.
      destruct (lu_split _ _ _ _ _ Hupd) as (pre & post & Hp & Hp').
      assert (HL : conc (run ++ [ARet (t, h) op ret]) = conc run) by (rewrite conc_app; simpl; apply app_nil_r).
      assert (HT : abs (run ++ [ARet (t, h) op ret]) = abs run ++ [rev_ (t, h) op ret]) by (rewrite abs_app; reflexivity).
      pose proof (ri_pwf _ _ _ _ HI) as Hpwf.
      assert (Hold : lin_lookup (t, h) (ls_lini op) pool) by (rewrite Hp; apply in_or_app; right; left; reflexivity).
      destruct (ri_llini _ _ _ _ HI _ _ Hold) as ((i0 & Hi0) & (a0 & Ha0) & Hnores).
      assert (Hdom : lin_domain pool' = lin_domain pool) by (rewrite Hp, Hp', !domain_split; reflexivity).
      assert (Hother : forall x, In x pool' -> x = make_lin_entry (t, h) (ls_linr op ret) \/
                (In x pool /\ lin_key x <> (t, h))).
      { intros x Hx. rewrite Hp' in Hx. rewrite Hp in Hpwf |- *.
        destruct (pool_other _ _ _ _ _ Hpwf Hx) as [-> | (Hx' & Hk)]; [left; reflexivity|].
        right. rewrite lin_key_make_lin_entry in Hk. auto. }
      assert (Hwf := ri_lwf _ _ _ _ HI).
      constructor; rewrite ?HL, ?HT.
      - exact (vf_path_snoc _ _ _ _ _ (ri_path _ _ _ _ HI) Hst).
      - exact (lin_update_well_formed _ _ _ _ _ Hupd Hpwf).
      - intros k m Hk. destruct (Hother _ Hk) as [Heq | (Hk' & Hne)].
        + apply make_entry_inj in Heq as [_ Heq]. discriminate.
        + destruct (ri_linv _ _ _ _ HI _ _ Hk') as (Hc & Ha). split; [exact Hc|].
          intros a m' Ha'. apply inv_snoc in Ha' as [Ha' | (_ & Hx)]; [exact (Ha _ _ Ha')|].
          exact (inv_not_res _ _ _ _ _ (eq_sym Hx)).
      - intros k m Hk. destruct (Hother _ Hk) as [Heq | (Hk' & Hne)].
        + apply make_entry_inj in Heq as [_ Heq]. discriminate.
        + rewrite lin_key_make_lin_entry in Hne.
          destruct (ri_llini _ _ _ _ HI _ _ Hk') as (Hc & (a & Ha) & Hr). split; [exact Hc|].
          split; [exists a; exact (inv_app_l _ _ _ _ _ Ha)|].
          intros b m' r' Hb. apply res_snoc in Hb as [Hb | (_ & Hx)]; [exact (Hr _ _ _ Hb)|].
          apply res_ev_inj in Hx as [Hkk _]. exact (Hne (eq_sym Hkk)).
      - intros k m r Hk. destruct (Hother _ Hk) as [Heq | (Hk' & Hne)].
        + apply make_entry_inj in Heq as [-> Heq]. destruct (linr_event (t, h) _ _ _ _ Heq) as [-> Hev].
          split; [exists i0; exact Hi0|]. split; [exists a0; exact (inv_app_l _ _ _ _ _ Ha0)|].
          exists (length (abs run)). rewrite <- Hev. apply res_snoc_new.
        + destruct (ri_llinr _ _ _ _ HI _ _ _ Hk') as (Hc & (a & Ha) & (b & Hb)).
          split; [exact Hc|]. split; [exists a; exact (inv_app_l _ _ _ _ _ Ha)|].
          exists b. exact (res_app_l _ _ _ _ _ _ Hb).
      - intros i k m Hi. rewrite Hdom. exact (ri_status _ _ _ _ HI _ _ _ Hi).
      - intros j k m r Hj. rewrite Hdom. destruct (ri_dead _ _ _ _ HI _ _ _ _ Hj) as (Hn & b & Hb).
        split; [exact Hn|]. exists b. exact (res_app_l _ _ _ _ _ _ Hb).
      - intros i1 i2 k1 k2 m1 m2 H1 H2 H12. rewrite Hdom. exact (ri_order _ _ _ _ HI _ _ _ _ _ _ H1 H2 H12).
      - intros a k m Ha. apply inv_snoc in Ha as [Ha | (_ & Hx)]; [exact (ri_ainv _ _ _ _ HI _ _ _ Ha)|].
        exfalso. exact (inv_not_res _ _ _ _ _ (eq_sym Hx)).
      - intros b k m r Hb. apply res_snoc in Hb as [Hb | (-> & Hx)].
        + destruct (ri_ares _ _ _ _ HI _ _ _ _ Hb) as (a & Hab & Ha). exists a. split; [exact Hab | exact (inv_app_l _ _ _ _ _ Ha)].
        + pose proof (res_ev_inj _ _ _ _ _ _ Hx) as [<- <-]. exists a0.
          split; [exact (inv_lt _ _ _ _ Ha0) | exact (inv_app_l _ _ _ _ _ Ha0)].
      - intros a a' k m m' Ha Ha'.
        apply inv_snoc in Ha as [Ha | (_ & Hx)]; [|exfalso; exact (inv_not_res _ _ _ _ _ (eq_sym Hx))].
        apply inv_snoc in Ha' as [Ha' | (_ & Hy)]; [|exfalso; exact (inv_not_res _ _ _ _ _ (eq_sym Hy))].
        exact (ri_auinv _ _ _ _ HI _ _ _ _ _ Ha Ha').
      - intros b b' k m m' r r' Hb Hb'. rewrite HT in Hb, Hb'.
        apply res_snoc in Hb as [Hb | (-> & Hx)]; apply res_snoc in Hb' as [Hb' | (-> & Hy)].
        + exact (ri_aures _ _ _ _ HI _ _ _ _ _ _ _ Hb Hb').
        + apply res_ev_inj in Hy as [<- _]. exfalso. exact (Hnores _ _ _ Hb).
        + apply res_ev_inj in Hx as [<- _]. exfalso. exact (Hnores _ _ _ Hb').
        + reflexivity.
      - apply TValid_snoc; [exact (ri_valid _ _ _ _ HI)|]. exists a0. exact Ha0.
      - exact (ri_cwf _ _ _ _ HI).
      - exact (ri_cin _ _ _ _ HI).
      - exact (ri_cact _ _ _ _ HI).
      - exact (ri_cdead _ _ _ _ HI).
      - exact Hwf.
    Qed.

    Lemma rinv_prun run calls v pool evs p :
      RInv run calls v pool -> prun (PossOk v pool) evs p ->
      exists v' pool', p = PossOk v' pool' /\ RInv (run ++ evs) calls v' pool' /\ conc evs = [].
    Proof.
      intros HI Hp. remember (PossOk v pool) as p0 eqn:Hp0. revert run v pool HI Hp0.
      induction Hp as [p | t h op v1 v1' pool1 pool1' rest p'' Hupd Hst Hrest IH
                         | t h op ret v1 v1' pool1 pool1' rest p'' Hupd Hst Hrest IH];
        intros run v pool HI Hp0.
      - subst. exists v, pool. split; [reflexivity|]. rewrite app_nil_r. auto.
      - injection Hp0 as -> ->.
        destruct (IH (run ++ [AInv (t, h) op]) v1' pool1' (rinv_ainv _ _ _ _ _ _ _ _ _ HI Hupd Hst) eq_refl)
          as (v' & pool' & -> & HI' & Hc).
        exists v', pool'. split; [reflexivity|]. rewrite <- app_assoc in HI'. split; [exact HI'|]. exact Hc.
      - injection Hp0 as -> ->.
        destruct (IH (run ++ [ARet (t, h) op ret]) v1' pool1' (rinv_aret _ _ _ _ _ _ _ _ _ _ HI Hupd Hst) eq_refl)
          as (v' & pool' & -> & HI' & Hc).
        exists v', pool'. split; [reflexivity|]. rewrite <- app_assoc in HI'. split; [exact HI'|]. exact Hc.
    Qed.

    (** *** Preservation: a concrete overlay invocation *)

    Lemma rinv_cinv run calls v pool t h op (ret : Sig.ar op) :
      RInv run calls v pool -> call_fresh (t, h) calls -> lin_fresh (t, h) pool ->
      RInv (run ++ [CEv (iev (t, h) op)]) (Build_CallEntry t h (ActiveCall op ret) :: calls) v
           (make_lin_entry (t, h) (ls_inv op) :: pool).
    Proof.
      intros HI Hcf Hlf.
      assert (HL : conc (run ++ [CEv (iev (t, h) op)]) = conc run ++ [iev (t, h) op]) by (rewrite conc_app; reflexivity).
      assert (HT : abs (run ++ [CEv (iev (t, h) op)]) = abs run) by (rewrite abs_app; simpl; apply app_nil_r).
      assert (Hwf := ri_lwf _ _ _ _ HI).
      assert (Hnoc : forall i m', ~ inv (conc run) i (t, h) m').
      { intros i m' Hi. apply Hcf. exact (ri_cin _ _ _ _ HI _ _ _ Hi). }
      assert (Hnor : forall j m' (r' : Sig.ar m'), ~ res (conc run) j (t, h) m' r').
      { intros j m' r' Hj. destruct (proj2 (proj2 Hwf) _ _ _ _ Hj) as (i & _ & Hi). exact (Hnoc _ _ Hi). }
      assert (Hnoa : forall a m', ~ inv (abs run) a (t, h) m').
      { intros a m' Ha. destruct (ri_ainv _ _ _ _ HI _ _ _ Ha) as (i & Hi). exact (Hnoc _ _ Hi). }
      (* An invocation of the extended concrete trace. *)
      assert (Hinv : forall i k m, inv (conc run ++ [iev (t, h) op]) i k m ->
                inv (conc run) i k m \/ (i = length (conc run) /\ k = (t, h) /\ m = op)).
      { intros i k m Hi. apply inv_snoc in Hi as [Hi | (-> & Hx)]; [left; exact Hi|].
        apply inv_ev_inj in Hx as [<- <-]. right. auto. }
      assert (Hres : forall j k m (r : Sig.ar m), res (conc run ++ [iev (t, h) op]) j k m r -> res (conc run) j k m r).
      { intros j k m r Hj. apply res_snoc in Hj as [Hj | (_ & Hx)]; [exact Hj|].
        exfalso. exact (inv_not_res _ _ _ _ _ Hx). }
      assert (Hpool : forall x, In x (make_lin_entry (t, h) (ls_inv op) :: pool) ->
                x = make_lin_entry (t, h) (ls_inv op) \/ (In x pool /\ lin_key x <> (t, h))).
      { intros x [<- | Hx]; [left; reflexivity | right; split; [exact Hx|]].
        intros Hk. apply Hlf. rewrite <- Hk. apply in_map. exact Hx. }
      constructor; rewrite ?HL, ?HT.
      - exact (ri_path _ _ _ _ HI).
      - unfold lin_pool_well_formed, lin_domain. simpl. rewrite lin_key_make_lin_entry.
        constructor; [exact Hlf | exact (ri_pwf _ _ _ _ HI)].
      - intros k m Hk. destruct (Hpool _ Hk) as [Heq | (Hk' & Hne)].
        + apply make_entry_inj in Heq as [-> Heq]. injection Heq as ->.
          split; [exists (length (conc run)); apply inv_snoc_new | exact Hnoa].
        + destruct (ri_linv _ _ _ _ HI _ _ Hk') as ((i & Hi) & Ha).
          split; [exists i; exact (inv_app_l _ _ _ _ _ Hi) | exact Ha].
      - intros k m Hk. destruct (Hpool _ Hk) as [Heq | (Hk' & Hne)].
        + apply make_entry_inj in Heq as [_ Heq]. discriminate.
        + destruct (ri_llini _ _ _ _ HI _ _ Hk') as ((i & Hi) & Ha & Hr).
          split; [exists i; exact (inv_app_l _ _ _ _ _ Hi)|]. auto.
      - intros k m r Hk. destruct (Hpool _ Hk) as [Heq | (Hk' & Hne)].
        + apply make_entry_inj in Heq as [_ Heq]. discriminate.
        + destruct (ri_llinr _ _ _ _ HI _ _ _ Hk') as ((i & Hi) & Ha & Hr).
          split; [exists i; exact (inv_app_l _ _ _ _ _ Hi)|]. auto.
      - intros i k m Hi. destruct (Hinv _ _ _ Hi) as [Hi' | (_ & -> & _)].
        + destruct (ri_status _ _ _ _ HI _ _ _ Hi') as [Hd | (j & m' & r' & Hj)].
          * left. right. exact Hd.
          * right. exists j, m', r'. exact (res_app_l _ _ _ _ _ _ Hj).
        + left. left. apply lin_key_make_lin_entry.
      - intros j k m r Hj. apply Hres in Hj. destruct (ri_dead _ _ _ _ HI _ _ _ _ Hj) as (Hn & Hb).
        split; [|exact Hb]. intros [Hk | Hk]; [|exact (Hn Hk)].
        rewrite lin_key_make_lin_entry in Hk. subst k. exact (Hnor _ _ _ Hj).
      - intros i1 i2 k1 k2 m1 m2 H1 H2 H12 Hd1 Hd2.
        destruct (Hinv _ _ _ H1) as [H1' | (-> & -> & ->)]; destruct (Hinv _ _ _ H2) as [H2' | (-> & -> & ->)].
        + simpl in Hd1, Hd2. rewrite lin_key_make_lin_entry in Hd1, Hd2.
          destruct Hd1 as [<- | Hd1]; [exfalso; exact (Hnoc _ _ H1')|].
          destruct Hd2 as [<- | Hd2]; [exfalso; exact (Hnoc _ _ H2')|].
          destruct (ri_order _ _ _ _ HI _ _ _ _ _ _ H1' H2' H12 Hd1 Hd2) as (l1 & l2 & Hl & Hin).
          exists (lin_key (make_lin_entry (t, h) (ls_inv op)) :: l1), l2.
          split; [simpl; rewrite Hl; reflexivity | exact Hin].
        + simpl in Hd1. rewrite lin_key_make_lin_entry in Hd1.
          destruct Hd1 as [<- | Hd1]; [exfalso; exact (Hnoc _ _ H1')|].
          exists [], (lin_domain pool). split; [simpl; rewrite lin_key_make_lin_entry; reflexivity | exact Hd1].
        + exfalso. pose proof (inv_lt _ _ _ _ H2'). lia.
        + lia.
      - intros a k m Ha. destruct (ri_ainv _ _ _ _ HI _ _ _ Ha) as (i & Hi).
        exists i. exact (inv_app_l _ _ _ _ _ Hi).
      - exact (ri_ares _ _ _ _ HI).
      - exact (ri_auinv _ _ _ _ HI).
      - intros b b' k m m' r r' Hb Hb'. rewrite HT in Hb, Hb'. exact (ri_aures _ _ _ _ HI _ _ _ _ _ _ _ Hb Hb').
      - apply TValid_snoc; [exact (ri_valid _ _ _ _ HI)|].
        intros k m r Heq. exfalso. exact (inv_not_res _ _ _ _ _ Heq).
      - unfold call_pool_well_formed. simpl. constructor; [exact Hcf | exact (ri_cwf _ _ _ _ HI)].
      - intros i k m Hi. destruct (Hinv _ _ _ Hi) as [Hi' | (_ & -> & _)].
        + right. exact (ri_cin _ _ _ _ HI _ _ _ Hi').
        + left. reflexivity.
      - intros t' h' op' ret' [Heq | Hin].
        + injection Heq as -> -> Hop. subst op'.
          split; [exists (length (conc run)); apply inv_snoc_new|].
          intros j m' r' Hj. exact (Hnor _ _ _ (Hres _ _ _ _ Hj)).
        + destruct (ri_cact _ _ _ _ HI _ _ _ _ Hin) as ((i & Hi) & Hn).
          split; [exists i; exact (inv_app_l _ _ _ _ _ Hi)|].
          intros j m' r' Hj. exact (Hn _ _ _ (Hres _ _ _ _ Hj)).
      - intros t' h' [Heq | Hin]; [discriminate|].
        destruct (ri_cdead _ _ _ _ HI _ _ Hin) as (j & m & r & Hj).
        exists j, m, r. exact (res_app_l _ _ _ _ _ _ Hj).
      - exact (wf_snoc_inv _ _ _ Hwf Hnoc).
    Qed.
    (** *** Preservation: a concrete overlay return *)

    Lemma res_transport (L : list (ThreadEvent F)) j k m (r : Sig.ar m) k' m' (r' : Sig.ar m') :
      rev_ k m r = rev_ k' m' r' -> res L j k m r -> res L j k' m' r'.
    Proof. intros Heq (y & Hy & Hs). exists y. split; [exact Hy|]. rewrite Hs, Heq. reflexivity. Qed.

    Lemma finish_src t h op (ret : Sig.ar op) (calls calls' : CallPool F) :
      finish_call t h op ret calls calls' -> In (Build_CallEntry t h (ActiveCall op ret)) calls.
    Proof. induction 1; [left; reflexivity | right; exact IHfinish_call]. Qed.

    Lemma finish_tgt t h op (ret : Sig.ar op) (calls calls' : CallPool F) :
      finish_call t h op ret calls calls' -> In (@Build_CallEntry F t h DeadCall) calls'.
    Proof. induction 1; [left; reflexivity | right; exact IHfinish_call]. Qed.

    Lemma finish_back t h op (ret : Sig.ar op) (calls calls' : CallPool F) e :
      finish_call t h op ret calls calls' -> In e calls' -> In e calls \/ e = Build_CallEntry t h DeadCall.
    Proof.
      induction 1 as [tail | t' h' cell pool pool' Hneq Hf IH]; intros [<- | Hin].
      - right. reflexivity.
      - left. right. exact Hin.
      - left. left. reflexivity.
      - destruct (IH Hin) as [H | H]; [left; right; exact H | right; exact H].
    Qed.

    Lemma rinv_cret run calls calls' v pool pool' t h op (ret : Sig.ar op) :
      RInv run calls v pool -> finish_call t h op ret calls calls' ->
      lin_remove (t, h) (ls_linr op ret) pool pool' ->
      RInv (run ++ [CEv (rev_ (t, h) op ret)]) calls' v pool'.
    Proof.
      intros HI Hfin Hrem.
      destruct (lr_split _ _ _ _ Hrem) as (pre & post & Hp & Hp').
      assert (HL : conc (run ++ [CEv (rev_ (t, h) op ret)]) = conc run ++ [rev_ (t, h) op ret])
        by (rewrite conc_app; reflexivity).
      assert (HT : abs (run ++ [CEv (rev_ (t, h) op ret)]) = abs run) by (rewrite abs_app; simpl; apply app_nil_r).
      pose proof (ri_pwf _ _ _ _ HI) as Hpwf.
      assert (Hwf := ri_lwf _ _ _ _ HI).
      assert (Hold : lin_lookup (t, h) (ls_linr op ret) pool) by (rewrite Hp; apply in_or_app; right; left; reflexivity).
      destruct (ri_llinr _ _ _ _ HI _ _ _ Hold) as ((i0 & Hi0) & (a0 & Ha0) & (b0 & Hb0)).
      destruct (ri_cact _ _ _ _ HI _ _ _ _ (finish_src _ _ _ _ _ _ Hfin)) as (_ & Hnor).
      assert (Hpool' : forall x, In x pool' -> In x pool /\ lin_key x <> (t, h)).
      { intros x Hx. rewrite Hp' in Hx. rewrite Hp in Hpwf |- *. split; [exact (in_unswap _ _ _ _ Hx)|].
        pose proof (split_in _ _ _ _ Hpwf Hx) as Hk. rewrite lin_key_make_lin_entry in Hk. exact Hk. }
      assert (Hdom1 : forall k, In k (lin_domain pool') -> In k (lin_domain pool) /\ k <> (t, h)).
      { intros k Hk. unfold lin_domain in Hk. apply in_map_iff in Hk as (x & <- & Hx).
        destruct (Hpool' _ Hx) as (Hx' & Hne). split; [apply in_map; exact Hx' | exact Hne]. }
      assert (Hinv : forall i k m, inv (conc run ++ [rev_ (t, h) op ret]) i k m -> inv (conc run) i k m).
      { intros i k m Hi. apply inv_snoc in Hi as [Hi | (_ & Hx)]; [exact Hi|].
        exfalso. exact (inv_not_res _ _ _ _ _ (eq_sym Hx)). }
      assert (Hres : forall j k m (r : Sig.ar m), res (conc run ++ [rev_ (t, h) op ret]) j k m r ->
                res (conc run) j k m r \/ (j = length (conc run) /\ rev_ (t, h) op ret = rev_ k m r)).
      { intros j k m r Hj. apply res_snoc in Hj as [Hj | (-> & Hx)]; [left; exact Hj | right; auto]. }
      assert (Hcwf' : call_pool_well_formed calls') by exact (finish_call_well_formed _ _ _ _ _ _ Hfin (ri_cwf _ _ _ _ HI)).
      constructor; rewrite ?HL, ?HT.
      - exact (ri_path _ _ _ _ HI).
      - exact (lin_remove_well_formed _ _ _ _ Hrem Hpwf).
      - intros k m Hk. destruct (Hpool' _ Hk) as (Hk' & _).
        destruct (ri_linv _ _ _ _ HI _ _ Hk') as ((i & Hi) & Ha).
        split; [exists i; exact (inv_app_l _ _ _ _ _ Hi) | exact Ha].
      - intros k m Hk. destruct (Hpool' _ Hk) as (Hk' & _).
        destruct (ri_llini _ _ _ _ HI _ _ Hk') as ((i & Hi) & Ha & Hr).
        split; [exists i; exact (inv_app_l _ _ _ _ _ Hi)|]. auto.
      - intros k m r Hk. destruct (Hpool' _ Hk) as (Hk' & _).
        destruct (ri_llinr _ _ _ _ HI _ _ _ Hk') as ((i & Hi) & Ha & Hr).
        split; [exists i; exact (inv_app_l _ _ _ _ _ Hi)|]. auto.
      - intros i k m Hi. apply Hinv in Hi.
        destruct (ri_status _ _ _ _ HI _ _ _ Hi) as [Hd | (j & m' & r' & Hj)].
        + rewrite Hp, domain_split in Hd. rewrite lin_key_make_lin_entry in Hd.
          apply in_app_or in Hd as [Hd | [<- | Hd]].
          * left. rewrite Hp'. unfold lin_domain. rewrite map_app. apply in_or_app. left. exact Hd.
          * right. exists (length (conc run)), op, ret. apply res_snoc_new.
          * left. rewrite Hp'. unfold lin_domain. rewrite map_app. apply in_or_app. right. exact Hd.
        + right. exists j, m', r'. exact (res_app_l _ _ _ _ _ _ Hj).
      - intros j k m r Hj. destruct (Hres _ _ _ _ Hj) as [Hj' | (_ & Hx)].
        + destruct (ri_dead _ _ _ _ HI _ _ _ _ Hj') as (Hn & Hb). split; [|exact Hb].
          intros Hk. exact (Hn (proj1 (Hdom1 _ Hk))).
        + pose proof (res_ev_inj _ _ _ _ _ _ Hx) as [Hk _]. subst k.
          split; [exact (lin_remove_absent _ _ _ _ Hrem Hpwf)|].
          exists b0. exact (res_transport _ _ _ _ _ _ _ _ Hx Hb0).
      - intros i1 i2 k1 k2 m1 m2 H1 H2 H12 Hd1 Hd2.
        apply Hinv in H1, H2. destruct (Hdom1 _ Hd1) as (Hd1' & Hn1). destruct (Hdom1 _ Hd2) as (Hd2' & Hn2).
        pose proof (ri_order _ _ _ _ HI _ _ _ _ _ _ H1 H2 H12 Hd1' Hd2') as Hb.
        rewrite Hp, domain_split, lin_key_make_lin_entry in Hb.
        rewrite Hp'. unfold lin_domain. rewrite map_app. exact (before_remove _ _ _ _ _ Hb Hn2 Hn1).
      - intros a k m Ha. destruct (ri_ainv _ _ _ _ HI _ _ _ Ha) as (i & Hi).
        exists i. exact (inv_app_l _ _ _ _ _ Hi).
      - exact (ri_ares _ _ _ _ HI).
      - exact (ri_auinv _ _ _ _ HI).
      - intros b b' k m m' r r' Hb Hb'. rewrite HT in Hb, Hb'. exact (ri_aures _ _ _ _ HI _ _ _ _ _ _ _ Hb Hb').
      - apply TValid_snoc; [exact (ri_valid _ _ _ _ HI)|].
        intros k m r Heq. exists b0. exact (res_transport _ _ _ _ _ _ _ _ Heq Hb0).
      - exact Hcwf'.
      - intros i k m Hi. apply Hinv in Hi. rewrite <- (finish_call_keys _ _ _ _ _ _ Hfin).
        exact (ri_cin _ _ _ _ HI _ _ _ Hi).
      - intros t' h' op' ret' Hin.
        destruct (finish_back _ _ _ _ _ _ _ Hfin Hin) as [Hin' | Heq]; [|discriminate].
        destruct (ri_cact _ _ _ _ HI _ _ _ _ Hin') as ((i & Hi) & Hn).
        split; [exists i; exact (inv_app_l _ _ _ _ _ Hi)|].
        intros j m' r' Hj. destruct (Hres _ _ _ _ Hj) as [Hj' | (_ & Hx)]; [exact (Hn _ _ _ Hj')|].
        pose proof (res_ev_inj _ _ _ _ _ _ Hx) as [Hk _]. injection Hk as <- <-.
        pose proof (NoDup_key_eq call_key _ _ _ Hcwf' Hin (finish_tgt _ _ _ _ _ _ Hfin) eq_refl) as Hc.
        discriminate.
      - intros t' h' Hin. destruct (finish_back _ _ _ _ _ _ _ Hfin Hin) as [Hin' | Heq].
        + destruct (ri_cdead _ _ _ _ HI _ _ Hin') as (j & m & r & Hj).
          exists j, m, r. exact (res_app_l _ _ _ _ _ _ Hj).
        + injection Heq as -> ->. exists (length (conc run)), op, ret. apply res_snoc_new.
      - exact (wf_snoc_res _ _ _ _ Hwf (ex_intro _ i0 Hi0) Hnor).
    Qed.
    (** *** Preservation along module steps *)

    Lemma poss_invoke_ok_inv t h op v pool p' :
      poss_invoke VF t h op (PossOk v pool) p' ->
      lin_fresh (t, h) pool /\ p' = PossOk v (make_lin_entry (t, h) (ls_inv op) :: pool).
    Proof.
      intros H. inversion H; subst.
      match goal with Hi : lin_insert _ _ _ _ |- _ => inversion Hi; subst end. auto.
    Qed.

    Lemma poss_return_inv t h op (ret : Sig.ar op) p p'' :
      poss_return VF t h op ret p p'' ->
      exists v pool pool', p = PossOk v pool /\ p'' = PossOk v pool' /\ lin_remove (t, h) (ls_linr op ret) pool pool'.
    Proof. intros [v pool pool' Hrem]. eauto 6. Qed.

    Lemma overlay_events_cons ev evs : overlay_events (ev :: evs) = overlay_events [ev] ++ overlay_events evs.
    Proof. destruct ev; reflexivity. Qed.

    Lemma rinv_step S c v pool run ev c' :
      GSimRel S -> S c (PossOk v pool) -> RInv run (tm_calls c) v pool ->
      module_step_tagged VE M ev c c' ->
      exists ext v' pool', S c' (PossOk v' pool') /\ RInv (run ++ ext) (tm_calls c') v' pool' /\
        conc ext = overlay_events [ev].
    Proof.
      intros HS Hc HI Hst.
      destruct (HS _ _ Hc) as (_ & Hinv & Hund & Hret).
      pose proof Hst as Hst0. revert Hc HI Hinv Hund Hret Hst0.
      destruct Hst as [t h op q calls queue used trace ret Hfresh Hmeth Hft
                      | cand q q' calls queue queue' used Hsel Hlts
                      | t h op ret q calls calls' queue used Hfin Hdone];
        intros Hc HI Hinv Hund Hret Hst0; simpl in HI.
      - destruct (Hinv _ _ _ _ Hst0) as (p' & Hpi & HS').
        destruct (poss_invoke_ok_inv _ _ _ _ _ _ Hpi) as (Hlf & ->).
        exists [CEv (iev (t, h) op)], v, (make_lin_entry (t, h) (ls_inv op) :: pool).
        split; [exact HS'|]. split; [exact (rinv_cinv _ _ _ _ _ _ _ ret HI Hfresh Hlf)|]. reflexivity.
      - destruct (Hund _ _ Hst0) as (p' & Hps & HS').
        destruct (HS _ _ HS') as ((v' & pool' & ->) & _).
        destruct (poss_steps_prun _ _ Hps ltac:(discriminate)) as (evs & Hpr).
        destruct (rinv_prun _ _ _ _ _ _ HI Hpr) as (v'' & pool'' & Heq & HI' & Hc').
        injection Heq as <- <-.
        exists evs, v', pool'. split; [exact HS'|]. split; [exact HI'|]. exact Hc'.
      - destruct (Hret _ _ _ _ _ Hst0) as (p' & p'' & Hps & Hpr & HS').
        destruct (poss_return_inv _ _ _ _ _ _ Hpr) as (v1 & pool1 & pool2 & -> & -> & Hrem).
        destruct (poss_steps_prun _ _ Hps ltac:(discriminate)) as (evs & Hpn).
        destruct (rinv_prun _ _ _ _ _ _ HI Hpn) as (v'' & pool'' & Heq & HI' & Hc').
        injection Heq as <- <-.
        exists (evs ++ [CEv (rev_ (t, h) op ret)]), v1, pool2.
        split; [exact HS'|]. split.
        + rewrite app_assoc. exact (rinv_cret _ _ _ _ _ _ _ _ _ _ HI' Hfin Hrem).
        + rewrite conc_app, Hc'. reflexivity.
    Qed.

    Lemma rinv_exec S c evs c' :
      GSimRel S -> module_execution_tagged VE M c evs c' ->
      forall run v pool, S c (PossOk v pool) -> RInv run (tm_calls c) v pool ->
      exists ext v' pool', S c' (PossOk v' pool') /\ RInv (run ++ ext) (tm_calls c') v' pool' /\
        conc ext = overlay_events evs.
    Proof.
      intros HS Hex. induction Hex as [c | c1 c2 c3 ev trace Hstep Hexec IH]; intros run v pool Hc HI.
      - exists [], v, pool. rewrite app_nil_r. split; [exact Hc | split; [exact HI | reflexivity]].
      - destruct (rinv_step _ _ _ _ _ _ _ HS Hc HI Hstep) as (e1 & v1 & pool1 & Hc1 & HI1 & He1).
        destruct (IH _ _ _ Hc1 HI1) as (e2 & v2 & pool2 & Hc2 & HI2 & He2).
        exists (e1 ++ e2), v2, pool2. rewrite app_assoc. split; [exact Hc2|]. split; [exact HI2|].
        rewrite conc_app, He1, He2, (overlay_events_cons ev trace). reflexivity.
    Qed.

    (** *** Soundness: GSim implies relaxed linearizability *)

    (** [HVF]: every complete well-formed trace the abstract specification
        [VF] can produce is relaxed-linearizable.  Under this hypothesis a
        global simulation from the initial configuration makes every
        complete overlay trace of the module relaxed-linearizable. *)
    Theorem gsim_rel_lin (nu : list (Op F) -> Prop) S q0 evs c :
      GSimRel S -> S (initial_tagged_module VE q0) (PossOk v0 []) ->
      module_execution_tagged VE M (initial_tagged_module VE q0) evs c ->
      (forall e, In e (tm_calls c) -> ce_cell F e = DeadCall) ->
      (forall T v, vf_path v0 T v -> PrefixView.wf T -> PrefixView.complete T ->
         RelaxedTraceLin.rel_lin (@PrefixView.sel F) T (RelaxedSig.semi_independent F) nu) ->
      RelaxedTraceLin.rel_lin (@PrefixView.sel F) (overlay_events evs) (RelaxedSig.semi_independent F) nu.
    Proof.
      intros HS H0 Hex Hdead HVF.
      destruct (rinv_exec _ _ _ _ HS Hex [] v0 [] H0 RInv_init) as (run & v & pool & _ & HI & Hc).
      simpl in HI. rewrite <- Hc.
      assert (Hwf := ri_lwf _ _ _ _ HI).
      assert (Hcomp : PrefixView.complete (conc run)).
      { intros i k m Hi. pose proof (ri_cin _ _ _ _ HI _ _ _ Hi) as Hk.
        apply in_map_iff in Hk as (e & Hke & He). pose proof (Hdead _ He) as Hd.
        destruct e as [t' h' cell]. simpl in Hd, Hke. subst cell k.
        destruct (ri_cdead _ _ _ _ HI _ _ He) as (j & m' & r' & Hj).
        pose proof (res_op_inv _ _ _ _ _ _ _ Hwf Hj Hi) as Heq. subst m'.
        exists j, r'. exact Hj. }
      assert (Hawf : PrefixView.wf (abs run)).
      { split; [exact (ri_auinv _ _ _ _ HI) | split; [exact (ri_aures _ _ _ _ HI) | exact (ri_ares _ _ _ _ HI)]]. }
      assert (Hacomp : PrefixView.complete (abs run)).
      { intros a k m Ha. destruct (ri_ainv _ _ _ _ HI _ _ _ Ha) as (i & Hi).
        destruct (Hcomp _ _ _ Hi) as (j & r & Hj).
        destruct (ri_dead _ _ _ _ HI _ _ _ _ Hj) as (_ & b & Hb). exists b, r. exact Hb. }
      exact (transfer _ nu run (ri_valid _ _ _ _ HI) Hwf Hcomp (ri_aures _ _ _ _ HI)
               (HVF _ _ (ri_path _ _ _ _ HI) Hawf Hacomp)).
    Qed.

    Corollary GSim_rel_lin (nu : list (Op F) -> Prop) q0 evs c :
      GSim (initial_tagged_module VE q0) (PossOk v0 []) ->
      module_execution_tagged VE M (initial_tagged_module VE q0) evs c ->
      (forall e, In e (tm_calls c) -> ce_cell F e = DeadCall) ->
      (forall T v, vf_path v0 T v -> PrefixView.wf T -> PrefixView.complete T ->
         RelaxedTraceLin.rel_lin (@PrefixView.sel F) T (RelaxedSig.semi_independent F) nu) ->
      RelaxedTraceLin.rel_lin (@PrefixView.sel F) (overlay_events evs) (RelaxedSig.semi_independent F) nu.
    Proof. intros (S & HS & H0). exact (gsim_rel_lin nu S q0 evs c HS H0). Qed.
  End GSim.
End RelaxedGSim.
