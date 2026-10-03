(** * Lock(O) as an instance of window composition

    [WindowLink.window_link] composes components whose operations each
    designate a window of underlay calls and a linearization call.  This
    file instantiates it on lock-bracketed components ([Lock(O)]), the
    setting of [BracketedLink]:

    - window: the acquire, [wlo = whi = wacq] (the index of the first
      acquire invocation of the method's local trace);
    - linearization call: the acquire, so the window is a single call;
    - positional correctness: from [BracketedLink.link_hyps] and
      [BracketedComposition.bracketed_composition];
    - mode inheritance: an acquire has an acquire-like mode, so the
      overlay may export any mode [≤ RFence]; a release-like overlay mode
      (LFence, Fence) would have to be carried by the acquire and is not
      allowed ([F_modes]).

    [lock_window_link] then concludes relaxed linearizability of the
    overlay w.r.t. the overlay signature's own semi-independence, not only
    the empty one as [BracketedLink.bracketed_link] does.  The hypotheses
    on the lock operations are stated as modes ([acq_mode], [rel_mode]);
    the semi-independence facts [BracketedLink] assumes follow from them
    by well-formedness. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Sorting.Sorted.
Require Import Stdlib.Sorting.Permutation.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.micromega.Lia.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedModuleFacts.
Require Import examples.Relaxed.BracketedComposition.
Require Import examples.Relaxed.BracketedLink.
Require Import examples.Relaxed.WindowComposition.
Require Import examples.Relaxed.WindowLink.

Import ListNotations.

Module BracketedWindow.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedTraceLin.
  Import RelaxedModuleFacts.

  Module BL := BracketedLink.BracketedLink.
  Module BC := BracketedComposition.BracketedComposition.
  Module WC := WindowComposition.WindowComposition.
  Module WL := WindowLink.WindowLink.

  Section Lock.
    Context {E F : RelaxedSig.t} (HwfE : well_formed E).
    Context (VE : RelaxedLTSSpec.LTS E) (M : RelaxedModuleImpl E F).
    Context (keyE_dec : forall k k' : CallKey E, {k = k'} + {k <> k'}).
    Context (keyF_dec : forall k k' : CallKey F, {k = k'} + {k <> k'}).
    Context {Comp : Type} (comp_dec : forall c c' : Comp, {c = c'} + {c <> c'}).
    Context (compE : Sig.op (effect E) -> Comp) (compF : Sig.op (effect F) -> Comp).
    Context (is_acq is_rel : Sig.op (effect E) -> bool).

    (** Lock operations, by their modes. *)
    Hypothesis acq_mode : forall a, is_acq a = true -> WC.acq_like (mode E a).
    Hypothesis rel_mode : forall r, is_rel r = true -> WC.rel_like (mode E r).
    Hypothesis acq_not_rel : forall o, is_acq o = true -> is_rel o = false.

    Hypothesis bracketed_bodies : forall t op tr ret,
      program_produces_tagged t (M op t) tr ret ->
      BL.bracketed compE is_acq is_rel (compF op) (map untag tr).

    Context (nuEc : Comp -> list (Op E) -> Prop) (nuFc : Comp -> list (Op F) -> Prop).
    Hypothesis nuE_locks : forall c w, nuEc c w -> BL.lock_alternates is_acq is_rel w.
    Hypothesis local_correct : forall c (G : list (Op F)) (b : Op F -> list (Op E)),
      NoDup (map op_key G) ->
      (forall s, In s G -> compF (op_op s) = c /\ BL.local_ok M s (b s)) ->
      nuEc c (concat (map b G)) -> nuFc c G.

    (** The overlay: modes at most RFence (the linearization call is the
        acquire); the mode-induced cross-component pairs are
        semi-independent (as in [Tens.omap]). *)
    Hypothesis F_modes : forall o, mode F o ≤f RFence.
    Hypothesis F_cross : forall o o', compF o <> compF o' ->
      WC.cross (mode F o) (mode F o') -> semi_independent F o o'.
    Hypothesis nuF_nil : forall c, nuFc c [].

    (** The semi-independence facts of [BracketedLink] follow from the
        modes. *)
    Lemma acq_rfence a x : is_acq a = true -> ~ semi_independent E a x.
    Proof. intros Ha Hi. apply (acq_mode a Ha). exact (semi_independent_left_compatible HwfE _ _ Hi). Qed.

    Lemma rel_lfence x r : is_rel r = true -> ~ semi_independent E x r.
    Proof. intros Hr Hi. apply (rel_mode r Hr). exact (semi_independent_right_compatible HwfE _ _ Hi). Qed.

    (** ** The window: the first acquire invocation *)

    Fixpoint acq_index (tr : list (ThreadEvent E)) : nat :=
      match tr with
      | [] => 0
      | ev :: tr' =>
          match te_ev E ev with
          | InvEv _ o => if is_acq o then 0 else S (acq_index tr')
          | ResEv _ _ _ => S (acq_index tr')
          end
      end.

    Definition wacq (op : Sig.op (effect F)) (tr : list (ThreadEvent E)) : nat := acq_index tr.

    Lemma acq_index_at tr : forall n k a,
      BL.inv_in tr n k a -> is_acq a = true ->
      (forall i k' o, i < n -> BL.inv_in tr i k' o -> is_acq o = false) ->
      acq_index tr = n.
    Proof.
      induction tr as [| ev tr IH]; intros n k a Hn Ha Hbefore.
      - unfold BL.inv_in in Hn. destruct n; discriminate.
      - destruct n as [| n].
        + unfold BL.inv_in in Hn. cbn in Hn. injection Hn as ->. cbn. rewrite Ha. reflexivity.
        + cbn. destruct ev as [t e]. cbn.
          assert (Hrest : acq_index tr = n).
          { apply (IH n k a); [exact Hn | exact Ha |].
            intros i k' o Hi Hin. apply (Hbefore (S i) k' o); [lia | exact Hin]. }
          destruct e as [h o | h o v].
          * destruct (is_acq o) eqn:Ho; [| rewrite Hrest; reflexivity].
            exfalso.
            assert (H0 : BL.inv_in ({| te_tid := t; te_ev := InvEv h o |} :: tr) 0 (t, h) o)
              by reflexivity.
            rewrite (Hbefore 0 (t, h) o ltac:(lia) H0) in Ho. discriminate.
          * rewrite Hrest. reflexivity.
    Qed.

    Lemma bracketed_acq_index c tr :
      BL.bracketed compE is_acq is_rel c tr ->
      exists k a, BL.inv_in tr (acq_index tr) k a /\ is_acq a = true.
    Proof.
      intros (ia & ka & a & ir & kr & rr & Ha & Hacq & _ & _ & _ & _ & Hlt & Hmid).
      rewrite (acq_index_at tr ia ka a Ha Hacq).
      - exists ka, a. split; assumption.
      - intros i k' o Hi Hin.
        assert (Hne1 : i <> ia) by lia. assert (Hne2 : i <> ir) by lia.
        destruct (Hmid i k' o Hin Hne1 Hne2) as (Hb & _ & _). lia.
    Qed.

    (** Mode inheritance for the acquire window. *)
    Lemma lock_window_bodies : forall t op tr ret,
      program_produces_tagged t (M op t) tr ret ->
      exists klo olo khi ohi,
        BL.inv_in (map untag tr) (wacq op (map untag tr)) klo olo /\
        BL.inv_in (map untag tr) (wacq op (map untag tr)) khi ohi /\
        (WC.acq_like (mode F op) -> WC.acq_like (mode E ohi)) /\
        (WC.rel_like (mode F op) -> WC.rel_like (mode E olo)).
    Proof.
      intros t op tr ret Hp.
      destruct (bracketed_acq_index _ _ (bracketed_bodies _ _ _ _ Hp)) as (k & a & Hin & Ha).
      exists k, a, k, a. unfold wacq.
      split; [exact Hin |]. split; [exact Hin |]. split.
      - intros _. exact (acq_mode a Ha).
      - intros Hr. exfalso. exact (Hr (F_modes op)).
    Qed.

    (** ** Positional correctness, from [BracketedLink] *)

    Section Instance.
      Context (IT : list (@ITraceEvent E F)) (ic : @IConfig E F VE).
      Context (Hinv : IInv VE M IT ic) (Hq : ic_queue VE ic = []).
      Context (Wu : list (Op E)).
      Context (HWu : rel_lin_witness BL.usel IT (semi_independent E) (BL.nuE_all comp_dec compE nuEc) Wu).
      Context (r0 : @InvRec E F) (u0 : Op E).

      Abbreviation acq := (BL.acq VE keyE_dec keyF_dec is_acq ic Wu r0 u0).
      Abbreviation lo := (WL.lo VE keyE_dec keyF_dec wacq ic Wu r0 u0).
      Abbreviation hi := (WL.hi VE keyE_dec keyF_dec wacq ic Wu r0 u0).
      Abbreviation secs := (BL.secs VE ic).
      Abbreviation pos := (BL.pos keyE_dec Wu).

      Definition H : BC.Hyps keyF_dec comp_dec (BL.comp VE keyF_dec compF ic r0) (BL.owner VE keyE_dec ic r0)
                       acq (BL.rel VE keyE_dec keyF_dec is_rel ic Wu r0 u0) (BL.ovl VE keyF_dec ic r0) pos secs Wu
                       (BL.po VE keyF_dec ic r0) (BL.rt VE keyF_dec IT ic r0) nuEc nuFc
                       (BL.body_ok VE M keyF_dec ic r0) :=
        BL.link_hyps VE M keyE_dec keyF_dec comp_dec compE compF is_acq is_rel acq_rfence rel_lfence
          acq_not_rel bracketed_bodies nuEc nuFc nuE_locks local_correct IT ic Hinv Hq Wu HWu r0 u0.

      (** The window call is the acquire of [BracketedLink]. *)
      Lemma lo_is_acq s : In s secs -> lo s = acq s.
      Proof.
        intros Hs. destruct (BL.secs_record VE ic s Hs) as (r & Hr & ->).
        destruct (BL.section_data VE M keyE_dec keyF_dec comp_dec compE compF is_acq is_rel acq_not_rel
                    bracketed_bodies nuEc IT ic Hinv Hq Wu HWu r0 u0 r Hr)
          as (ia & ir & mA & pA & mR & pR & _ & HsA & _ & HAin & _ & _ & _ & _ & _ & Hprop).
        destruct (bracketed_acq_index _ _ (bracketed_bodies _ _ _ _ (ii_produced _ _ _ _ Hinv r Hr)))
          as (k & a & Hin & Ha).
        destruct (WL.call_at_spec VE M keyE_dec keyF_dec comp_dec compE nuEc IT ic Hinv Hq Wu HWu r0 u0
                    wacq r _ k a Hr eq_refl Hin) as (m & p & Hsl & Hu & Ho).
        change (WL.call_at VE keyE_dec keyF_dec ic Wu r0 u0 wacq (ir_key r)) with (lo (ir_key r)) in Hsl, Hu, Ho.
        pose proof Hsl as (_ & Hj & Hm & _). pose proof HsA as (_ & HjA & HmA & _).
        assert (Hia : acq_index (BL.ltr r) = ia).
        { rewrite Ho in Hm. apply (proj1 (proj2 (proj2 (Hprop _ m _ _ Hj Hm)))). exact Ha. }
        change (wacq (ir_op r) (BL.ltr r)) with (acq_index (BL.ltr r)) in Hj.
        rewrite Hia, HjA in Hj. injection Hj as <-.
        rewrite Hm in HmA. destruct (BL.inv_ev_inj _ _ _ _ HmA) as [Hk _].
        exact (BL.wu_key_inj comp_dec compE nuEc IT Wu HWu _ _ Hu HAin Hk).
      Qed.

      Lemma lock_positional :
        WL.Positional VE keyE_dec keyF_dec comp_dec compF nuFc wacq wacq IT ic Wu r0 u0 lo.
      Proof.
        pose (key := BC.lp acq pos).
        assert (Hkey : forall s, In s secs -> WL.pos keyE_dec Wu (lo s) = key s)
          by (intros s Hs; unfold key, BC.lp; rewrite (lo_is_acq s Hs); reflexivity).
        assert (Hinj : forall s s', In s secs -> In s' secs -> key s = key s' -> s = s')
          by exact (BC.lp_inj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
        assert (Hnd : NoDup secs) by exact (ii_invs_nodup _ _ _ _ Hinv).
        constructor.
        - intros s s' Hs Hs' Heq. rewrite (Hkey s Hs), (Hkey s' Hs') in Heq. exact (Hinj s s' Hs Hs' Heq).
        - intros s Hs. unfold WL.hi, WL.lo. lia.
        - intros c.
          destruct (BC.bracketed_composition _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H)
            as (ow & Hperm & Hsort & _ & Hspec).
          set (f := WC.in_comp (WL.setting VE keyE_dec keyF_dec comp_dec compF nuFc wacq wacq IT ic Wu r0 u0 lo) c).
          assert (Eow : ow = WC.isort key secs).
          { apply (WC.ss_perm_eq key).
            - exact Hsort.
            - apply WC.isort_sorted; assumption.
            - eapply perm_trans; [exact Hperm |]. apply Permutation_sym, WC.isort_perm. }
          assert (Efl : filter f ow = WC.isort key (filter f secs))
            by (rewrite Eow; apply WC.filter_isort; assumption).
          assert (Ekey : WC.isort (WC.lp (WL.setting VE keyE_dec keyF_dec comp_dec compF nuFc wacq wacq IT ic Wu r0 u0 lo))
                           (filter f secs) = WC.isort key (filter f secs)).
          { apply WC.isort_key_equiv.
            - intros x y Hx Hy. apply filter_In in Hx as [Hx _]. apply filter_In in Hy as [Hy _].
              unfold WC.lp. cbn. rewrite (Hkey x Hx), (Hkey y Hy). reflexivity.
            - intros x y Hx Hy Heq. apply filter_In in Hx as [Hx _]. apply filter_In in Hy as [Hy _].
              unfold WC.lp in Heq. cbn in Heq. rewrite (Hkey x Hx), (Hkey y Hy) in Heq. exact (Hinj x y Hx Hy Heq).
            - intros x y Hx Hy Heq. apply filter_In in Hx as [Hx _]. apply filter_In in Hy as [Hy _].
              exact (Hinj x y Hx Hy Heq).
            - apply NoDup_filter, Hnd. }
          change (nuFc c (map (BL.ovl VE keyF_dec ic r0)
                    (WC.isort (WC.lp (WL.setting VE keyE_dec keyF_dec comp_dec compF nuFc wacq wacq IT ic Wu r0 u0 lo))
                       (filter f secs)))).
          rewrite Ekey, <- Efl. exact (Hspec c).
        - intros s s' Hs Hs' _ Hpo _. rewrite (Hkey s Hs), (Hkey s' Hs').
          exact (BC.lp_po _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H s s' Hs Hs' Hpo).
      Qed.
    End Instance.

    (** ** Lock(O) *)

    Theorem lock_window_link q0 T c :
      module_execution_tagged VE M (initial_tagged_module VE q0) T c ->
      tm_queue c = [] ->
      (forall e, In e (tm_calls c) -> ce_cell F e = DeadCall) ->
      rel_lin BL.under_sel T (semi_independent E) (BL.nuE_all comp_dec compE nuEc) ->
      rel_lin BL.over_sel T (semi_independent F) (BL.nuF_all comp_dec compF nuFc).
    Proof.
      apply (WL.window_link HwfE VE M keyE_dec keyF_dec comp_dec compE compF nuEc nuFc F_cross nuF_nil
               wacq wacq lock_window_bodies).
      intros IT ic Wu r0 u0 Hinv Hq _ HWu.
      exists (WL.lo VE keyE_dec keyF_dec wacq ic Wu r0 u0).
      exact (lock_positional IT ic Hinv Hq Wu HWu r0 u0).
    Qed.
  End Lock.

End BracketedWindow.
