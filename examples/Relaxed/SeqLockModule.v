(** * SeqLock ⊎ COH[z] in the module semantics

    [SeqLockCOH] proves the SeqLock layer, and its composition with a
    client cell z, at the level of underlay witnesses ([SeqLockCOH.WF],
    [seqlock_S1], [z_S1], ...).  [SeqLockProg] writes the module [M rc K]
    of SeqLock ⊎ COH[z] in the futures language and shows that every
    method trace is the trace of one block ([M_shape]).  This file joins
    the two through [WindowLinkTable.window_link_table]:

      [seqlock_module_rel_lin]: every complete execution of
      [M rc plainTL] in the dependency-frontier module semantics whose
      underlay part is relaxed linearizable w.r.t. the tensor of the
      component specifications (TicketLock with version counter ⊗ x ⊗ y ⊗
      barriers, and COH[z]) has an overlay part that is relaxed
      linearizable w.r.t. the tensor of ν_SeqLock and ν_COH[z], for the
      overlay semi-independence of [SeqLockProg.F] (different components
      whose categories [WindowTable.dto] does not order).

    The instance of [window_link_table]:
    - table [WindowTable.dtable rc]; underlay categories
      [SeqLockCOH.ucat K] of the calls ([catE]), overlay categories
      [SeqLockProg.fcat] (read ↦ rmb, write ↦ wmb, z ↦ R/W);
    - [E_compat], [F_cross]: read off [SeqLockProg.sindep] and [findep];
    - windows [wlo = whi = wsel]: the second invocation of a write (its
      first wmb), the second invocation of the last iteration of a read
      (its first rmb), the invocation of a z access.  Each window is one
      call of the overlay category, so dominance is reflexivity
      ([window_bodies]);
    - [positional]: from the instrumented execution and the underlay
      witness [Wu], an execution [SX] of [SeqLockCOH] is built.  Its
      threads are the overlay thread identifiers (as numbers); the
      program of a thread is the list of blocks of its overlay calls in
      invocation order, each block decoded from the local trace of the
      call ([decode], [parse], with [parse (calls k) = k]); its witness is
      [Wu], each call placed at its index among the calls of its thread.
      [SX_wf] proves [SeqLockCOH.WF]: completeness from
      [complete_all_emitted], the preserved order from
      [BracketedLink.inv_order] (index order is enqueue order inside a
      thread, [src_order]), validity from the component specifications
      ([replay_merge]).  The overlay calls are in bijection with
      [SeqLockCOH.all_ops SX] ([phi]), the window call of a call is its
      [SeqLockCOH.lpc] ([phi_lpq]), and [seqlock_S1], [z_S1],
      [seqlock_S1_ord], [z_S1_ord], [lp_inj] transport along [phi]
      ([isort_transport]).

    Real time comes from the module semantics inside [window_link_table];
    no timing assumption is made.  The theorem holds for every TicketLock
    signature [K] with [SeqLockCOH.K_ok K] ([seqlock_module_rel_lin_K]);
    [plainTL] is the one [TicketLockCOH] exports.  Only complete
    executions and safety, as in [BracketedLink]. *)

From Stdlib Require Import List Bool Arith.PeanoNat PArith micromega.Lia.
From Stdlib Require Import Sorting.Sorted Sorting.Permutation.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedModuleFacts.
Require Import examples.Relaxed.BracketedLink.
Require Import examples.Relaxed.WindowComposition.
Require Import examples.Relaxed.WindowTable.
Require Import examples.Relaxed.WindowLinkTable.
Require Import examples.Relaxed.SeqLockCOH.
Require Import examples.Relaxed.SeqLockProg.

Import ListNotations.

Module SeqLockModule.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedTraceLin.
  Import RelaxedModuleFacts.
  Import SeqLockProg.SeqLockProg.

  Module BL := BracketedLink.BracketedLink.
  Module WC := WindowComposition.WindowComposition.
  Module WLT := WindowLinkTable.WindowLinkTable.

  (** ** List facts *)

  Section Index.
    Context {A : Type} (dec : forall a b : A, {a = b} + {a <> b}).

    (** Index of the first occurrence. *)
    Fixpoint lindex (a : A) (l : list A) : nat :=
      match l with
      | [] => 0
      | b :: l' => if dec b a then 0 else S (lindex a l')
      end.

    Lemma lindex_nth a l : In a l -> nth_error l (lindex a l) = Some a.
    Proof.
      induction l as [|b l IH]; cbn; [intros []|].
      destruct (dec b a) as [->|Hne]; [reflexivity|].
      intros [->|H]; [contradiction|]. apply IH, H.
    Qed.

    Lemma lindex_of_nth l i a : NoDup l -> nth_error l i = Some a -> lindex a l = i.
    Proof.
      revert i. induction l as [|b l IH]; intros i Hnd H; [destruct i; discriminate|].
      inversion Hnd as [|? ? Hni Hnd']; subst.
      destruct i as [|i]; cbn in H |- *.
      - injection H as ->. destruct (dec a a); [reflexivity|contradiction].
      - destruct (dec b a) as [->|Hne].
        + exfalso. apply Hni. eapply nth_error_In. exact H.
        + f_equal. apply IH; assumption.
    Qed.
  End Index.

  Lemma NoDup_map_in {A B} (f : A -> B) l :
    NoDup l -> (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup (map f l).
  Proof.
    induction 1 as [|a l Hni Hnd IH]; intros Hinj; cbn; constructor.
    - intros Hin. apply in_map_iff in Hin as (b & Eb & Hb).
      apply Hni. rewrite <- (Hinj b a (or_intror Hb) (or_introl eq_refl) Eb). exact Hb.
    - apply IH. intros x y Hx Hy. apply Hinj; right; assumption.
  Qed.

  Lemma nth_error_nodup_inj {A} (l : list A) i j a :
    NoDup l -> nth_error l i = Some a -> nth_error l j = Some a -> i = j.
  Proof.
    intros Hnd Hi Hj. apply (proj1 (NoDup_nth_error l) Hnd i j); [|congruence].
    apply nth_error_Some. congruence.
  Qed.

  Lemma pair_nodup_fst {B} (l : list (nat * B)) h c c' :
    NoDup (map fst l) -> In (h, c) l -> In (h, c') l -> c = c'.
  Proof.
    intros Hnd H H'. pose proof (nodup_map_inj fst l (h, c) (h, c') Hnd H H' eq_refl) as E.
    congruence.
  Qed.

  Lemma in_firstn {A} (l : list A) n x : In x (firstn n l) -> In x l.
  Proof. intros H. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H. Qed.

  Lemma firstn_prefix {A} (l : list A) j j' : j <= j' -> exists l', firstn j' l = firstn j l ++ l'.
  Proof.
    intros Hle. exists (skipn j (firstn j' l)).
    rewrite <- (firstn_skipn j (firstn j' l)) at 1. rewrite firstn_firstn.
    replace (Nat.min j j') with j by lia. reflexivity.
  Qed.

  Lemma map_flat_map {A B C} (f : B -> C) (g : A -> list B) l :
    map f (flat_map g l) = flat_map (fun a => map f (g a)) l.
  Proof. induction l as [|a l IH]; cbn; [reflexivity|]. rewrite map_app, IH. reflexivity. Qed.

  Lemma flat_map_ext_in {A B} (f g : A -> list B) l :
    (forall a, In a l -> f a = g a) -> flat_map f l = flat_map g l.
  Proof.
    induction l as [|a l IH]; intros H; cbn; [reflexivity|].
    rewrite (H a (or_introl eq_refl)), IH; [reflexivity|]. intros b Hb. apply H. right. exact Hb.
  Qed.

  Lemma NoDup_flat_map_filter {A B} (f : A -> list B) (p : A -> bool) l :
    NoDup (flat_map f l) -> NoDup (flat_map f (filter p l)).
  Proof.
    induction l as [|a l IH]; cbn; intros Hnd; [constructor|].
    specialize (IH (NoDup_app_remove_l _ _ Hnd)).
    destruct (p a); cbn; [|exact IH].
    apply NoDup_app; [exact (NoDup_app_remove_r _ _ Hnd)|exact IH|].
    intros x Hx Hx'. apply (nodup_app_disj _ _ x Hnd Hx).
    apply in_flat_map in Hx' as (b & Hb & Hx'). apply in_flat_map. exists b.
    split; [apply filter_In in Hb; tauto|exact Hx'].
  Qed.

  Lemma NoDup_snd_same_fst {A B} (L : list (A * B)) :
    NoDup L -> (forall x y, In x L -> In y L -> fst x = fst y) -> NoDup (map snd L).
  Proof.
    intros Hnd Hf. apply NoDup_map_in; [exact Hnd|].
    intros x y Hx Hy Hs. apply injective_projections; [apply Hf|]; assumption.
  Qed.

  (** Offsets in a [flat_map]. *)
  Section FlatMap.
    Context {A B : Type} (f : A -> list B).

    Definition foff (l : list A) (j : nat) : nat := length (flat_map f (firstn j l)).

    Lemma foff_mono l j j' : j <= j' -> foff l j <= foff l j'.
    Proof.
      intros H. destruct (firstn_prefix l j j' H) as (l' & E).
      unfold foff. rewrite E, flat_map_app, length_app. lia.
    Qed.

    Lemma foff_S l j a : nth_error l j = Some a -> foff l (S j) = foff l j + length (f a).
    Proof.
      intros H. unfold foff. rewrite SL.firstn_S_nth, H, flat_map_app, length_app.
      cbn. rewrite app_nil_r. reflexivity.
    Qed.

    Lemma foff_lt l j j' a i : nth_error l j = Some a -> i < length (f a) -> j < j' -> foff l j + i < foff l j'.
    Proof. intros Hj Hi Hlt. pose proof (foff_S l j a Hj). pose proof (foff_mono l (S j) j' Hlt). lia. Qed.

    Lemma flat_map_nth l j a i b :
      nth_error l j = Some a -> nth_error (f a) i = Some b -> nth_error (flat_map f l) (foff l j + i) = Some b.
    Proof.
      intros Hj Hi. destruct (nth_error_split l j Hj) as (l1 & l2 & -> & <-).
      unfold foff. rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r, flat_map_app. cbn.
      rewrite nth_error_app2 by lia.
      replace (length (flat_map f l1) + i - length (flat_map f l1)) with i by lia.
      rewrite nth_error_app1; [exact Hi|]. apply nth_error_Some. congruence.
    Qed.

    Lemma flat_map_nth_inv l i b :
      nth_error (flat_map f l) i = Some b ->
      exists j a i', nth_error l j = Some a /\ i = foff l j + i' /\ nth_error (f a) i' = Some b.
    Proof.
      revert i. induction l as [|a l IH]; intros i H; [destruct i; discriminate|].
      cbn [flat_map] in H.
      destruct (Nat.lt_ge_cases i (length (f a))) as [Hi|Hi].
      - rewrite nth_error_app1 in H by exact Hi. exists 0, a, i. unfold foff. cbn. auto.
      - rewrite nth_error_app2 in H by exact Hi.
        destruct (IH _ H) as (j & a' & i' & Hj & Ei & Ha).
        exists (S j), a', i'. split; [exact Hj|]. split; [|exact Ha].
        unfold foff in *. cbn [firstn flat_map]. rewrite length_app. lia.
    Qed.
  End FlatMap.

  (** Sortedness. *)
  Lemma ss_map {A B} (R : B -> B -> Prop) (f : A -> B) l :
    StronglySorted (fun a b => R (f a) (f b)) l -> StronglySorted R (map f l).
  Proof.
    induction 1 as [|a l Hs IH Hf]; cbn; constructor; [exact IH|].
    apply Forall_map. exact Hf.
  Qed.

  Lemma ss_of_split {A} (R : A -> A -> Prop) l :
    (forall pre a post, l = pre ++ a :: post -> forall b, In b post -> R a b) -> StronglySorted R l.
  Proof.
    induction l as [|a l IH]; intros H; constructor.
    - apply IH. intros pre x post E. apply (H (a :: pre)). rewrite E. reflexivity.
    - apply Forall_forall. apply (H [] a l eq_refl).
  Qed.

  Lemma ss_nth {A} (R : A -> A -> Prop) l i j a b :
    StronglySorted R l -> nth_error l i = Some a -> nth_error l j = Some b -> i < j -> R a b.
  Proof.
    intros Hs Hi Hj Hlt. destruct (nth_error_split l i Hi) as (l1 & l2 & -> & <-).
    apply (ss_after R l1 a l2 b Hs).
    rewrite nth_error_app2 in Hj by lia. destruct (j - length l1) as [|d] eqn:Hd; [lia|].
    cbn in Hj. eapply nth_error_In. exact Hj.
  Qed.

  Lemma ss_nth_rev {A} (key : A -> nat) l i j a b :
    StronglySorted (fun x y => key x < key y) l ->
    nth_error l i = Some a -> nth_error l j = Some b -> key a < key b -> i < j.
  Proof.
    intros Hs Hi Hj Hlt. destruct (Nat.lt_trichotomy i j) as [H|[<-|H]]; [exact H| |].
    - rewrite Hi in Hj. injection Hj as <-. lia.
    - assert (key b < key a) by exact (ss_nth _ l j i b a Hs Hj Hi H). lia.
  Qed.

  (** Sorting along a bijection that preserves keys and filters. *)
  Lemma isort_transport {A B} (phi : A -> B) (kA : A -> nat) (kB : B -> nat)
      (fA : A -> bool) (fB : B -> bool) (LA : list A) (LB : list B) :
    NoDup LA -> NoDup LB ->
    (forall a, In a LA -> In (phi a) LB) ->
    (forall b, In b LB -> exists a, In a LA /\ phi a = b) ->
    (forall a a', In a LA -> In a' LA -> phi a = phi a' -> a = a') ->
    (forall a, In a LA -> kB (phi a) = kA a) ->
    (forall b b', In b LB -> In b' LB -> kB b = kB b' -> b = b') ->
    (forall a, In a LA -> fB (phi a) = fA a) ->
    map phi (WC.isort kA (filter fA LA)) = WC.isort kB (filter fB LB).
  Proof.
    intros HndA HndB Hin Honto Hinj Hk HkB Hf.
    assert (HkA : forall a a', In a LA -> In a' LA -> kA a = kA a' -> a = a').
    { intros a a' Ha Ha' E. apply Hinj; [exact Ha|exact Ha'|].
      apply HkB; [apply Hin, Ha|apply Hin, Ha'|]. rewrite (Hk a Ha), (Hk a' Ha'). exact E. }
    assert (HinA : forall a, In a (WC.isort kA (filter fA LA)) -> In a LA).
    { intros a Ha. apply (Permutation_in _ (WC.isort_perm _ _)) in Ha. apply filter_In in Ha. tauto. }
    apply (WC.ss_perm_eq kB).
    - apply ss_map. apply (WC.ss_impl_in (fun a b => kA a < kA b)).
      + intros x y Hx Hy Hlt. cbv beta. rewrite (Hk x (HinA x Hx)), (Hk y (HinA y Hy)). exact Hlt.
      + apply WC.isort_sorted; [|apply NoDup_filter, HndA].
        intros x y Hx Hy. apply filter_In in Hx as [Hx _]. apply filter_In in Hy as [Hy _].
        apply HkA; assumption.
    - apply WC.isort_sorted; [|apply NoDup_filter, HndB].
      intros x y Hx Hy. apply filter_In in Hx as [Hx _]. apply filter_In in Hy as [Hy _].
      apply HkB; assumption.
    - eapply perm_trans; [apply Permutation_map, WC.isort_perm|].
      eapply perm_trans; [|apply Permutation_sym, WC.isort_perm].
      apply NoDup_Permutation.
      + apply NoDup_map_in; [apply NoDup_filter, HndA|].
        intros x y Hx Hy. apply filter_In in Hx as [Hx _]. apply filter_In in Hy as [Hy _].
        apply Hinj; assumption.
      + apply NoDup_filter, HndB.
      + intros b. rewrite in_map_iff, filter_In. split.
        * intros (a & <- & Ha). apply filter_In in Ha as [Ha Hfa].
          split; [apply Hin, Ha|]. rewrite Hf; assumption.
        * intros [Hb Hfb]. destruct (Honto b Hb) as (a & Ha & <-). exists a. split; [reflexivity|].
          apply filter_In. split; [exact Ha|]. rewrite <- Hf; assumption.
  Qed.

  (** ** Local traces *)

  Lemma inv_list_app {G} (l1 l2 : list (ThreadEvent G)) :
    inv_list (l1 ++ l2) = inv_list l1 ++ inv_list l2.
  Proof. induction l1 as [|[t [h o|h o v]] l1 IH]; cbn; rewrite ?IH; reflexivity. Qed.

  (** The invocation at trace position [j] is the [n]-th invocation,
      [n] the number of invocations before [j]. *)
  Lemma inv_list_at {G} (l : list (ThreadEvent G)) j ev h o :
    nth_error l j = Some ev -> te_ev G ev = InvEv h o ->
    nth_error (inv_list l) (length (inv_list (firstn j l))) = Some (h, o).
  Proof.
    intros Hj He. destruct (nth_error_split l j Hj) as (l1 & l2 & -> & <-).
    rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r, inv_list_app.
    rewrite nth_error_app2, Nat.sub_diag by lia. cbn. rewrite He. reflexivity.
  Qed.

  Lemma inv_count_lt {G} (l : list (ThreadEvent G)) j j' ev h o :
    nth_error l j = Some ev -> te_ev G ev = InvEv h o -> j < j' ->
    length (inv_list (firstn j l)) < length (inv_list (firstn j' l)).
  Proof.
    intros Hj He Hlt. destruct (firstn_prefix l (S j) j' Hlt) as (l' & E).
    rewrite E, inv_list_app, length_app, SL.firstn_S_nth, Hj, inv_list_app, length_app.
    cbn. rewrite He. cbn. lia.
  Qed.

  (** Position of the [j]-th invocation. *)
  Fixpoint inv_pos {G} (j : nat) (l : list (ThreadEvent G)) : nat :=
    match l with
    | [] => 0
    | ev :: l' =>
        match te_ev G ev with
        | InvEv _ _ => match j with 0 => 0 | S j' => S (inv_pos j' l') end
        | ResEv _ _ _ => S (inv_pos j l')
        end
    end.

  Lemma inv_pos_spec {G} (l : list (ThreadEvent G)) : forall j h o,
    nth_error (inv_list l) j = Some (h, o) ->
    exists ev, nth_error l (inv_pos j l) = Some ev /\ te_ev G ev = InvEv h o /\
      length (inv_list (firstn (inv_pos j l) l)) = j.
  Proof.
    induction l as [|ev l IH]; intros j h o H; [destruct j; discriminate|].
    cbn in H |- *. destruct (te_ev G ev) as [h' o'|h' o' v] eqn:He.
    - destruct j as [|j]; cbn in H.
      + injection H as -> ->. exists ev. cbn. auto.
      + destruct (IH j h o H) as (ev' & H1 & H2 & H3). exists ev'. split; [exact H1|]. split; [exact H2|].
        cbn. rewrite He. cbn. rewrite H3. reflexivity.
    - destruct (IH j h o H) as (ev' & H1 & H2 & H3). exists ev'. split; [exact H1|]. split; [exact H2|].
      cbn. rewrite He. exact H3.
  Qed.

  Lemma inv_keys_tid {G} (l : list (ThreadEvent G)) t :
    Forall (fun ev => te_tid G ev = t) l -> invocation_keys l = map (fun ho => (t, fst ho)) (inv_list l).
  Proof.
    induction 1 as [|ev l Hev _ IH]; [reflexivity|].
    destruct ev as [t' [h o|h o v]]; cbn in *; subst; rewrite IH; reflexivity.
  Qed.

  Lemma res_list_in rc K (l : list (ThreadEvent (E rc K))) j ev h o v :
    nth_error l j = Some ev -> te_ev _ ev = ResEv h o v -> In (h, uc_of o v) (res_list l).
  Proof.
    revert j. induction l as [|ev' l IH]; intros j Hj He; [destruct j; discriminate|].
    rewrite res_list_cons. apply in_or_app. destruct j as [|j]; cbn in Hj.
    - injection Hj as ->. left. cbn. rewrite He. left. reflexivity.
    - right. eapply IH; eassumption.
  Qed.

  (** ** Decoding a block from a local trace *)

  Fixpoint res_find (h : nat) (l : list (nat * SL.UC)) : option SL.UC :=
    match l with
    | [] => None
    | (h', c) :: l' => if Nat.eqb h h' then Some c else res_find h l'
    end.

  Lemma res_find_in h c l : NoDup (map fst l) -> In (h, c) l -> res_find h l = Some c.
  Proof.
    induction l as [|[h' c'] l IH]; cbn; [intros _ []|].
    intros Hnd Hin. inversion Hnd as [|? ? Hni Hnd']; subst.
    destruct Hin as [E|Hin].
    - injection E as -> ->. rewrite Nat.eqb_refl. reflexivity.
    - destruct (Nat.eqb_spec h h') as [->|Hne].
      + exfalso. apply Hni. apply (in_map fst) in Hin. exact Hin.
      + apply IH; assumption.
  Qed.

  (** The read loop: failed iterations, then the last one. *)
  Fixpoint parse_read (l : list SL.UC) : list (nat * nat * nat) * (nat * nat * nat) :=
    match l with
    | SL.GT s :: SL.RmbC :: SL.RdX a :: SL.RdY b :: SL.RmbC :: SL.TT _ r :: l' =>
        if r then let p := parse_read l' in ((s, a, b) :: fst p, snd p) else ([], (s, a, b))
    | _ => ([], (0, 0, 0))
    end.

  Definition parse (l : list SL.UC) : SL.Blk :=
    match l with
    | SL.Acq :: _ :: SL.WrX vx :: SL.WrY vy :: _ => SL.BW vx vy
    | [SL.WrZ v] => SL.BZw v
    | [SL.RdZ v] => SL.BZr v
    | _ => match parse_read l with (fs, (s, a, b)) => SL.BR fs s a b end
    end.

  Lemma parse_read_spec fs s a b :
    parse_read (SL.fail_calls fs ++ SL.iter s a b false) = (fs, (s, a, b)).
  Proof.
    induction fs as [|[[s' a'] b'] fs IH]; [reflexivity|].
    change (SL.fail_calls (((s', a'), b') :: fs)) with (SL.iter s' a' b' true ++ SL.fail_calls fs).
    cbn [SL.iter app]. cbn [parse_read]. rewrite IH. reflexivity.
  Qed.

  Lemma parse_calls k : parse (SL.calls k) = k.
  Proof.
    destruct k as [vx vy|fs s a b|v|v]; try reflexivity.
    assert (E : parse (SL.calls (SL.BR fs s a b)) =
                match parse_read (SL.calls (SL.BR fs s a b)) with
                | (fs', (s', a', b')) => SL.BR fs' s' a' b' end).
    { destruct fs as [|[[s' a'] b'] fs]; reflexivity. }
    rewrite E. change (SL.calls (SL.BR fs s a b)) with (SL.fail_calls fs ++ SL.iter s a b false).
    rewrite parse_read_spec. reflexivity.
  Qed.

  (** The window call of a block, and facts about [blk_matches]. *)
  Definition wcall (k : SL.Blk) : SL.UC :=
    match k with
    | SL.BW _ _ => SL.WmbC | SL.BR _ _ _ _ => SL.RmbC | SL.BZw v => SL.WrZ v | SL.BZr v => SL.RdZ v
    end.

  Lemma wcall_at k : nth_error (SL.calls k) (SL.lpi k) = Some (wcall k).
  Proof.
    destruct k as [vx vy|fs s a b|v|v]; try reflexivity.
    cbn [SL.lpi wcall]. rewrite SL.calls_BR_final by lia. reflexivity.
  Qed.

  Definition ovk (k : SL.Blk) : SL.OvEv :=
    match k with
    | SL.BW x y => SL.OW x y | SL.BR _ _ a b => SL.OR a b | SL.BZw v => SL.OZW v | SL.BZr v => SL.OZR v
    end.

  (** Overlay events as [SeqLockCOH.OvEv]. *)
  Definition ovev_of (o : FOp) : far o -> SL.OvEv :=
    match o as o0 return far o0 -> SL.OvEv with
    | fWrite vx vy => fun _ => SL.OW vx vy
    | fRead => fun r => SL.OR (fst r) (snd r)
    | fZw v => fun _ => SL.OZW v
    | fZr => fun r => SL.OZR r
    end.

  Lemma ovk_matches op k ret : blk_matches op k ret -> ovk k = ovev_of op ret.
  Proof.
    destruct op; cbn; intros Hm.
    - subst k. reflexivity.
    - destruct Hm as (fs & s & a & b & -> & ->). reflexivity.
    - subst k. reflexivity.
    - destruct Hm as (v & -> & ->). reflexivity.
  Qed.

  Lemma is_sl_matches op k ret :
    blk_matches op k ret -> SL.is_sl k = match fcomp op with SL.CSL => true | SL.CZ => false end.
  Proof.
    destruct op; cbn; intros Hm.
    - subst k. reflexivity.
    - destruct Hm as (fs & s & a & b & -> & _). reflexivity.
    - subst k. reflexivity.
    - destruct Hm as (v & -> & _). reflexivity.
  Qed.

  (** Index, among the invocations, of the window call. *)
  Definition widx {G} (o : FOp) (l : list (ThreadEvent G)) : nat :=
    match o with fWrite _ _ => 1 | fRead => length (inv_list l) - 5 | fZw _ | fZr => 0 end.

  Lemma widx_lpi {G} op (l : list (ThreadEvent G)) k ret (cs : list (nat * SL.UC)) :
    blk_matches op k ret -> SL.calls k = map snd cs -> length (inv_list l) = length cs ->
    widx op l = SL.lpi k.
  Proof.
    intros Hm Hc Hl. destruct op; cbn in Hm |- *.
    - subst k. reflexivity.
    - destruct Hm as (fs & s & a & b & -> & _).
      rewrite Hl, <- (length_map snd cs), <- Hc, SL.length_calls_BR. cbn [SL.lpi]. lia.
    - subst k. reflexivity.
    - destruct Hm as (v & -> & _). reflexivity.
  Qed.

  (** ** Signatures, specifications, windows *)

  Section Signature.
    Context (rc : bool) (K : SL.TLCats).
    Local Abbreviation G := (E rc K).

    Definition keyE_dec : forall k k' : CallKey G, {k = k'} + {k <> k'}.
    Proof.
      intros [t h] [t' h']. destruct (Pos.eq_dec t t') as [->|Ht]; [|right; congruence].
      destruct (Nat.eq_dec h h') as [->|Hh]; [left; reflexivity|right; congruence].
    Defined.

    Definition keyF_dec : forall k k' : CallKey (F rc), {k = k'} + {k <> k'}.
    Proof.
      intros [t h] [t' h']. destruct (Pos.eq_dec t t') as [->|Ht]; [|right; congruence].
      destruct (Nat.eq_dec h h') as [->|Hh]; [left; reflexivity|right; congruence].
    Defined.

    (** Underlay components: the client cell z, and the rest. *)
    Definition compE (o : SOp) : SL.CompT :=
      match o with sWrZ _ | sRdZ => SL.CZ | _ => SL.CSL end.

    (** Categories of the table, as in [SeqLockCOH.ucat]. *)
    Definition catE (o : SOp) : WT.DCat := SL.ucat K (uc_of o (dflt o)).

    Definition uc (u : Op G) : SL.UC := uc_of (op_op u) (op_ret u).
    Definition uev (u : Op G) : SL.Ev := SL.mkEv (Pos.to_nat (fst (op_key u))) 0 (uc u).

    (** Sequential specifications of the underlay components.  [CSL]:
        TicketLock with version counter ⊗ x ⊗ y ⊗ barriers, i.e. the
        [SeqLockCOH.pre]/[post] steps succeed from [SeqLockCOH.init];
        [CZ]: a register. *)
    Fixpoint replay (s : SL.State) (l : list SL.Ev) : Prop :=
      match l with
      | [] => True
      | e :: l' => SL.pre s e = true /\ replay (SL.post s e) l'
      end.

    Fixpoint zreg (cur : nat) (l : list SL.UC) : Prop :=
      match l with
      | [] => True
      | c :: l' =>
          match c with
          | SL.WrZ v => zreg v l'
          | SL.RdZ v => v = cur /\ zreg cur l'
          | _ => zreg cur l'
          end
      end.

    Definition nuEc (c : SL.CompT) (w : list (Op G)) : Prop :=
      match c with
      | SL.CSL => replay SL.init (map uev w)
      | SL.CZ => zreg 0 (map uc w)
      end.

    (** Overlay specifications: [SeqLockCOH.nu_sl] and [nu_z]. *)
    Definition ovev (s : Op (F rc)) : SL.OvEv := ovev_of (op_op s) (op_ret s).

    Definition nuFc (c : SL.CompT) (h : list (Op (F rc))) : Prop :=
      match c with
      | SL.CSL => SL.nu_sl (map ovev h)
      | SL.CZ => SL.nu_z (map ovev h)
      end.

    Lemma E_compat o o' : semi_independent G o o' -> ~ WT.dtable rc (catE o) (catE o').
    Proof.
      intros H. change (sindep rc K o o') in H. unfold sindep, SL.upres in H.
      apply orb_false_iff in H as [_ H]. unfold WT.dtable, catE. congruence.
    Qed.

    Lemma F_cross o o' :
      fcomp o <> fcomp o' -> ~ WT.dtable rc (fcat o) (fcat o') -> semi_independent (F rc) o o'.
    Proof.
      intros Hc Hn. change (findep rc o o'). split; [exact Hc|].
      unfold WT.dtable in Hn. destruct (WT.dto rc (fcat o) (fcat o')); [contradiction (Hn eq_refl)|reflexivity].
    Qed.

    Lemma nuF_nil c : nuFc c [].
    Proof. destruct c; exact I. Qed.

    (** *** Windows *)

    (** The window of an overlay call: the position in its local trace of
        the [widx]-th invocation. *)
    Definition wsel (o : FOp) (l : list (ThreadEvent G)) : nat := inv_pos (widx o l) l.

    (** The (handle, call) list of a local trace: the invocations in
        order, each with the response to its handle. *)
    Definition decode (l : list (ThreadEvent G)) : list (nat * SL.UC) :=
      map (fun ho => (fst ho, match res_find (fst ho) (res_list l) with Some c => c | None => SL.WmbC end))
          (inv_list l).

    Lemma decode_spec (l : list (ThreadEvent G)) (cs : list (nat * SL.UC)) :
      inv_list l = map (fun c => (fst c, op_of (snd c))) cs -> NoDup (map fst cs) ->
      Permutation (res_list l) cs -> decode l = cs.
    Proof.
      intros Hinv Hnd Hp. unfold decode. rewrite Hinv, map_map.
      transitivity (map (fun c => c) cs); [|apply map_id].
      apply map_ext_in. intros [h c] Hin. cbn.
      rewrite (res_find_in h c (res_list l)); [reflexivity| |].
      - apply (Permutation_NoDup (Permutation_map fst (Permutation_sym Hp))). exact Hnd.
      - apply (Permutation_in _ (Permutation_sym Hp)). exact Hin.
    Qed.

    (** [SeqLockProg.M_shape], with the block decoded from the trace. *)
    Lemma produced_shape t op tr ret :
      program_produces_tagged t (M rc K op t) tr ret ->
      SL.calls (parse (map snd (decode (map untag tr)))) = map snd (decode (map untag tr)) /\
      inv_list (map untag tr) = map (fun c => (fst c, op_of (snd c))) (decode (map untag tr)) /\
      NoDup (map fst (decode (map untag tr))) /\
      Permutation (res_list (map untag tr)) (decode (map untag tr)) /\
      Forall (fun ev => te_tid _ ev = t) (map untag tr) /\
      blk_matches op (parse (map snd (decode (map untag tr)))) ret.
    Proof.
      intros Hp. destruct (M_shape rc K op t tr ret Hp) as (k & cs & Hk & Hinv & Hnd & Hperm & Htid & Hm).
      assert (Hd : decode (map untag tr) = cs) by (apply decode_spec; assumption).
      rewrite Hd, <- Hk, parse_calls. auto 6.
    Qed.

    Lemma window_at t op tr ret :
      program_produces_tagged t (M rc K op t) tr ret ->
      exists h,
        BL.inv_in (map untag tr) (wsel op (map untag tr)) (t, h)
          (op_of (wcall (parse (map snd (decode (map untag tr)))))) /\
        length (inv_list (firstn (wsel op (map untag tr)) (map untag tr))) =
          SL.lpi (parse (map snd (decode (map untag tr)))).
    Proof.
      intros Hp. destruct (produced_shape t op tr ret Hp) as (Hc & Hinv & Hnd & Hperm & Htid & Hm).
      set (l := map untag tr) in *. set (k := parse (map snd (decode l))) in *.
      assert (Hw : widx op l = SL.lpi k).
      { apply (widx_lpi op l k ret (decode l) Hm Hc). rewrite Hinv, length_map. reflexivity. }
      pose proof (wcall_at k) as Hwc. rewrite Hc, nth_error_map in Hwc.
      destruct (nth_error (decode l) (SL.lpi k)) as [[h c]|] eqn:Hd; cbn in Hwc; [|discriminate].
      injection Hwc as Hwc.
      assert (Hi : nth_error (inv_list l) (SL.lpi k) = Some (h, op_of (wcall k))).
      { rewrite Hinv, nth_error_map, Hd. cbn. rewrite Hwc. reflexivity. }
      destruct (inv_pos_spec l _ _ _ Hi) as (ev & Hev & He & Hlen).
      exists h. unfold wsel. rewrite Hw. split; [|exact Hlen].
      unfold BL.inv_in, BL.inv_ev. rewrite Hev. f_equal.
      rewrite Forall_forall in Htid. specialize (Htid _ (nth_error_In _ _ Hev)).
      destruct ev as [t' e]. cbn in He, Htid |- *. subst. reflexivity.
    Qed.

    Lemma catE_wcall op k ret : blk_matches op k ret -> catE (op_of (wcall k)) = fcat op.
    Proof.
      intros Hm. destruct op; cbn in Hm.
      - subst k. reflexivity.
      - destruct Hm as (? & ? & ? & ? & -> & _). reflexivity.
      - subst k. reflexivity.
      - destruct Hm as (? & -> & _). reflexivity.
    Qed.

    (** Dominance: every window is one call of the overlay category. *)
    Lemma window_bodies t op tr ret :
      program_produces_tagged t (M rc K op t) tr ret ->
      exists klo olo khi ohi,
        BL.inv_in (map untag tr) (wsel op (map untag tr)) klo olo /\
        BL.inv_in (map untag tr) (wsel op (map untag tr)) khi ohi /\
        WT.out_le (WT.dtable rc) (fcat op) (catE ohi) /\ WT.in_le (WT.dtable rc) (fcat op) (catE olo).
    Proof.
      intros Hp. destruct (window_at t op tr ret Hp) as (h & Hin & _).
      destruct (produced_shape t op tr ret Hp) as (_ & _ & _ & _ & _ & Hm).
      do 4 eexists. split; [exact Hin|]. split; [exact Hin|].
      rewrite (catE_wcall _ _ _ Hm). split; [apply WT.out_le_refl|apply WT.in_le_refl].
    Qed.
  End Signature.

  (** ** Merging the component specifications *)

  Section Merge.
    Context (rc : bool) (K : SL.TLCats).
    Local Abbreviation G := (E rc K).

    (** [CSL] calls touch only [own], [hold], [sx], [sy]; [CZ] calls only
        [sz]. *)
    Lemma replay_merge (l : list (Op G)) : forall o hd x y zA z,
      replay (SL.mkSt o hd x y zA) (map (uev rc K) (BL.proj_E (E := G) SL.comp_dec compE SL.CSL l)) ->
      zreg z (map (uc rc K) (BL.proj_E (E := G) SL.comp_dec compE SL.CZ l)) ->
      replay (SL.mkSt o hd x y z) (map (uev rc K) l).
    Proof.
      induction l as [|u l IH]; intros o hd x y zA z H1 H2; [exact I|].
      destruct u as [[tp h] op ret]. destruct op; cbn in H1, H2 |- *;
        first [ destruct H1 as [Hp H1]; split; [exact Hp|]; eapply IH; eassumption
              | split; [reflexivity|]; eapply IH; eassumption
              | destruct H2 as [-> H2]; split; [apply Nat.eqb_refl|]; eapply IH; eassumption ].
    Qed.

    Lemma nuE_replay (w : list (Op G)) :
      BL.nuE_all (E := G) SL.comp_dec compE (nuEc rc K) w -> replay SL.init (map (uev rc K) w).
    Proof. intros H. exact (replay_merge w 0 None 0 0 0 0 (H SL.CSL) (H SL.CZ)). Qed.
  End Merge.

  Lemma replay_pre s l : replay s l ->
    forall p e, nth_error l p = Some e -> SL.pre (SL.run s (firstn p l)) e = true.
  Proof.
    revert s. induction l as [|e' l IH]; intros s H p e Hp; [destruct p; discriminate|].
    destruct H as [Hpre H]. destruct p as [|p]; cbn in Hp |- *.
    - injection Hp as <-. exact Hpre.
    - exact (IH _ H p e Hp).
  Qed.

  (** ** The underlay witness as an execution of [SeqLockCOH] *)

  Section Execution.
    Context (rc : bool) (K : SL.TLCats).
    Local Abbreviation G := (E rc K).
    Context (VE : LTS G).
    Context (IT : list (@ITraceEvent G (F rc))) (ic : @IConfig G (F rc) VE).
    Context (Hinv : IInv VE (M rc K) IT ic) (Hq : ic_queue VE ic = []).
    Context (Wu : list (Op G)).
    Context (HWu : rel_lin_witness BL.usel IT (semi_independent G)
                     (BL.nuE_all (E := G) SL.comp_dec compE (nuEc rc K)) Wu).
    Context (r0 : @InvRec G (F rc)).

    Local Abbreviation Rec := (@InvRec G (F rc)).

    (** The (handle, call) list and the block of an overlay call. *)
    Definition dcs (r : Rec) : list (nat * SL.UC) := decode rc K (BL.ltr r).
    Definition blk_of (r : Rec) : SL.Blk := parse (map snd (dcs r)).

    (** Threads as natural numbers; the calls of a thread in invocation
        order. *)
    Definition rth (r : Rec) : nat := Pos.to_nat (fst (ir_key r)).
    Definition recs (t : nat) : list Rec := filter (fun r => Nat.eqb (rth r) t) (ic_invs VE ic).
    Definition tcs (t : nat) : list (nat * SL.UC) := flat_map dcs (recs t).

    (** An underlay call: its thread, its index in the thread's calls. *)
    Definition tn (u : Op G) : nat := Pos.to_nat (fst (op_key u)).
    Definition ix (u : Op G) : nat := lindex Nat.eq_dec (snd (op_key u)) (map fst (tcs (tn u))).
    Definition toEv (u : Op G) : SL.Ev := SL.mkEv (tn u) (ix u) (uc rc K u).

    Definition SX : SL.Exec := {|
      SL.ths := nodup Nat.eq_dec (map rth (ic_invs VE ic));
      SL.prog := fun t => map blk_of (recs t);
      SL.wit := map toEv Wu;
    |}.

    (** *** Records *)

    Lemma rec_shape r : In r (ic_invs VE ic) ->
      SL.calls (blk_of r) = map snd (dcs r) /\
      inv_list (BL.ltr r) = map (fun c => (fst c, op_of (snd c))) (dcs r) /\
      NoDup (map fst (dcs r)) /\
      Permutation (res_list (BL.ltr r)) (dcs r) /\
      Forall (fun ev => te_tid _ ev = fst (ir_key r)) (BL.ltr r) /\
      blk_matches (ir_op r) (blk_of r) (ir_ret r).
    Proof. intros Hr. exact (produced_shape rc K _ _ _ _ (ii_produced _ _ _ _ Hinv r Hr)). Qed.

    Lemma rec_window r : In r (ic_invs VE ic) ->
      exists h, BL.inv_in (BL.ltr r) (wsel rc K (ir_op r) (BL.ltr r)) (fst (ir_key r), h)
                  (op_of (wcall (blk_of r))) /\
        length (inv_list (firstn (wsel rc K (ir_op r) (BL.ltr r)) (BL.ltr r))) = SL.lpi (blk_of r).
    Proof. intros Hr. exact (window_at rc K _ _ _ _ (ii_produced _ _ _ _ Hinv r Hr)). Qed.

    Lemma recs_in t r : In r (recs t) <-> In r (ic_invs VE ic) /\ rth r = t.
    Proof. unfold recs. rewrite filter_In, Nat.eqb_eq. tauto. Qed.

    Lemma rec_keys r : In r (ic_invs VE ic) ->
      invocation_keys (BL.ltr r) = map (fun c => (fst (ir_key r), fst c)) (dcs r).
    Proof.
      intros Hr. destruct (rec_shape r Hr) as (_ & Hinvl & _ & _ & Htid & _).
      rewrite (inv_keys_tid _ _ Htid), Hinvl, map_map. reflexivity.
    Qed.

    Lemma tcs_nodup t : NoDup (map fst (tcs t)).
    Proof.
      pose proof (ii_used_nodup _ _ _ _ Hinv) as Hnd. rewrite (ii_used _ _ _ _ Hinv) in Hnd.
      apply (NoDup_flat_map_filter _ (fun r => Nat.eqb (rth r) t)) in Hnd.
      change (filter (fun r => Nat.eqb (rth r) t) (ic_invs VE ic)) with (recs t) in Hnd.
      rewrite (flat_map_ext_in _ (fun r => map (fun c => (fst (ir_key r), fst c)) (dcs r))) in Hnd.
      2:{ intros r Hr. apply recs_in in Hr as [Hr _]. exact (rec_keys r Hr). }
      apply NoDup_snd_same_fst in Hnd.
      - rewrite map_flat_map in Hnd. unfold tcs. rewrite map_flat_map.
        replace (flat_map (fun a => map fst (dcs a)) (recs t))
          with (flat_map (fun a => map snd (map (fun c => (fst (ir_key a), fst c)) (dcs a))) (recs t));
          [exact Hnd|].
        apply flat_map_ext_in. intros r _. rewrite map_map. reflexivity.
      - intros a b Ha Hb.
        apply in_flat_map in Ha as (r & Hr & Ha). apply in_flat_map in Hb as (r' & Hr' & Hb).
        apply in_map_iff in Ha as (c & <- & _). apply in_map_iff in Hb as (c' & <- & _).
        apply recs_in in Hr as [_ Hr]. apply recs_in in Hr' as [_ Hr']. cbn.
        apply Pos2Nat.inj. transitivity t; [exact Hr|symmetry; exact Hr'].
    Qed.

    Lemma recs_keys_nodup t : NoDup (map ir_key (recs t)).
    Proof. apply BL.nodup_map_filter. exact (ii_invs_nodup _ _ _ _ Hinv). Qed.

    Lemma recs_nodup t : NoDup (recs t).
    Proof. exact (NoDup_map_inv _ _ (recs_keys_nodup t)). Qed.

    Lemma invs_sorted : StronglySorted (fun r r' => ir_pos r < ir_pos r') (ic_invs VE ic).
    Proof.
      apply ss_of_split. intros pre a post E b Hb. exact (proj2 (ii_pos _ _ _ _ Hinv pre a post E) b Hb).
    Qed.

    Lemma recs_sorted t : StronglySorted (fun r r' => ir_pos r < ir_pos r') (recs t).
    Proof. apply WC.ss_filter, invs_sorted. Qed.

    (** *** Traces and offsets *)

    Lemma trace_map_blk L : (forall r, In r L -> In r (ic_invs VE ic)) ->
      SL.trace (map blk_of L) = map snd (flat_map dcs L).
    Proof.
      induction L as [|r L IH]; intros HL; [reflexivity|].
      change (SL.trace (map blk_of (r :: L))) with (SL.calls (blk_of r) ++ SL.trace (map blk_of L)).
      cbn [flat_map]. rewrite map_app, (proj1 (rec_shape r (HL r (or_introl eq_refl)))), IH; [reflexivity|].
      intros r' Hr'. apply HL. right. exact Hr'.
    Qed.

    Lemma prog_trace t : SL.trace (SL.prog SX t) = map snd (tcs t).
    Proof. apply trace_map_blk. intros r Hr. apply recs_in in Hr. tauto. Qed.

    Lemma off_foff t j : SL.off (SL.prog SX t) j = foff dcs (recs t) j.
    Proof.
      unfold SL.off, foff. change (SL.prog SX t) with (map blk_of (recs t)).
      rewrite firstn_map, trace_map_blk, length_map; [reflexivity|].
      intros r Hr. apply in_firstn in Hr. apply recs_in in Hr. tauto.
    Qed.

    (** *** Where the calls of the witness are *)

    Lemma wu_src u : In u Wu -> exists r j m p, BL.usrc VE IT ic u r j m p.
    Proof. exact (BL.wu_src VE (M rc K) SL.comp_dec compE (nuEc rc K) IT ic Hinv Wu HWu u). Qed.

    Lemma usrc_inv u r j m p : BL.usrc VE IT ic u r j m p ->
      In r (ic_invs VE ic) /\ nth_error (BL.ltr r) j = Some (BL.inv_ev (op_key u) (op_op u)).
    Proof.
      intros (Hr & Hj & Hm & _). split; [exact Hr|].
      unfold BL.ltr. rewrite nth_error_map, Hj. cbn. rewrite Hm. reflexivity.
    Qed.

    (** The index of a call: offset of its overlay call, plus the number
        of invocations before it in the local trace. *)
    Lemma ix_src u r j m p jr :
      BL.usrc VE IT ic u r j m p -> nth_error (recs (rth r)) jr = Some r ->
      tn u = rth r /\
      ix u = foff dcs (recs (rth r)) jr + length (inv_list (firstn j (BL.ltr r))) /\
      exists c, nth_error (dcs r) (length (inv_list (firstn j (BL.ltr r)))) = Some (snd (op_key u), c).
    Proof.
      intros Hs Hjr.
      assert (Ht : tn u = rth r).
      { unfold tn, rth. rewrite (BL.usrc_tid VE (M rc K) IT ic Hinv u r j m p Hs). reflexivity. }
      destruct (usrc_inv u r j m p Hs) as [Hr Hj].
      destruct (rec_shape r Hr) as (_ & Hinvl & _ & _ & _ & _).
      pose proof (inv_list_at _ _ _ (snd (op_key u)) (op_op u) Hj eq_refl) as Hn.
      set (n := length (inv_list (firstn j (BL.ltr r)))) in *.
      rewrite Hinvl, nth_error_map in Hn.
      destruct (nth_error (dcs r) n) as [[h c]|] eqn:Hd; cbn in Hn; [|discriminate].
      injection Hn as Eh _. subst h.
      split; [exact Ht|]. split; [|exists c; reflexivity].
      unfold ix. rewrite Ht. apply lindex_of_nth; [apply tcs_nodup|].
      unfold tcs. rewrite nth_error_map, (flat_map_nth dcs _ _ _ _ _ Hjr Hd). reflexivity.
    Qed.

    Lemma wu_call u : In u Wu ->
      In (tn u) (SL.ths SX) /\ nth_error (tcs (tn u)) (ix u) = Some (snd (op_key u), uc rc K u).
    Proof.
      intros Hu. destruct (wu_src u Hu) as (r & j & m & p & Hs).
      destruct (usrc_inv u r j m p Hs) as [Hr Hj].
      assert (Hin : In r (recs (rth r))) by (apply recs_in; auto).
      destruct (In_nth_error _ _ Hin) as [jr Hjr].
      destruct (ix_src u r j m p jr Hs Hjr) as (Ht & Hix & c & Hc).
      assert (Ec : c = uc rc K u).
      { destruct (BL.wu_res_src VE (M rc K) (keyE_dec rc K) SL.comp_dec compE (nuEc rc K) IT ic Hinv Wu HWu
                    r0 u Hu) as (r' & j' & m' & p' & Hr' & Hj' & Hm' & _ & Ho').
        assert (r' = r).
        { apply (record_key_unique _ _ _ _ Hinv); [exact Hr'|exact Hr|].
          rewrite <- Ho'. exact (BL.usrc_owner VE (M rc K) (keyE_dec rc K) IT ic Hinv r0 u r j m p Hs). }
        subst r'.
        destruct (rec_shape r Hr) as (_ & _ & Hnd & Hperm & _ & _).
        assert (Hres : In (snd (op_key u), uc rc K u) (res_list (BL.ltr r))).
        { unfold uc. apply (res_list_in rc K (BL.ltr r) j' (untag m') _ (op_op u) (op_ret u)).
          - unfold BL.ltr. rewrite nth_error_map, Hj'. reflexivity.
          - rewrite Hm'. reflexivity. }
        apply (Permutation_in _ Hperm) in Hres.
        exact (pair_nodup_fst (dcs r) _ _ _ Hnd (nth_error_In _ _ Hc) Hres). }
      subst c. split.
      - rewrite Ht. cbn [SL.ths SX]. apply nodup_In, in_map, Hr.
      - rewrite Hix, Ht. unfold tcs. apply (flat_map_nth dcs _ _ _ _ _ Hjr Hc).
    Qed.

    Lemma toEv_evt u : In u Wu -> toEv u = SL.evt SX (tn u) (ix u).
    Proof.
      intros Hu. destruct (wu_call u Hu) as [_ Hn]. unfold SL.evt, toEv. f_equal.
      symmetry. apply nth_error_nth. rewrite prog_trace, nth_error_map, Hn. reflexivity.
    Qed.

    Lemma wit_nodup : NoDup (map toEv Wu).
    Proof.
      pose proof HWu as (_ & Hnd & _). apply NoDup_map_in; [exact (NoDup_map_inv _ _ Hnd)|].
      intros u u' Hu Hu' Eq. unfold toEv in Eq. injection Eq as Et Ei _.
      apply (BL.wu_key_inj (E := G) SL.comp_dec compE (nuEc rc K) IT Wu HWu u u' Hu Hu').
      destruct (wu_call u Hu) as [_ Hn]. destruct (wu_call u' Hu') as [_ Hn'].
      rewrite <- Et, <- Ei, Hn in Hn'. injection Hn' as Eh _.
      apply injective_projections; [|exact Eh].
      apply Pos2Nat.inj. exact Et.
    Qed.

    Lemma key_index_lindex k l : BL.key_index (keyE_dec rc K) k l = lindex (keyE_dec rc K) k l.
    Proof. induction l as [|k' l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

    Lemma idx_pos u : In u Wu -> SL.idx (toEv u) (SL.wit SX) = BL.pos (keyE_dec rc K) Wu u.
    Proof.
      intros Hu. unfold BL.pos. rewrite key_index_lindex.
      set (i := lindex (keyE_dec rc K) (op_key u) (map op_key Wu)).
      assert (Hi : nth_error (map op_key Wu) i = Some (op_key u)) by (apply lindex_nth, in_map, Hu).
      rewrite nth_error_map in Hi.
      destruct (nth_error Wu i) as [u'|] eqn:Hu'; cbn in Hi; [|discriminate].
      injection Hi as Hk.
      assert (u' = u).
      { apply (BL.wu_key_inj (E := G) SL.comp_dec compE (nuEc rc K) IT Wu HWu); [|exact Hu|exact Hk].
        eapply nth_error_In. exact Hu'. }
      subst u'. apply SL.nth_idx; [exact wit_nodup|].
      cbn [SL.wit SX]. rewrite nth_error_map, Hu'. reflexivity.
    Qed.

    (** Calls of one thread with increasing indices are enqueued in this
        order. *)
    Lemma src_order u1 u2 r1 j1 m1 p1 r2 j2 m2 p2 :
      BL.usrc VE IT ic u1 r1 j1 m1 p1 -> BL.usrc VE IT ic u2 r2 j2 m2 p2 ->
      tn u1 = tn u2 -> ix u1 < ix u2 -> ir_start r1 + j1 < ir_start r2 + j2.
    Proof.
      intros Hs1 Hs2 Ht Hlt.
      destruct (usrc_inv _ _ _ _ _ Hs1) as [Hr1 Hj1]. destruct (usrc_inv _ _ _ _ _ Hs2) as [Hr2 Hj2].
      assert (Hin1 : In r1 (recs (rth r1))) by (apply recs_in; auto).
      assert (Hin2 : In r2 (recs (rth r2))) by (apply recs_in; auto).
      destruct (In_nth_error _ _ Hin1) as [jr1 Hjr1]. destruct (In_nth_error _ _ Hin2) as [jr2 Hjr2].
      destruct (ix_src u1 r1 j1 m1 p1 jr1 Hs1 Hjr1) as (Ht1 & Hix1 & c1 & Hc1).
      destruct (ix_src u2 r2 j2 m2 p2 jr2 Hs2 Hjr2) as (Ht2 & Hix2 & c2 & Hc2).
      assert (Et : rth r1 = rth r2) by congruence.
      rewrite <- Et in Hjr2, Hix2.
      set (t := rth r1) in *.
      destruct (Nat.lt_trichotomy jr1 jr2) as [Hjr|[<-|Hjr]].
      - assert (Hpos : ir_pos r1 < ir_pos r2) by exact (ss_nth _ _ _ _ _ _ (recs_sorted t) Hjr1 Hjr2 Hjr).
        pose proof Hs1 as (_ & Hj1' & _ & _). pose proof Hs2 as (_ & Hj2' & _ & _).
        exact (record_ids_ordered _ _ _ _ Hinv r1 r2
                 (ir_start r1 + j1, Build_TaggedScheduledEvent (ir_key r1) m1)
                 (ir_start r2 + j2, Build_TaggedScheduledEvent (ir_key r2) m2)
                 Hr1 Hr2 Hpos (block_of_trace r1 j1 m1 Hj1') (block_of_trace r2 j2 m2 Hj2')).
      - rewrite Hjr1 in Hjr2. injection Hjr2 as <-.
        destruct (Nat.lt_trichotomy j1 j2) as [H|[<-|H]]; [lia|lia|].
        exfalso. pose proof (inv_count_lt (BL.ltr r1) j2 j1 _ _ _ Hj2 eq_refl H). lia.
      - exfalso.
        assert (Hn2 : length (inv_list (firstn j2 (BL.ltr r2))) < length (dcs r2))
          by (apply nth_error_Some; congruence).
        pose proof (foff_lt dcs (recs t) jr2 jr1 r2 _ Hjr2 Hn2 Hjr). lia.
    Qed.

    (** *** Well-formedness *)

    (** [pre] and [post] do not look at the index. *)
    Lemma replay_toEv l : forall s, replay s (map (uev rc K) l) -> replay s (map toEv l).
    Proof.
      induction l as [|u l IH]; intros s H; [exact I|].
      destruct H as [Hp H]. split; [exact Hp|]. exact (IH _ H).
    Qed.

    Lemma wit_replay : replay SL.init (map toEv Wu).
    Proof.
      pose proof HWu as (HnuE & _). exact (replay_toEv Wu _ (nuE_replay rc K Wu HnuE)).
    Qed.

    Lemma SX_wf : SL.WF rc K SX.
    Proof.
      constructor.
      - exact wit_nodup.
      - apply NoDup_nodup.
      - intros e He. cbn [SL.wit SX] in He. apply in_map_iff in He as (u & <- & Hu).
        destruct (wu_call u Hu) as [Ht Hn]. split; [exact Ht|].
        change (nth_error (SL.trace (SL.prog SX (tn u))) (ix u) = Some (uc rc K u)).
        rewrite prog_trace, nth_error_map, Hn. reflexivity.
      - intros t i _ Hi.
        rewrite prog_trace, length_map in Hi.
        destruct (nth_error (tcs t) i) as [[h c]|] eqn:Hti; [|apply nth_error_None in Hti; lia].
        pose proof Hti as Hti'. unfold tcs in Hti'.
        destruct (flat_map_nth_inv dcs _ _ _ Hti') as (jr & r & i' & Hjr & Ei & Hc).
        assert (Hr : In r (recs t)) by (eapply nth_error_In; exact Hjr).
        apply recs_in in Hr as [Hr Hrt].
        destruct (rec_shape r Hr) as (_ & Hinvl & _ & _ & Htid & _).
        assert (Hil : nth_error (inv_list (BL.ltr r)) i' = Some (h, op_of c))
          by (rewrite Hinvl, nth_error_map, Hc; reflexivity).
        destruct (inv_pos_spec _ _ _ _ Hil) as (ev & Hev & He & _).
        set (jp := inv_pos i' (BL.ltr r)) in *.
        assert (Hev' := Hev). unfold BL.ltr in Hev'. rewrite nth_error_map in Hev'.
        destruct (nth_error (ir_trace r) jp) as [m|] eqn:Hm; cbn in Hev'; [|discriminate].
        injection Hev' as Hev'.
        destruct (complete_all_emitted _ _ _ _ Hinv r jp m Hq Hr Hm) as (p & Hp).
        pose proof HWu as (_ & _ & _ & Hall & _).
        assert (Htev : te_tid _ ev = fst (ir_key r)).
        { rewrite Forall_forall in Htid. apply Htid. eapply nth_error_In. exact Hev. }
        destruct (Hall p (fst (ir_key r), h) (op_of c)) as (u & Hu & Hk).
        { exists (IUnder (ir_start r + jp, Build_TaggedScheduledEvent (ir_key r) m)).
          split; [exact Hp|].
          change (Some (untag m) = Some (Build_ThreadEvent (fst (ir_key r)) (@InvEv G h (op_of c)))).
          rewrite Hev'. destruct ev as [t' e]. cbn in He, Htev. subst. reflexivity. }
        assert (Htu : tn u = t) by (unfold tn; rewrite Hk; exact Hrt).
        assert (Hix : ix u = i).
        { unfold ix. rewrite Htu, Hk. apply lindex_of_nth; [apply tcs_nodup|].
          rewrite nth_error_map, Hti. reflexivity. }
        rewrite <- Hix, <- Htu, <- (toEv_evt u Hu). cbn [SL.wit SX]. apply in_map, Hu.
      - intros e1 e2 He1 He2 Ht Hlt Hu.
        cbn [SL.wit SX] in He1, He2.
        apply in_map_iff in He1 as (u1 & <- & Hu1). apply in_map_iff in He2 as (u2 & <- & Hu2).
        cbn [toEv SL.th SL.ix SL.call] in Ht, Hlt, Hu.
        rewrite (idx_pos u1 Hu1), (idx_pos u2 Hu2).
        apply (BL.before_pos (keyE_dec rc K) SL.comp_dec compE (nuEc rc K) IT Wu HWu).
        destruct (wu_src u1 Hu1) as (r1 & j1 & m1 & p1 & Hs1).
        destruct (wu_src u2 Hu2) as (r2 & j2 & m2 & p2 & Hs2).
        apply (BL.inv_order VE (M rc K) SL.comp_dec compE (nuEc rc K) IT ic Hinv Wu HWu
                 u1 u2 r1 j1 m1 p1 r2 j2 m2 p2 Hu1 Hu2 Hs1 Hs2).
        + exact (src_order u1 u2 r1 j1 m1 p1 r2 j2 m2 p2 Hs1 Hs2 Ht Hlt).
        + apply Pos2Nat.inj. exact Ht.
        + intros Hsi. change (sindep rc K (op_op u1) (op_op u2)) in Hsi. unfold sindep in Hsi.
          unfold uc in Hu. rewrite upres_ret_indep in Hu. congruence.
      - intros p e Hn. unfold SL.at_. exact (replay_pre SL.init _ wit_replay p e Hn).
    Qed.
  End Execution.

  (** ** Transport to the overlay

      The overlay calls ([secs]) are in bijection with the operations of
      [SX] ([phi]: thread, rank among the thread's calls).  Along [phi]
      the window call has the position [SeqLockCOH.lpq], the overlay
      event is [SeqLockCOH.ovl], the component is [SeqLockCOH.is_sl_op],
      and program order is block order. *)

  Section Transport.
    Context (rc : bool) (K : SL.TLCats) (HK : SL.K_ok K = true).
    Local Abbreviation G := (E rc K).
    Context (VE : LTS G).
    Context (IT : list (@ITraceEvent G (F rc))) (ic : @IConfig G (F rc) VE).
    Context (Hinv : IInv VE (M rc K) IT ic) (Hq : ic_queue VE ic = []).
    Context (Wu : list (Op G)).
    Context (HWu : rel_lin_witness BL.usel IT (semi_independent G)
                     (BL.nuE_all (E := G) SL.comp_dec compE (nuEc rc K)) Wu).
    Context (r0 : @InvRec G (F rc)) (u0 : Op G).

    Local Abbreviation X := (SX rc K VE ic Wu).
    Local Abbreviation secs := (BL.secs VE ic).

    Lemma X_wf : SL.WF rc K X.
    Proof. exact (SX_wf rc K VE IT ic Hinv Hq Wu HWu r0). Qed.

    (** The linearization call of an overlay call: its window call. *)
    Definition lpu : CallKey (F rc) -> Op G := WLT.lo VE (keyE_dec rc K) (keyF_dec rc) (wsel rc K) ic Wu r0 u0.

    (** Overlay calls as operations [(thread, block index)] of [X]. *)
    Definition kpos (s : CallKey (F rc)) : nat :=
      lindex (keyF_dec rc) s (map ir_key (recs rc K VE ic (Pos.to_nat (fst s)))).
    Definition phi (s : CallKey (F rc)) : nat * nat := (Pos.to_nat (fst s), kpos s).

    Lemma phi_rec r : In r (ic_invs VE ic) ->
      phi (ir_key r) = (rth rc K r, kpos (ir_key r)) /\
      nth_error (recs rc K VE ic (rth rc K r)) (kpos (ir_key r)) = Some r.
    Proof.
      intros Hr. split; [reflexivity|].
      assert (Hin : In (ir_key r) (map ir_key (recs rc K VE ic (rth rc K r)))).
      { apply in_map. apply recs_in. auto. }
      pose proof (lindex_nth (keyF_dec rc) _ _ Hin) as Hn.
      change (nth_error (recs rc K VE ic (rth rc K r))
                (lindex (keyF_dec rc) (ir_key r) (map ir_key (recs rc K VE ic (rth rc K r)))) = Some r).
      rewrite nth_error_map in Hn.
      destruct (nth_error (recs rc K VE ic (rth rc K r)) _) as [r'|] eqn:Er; cbn in Hn; [|discriminate].
      injection Hn as Hk. f_equal. apply (record_key_unique _ _ _ _ Hinv); [|exact Hr|exact Hk].
      apply (proj1 (proj1 (recs_in rc K VE ic _ _) (nth_error_In _ _ Er))).
    Qed.

    Lemma phi_all_ops r : In r (ic_invs VE ic) -> In (phi (ir_key r)) (SL.all_ops X).
    Proof.
      intros Hr. destruct (phi_rec r Hr) as [-> Hn]. apply SL.all_ops_In. cbn [fst snd]. split.
      - cbn [SL.ths SX]. apply nodup_In, in_map, Hr.
      - cbn [SL.prog SX]. rewrite length_map. apply nth_error_Some. congruence.
    Qed.

    Lemma phi_onto q : In q (SL.all_ops X) -> exists r, In r (ic_invs VE ic) /\ phi (ir_key r) = q.
    Proof.
      intros Hq'. apply SL.all_ops_In in Hq' as [_ Hj]. destruct q as [t j]. cbn [fst snd SL.prog SX] in *.
      rewrite length_map in Hj.
      destruct (nth_error (recs rc K VE ic t) j) as [r|] eqn:Er; [|apply nth_error_None in Er; lia].
      assert (Hr : In r (recs rc K VE ic t)) by (eapply nth_error_In; exact Er).
      apply (recs_in rc K VE ic) in Hr as [Hr Hrt].
      exists r. split; [exact Hr|]. destruct (phi_rec r Hr) as [-> Hn]. rewrite Hrt in *. f_equal.
      exact (nth_error_nodup_inj _ _ _ _ (recs_nodup rc K VE IT ic Hinv t) Hn Er).
    Qed.

    Lemma phi_inj r r' : In r (ic_invs VE ic) -> In r' (ic_invs VE ic) ->
      phi (ir_key r) = phi (ir_key r') -> r = r'.
    Proof.
      intros Hr Hr' Eq. destruct (phi_rec r Hr) as [E1 Hn]. destruct (phi_rec r' Hr') as [E2 Hn'].
      rewrite E1, E2 in Eq. injection Eq as Et Ek. rewrite Et, Ek in Hn. congruence.
    Qed.

    Lemma phi_blk r : In r (ic_invs VE ic) -> SL.blk X (phi (ir_key r)) = Some (blk_of rc K r).
    Proof.
      intros Hr. unfold SL.blk. destruct (phi_rec r Hr) as [-> Hn]. cbn [fst snd SL.prog SX].
      rewrite nth_error_map, Hn. reflexivity.
    Qed.

    Lemma lpu_src r : In r (ic_invs VE ic) ->
      In (lpu (ir_key r)) Wu /\
      exists m p, BL.usrc VE IT ic (lpu (ir_key r)) r (wsel rc K (ir_op r) (BL.ltr r)) m p.
    Proof.
      intros Hr. destruct (rec_window rc K VE IT ic Hinv r Hr) as (h & Hin & _).
      destruct (WLT.call_at_spec VE (M rc K) (keyE_dec rc K) (keyF_dec rc) SL.comp_dec compE (nuEc rc K)
                  IT ic Hinv Hq Wu HWu r0 u0 (wsel rc K) r _ _ _ Hr eq_refl Hin) as (m & p & Hs & Hu & _).
      split; [exact Hu|]. exists m, p. exact Hs.
    Qed.

    (** The position of the linearization call is [SeqLockCOH.lpq]. *)
    Lemma phi_lpq r : In r (ic_invs VE ic) ->
      SL.lpq X (phi (ir_key r)) = BL.pos (keyE_dec rc K) Wu (lpu (ir_key r)).
    Proof.
      intros Hr. destruct (lpu_src r Hr) as (Hu & m & p & Hs).
      destruct (phi_rec r Hr) as [Ephi Hn].
      destruct (ix_src rc K VE IT ic Hinv _ r _ m p _ Hs Hn) as (Ht & Hix & _).
      destruct (rec_window rc K VE IT ic Hinv r Hr) as (h & _ & Hlen).
      rewrite <- (idx_pos rc K VE IT ic Hinv Wu HWu r0 _ Hu), (toEv_evt rc K VE IT ic Hinv Wu HWu r0 _ Hu).
      rewrite Ht, Hix, Hlen.
      unfold SL.lpq, SL.lpc, SL.lpi_of. rewrite (phi_blk r Hr), Ephi. cbn [fst snd].
      rewrite (off_foff rc K VE IT ic Hinv). reflexivity.
    Qed.

    Lemma phi_ovl r : In r (ic_invs VE ic) ->
      SL.ovl X (phi (ir_key r)) = ovev rc (BL.ovl VE (keyF_dec rc) ic r0 (ir_key r)).
    Proof.
      intros Hr. unfold SL.ovl. rewrite (phi_blk r Hr).
      unfold BL.ovl, ovev. rewrite (BL.rec_of_spec VE (M rc K) (keyF_dec rc) IT ic Hinv r0 r Hr).
      destruct (rec_shape rc K VE IT ic Hinv r Hr) as (_ & _ & _ & _ & _ & Hm).
      change (ovk (blk_of rc K r) = ovev_of (ir_op r) (ir_ret r)). exact (ovk_matches _ _ _ Hm).
    Qed.

    Lemma phi_sl r : In r (ic_invs VE ic) ->
      SL.is_sl_op X (phi (ir_key r)) =
        match fcomp (ir_op (BL.rec_of VE (keyF_dec rc) ic r0 (ir_key r))) with
        | SL.CSL => true | SL.CZ => false
        end.
    Proof.
      intros Hr. unfold SL.is_sl_op. rewrite (phi_blk r Hr).
      rewrite (BL.rec_of_spec VE (M rc K) (keyF_dec rc) IT ic Hinv r0 r Hr).
      destruct (rec_shape rc K VE IT ic Hinv r Hr) as (_ & _ & _ & _ & _ & Hm).
      exact (is_sl_matches _ _ _ Hm).
    Qed.

    Lemma phi_po r r' : In r (ic_invs VE ic) -> In r' (ic_invs VE ic) ->
      fst (ir_key r) = fst (ir_key r') -> ir_pos r < ir_pos r' ->
      fst (phi (ir_key r)) = fst (phi (ir_key r')) /\ snd (phi (ir_key r)) < snd (phi (ir_key r')).
    Proof.
      intros Hr Hr' Ht Hlt. destruct (phi_rec r Hr) as [E1 Hn1]. destruct (phi_rec r' Hr') as [E2 Hn2].
      rewrite E1, E2. cbn [fst snd].
      assert (Et : rth rc K r = rth rc K r') by (unfold rth; rewrite Ht; reflexivity).
      split; [exact Et|]. rewrite Et in Hn1.
      exact (ss_nth_rev ir_pos _ _ _ _ _ (recs_sorted rc K VE IT ic Hinv (rth rc K r')) Hn1 Hn2 Hlt).
    Qed.

    (** *** Positional correctness *)

    Local Abbreviation St := (WLT.setting VE (keyE_dec rc K) (keyF_dec rc) SL.comp_dec fcomp (nuFc rc)
                         (catE K) fcat
                         (wsel rc K) (wsel rc K) IT ic Wu r0 u0 lpu).

    Lemma secs_nodup : NoDup secs.
    Proof. exact (ii_invs_nodup _ _ _ _ Hinv). Qed.

    Lemma S1_transport (fB : nat * nat -> bool) (c : SL.CompT) :
      (forall s, In s secs -> fB (phi s) = WT.in_comp St c s) ->
      map (ovev rc) (map (BL.ovl VE (keyF_dec rc) ic r0)
                       (WC.isort (WT.lp St) (filter (WT.in_comp St c) secs))) =
        map (SL.ovl X) (WC.isort (SL.lpq X) (filter fB (SL.all_ops X))).
    Proof.
      intros Hf.
      rewrite <- (isort_transport phi (WT.lp St) (SL.lpq X) (WT.in_comp St c) fB secs (SL.all_ops X)).
      - rewrite !map_map. apply map_ext_in. intros s Hs.
        apply (Permutation_in _ (WC.isort_perm _ _)) in Hs. apply filter_In in Hs as [Hs _].
        destruct (BL.secs_record VE ic s Hs) as (r & Hr & ->). symmetry. exact (phi_ovl r Hr).
      - exact secs_nodup.
      - exact (SL.all_ops_nodup X (SL.wf_ths _ _ _ X_wf)).
      - intros s Hs. destruct (BL.secs_record VE ic s Hs) as (r & Hr & ->). exact (phi_all_ops r Hr).
      - intros q Hq'. destruct (phi_onto q Hq') as (r & Hr & <-). exists (ir_key r). split; [|reflexivity].
        apply in_map, Hr.
      - intros s s' Hs Hs' Eq. destruct (BL.secs_record VE ic s Hs) as (r & Hr & ->).
        destruct (BL.secs_record VE ic s' Hs') as (r' & Hr' & ->). f_equal. exact (phi_inj r r' Hr Hr' Eq).
      - intros s Hs. destruct (BL.secs_record VE ic s Hs) as (r & Hr & ->). exact (phi_lpq r Hr).
      - intros q q' Hq1 Hq2. exact (SL.lp_inj rc K X X_wf q q' Hq1 Hq2).
      - exact Hf.
    Qed.

    Lemma positional :
      WLT.Positional VE (keyE_dec rc K) (keyF_dec rc) SL.comp_dec fcomp (nuFc rc) (catE K) fcat
        (wsel rc K) (wsel rc K) IT ic Wu r0 u0 lpu.
    Proof.
      constructor.
      - intros s s' Hs Hs' Eq.
        destruct (BL.secs_record VE ic s Hs) as (r & Hr & ->).
        destruct (BL.secs_record VE ic s' Hs') as (r' & Hr' & ->).
        f_equal. apply phi_inj; [exact Hr|exact Hr'|].
        apply (SL.lp_inj rc K X X_wf); [apply phi_all_ops, Hr|apply phi_all_ops, Hr'|].
        rewrite (phi_lpq r Hr), (phi_lpq r' Hr'). exact Eq.
      - intros s Hs. unfold lpu, WLT.lo, WLT.hi. lia.
      - intros c.
        assert (Hsl : forall s, In s secs -> SL.is_sl_op X (phi s) = WT.in_comp St SL.CSL s).
        { intros s Hs. destruct (BL.secs_record VE ic s Hs) as (r & Hr & ->). rewrite (phi_sl r Hr).
          change (WT.in_comp St SL.CSL (ir_key r)) with
            (if SL.comp_dec (fcomp (ir_op (BL.rec_of VE (keyF_dec rc) ic r0 (ir_key r)))) SL.CSL
             then true else false).
          destruct (fcomp _); reflexivity. }
        assert (Hz : forall s, In s secs -> negb (SL.is_sl_op X (phi s)) = WT.in_comp St SL.CZ s).
        { intros s Hs. destruct (BL.secs_record VE ic s Hs) as (r & Hr & ->). rewrite (phi_sl r Hr).
          change (WT.in_comp St SL.CZ (ir_key r)) with
            (if SL.comp_dec (fcomp (ir_op (BL.rec_of VE (keyF_dec rc) ic r0 (ir_key r)))) SL.CZ
             then true else false).
          destruct (fcomp _); reflexivity. }
        destruct c.
        + change (SL.nu_sl (map (ovev rc) (map (BL.ovl VE (keyF_dec rc) ic r0)
                     (WC.isort (WT.lp St) (filter (WT.in_comp St SL.CSL) secs))))).
          rewrite (S1_transport (SL.is_sl_op X) SL.CSL Hsl).
          exact (SL.seqlock_S1 rc K X X_wf HK).
        + change (SL.nu_z (map (ovev rc) (map (BL.ovl VE (keyF_dec rc) ic r0)
                     (WC.isort (WT.lp St) (filter (WT.in_comp St SL.CZ) secs))))).
          rewrite (S1_transport (fun q => negb (SL.is_sl_op X q)) SL.CZ Hz).
          exact (SL.z_S1 rc K X X_wf).
      - intros s s' Hs Hs' Hc Hpo _.
        destruct (BL.secs_record VE ic s Hs) as (r & Hr & ->).
        destruct (BL.secs_record VE ic s' Hs') as (r' & Hr' & ->).
        destruct Hpo as [Ht Hpos].
        rewrite (BL.rec_of_spec VE (M rc K) (keyF_dec rc) IT ic Hinv r0 r Hr),
                (BL.rec_of_spec VE (M rc K) (keyF_dec rc) IT ic Hinv r0 r' Hr') in Hpos.
        change (BL.pos (keyE_dec rc K) Wu (lpu (ir_key r)) < BL.pos (keyE_dec rc K) Wu (lpu (ir_key r'))).
        rewrite <- (phi_lpq r Hr), <- (phi_lpq r' Hr').
        destruct (phi_po r r' Hr Hr' Ht Hpos) as [Hfst Hsnd].
        change (fcomp (ir_op (BL.rec_of VE (keyF_dec rc) ic r0 (ir_key r))) =
                fcomp (ir_op (BL.rec_of VE (keyF_dec rc) ic r0 (ir_key r')))) in Hc.
        pose proof (phi_sl r Hr) as S1. pose proof (phi_sl r' Hr') as S2. rewrite <- Hc in S2.
        destruct (fcomp (ir_op (BL.rec_of VE (keyF_dec rc) ic r0 (ir_key r)))).
        + apply (SL.seqlock_S1_ord rc K X X_wf HK); [| |exact Hfst|exact Hsnd];
            unfold SL.sl_ops; apply filter_In; (split; [apply phi_all_ops; assumption|assumption]).
        + apply (SL.z_S1_ord rc K X X_wf); [| |exact Hfst|exact Hsnd];
            unfold SL.z_ops; apply filter_In; (split; [apply phi_all_ops; assumption|]).
          * rewrite S1. reflexivity.
          * rewrite S2. reflexivity.
    Qed.
  End Transport.

  (** ** The theorem *)

  (** For every TicketLock signature with [K_ok]. *)
  Theorem seqlock_module_rel_lin_K rc K (HK : SL.K_ok K = true) (VE : LTS (E rc K)) q0 T c :
    module_execution_tagged VE (M rc K) (initial_tagged_module VE q0) T c ->
    tm_queue c = [] -> (forall e, In e (tm_calls c) -> ce_cell (F rc) e = DeadCall) ->
    rel_lin BL.under_sel T (semi_independent (E rc K))
      (BL.nuE_all (E := E rc K) SL.comp_dec compE (nuEc rc K)) ->
    rel_lin BL.over_sel T (semi_independent (F rc)) (BL.nuF_all (F := F rc) SL.comp_dec fcomp (nuFc rc)).
  Proof.
    apply (WLT.window_link_table VE (M rc K) (keyE_dec rc K) (keyF_dec rc) SL.comp_dec compE fcomp
             (nuEc rc K) (nuFc rc) (WT.dtable rc) (catE K) fcat (E_compat rc K) (F_cross rc) (nuF_nil rc)
             (wsel rc K) (wsel rc K) (window_bodies rc K)).
    intros IT ic Wu r0 u0 Hinv Hq _ HWu.
    exists (lpu rc K VE ic Wu r0 u0).
    exact (positional rc K HK VE IT ic Hinv Hq Wu HWu r0 u0).
  Qed.

  (** SeqLock ⊎ COH[z] over the plain TicketLock: relaxed linearizable
      w.r.t. ν_SeqLock ⊗ ν_COH[z] with read ↦ rmb, write ↦ wmb. *)
  Theorem seqlock_module_rel_lin rc (VE : LTS (E rc SL.plainTL)) q0 T c :
    module_execution_tagged VE (M rc SL.plainTL) (initial_tagged_module VE q0) T c ->
    tm_queue c = [] -> (forall e, In e (tm_calls c) -> ce_cell (F rc) e = DeadCall) ->
    rel_lin BL.under_sel T (semi_independent (E rc SL.plainTL))
      (BL.nuE_all (E := E rc SL.plainTL) SL.comp_dec compE (nuEc rc SL.plainTL)) ->
    rel_lin BL.over_sel T (semi_independent (F rc)) (BL.nuF_all (F := F rc) SL.comp_dec fcomp (nuFc rc)).
  Proof. exact (seqlock_module_rel_lin_K rc SL.plainTL SL.plainTL_ok VE q0 T c). Qed.

End SeqLockModule.
