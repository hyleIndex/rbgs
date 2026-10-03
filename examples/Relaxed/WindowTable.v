(** * Window composition over an arbitrary ordering table

    Generalizes [WindowComposition] from the four fence modes to an
    arbitrary set of categories [Cat] with one global ordering table
    [to : Cat -> Cat -> Prop], in the style of the stamp order of Ambal et
    al., "A Verified High-Performance Composable Object Library for Remote
    Direct Memory Access" (POPL 2026), Def. 3.3: a same-thread pair of
    operations of different objects, of categories [c] (earlier) and [d]
    (later), is ordered iff [to c d].

    Mode inheritance becomes dominance, checked per implementation:
    - the last call of the window orders at least what the overlay
      operation orders after itself ([out_le]);
    - the first call orders at least what the overlay operation orders
      before itself ([in_le]).

    The only place the old proof used the fence modes was order
    reflection ([WindowComposition.cross_reflect]); here it is [transfer].

    Part 1: the theorem, and [window_composition_sequential]: a client
    that never overlaps its own operations needs no inheritance.  Part 2: the four fence modes are the rectangular
    table [rect m m' := acq_like m \/ rel_like m'], dominance for [rect] is
    exactly [WindowComposition.Inherit], and [WindowComposition]'s theorem
    is an instance ([wc_is_special_case]).  Part 3: identity windows
    always inherit.  Part 4: tables and rectangularity: TSO's preserved
    program order is rectangular; selective barriers and RCsc
    release/acquire are not. *)

From Stdlib Require Import List Sorting.Sorted Sorting.Permutation.
From Stdlib Require Import Arith.PeanoNat micromega.Lia.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import examples.Relaxed.WindowComposition.

Import ListNotations.

Module WindowTable.
  Module WC := WindowComposition.
  Import RelaxedSig.

  (** ** Dominance *)

  Section Dominance.
    Context {Cat : Type} (to : Cat -> Cat -> Prop).

    (** [c'] orders every later category that [c] orders. *)
    Definition out_le (c c' : Cat) : Prop := forall d, to c d -> to c' d.
    (** [d'] is ordered after every earlier category that [d] is. *)
    Definition in_le (d d' : Cat) : Prop := forall c, to c d -> to c d'.

    Lemma out_le_refl c : out_le c c.
    Proof. intros d H; exact H. Qed.

    Lemma in_le_refl d : in_le d d.
    Proof. intros c H; exact H. Qed.

    Lemma out_le_trans c1 c2 c3 : out_le c1 c2 -> out_le c2 c3 -> out_le c1 c3.
    Proof. intros H1 H2 d H; apply H2, H1, H. Qed.

    Lemma in_le_trans d1 d2 d3 : in_le d1 d2 -> in_le d2 d3 -> in_le d1 d3.
    Proof. intros H1 H2 c H; apply H2, H1, H. Qed.

    Lemma transfer c c' d d' : out_le c c' -> in_le d d' -> to c d -> to c' d'.
    Proof. intros Ho Hi H. apply Hi, Ho, H. Qed.
  End Dominance.

  (** ** Part 1: the theorem *)

  Record Setting (Cat : Type) : Type := {
    Op : Type;
    Call : Type;
    OvOp : Type;
    Comp : Type;
    comp_dec : forall c c' : Comp, {c = c'} + {c <> c'};
    comp : Op -> Comp;
    ovl : Op -> OvOp;
    cF : Op -> Cat;                  (* overlay categories *)
    IFc : Op -> Op -> Prop;
    ucomp : Call -> Comp;
    cE : Call -> Cat;                (* underlay categories *)
    IEc : Call -> Call -> Prop;
    lo : Op -> Call;
    hi : Op -> Call;
    lpc : Op -> Call;
    pos : Call -> nat;
    ops : list Op;
    po : Op -> Op -> Prop;
    rt : Op -> Op -> Prop;
    nuF : Comp -> list OvOp -> Prop;
  }.

  Arguments Op {Cat}. Arguments Call {Cat}. Arguments OvOp {Cat}.
  Arguments Comp {Cat}. Arguments comp_dec {Cat}. Arguments comp {Cat}.
  Arguments ovl {Cat}. Arguments cF {Cat}. Arguments IFc {Cat}.
  Arguments ucomp {Cat}. Arguments cE {Cat}. Arguments IEc {Cat}.
  Arguments lo {Cat}. Arguments hi {Cat}. Arguments lpc {Cat}.
  Arguments pos {Cat}. Arguments ops {Cat}. Arguments po {Cat}.
  Arguments rt {Cat}. Arguments nuF {Cat}.

  Section Window.
    Context {Cat : Type} (to : Cat -> Cat -> Prop) (S : Setting Cat).

    (** Semi-independence of the tensors: inside a component as given,
        across components exactly the pairs the table does not order. *)
    Definition IF (q q' : Op S) : Prop :=
      if comp_dec S (comp S q) (comp S q') then IFc S q q'
      else ~ to (cF S q) (cF S q').
    Definition IE (u u' : Call S) : Prop :=
      if comp_dec S (ucomp S u) (ucomp S u') then IEc S u u'
      else ~ to (cE S u) (cE S u').

    Definition lp (q : Op S) : nat := pos S (lpc S q).

    Definition in_comp (c : Comp S) (q : Op S) : bool :=
      if comp_dec S (comp S q) c then true else false.

    (** Same as [WindowComposition.Hyps0], over the table-induced [IE]. *)
    Record Hyps0 : Prop := {
      h_nodup : NoDup (ops S);
      h_lp_inj : forall q q', In q (ops S) -> In q' (ops S) -> lp q = lp q' -> q = q';
      h_lo_comp : forall q, In q (ops S) -> ucomp S (lo S q) = comp S q;
      h_hi_comp : forall q, In q (ops S) -> ucomp S (hi S q) = comp S q;
      h_window : forall q, In q (ops S) -> pos S (lo S q) <= lp q <= pos S (hi S q);
      h_ord : forall q q', In q (ops S) -> In q' (ops S) -> po S q q' ->
                           ~ IE (hi S q) (lo S q') -> pos S (hi S q) < pos S (lo S q');
      h_rt : forall q q', In q (ops S) -> In q' (ops S) -> rt S q q' ->
                          pos S (hi S q) < pos S (lo S q');
      h_S1 : forall c, nuF S c (map (ovl S) (WC.isort lp (filter (in_comp c) (ops S))));
      h_S1_ord : forall q q', In q (ops S) -> In q' (ops S) -> comp S q = comp S q' ->
                              po S q q' -> ~ IFc S q q' -> lp q < lp q';
    }.

    (** Inheritance as dominance, per implementation. *)
    Definition Inherit : Prop :=
      (forall q, In q (ops S) -> out_le to (cF S q) (cE S (hi S q))) /\
      (forall q, In q (ops S) -> in_le to (cF S q) (cE S (lo S q))).

    Definition Conclusion : Prop :=
      exists ow : list (Op S),
        Permutation ow (ops S) /\
        (forall q q', In q (ops S) -> In q' (ops S) ->
           (po S q q' /\ ~ IF q q') \/ rt S q q' ->
           exists l1 l2, ow = l1 ++ q :: l2 /\ In q' l2) /\
        (forall c, nuF S c (map (ovl S) (filter (in_comp c) ow))).

    (** Sorting by [lp] gives the conclusion as soon as [lp] respects the
        overlay order; shared by both theorems below. *)
    Lemma conclusion_of_lp_before (H : Hyps0) :
      (forall q q', In q (ops S) -> In q' (ops S) ->
                    (po S q q' /\ ~ IF q q') \/ rt S q q' -> lp q < lp q') ->
      Conclusion.
    Proof.
      intros Hlpb.
      exists (WC.isort lp (ops S)).
      assert (Hperm : Permutation (WC.isort lp (ops S)) (ops S)) by apply WC.isort_perm.
      pose proof (h_lp_inj H) as Hinj.
      assert (Hsort : StronglySorted (fun q q' => lp q < lp q') (WC.isort lp (ops S)))
        by (apply WC.isort_sorted; [exact Hinj | exact (h_nodup H)]).
      split; [exact Hperm|]. split.
      - intros q q' Hq Hq' Hord.
        assert (Hlt : lp q < lp q') by (apply Hlpb; assumption).
        assert (Hin : In q (WC.isort lp (ops S)))
          by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hq).
        assert (Hin' : In q' (WC.isort lp (ops S)))
          by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hq').
        destruct (in_split _ _ Hin) as (l1 & l2 & E).
        exists l1, l2. split; [exact E|].
        rewrite E in Hin'. apply in_app_or in Hin' as [H1|[<-|H2]].
        + exfalso. rewrite E in Hsort.
          pose proof (WC.ss_app_cons _ _ _ _ _ Hsort H1) as Hc. cbn in Hc. lia.
        + lia.
        + exact H2.
      - intros c. rewrite WC.filter_isort by (exact Hinj || exact (h_nodup H)).
        apply (h_S1 H).
    Qed.

    (** A client that never overlaps its own operations (every same-thread
        pair is also a real-time pair: the setting of Herlihy–Wing and of
        conditions that keep per-thread calls sequential) needs no
        inheritance at all. *)
    Theorem window_composition_sequential (H : Hyps0) :
      (forall q q', In q (ops S) -> In q' (ops S) -> po S q q' -> rt S q q') ->
      Conclusion.
    Proof.
      intros Hseq. apply (conclusion_of_lp_before H).
      intros q q' Hq Hq' Hord.
      pose proof (h_window H q Hq) as [_ W1].
      pose proof (h_window H q' Hq') as [W2 _].
      assert (Hrt : rt S q q') by (destruct Hord as [[Hpo _]|Hrt]; [apply Hseq|]; assumption).
      assert (pos S (hi S q) < pos S (lo S q')) by (apply (h_rt H); assumption).
      lia.
    Qed.

    Section WithHyps.
      Context (H : Hyps0) (Hinh : Inherit).

      (** Order reflection.  No decidability of [to] is needed: double
          negation is functorial. *)
      Lemma cross_reflect q q' :
        In q (ops S) -> In q' (ops S) -> comp S q <> comp S q' ->
        ~ IF q q' -> ~ IE (hi S q) (lo S q').
      Proof.
        intros Hq Hq' Hne. unfold IE, IF.
        rewrite (h_hi_comp H q Hq), (h_lo_comp H q' Hq').
        destruct (comp_dec S (comp S q) (comp S q')) as [E|NE]; [contradiction|].
        intros HnnF HnE. apply HnnF. intros HF. apply HnE.
        exact (transfer to _ _ _ _ (proj1 Hinh q Hq) (proj2 Hinh q' Hq') HF).
      Qed.

      Lemma lp_before q q' :
        In q (ops S) -> In q' (ops S) -> (po S q q' /\ ~ IF q q') \/ rt S q q' -> lp q < lp q'.
      Proof.
        intros Hq Hq' Hord.
        pose proof (h_window H q Hq) as [_ W1].
        pose proof (h_window H q' Hq') as [W2 _].
        destruct Hord as [[Hpo HnIF]|Hrt].
        - destruct (comp_dec S (comp S q) (comp S q')) as [E|NE].
          + apply (h_S1_ord H); try assumption.
            unfold IF in HnIF. destruct (comp_dec S (comp S q) (comp S q'));
              [exact HnIF|contradiction].
          + assert (pos S (hi S q) < pos S (lo S q'))
              by (apply (h_ord H); try assumption; apply cross_reflect; assumption).
            lia.
        - assert (pos S (hi S q) < pos S (lo S q')) by (apply (h_rt H); assumption).
          lia.
      Qed.

      Theorem window_composition : Conclusion.
      Proof. apply (conclusion_of_lp_before H). exact lp_before. Qed.
    End WithHyps.
  End Window.

  Arguments Hyps0 {Cat} to S.
  Arguments Inherit {Cat} to S.
  Arguments Conclusion {Cat} to S.

  (** ** Part 2: the four fence modes are the rectangular table *)

  Definition rect (m m' : FenceMode) : Prop := WC.acq_like m \/ WC.rel_like m'.

  Lemma rect_indep_iff m m' : ~ rect m m' <-> WC.cross m m'.
  Proof.
    unfold rect, WC.cross, WC.acq_like, WC.rel_like. split.
    - intros Hn.
      destruct (WC.fence_le_dec m LFence) as [H1|H1]; [|exfalso; apply Hn; left; exact H1].
      destruct (WC.fence_le_dec m' RFence) as [H2|H2]; [|exfalso; apply Hn; right; exact H2].
      split; assumption.
    - intros [H1 H2] [Ha|Hr]; [exact (Ha H1) | exact (Hr H2)].
  Qed.

  Lemma local_not_acq : ~ WC.acq_like Local.
  Proof. unfold WC.acq_like. intros Hn. apply Hn. exact I. Qed.

  Lemma local_not_rel : ~ WC.rel_like Local.
  Proof. unfold WC.rel_like. intros Hn. apply Hn. exact I. Qed.

  (** Dominance for [rect] is the old per-side inheritance. *)
  Lemma rect_out_le_iff m m' : out_le rect m m' <-> (WC.acq_like m -> WC.acq_like m').
  Proof.
    unfold out_le, rect. split.
    - intros Ho Ha. destruct (Ho Local (or_introl Ha)) as [Ha'|Hr]; [exact Ha'|].
      exfalso; exact (local_not_rel Hr).
    - intros Hi d [Ha|Hr]; [left; exact (Hi Ha) | right; exact Hr].
  Qed.

  Lemma rect_in_le_iff m m' : in_le rect m m' <-> (WC.rel_like m -> WC.rel_like m').
  Proof.
    unfold in_le, rect. split.
    - intros Ho Hr. destruct (Ho Local (or_intror Hr)) as [Ha|Hr']; [|exact Hr'].
      exfalso; exact (local_not_acq Ha).
    - intros Hi c [Ha|Hr]; [left; exact Ha | right; exact (Hi Hr)].
  Qed.

  (** Every [WindowComposition] setting, read over the rectangular table. *)
  Definition of_wc (S : WC.Setting) : Setting FenceMode := {|
    Op := WC.Op S; Call := WC.Call S; OvOp := WC.OvOp S; Comp := WC.Comp S;
    comp_dec := WC.comp_dec S; comp := WC.comp S; ovl := WC.ovl S;
    cF := WC.mF S; IFc := WC.IFc S; ucomp := WC.ucomp S; cE := WC.mE S;
    IEc := WC.IEc S; lo := WC.lo S; hi := WC.hi S; lpc := WC.lpc S;
    pos := WC.pos S; ops := WC.ops S; po := WC.po S; rt := WC.rt S;
    nuF := WC.nuF S |}.

  Section OfWC.
    Context (S : WC.Setting).

    Lemma of_wc_IF q q' : IF rect (of_wc S) q q' <-> WC.IF S q q'.
    Proof.
      unfold IF, WC.IF; cbn.
      destruct (WC.comp_dec S (WC.comp S q) (WC.comp S q')); [tauto|apply rect_indep_iff].
    Qed.

    Lemma of_wc_IE u u' : IE rect (of_wc S) u u' <-> WC.IE S u u'.
    Proof.
      unfold IE, WC.IE; cbn.
      destruct (WC.comp_dec S (WC.ucomp S u) (WC.ucomp S u')); [tauto|apply rect_indep_iff].
    Qed.

    Lemma of_wc_hyps0 : WC.Hyps0 S -> Hyps0 rect (of_wc S).
    Proof.
      intros H. constructor; cbn.
      - exact (WC.h_nodup _ H).
      - exact (WC.h_lp_inj _ H).
      - exact (WC.h_lo_comp _ H).
      - exact (WC.h_hi_comp _ H).
      - exact (WC.h_window _ H).
      - intros q q' Hq Hq' Hpo HnIE. apply (WC.h_ord _ H); try assumption.
        intros HIE. apply HnIE. apply of_wc_IE. exact HIE.
      - exact (WC.h_rt _ H).
      - exact (WC.h_S1 _ H).
      - exact (WC.h_S1_ord _ H).
    Qed.

    Lemma of_wc_inherit : WC.Inherit S <-> Inherit rect (of_wc S).
    Proof.
      unfold WC.Inherit, Inherit; cbn. split.
      - intros [Ha Hr]. split.
        + intros q Hq. apply rect_out_le_iff. exact (Ha q Hq).
        + intros q Hq. apply rect_in_le_iff. exact (Hr q Hq).
      - intros [Ha Hr]. split.
        + intros q Hq. apply rect_out_le_iff. exact (Ha q Hq).
        + intros q Hq. apply rect_in_le_iff. exact (Hr q Hq).
    Qed.

    Lemma of_wc_conclusion : Conclusion rect (of_wc S) -> WC.Conclusion S.
    Proof.
      intros (ow & Hp & Ho & Hs). exists ow. split; [exact Hp|]. split; [|exact Hs].
      intros q q' Hq Hq' Hord. apply (Ho q q' Hq Hq').
      destruct Hord as [[Hpo HnIF]|Hrt]; [left|right; exact Hrt].
      split; [exact Hpo|]. intros HIF. apply HnIF. apply of_wc_IF. exact HIF.
    Qed.
  End OfWC.

  (** The fence-mode theorem is the rectangular instance. *)
  Theorem wc_is_special_case (S : WC.Setting) :
    WC.Hyps0 S -> WC.Inherit S -> WC.Conclusion S.
  Proof.
    intros H Hi. apply of_wc_conclusion.
    apply (window_composition rect (of_wc S) (of_wc_hyps0 S H)).
    apply of_wc_inherit. exact Hi.
  Qed.

  (** ** Part 3: identity windows always inherit *)

  (** A single-call window inherits iff the call dominates the overlay
      category on both sides; in particular a primitive object exported
      as itself (overlay category = category of its own call) always
      does. *)
  Lemma single_window_inherits {Cat} (to : Cat -> Cat -> Prop) (c : Cat) :
    out_le to c c /\ in_le to c c.
  Proof. split; [apply out_le_refl | apply in_le_refl]. Qed.

  (** ** Part 4: tables and rectangularity *)

  Definition rectangular {Cat} (to : Cat -> Cat -> Prop) : Prop :=
    exists f : Cat -> FenceMode, forall c d, to c d <-> rect (f c) (f d).

  (** TSO: every pair ordered except write-then-read. *)
  Inductive TsoCat := TR | TW.
  Definition tso_to (c d : TsoCat) : Prop :=
    match c, d with TW, TR => False | _, _ => True end.

  Lemma tso_rectangular : rectangular tso_to.
  Proof.
    exists (fun c => match c with TR => RFence | TW => LFence end).
    unfold rect, WC.acq_like, WC.rel_like.
    intros [|] [|]; cbn; split.
    - intros _. left. intro Hf. exact Hf.
    - intros _. exact I.
    - intros _. left. intro Hf. exact Hf.
    - intros _. exact I.
    - intros [].
    - intros [Ha|Hr]; [apply Ha; exact I | apply Hr; exact I].
    - intros _. right. intro Hf. exact Hf.
    - intros _. exact I.
  Qed.

  (** Plain accesses with selective barriers (smp_wmb, smp_rmb) and a
      full barrier; plain accesses are not ordered across locations. *)
  Inductive BarCat := BR | BW | Bwmb | Brmb | Bmb.
  Definition bar_to (c d : BarCat) : Prop :=
    match c, d with
    | Bmb, _ | _, Bmb => True
    | BW, Bwmb | Bwmb, BW => True
    | BR, Brmb | Brmb, BR => True
    | _, _ => False
    end.

  (** A selective barrier cannot be a fence mode: it would have to order
      every later operation after the preceding writes. *)
  Lemma wmb_not_rectangular : ~ rectangular bar_to.
  Proof.
    intros (f & Hf).
    assert (H1 : rect (f BW) (f Bwmb)) by (apply Hf; exact I).
    assert (H2 : ~ rect (f BR) (f Bwmb)) by (intros Hr; exact (proj2 (Hf BR Bwmb) Hr)).
    assert (H3 : ~ rect (f BW) (f BR)) by (intros Hr; exact (proj2 (Hf BW BR) Hr)).
    destruct H1 as [Ha|Hr].
    - apply H3. left. exact Ha.
    - apply H2. right. exact Hr.
  Qed.

  (** RCsc release/acquire (ARMv8 [bob]: [A];po, po;[L], [L];po;[A]). *)
  Inductive RaCat := Rx | Wx | Racq | Wrel.
  Definition ra_to (c d : RaCat) : Prop :=
    match c, d with
    | Racq, _ => True
    | _, Wrel => True
    | Wrel, Racq => True
    | _, _ => False
    end.

  (** Ordering a release before a later acquire, and nothing else extra,
      is not a fence mode; this is the pair that the four modes miss in
      store buffering with release/acquire (Mem.tex L6). *)
  Lemma rcsc_not_rectangular : ~ rectangular ra_to.
  Proof.
    intros (f & Hf).
    assert (H1 : rect (f Wrel) (f Racq)) by (apply Hf; exact I).
    assert (H2 : ~ rect (f Wrel) (f Rx)) by (intros Hr; exact (proj2 (Hf Wrel Rx) Hr)).
    assert (H3 : ~ rect (f Wx) (f Racq)) by (intros Hr; exact (proj2 (Hf Wx Racq) Hr)).
    destruct H1 as [Ha|Hr].
    - apply H2. left. exact Ha.
    - apply H3. right. exact Hr.
  Qed.

  (** ** Part 5: the default table

      A category is an access kind (none / read / write / RMW) with an
      acquire bit and a release bit, or one of the two selective barriers.
      [Local], [RFence], [LFence], [Fence] are the kind-less categories
      with bits 00, 10, 01, 11; [Fence] also serves as [mb].

      [c] (earlier) is ordered before [d] (later, another object) iff
      - [c] is acquire-like or [d] is release-like (the old rule), or
      - a write is followed by [wmb], [wmb] by a write, or [wmb] by [wmb],
        and likewise for reads and [rmb], or
      - optionally ([rcsc = true], ARMv8 [bob]'s [L];po;[A]): a release
        write is followed by an acquire read. *)

  Inductive Kind := KN | KR | KW | KRW.
  Inductive DCat := Acc (k : Kind) (acq rel : bool) | Rmb | Wmb.

  Definition DLocal := Acc KN false false.
  Definition DRFence := Acc KN true false.
  Definition DLFence := Acc KN false true.
  Definition DFence := Acc KN true true.
  Definition DR := Acc KR false false.
  Definition DW := Acc KW false false.
  Definition DRacq := Acc KR true false.
  Definition DWrel := Acc KW false true.

  Definition acqc (c : DCat) : bool := match c with Acc _ a _ => a | _ => false end.
  Definition relc (c : DCat) : bool := match c with Acc _ _ r => r | _ => false end.
  Definition isR (c : DCat) : bool :=
    match c with Acc KR _ _ | Acc KRW _ _ => true | _ => false end.
  Definition isW (c : DCat) : bool :=
    match c with Acc KW _ _ | Acc KRW _ _ => true | _ => false end.
  Definition isRmb (c : DCat) : bool := match c with Rmb => true | _ => false end.
  Definition isWmb (c : DCat) : bool := match c with Wmb => true | _ => false end.

  Definition dto (rcsc : bool) (c d : DCat) : bool :=
    acqc c || relc d
    || (isW c && isWmb d) || (isWmb c && isW d) || (isWmb c && isWmb d)
    || (isR c && isRmb d) || (isRmb c && isR d) || (isRmb c && isRmb d)
    || (rcsc && relc c && isW c && acqc d && isR d).

  Definition dtable (rcsc : bool) (c d : DCat) : Prop := dto rcsc c d = true.

  (** The eight categories shown in the note, in display order. *)
  Definition shown : list DCat := [DLocal; DR; DW; DRacq; DWrel; Rmb; Wmb; DFence].

  (** Finite enumeration, for deciding dominance. *)
  Definition all_kinds := [KN; KR; KW; KRW].
  Definition all_dcat : list DCat :=
    Rmb :: Wmb ::
    flat_map (fun k => [Acc k false false; Acc k true false; Acc k false true; Acc k true true])
             all_kinds.

  Lemma all_dcat_complete c : In c all_dcat.
  Proof.
    destruct c as [k [|] [|]| |]; cbn; [destruct k; cbn; tauto ..| tauto | tauto].
  Qed.

  Definition out_leb rcsc c c' : bool :=
    forallb (fun d => implb (dto rcsc c d) (dto rcsc c' d)) all_dcat.
  Definition in_leb rcsc d d' : bool :=
    forallb (fun c => implb (dto rcsc c d) (dto rcsc c d')) all_dcat.

  Lemma out_leb_spec rcsc c c' : out_leb rcsc c c' = true <-> out_le (dtable rcsc) c c'.
  Proof.
    unfold out_leb, out_le, dtable. rewrite forallb_forall. split.
    - intros H d Hd. specialize (H d (all_dcat_complete d)). rewrite Hd in H. exact H.
    - intros H d _. destruct (dto rcsc c d) eqn:E; cbn; [apply H; exact E | reflexivity].
  Qed.

  Lemma in_leb_spec rcsc d d' : in_leb rcsc d d' = true <-> in_le (dtable rcsc) d d'.
  Proof.
    unfold in_leb, in_le, dtable. rewrite forallb_forall. split.
    - intros H c Hc. specialize (H c (all_dcat_complete c)). rewrite Hc in H. exact H.
    - intros H c _. destruct (dto rcsc c d) eqn:E; cbn; [apply H; exact E | reflexivity].
  Qed.

  (** Conservativity: on the four kind-less categories the table is the
      old rule, under both profiles. *)
  Definition emb (m : FenceMode) : DCat :=
    match m with Local => DLocal | RFence => DRFence | LFence => DLFence | Fence => DFence end.

  Lemma abstract_is_rect rcsc m m' : dtable rcsc (emb m) (emb m') <-> rect m m'.
  Proof.
    unfold dtable, rect, WC.acq_like, WC.rel_like.
    destruct rcsc, m, m'; cbn; split; intros H; try discriminate; try reflexivity;
      try (left; intro Hf; exact Hf); try (right; intro Hf; exact Hf);
      try (exfalso; destruct H as [Ha|Hr]; [apply Ha; exact I | apply Hr; exact I]).
  Qed.

  (** Running-example facts, for either profile. *)

  (** Lock(O) with window {acquire}: exports [Racq], cannot export [Fence]. *)
  Lemma lock_exports_racq rcsc :
    out_le (dtable rcsc) DRacq DRacq /\ in_le (dtable rcsc) DRacq DRacq.
  Proof. apply single_window_inherits. Qed.

  Lemma lock_not_fence rcsc : ~ in_le (dtable rcsc) DFence DRacq.
  Proof. rewrite <- in_leb_spec. destruct rcsc; vm_compute; discriminate. Qed.

  (** LatchSet: update with window {second seq++ write} exports [W];
      contains with window {first seq read .. retry read} exports [R].
      Neither can claim acquire/release, and both say strictly more than
      [Local] (a client [wmb]/[rmb] orders them). *)
  Lemma latch_update_not_rel rcsc : ~ in_le (dtable rcsc) DWrel DW.
  Proof. rewrite <- in_leb_spec. destruct rcsc; vm_compute; discriminate. Qed.

  Lemma latch_query_not_acq rcsc : ~ out_le (dtable rcsc) DRacq DR.
  Proof. rewrite <- out_leb_spec. destruct rcsc; vm_compute; discriminate. Qed.

  Lemma latch_W_stronger_than_local rcsc :
    in_le (dtable rcsc) DLocal DW /\ ~ in_le (dtable rcsc) DW DLocal.
  Proof.
    rewrite <- !in_leb_spec. destruct rcsc; vm_compute; split; [reflexivity|discriminate|reflexivity|discriminate].
  Qed.

  Lemma latch_R_stronger_than_local rcsc :
    out_le (dtable rcsc) DLocal DR /\ ~ out_le (dtable rcsc) DR DLocal.
  Proof.
    rewrite <- !out_leb_spec. destruct rcsc; vm_compute; split; [reflexivity|discriminate|reflexivity|discriminate].
  Qed.
End WindowTable.
