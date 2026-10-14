(** * Window composition linked to the module semantics, for a joint overlay specification

    [WindowLinkTable.window_link_table] concludes that the overlay part of
    a complete execution is relaxed linearizable w.r.t. the product
    [BL.nuF_all comp_dec compF nuFc] of per-component overlay
    specifications.  [window_link_table_J] replaces that product by an
    arbitrary predicate [nuJ : list (Op F) -> Prop] on the whole overlay
    witness (a joint specification).  Everything else of the section
    context of [WindowLinkTable.Link] is kept: [compF] still decides which
    overlay pairs are same-component (ordered by the component's own
    proof, [p_S1_ord]) and which are cross-component (ordered through the
    windows, the table [to] and the underlay witness); [catE], [catF],
    [E_compat], [F_cross], [wlo] / [whi] and [window_bodies] are
    unchanged; [nuJ_nil] replaces [nuF_nil].  [PositionalJ] replaces
    [WindowLinkTable.Positional]: [p_lp_inj], [p_window] and [p_S1_ord]
    are the same, and the per-component obligation [p_S1] becomes one
    joint obligation [p_S1J]: [nuJ] holds of the overlay operations of all
    components, sorted by linearization point.  [settingJ_lp] unfolds the
    sort key of [p_S1J] to [fun s => WLT.pos keyE_dec Wu (lpc s)].

    Proof and reuse.  No lemma of [WindowLinkTable] is re-proved; the
    only proof lines taken from it are the seven-line [F_cross] step of
    [WindowLinkTable.window_overlay] (a cross-component pair that is not
    semi-independent is ordered by the table), adapted in
    [link_lp_ord_fields].
    - [link_hyps0J], [link_inheritJ]: [WindowLinkTable.link_hyps0] and
      [link_inherit], instantiated with the trivial component
      specification [no_spec], give [WindowTableJ.Hyps0J] and
      [WindowTable.Inherit] for the module setting;
      [link_window_composition_J] applies
      [WindowTableJ.window_composition_J] to it.
    - [link_lp_ord_fields]: every same-thread overlay pair that is not
      semi-independent is ordered by linearization point, from the three
      ordering fields [p_lp_inj], [p_window], [p_S1_ord] alone (not
      [p_S1J], so it is available while [p_S1J] is being proved).  Across
      components this is [WindowTable.lp_before] (windows, dominance, and
      the positions in the underlay witness [Wu] through [h_ord], which
      uses [E_compat], and [h_rt], both proved by
      [WindowLinkTable.link_hyps0]) plus [F_cross].  [link_lp_ord] is the same for a [PositionalJ].
    - [window_link_table_J] is [WindowLinkTable.window_link_table] for the
      one-component reading [Comp := unit].  With one component, the
      product [BL.nuF_all] is [nuJ] and the product [BL.nuE_all] is the
      original underlay tensor ([tensor_const]).  The [positional]
      hypothesis of that instance ([positional1]) asks for the lp order of
      every same-thread pair that is not semi-independent, which
      [link_lp_ord] provides.  So the trace-level packaging (the overlay
      witness, the no-overlay-call case and the empty-underlay case) is
      the proof of [WindowLinkTable.window_link_table] itself.
    Statements copied from [WindowLinkTable]: the section context of
    [WindowLinkTable.Link] (in Section [Product] verbatim; in Section
    [LinkJ] with [nuJ] / [nuJ_nil] / [positional_J] in place of
    [nuFc] / [nuF_nil] / [positional]; in Section [JointUnderlay] in the
    same way and without [compE] / [nuEc]), and the fields [p_lp_inj],
    [p_window], [p_S1_ord] of [WindowLinkTable.Positional].

    Equivalence with the product theorem.  [window_link_table_J] and
    [WindowLinkTable.window_link_table] are inter-derivable:
    [window_link_table_J] is proved as [WindowLinkTable.window_link_table]
    at [Comp := unit], and [window_link_table_of_J] derives
    [WindowLinkTable.window_link_table] back from [window_link_table_J].
    So [window_link_table_of_J] does not validate the joint theorem
    independently ([WindowLinkTable.window_link_table] is in its
    dependency cone); its own content is [positional_J_of_positional]
    ([Positional] implies [PositionalJ] for the product).  The content
    specific to the joint theorem is [link_lp_ord_fields] / [link_lp_ord]:
    cross-component lp order from the windows, which turns the
    all-pairs [positional] obligation of the one-component instance into
    the per-component [p_S1_ord].

    Modularity.  The ordering argument stays component-wise: each
    component orders its own pairs ([p_S1_ord]), and cross-component pairs
    are ordered through the windows and dominance together with the
    underlay witness ([h_ord] / [h_rt] over the positions in [Wu]; [h_ord]
    uses [E_compat]) and [F_cross].  The specification obligation does not:
    [p_S1J] is a single joint obligation on the lp-sorted list of the
    operations of all components, not one obligation per component.  So
    [window_link_table_J] is a composition theorem for the ordering, not
    for the specifications.  The product case, [window_link_table_of_J],
    recovers per-component specification obligations.

    Section [Product]: [window_link_table_of_J] proves the statement of
    [WindowLinkTable.window_link_table] (product [BL.nuF_all], hypothesis
    [positional] with per-component [p_S1]) from [window_link_table_J]
    with [nuJ := BL.nuF_all comp_dec compF nuFc]
    ([positional_J_of_positional]); [window_link_table_of_J_statement]
    checks in the kernel that the two statements coincide.  This product
    case has the overlay-specification shape (product [ν_F1 ⊗ ν_F2],
    trace.tex [def:spec-tensor]) of the paper's Horizontal Composition
    (overview.tex [prop:locality], relaxedlin.tex [prop:tensor-impl]).
    The gaps of the concern-matrix row "Horizontal composition /
    compatibility" apply unchanged:
    - one module [M : E -> F] whose components are given by [compF], not
      two separately verified implementations each on its own underlay;
    - [positional] is a hypothesis about whole executions;
    - complete executions only;
    - the underlay is assumed relaxed linearizable;
    - [compatible] is replaced by window dominance ([window_bodies])
      together with [E_compat] / [F_cross].
    The joint version is new relative to the paper.

    Section [JointUnderlay]: [compE] enters [WindowLinkTable] only
    through the underlay tensor [BL.nuE_all comp_dec compE nuEc]; the
    setting reads the component of an underlay call off its owner's
    [compF].  With a constant [compE] the tensor is an arbitrary joint
    underlay specification ([nuE_all_const]).  [window_link_table_J_jointE]
    instantiates [window_link_table_J] with [compE := fun _ => None] over
    [option Comp] (the overlay keeps its real components, as
    [Some ∘ compF]; no inhabitant of [Comp] is needed) and takes
    [rel_lin ... nuJE] for an arbitrary [nuJE].  This checks in the
    kernel that the lemmas of [BracketedLink] and [WindowLinkTable] used
    by the proof are generic in [compE] and [nuEc].

    Limitations.  No instance with a non-product [nuJ] is given here.
    The hypotheses of [window_link_table_J] are satisfiable whenever
    those of [WindowLinkTable.window_link_table] are:
    [positional_J_of_positional] and [nuF_all_nil] derive them, with
    [nuJ := BL.nuF_all comp_dec compF nuFc], from the product hypotheses,
    which [SeqLockModule.seqlock_module_rel_lin_K] discharges for its
    two-component instance.  That composition is not stated as a lemma
    (this file precedes [SeqLockModule]).  So non-vacuity is known only
    for product specifications.  Only complete executions and safety, as
    in [WindowLinkTable]. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Sorting.Sorted.
Require Import Stdlib.Sorting.Permutation.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Relations.Relation_Definitions.

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
Require Import examples.Relaxed.WindowTableJ.

Import ListNotations.

Module WindowLinkTableJ.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedTraceLin.
  Import RelaxedModuleFacts.

  Module BL := BracketedLink.BracketedLink.
  Module WC := WindowComposition.WindowComposition.
  Module WT := WindowTable.WindowTable.
  Module WLT := WindowLinkTable.WindowLinkTable.
  Module WTJ := WindowTableJ.WindowTableJ.

  (** ** Specifications: monotonicity, one component *)

  Lemma rel_lin_witness_nu_mono {G : RelaxedSig.t} {X : Type}
      (sel : X -> option (ThreadEvent G)) (L : list X)
      (indep : relation (Sig.op (effect G))) (nu nu' : list (Op G) -> Prop) W :
    (forall w, nu w -> nu' w) ->
    rel_lin_witness sel L indep nu W -> rel_lin_witness sel L indep nu' W.
  Proof. intros Hn [H1 H2]. exact (conj (Hn W H1) H2). Qed.

  Lemma rel_lin_nu_mono {G : RelaxedSig.t} {X : Type}
      (sel : X -> option (ThreadEvent G)) (L : list X)
      (indep : relation (Sig.op (effect G))) (nu nu' : list (Op G) -> Prop) :
    (forall w, nu w -> nu' w) -> rel_lin sel L indep nu -> rel_lin sel L indep nu'.
  Proof.
    intros Hn (W & HW). exists W. exact (rel_lin_witness_nu_mono sel L indep nu nu' W Hn HW).
  Qed.

  (** A tensor by projection ([BL.nuE_all], [BL.nuF_all]) over a constant
      component map is the specification of that component, provided the
      other components accept the empty list. *)
  Lemma tensor_const {G : RelaxedSig.t} {Comp : Type}
      (comp_dec : forall c c' : Comp, {c = c'} + {c <> c'}) (c0 : Comp)
      (nuc : Comp -> list (Op G) -> Prop) (nuJ : list (Op G) -> Prop) :
    (forall l, nuc c0 l <-> nuJ l) -> (forall c, c <> c0 -> nuc c []) ->
    forall w,
      (forall c, nuc c (filter (fun _ : Op G => if comp_dec c0 c then true else false) w)) <->
      nuJ w.
  Proof.
    intros H0 Hnil w. split.
    - intros H. specialize (H c0).
      rewrite WTJ.filter_all_true in H.
      + apply H0. exact H.
      + intros o _. destruct (comp_dec c0 c0) as [_|Hn]; [reflexivity | contradiction Hn; reflexivity].
    - intros H c. destruct (comp_dec c0 c) as [<-|Hne].
      + rewrite WTJ.filter_all_true by (intros; reflexivity). apply H0. exact H.
      + rewrite WTJ.filter_all_false by (intros; reflexivity).
        apply Hnil. intros E. apply Hne. symmetry. exact E.
  Qed.

  Lemma nuE_all_const_gen {E : RelaxedSig.t} {Comp : Type}
      (comp_dec : forall c c' : Comp, {c = c'} + {c <> c'}) (c0 : Comp)
      (nuEc : Comp -> list (Op E) -> Prop) (nuJE : list (Op E) -> Prop) :
    (forall l, nuEc c0 l <-> nuJE l) -> (forall c, c <> c0 -> nuEc c []) ->
    forall w, BL.nuE_all comp_dec (fun _ => c0) nuEc w <-> nuJE w.
  Proof. exact (tensor_const comp_dec c0 nuEc nuJE). Qed.

  Lemma nuF_all_const_gen {F : RelaxedSig.t} {Comp : Type}
      (comp_dec : forall c c' : Comp, {c = c'} + {c <> c'}) (c0 : Comp)
      (nuFc : Comp -> list (Op F) -> Prop) (nuJ : list (Op F) -> Prop) :
    (forall l, nuFc c0 l <-> nuJ l) -> (forall c, c <> c0 -> nuFc c []) ->
    forall w, BL.nuF_all comp_dec (fun _ => c0) nuFc w <-> nuJ w.
  Proof. exact (tensor_const comp_dec c0 nuFc nuJ). Qed.

  (** The constant-[compE] check: the underlay tensor with every underlay
      operation in component [c0], and [nuJE] as the specification of
      [c0], is [nuJE]. *)
  Lemma nuE_all_const {E : RelaxedSig.t} {Comp : Type}
      (comp_dec : forall c c' : Comp, {c = c'} + {c <> c'}) (c0 : Comp)
      (nuJE : list (Op E) -> Prop) w :
    BL.nuE_all comp_dec (fun _ => c0) (fun c l => if comp_dec c c0 then nuJE l else True) w <->
    nuJE w.
  Proof.
    apply nuE_all_const_gen.
    - intros l. destruct (comp_dec c0 c0) as [_|Hn]; [apply iff_refl | contradiction Hn; reflexivity].
    - intros c Hne. destruct (comp_dec c c0) as [Hc|_]; [contradiction | exact I].
  Qed.

  (** The trivial component specification.  It fills the [nuFc] argument
      of [WLT.setting] and [WLT.Positional], where nothing used below
      reads it. *)
  Definition no_spec {G : RelaxedSig.t} {C : Type} : C -> list (Op G) -> Prop :=
    fun _ _ => True.

  (** ** The joint theorem *)

  Section LinkJ.
    Context {E F : RelaxedSig.t}.
    Context (VE : RelaxedLTSSpec.LTS E) (M : RelaxedModuleImpl E F).
    Context (keyE_dec : forall k k' : CallKey E, {k = k'} + {k <> k'}).
    Context (keyF_dec : forall k k' : CallKey F, {k = k'} + {k <> k'}).
    Context {Comp : Type} (comp_dec : forall c c' : Comp, {c = c'} + {c <> c'}).
    Context (compE : Sig.op (effect E) -> Comp) (compF : Sig.op (effect F) -> Comp).
    Context (nuEc : Comp -> list (Op E) -> Prop) (nuJ : list (Op F) -> Prop).

    Context {Cat : Type} (to : Cat -> Cat -> Prop).
    Context (catE : Sig.op (effect E) -> Cat) (catF : Sig.op (effect F) -> Cat).

    Hypothesis E_compat : forall o o',
      semi_independent E o o' -> ~ to (catE o) (catE o').
    Hypothesis F_cross : forall o o', compF o <> compF o' ->
      ~ to (catF o) (catF o') -> semi_independent F o o'.
    Hypothesis nuJ_nil : nuJ [].

    Context (wlo whi : Sig.op (effect F) -> list (ThreadEvent E) -> nat).
    Hypothesis window_bodies : forall t op tr ret,
      program_produces_tagged t (M op t) tr ret ->
      exists klo olo khi ohi,
        BL.inv_in (map untag tr) (wlo op (map untag tr)) klo olo /\
        BL.inv_in (map untag tr) (whi op (map untag tr)) khi ohi /\
        WT.out_le to (catF op) (catE ohi) /\
        WT.in_le to (catF op) (catE olo).

    Section Data.
      Context (IT : list (@ITraceEvent E F)) (ic : @IConfig E F VE).
      Context (Wu : list (Op E)) (r0 : @InvRec E F) (u0 : Op E).

      Abbreviation secs := (WLT.secs VE ic).
      Abbreviation pos := (WLT.pos keyE_dec Wu).
      Abbreviation ovl := (WLT.ovl VE keyF_dec ic r0).
      Abbreviation comp := (WLT.comp VE keyF_dec compF ic r0).
      Abbreviation po := (WLT.po VE keyF_dec ic r0).
      Abbreviation opF := (WLT.opF VE keyF_dec ic r0).
      Abbreviation lo := (WLT.lo VE keyE_dec keyF_dec wlo ic Wu r0 u0).
      Abbreviation hi := (WLT.hi VE keyE_dec keyF_dec whi ic Wu r0 u0).

      (** The abstract setting of [WLT], with the trivial component
          specification. *)
      Definition settingJ (lpc : CallKey F -> Op E) : WT.Setting Cat :=
        WLT.setting VE keyE_dec keyF_dec comp_dec compF no_spec catE catF wlo whi
          IT ic Wu r0 u0 lpc.

      Record PositionalJ (lpc : CallKey F -> Op E) : Prop := {
        p_lp_inj : forall s s', In s secs -> In s' secs -> pos (lpc s) = pos (lpc s') -> s = s';
        p_window : forall s, In s secs -> pos (lo s) <= pos (lpc s) <= pos (hi s);
        p_S1J : nuJ (map ovl (WC.isort (WT.lp (settingJ lpc)) secs));
        p_S1_ord : forall s s', In s secs -> In s' secs -> comp s = comp s' -> po s s' ->
                                ~ semi_independent F (opF s) (opF s') -> pos (lpc s) < pos (lpc s');
      }.
    End Data.

    (** The sort key of [p_S1J], unfolded (for rewriting [p_S1J]). *)
    Lemma settingJ_lp IT ic Wu r0 u0 lpc :
      WT.lp (settingJ IT ic Wu r0 u0 lpc) = fun s => WLT.pos keyE_dec Wu (lpc s).
    Proof. reflexivity. Qed.

    Hypothesis positional_J : forall IT ic Wu r0 u0,
      IInv VE M IT ic -> ic_queue VE ic = [] ->
      (forall e, In e (ic_calls VE ic) -> ce_cell F e = DeadCall) ->
      rel_lin_witness BL.usel IT (semi_independent E) (BL.nuE_all comp_dec compE nuEc) Wu ->
      exists lpc, PositionalJ IT ic Wu r0 u0 lpc.

    (** *** One complete instrumented execution *)

    Section Instance.
      Context (IT : list (@ITraceEvent E F)) (ic : @IConfig E F VE).
      Context (Hinv : IInv VE M IT ic) (Hq : ic_queue VE ic = []).
      Context (Wu : list (Op E)).
      Context (HWu : rel_lin_witness BL.usel IT (semi_independent E)
                       (BL.nuE_all comp_dec compE nuEc) Wu).
      Context (r0 : @InvRec E F) (u0 : Op E).

      Lemma positional_no_spec lpc : PositionalJ IT ic Wu r0 u0 lpc ->
        WLT.Positional VE keyE_dec keyF_dec comp_dec compF no_spec catE catF wlo whi
          IT ic Wu r0 u0 lpc.
      Proof.
        intros [Hinj Hwin _ Hord].
        constructor; [exact Hinj | exact Hwin | intros c; exact I | exact Hord].
      Qed.

      Lemma link_hyps0J lpc : PositionalJ IT ic Wu r0 u0 lpc ->
        WTJ.Hyps0J to (settingJ IT ic Wu r0 u0 lpc) nuJ.
      Proof.
        intros HP. apply (WTJ.hyps0J_intro to (settingJ IT ic Wu r0 u0 lpc) nuJ).
        - exact (WLT.link_hyps0 VE M keyE_dec keyF_dec comp_dec compE compF nuEc no_spec
                   to catE catF E_compat wlo whi window_bodies IT ic Hinv Hq Wu HWu r0 u0 lpc
                   (positional_no_spec lpc HP)).
        - exact (p_S1J _ _ _ _ _ _ HP).
      Qed.

      Lemma link_inheritJ lpc : WT.Inherit to (settingJ IT ic Wu r0 u0 lpc).
      Proof.
        exact (WLT.link_inherit VE M keyE_dec keyF_dec comp_dec compE compF nuEc no_spec
                 to catE catF wlo whi window_bodies IT ic Hinv Hq Wu HWu r0 u0 lpc).
      Qed.

      (** The abstract joint theorem holds of the module setting.  (Not
          used below: the trace-level witness is built by
          [WLT.window_link_table], see [window_link_table_J].) *)
      Lemma link_window_composition_J lpc : PositionalJ IT ic Wu r0 u0 lpc ->
        WTJ.ConclusionJ to (settingJ IT ic Wu r0 u0 lpc) nuJ.
      Proof.
        intros HP.
        exact (WTJ.window_composition_J to (settingJ IT ic Wu r0 u0 lpc) nuJ
                 (link_hyps0J lpc HP) (link_inheritJ lpc)).
      Qed.

      (** Every same-thread overlay pair that is not semi-independent is
          ordered by linearization point: in one component by [p_S1_ord],
          across components by [WT.lp_before] (windows, dominance, and the
          underlay witness [Wu] through [h_ord] / [h_rt] with [E_compat])
          and [F_cross].  Only the three ordering fields of [PositionalJ]
          are needed, not [p_S1J], so this can be used while proving
          [p_S1J]. *)
      Lemma link_lp_ord_fields (lpc : CallKey F -> Op E)
          (Hinj : forall s s', In s (WLT.secs VE ic) -> In s' (WLT.secs VE ic) ->
                    WLT.pos keyE_dec Wu (lpc s) = WLT.pos keyE_dec Wu (lpc s') -> s = s')
          (Hwin : forall s, In s (WLT.secs VE ic) ->
                    WLT.pos keyE_dec Wu (WLT.lo VE keyE_dec keyF_dec wlo ic Wu r0 u0 s)
                      <= WLT.pos keyE_dec Wu (lpc s)
                      <= WLT.pos keyE_dec Wu (WLT.hi VE keyE_dec keyF_dec whi ic Wu r0 u0 s))
          (Hord : forall s s', In s (WLT.secs VE ic) -> In s' (WLT.secs VE ic) ->
                    WLT.comp VE keyF_dec compF ic r0 s = WLT.comp VE keyF_dec compF ic r0 s' ->
                    WLT.po VE keyF_dec ic r0 s s' ->
                    ~ semi_independent F (WLT.opF VE keyF_dec ic r0 s)
                                         (WLT.opF VE keyF_dec ic r0 s') ->
                    WLT.pos keyE_dec Wu (lpc s) < WLT.pos keyE_dec Wu (lpc s')) :
        forall s s', In s (WLT.secs VE ic) -> In s' (WLT.secs VE ic) ->
          WLT.po VE keyF_dec ic r0 s s' ->
          ~ semi_independent F (WLT.opF VE keyF_dec ic r0 s) (WLT.opF VE keyF_dec ic r0 s') ->
          WLT.pos keyE_dec Wu (lpc s) < WLT.pos keyE_dec Wu (lpc s').
      Proof.
        intros s s' Hs Hs' Hpo Hn.
        set (S := settingJ IT ic Wu r0 u0 lpc).
        assert (H0 : WT.Hyps0 to S).
        { exact (WLT.link_hyps0 VE M keyE_dec keyF_dec comp_dec compE compF nuEc no_spec
                   to catE catF E_compat wlo whi window_bodies IT ic Hinv Hq Wu HWu r0 u0 lpc
                   (WLT.Build_Positional VE keyE_dec keyF_dec comp_dec compF no_spec catE catF
                      wlo whi IT ic Wu r0 u0 lpc Hinj Hwin (fun _ => I) Hord)). }
        assert (HnIF : ~ WT.IF to S s s').
        { change (~ (if comp_dec (WLT.comp VE keyF_dec compF ic r0 s)
                                 (WLT.comp VE keyF_dec compF ic r0 s')
                     then semi_independent F (WLT.opF VE keyF_dec ic r0 s)
                                             (WLT.opF VE keyF_dec ic r0 s')
                     else ~ to (catF (WLT.opF VE keyF_dec ic r0 s))
                               (catF (WLT.opF VE keyF_dec ic r0 s')))).
          destruct (comp_dec (WLT.comp VE keyF_dec compF ic r0 s)
                             (WLT.comp VE keyF_dec compF ic r0 s')) as [_ | Nc];
            [exact Hn |].
          intros Hnto. apply Hn. apply F_cross; [exact Nc | exact Hnto]. }
        exact (WT.lp_before to S H0 (link_inheritJ lpc) s s' Hs Hs' (or_introl (conj Hpo HnIF))).
      Qed.

      Lemma link_lp_ord lpc : PositionalJ IT ic Wu r0 u0 lpc ->
        forall s s', In s (WLT.secs VE ic) -> In s' (WLT.secs VE ic) ->
          WLT.po VE keyF_dec ic r0 s s' ->
          ~ semi_independent F (WLT.opF VE keyF_dec ic r0 s) (WLT.opF VE keyF_dec ic r0 s') ->
          WLT.pos keyE_dec Wu (lpc s) < WLT.pos keyE_dec Wu (lpc s').
      Proof.
        intros HP.
        exact (link_lp_ord_fields lpc (p_lp_inj _ _ _ _ _ _ HP) (p_window _ _ _ _ _ _ HP)
                 (p_S1_ord _ _ _ _ _ _ HP)).
      Qed.
    End Instance.

    (** *** The one-component reading *)

    Definition nuE1 : unit -> list (Op E) -> Prop := fun _ w => BL.nuE_all comp_dec compE nuEc w.
    Definition nuF1 : unit -> list (Op F) -> Prop := fun _ w => nuJ w.

    Lemma nuE1_iff w :
      BL.nuE_all WTJ.unit_dec (fun _ => tt) nuE1 w <-> BL.nuE_all comp_dec compE nuEc w.
    Proof.
      apply nuE_all_const_gen.
      - intros l. split; intros H; exact H.
      - intros [] Hn. exfalso. apply Hn. reflexivity.
    Qed.

    Lemma nuF1_iff w : BL.nuF_all WTJ.unit_dec (fun _ => tt) nuF1 w <-> nuJ w.
    Proof.
      apply nuF_all_const_gen.
      - intros l. split; intros H; exact H.
      - intros [] Hn. exfalso. apply Hn. reflexivity.
    Qed.

    Lemma F_cross1 : forall o o' : Sig.op (effect F),
      (fun _ => tt) o <> (fun _ => tt) o' -> ~ to (catF o) (catF o') -> semi_independent F o o'.
    Proof. intros o o' Hn. exfalso. apply Hn. reflexivity. Qed.

    Lemma nuF1_nil : forall c, nuF1 c [].
    Proof. intros c. exact nuJ_nil. Qed.

    (** The [positional] hypothesis of the one-component instance. *)
    Lemma positional1 : forall IT ic Wu r0 u0,
      IInv VE M IT ic -> ic_queue VE ic = [] ->
      (forall e, In e (ic_calls VE ic) -> ce_cell F e = DeadCall) ->
      rel_lin_witness BL.usel IT (semi_independent E)
        (BL.nuE_all WTJ.unit_dec (fun _ => tt) nuE1) Wu ->
      exists lpc, WLT.Positional VE keyE_dec keyF_dec WTJ.unit_dec (fun _ => tt) nuF1
                    catE catF wlo whi IT ic Wu r0 u0 lpc.
    Proof.
      intros IT ic Wu r0 u0 Hinv Hq Hd HWu1.
      assert (HWu : rel_lin_witness BL.usel IT (semi_independent E)
                      (BL.nuE_all comp_dec compE nuEc) Wu).
      { apply (rel_lin_witness_nu_mono _ _ _ _ _ _ (fun w => proj1 (nuE1_iff w))). exact HWu1. }
      destruct (positional_J IT ic Wu r0 u0 Hinv Hq Hd HWu) as (lpc & HP).
      exists lpc. constructor.
      - exact (p_lp_inj _ _ _ _ _ _ HP).
      - exact (p_window _ _ _ _ _ _ HP).
      - intros [].
        rewrite WTJ.filter_all_true by (intros s _; reflexivity).
        exact (p_S1J _ _ _ _ _ _ HP).
      - intros s s' Hs Hs' _ Hpo Hn.
        exact (link_lp_ord IT ic Hinv Hq Wu HWu r0 u0 lpc HP s s' Hs Hs' Hpo Hn).
    Qed.

    (** ** The linking theorem *)

    Theorem window_link_table_J q0 T c :
      module_execution_tagged VE M (initial_tagged_module VE q0) T c ->
      tm_queue c = [] ->
      (forall e, In e (tm_calls c) -> ce_cell F e = DeadCall) ->
      rel_lin BL.under_sel T (semi_independent E) (BL.nuE_all comp_dec compE nuEc) ->
      rel_lin BL.over_sel T (semi_independent F) nuJ.
    Proof.
      intros Hexec Hqc Hdc Hunder.
      apply (rel_lin_nu_mono BL.over_sel T (semi_independent F) _ _
               (fun w => proj1 (nuF1_iff w))).
      apply (WLT.window_link_table VE M keyE_dec keyF_dec WTJ.unit_dec (fun _ => tt) (fun _ => tt)
               nuE1 nuF1 to catE catF E_compat F_cross1 nuF1_nil wlo whi window_bodies
               positional1 q0 T c Hexec Hqc Hdc).
      apply (rel_lin_nu_mono BL.under_sel T (semi_independent E) _ _
               (fun w => proj2 (nuE1_iff w))).
      exact Hunder.
    Qed.
  End LinkJ.

  (** ** Conservativity: the product is an instance *)

  Section Product.
    Context {E F : RelaxedSig.t}.
    Context (VE : RelaxedLTSSpec.LTS E) (M : RelaxedModuleImpl E F).
    Context (keyE_dec : forall k k' : CallKey E, {k = k'} + {k <> k'}).
    Context (keyF_dec : forall k k' : CallKey F, {k = k'} + {k <> k'}).
    Context {Comp : Type} (comp_dec : forall c c' : Comp, {c = c'} + {c <> c'}).
    Context (compE : Sig.op (effect E) -> Comp) (compF : Sig.op (effect F) -> Comp).
    Context (nuEc : Comp -> list (Op E) -> Prop) (nuFc : Comp -> list (Op F) -> Prop).

    Context {Cat : Type} (to : Cat -> Cat -> Prop).
    Context (catE : Sig.op (effect E) -> Cat) (catF : Sig.op (effect F) -> Cat).

    Hypothesis E_compat : forall o o',
      semi_independent E o o' -> ~ to (catE o) (catE o').
    Hypothesis F_cross : forall o o', compF o <> compF o' ->
      ~ to (catF o) (catF o') -> semi_independent F o o'.
    Hypothesis nuF_nil : forall c, nuFc c [].

    Context (wlo whi : Sig.op (effect F) -> list (ThreadEvent E) -> nat).
    Hypothesis window_bodies : forall t op tr ret,
      program_produces_tagged t (M op t) tr ret ->
      exists klo olo khi ohi,
        BL.inv_in (map untag tr) (wlo op (map untag tr)) klo olo /\
        BL.inv_in (map untag tr) (whi op (map untag tr)) khi ohi /\
        WT.out_le to (catF op) (catE ohi) /\
        WT.in_le to (catF op) (catE olo).

    Hypothesis positional : forall IT ic Wu r0 u0,
      IInv VE M IT ic -> ic_queue VE ic = [] ->
      (forall e, In e (ic_calls VE ic) -> ce_cell F e = DeadCall) ->
      rel_lin_witness BL.usel IT (semi_independent E) (BL.nuE_all comp_dec compE nuEc) Wu ->
      exists lpc, WLT.Positional VE keyE_dec keyF_dec comp_dec compF nuFc catE catF wlo whi
                    IT ic Wu r0 u0 lpc.

    (** Per-component [p_S1] gives the joint [p_S1J] for the product:
        projecting the lp-sorted list is sorting the projection. *)
    Lemma positional_J_of_positional : forall IT ic Wu r0 u0,
      IInv VE M IT ic -> ic_queue VE ic = [] ->
      (forall e, In e (ic_calls VE ic) -> ce_cell F e = DeadCall) ->
      rel_lin_witness BL.usel IT (semi_independent E) (BL.nuE_all comp_dec compE nuEc) Wu ->
      exists lpc, PositionalJ VE keyE_dec keyF_dec comp_dec compF (BL.nuF_all comp_dec compF nuFc)
                    catE catF wlo whi IT ic Wu r0 u0 lpc.
    Proof.
      intros IT ic Wu r0 u0 Hinv Hq Hd HWu.
      destruct (positional IT ic Wu r0 u0 Hinv Hq Hd HWu) as (lpc & [Hinj Hwin HS1 HS1o]).
      exists lpc. constructor; [exact Hinj | exact Hwin | | exact HS1o].
      intros c. unfold BL.proj_F. rewrite filter_map_swap. rewrite WC.filter_isort.
      - exact (HS1 c).
      - exact Hinj.
      - exact (ii_invs_nodup _ _ _ _ Hinv).
    Qed.

    Lemma nuF_all_nil : BL.nuF_all comp_dec compF nuFc [].
    Proof. intros c. exact (nuF_nil c). Qed.

    Theorem window_link_table_of_J q0 T c :
      module_execution_tagged VE M (initial_tagged_module VE q0) T c ->
      tm_queue c = [] ->
      (forall e, In e (tm_calls c) -> ce_cell F e = DeadCall) ->
      rel_lin BL.under_sel T (semi_independent E) (BL.nuE_all comp_dec compE nuEc) ->
      rel_lin BL.over_sel T (semi_independent F) (BL.nuF_all comp_dec compF nuFc).
    Proof.
      exact (window_link_table_J VE M keyE_dec keyF_dec comp_dec compE compF nuEc
               (BL.nuF_all comp_dec compF nuFc) to catE catF E_compat F_cross nuF_all_nil
               wlo whi window_bodies positional_J_of_positional q0 T c).
    Qed.
  End Product.

  (** [window_link_table_of_J] has literally the statement of
      [WindowLinkTable.window_link_table]. *)
  Example window_link_table_of_J_statement :
    ltac:(let T := type of @WLT.window_link_table in exact T).
  Proof. exact @window_link_table_of_J. Qed.

  (** ** A joint underlay specification: constant [compE] *)

  Section JointUnderlay.
    Context {E F : RelaxedSig.t}.
    Context (VE : RelaxedLTSSpec.LTS E) (M : RelaxedModuleImpl E F).
    Context (keyE_dec : forall k k' : CallKey E, {k = k'} + {k <> k'}).
    Context (keyF_dec : forall k k' : CallKey F, {k = k'} + {k <> k'}).
    Context {Comp : Type} (comp_dec : forall c c' : Comp, {c = c'} + {c <> c'}).
    Context (compF : Sig.op (effect F) -> Comp).
    Context (nuJE : list (Op E) -> Prop) (nuJ : list (Op F) -> Prop).

    Context {Cat : Type} (to : Cat -> Cat -> Prop).
    Context (catE : Sig.op (effect E) -> Cat) (catF : Sig.op (effect F) -> Cat).

    Hypothesis E_compat : forall o o',
      semi_independent E o o' -> ~ to (catE o) (catE o').
    Hypothesis F_cross : forall o o', compF o <> compF o' ->
      ~ to (catF o) (catF o') -> semi_independent F o o'.
    Hypothesis nuJ_nil : nuJ [].

    Context (wlo whi : Sig.op (effect F) -> list (ThreadEvent E) -> nat).
    Hypothesis window_bodies : forall t op tr ret,
      program_produces_tagged t (M op t) tr ret ->
      exists klo olo khi ohi,
        BL.inv_in (map untag tr) (wlo op (map untag tr)) klo olo /\
        BL.inv_in (map untag tr) (whi op (map untag tr)) khi ohi /\
        WT.out_le to (catF op) (catE ohi) /\
        WT.in_le to (catF op) (catE olo).

    (** [PositionalJ] as in Section [LinkJ], against a joint underlay
        witness. *)
    Hypothesis positional_JE : forall IT ic Wu r0 u0,
      IInv VE M IT ic -> ic_queue VE ic = [] ->
      (forall e, In e (ic_calls VE ic) -> ce_cell F e = DeadCall) ->
      rel_lin_witness BL.usel IT (semi_independent E) nuJE Wu ->
      exists lpc, PositionalJ VE keyE_dec keyF_dec comp_dec compF nuJ catE catF wlo whi
                    IT ic Wu r0 u0 lpc.

    (** Overlay components [Some c]; the whole underlay is component [None]. *)
    Definition opt_dec (a b : option Comp) : {a = b} + {a <> b}.
    Proof.
      destruct a as [a|], b as [b|].
      - destruct (comp_dec a b) as [<-|Hn]; [left; reflexivity|].
        right. intros H. injection H as H. exact (Hn H).
      - right. discriminate.
      - right. discriminate.
      - left. reflexivity.
    Defined.

    Lemma F_cross_opt : forall o o' : Sig.op (effect F),
      (fun o => Some (compF o)) o <> (fun o => Some (compF o)) o' ->
      ~ to (catF o) (catF o') -> semi_independent F o o'.
    Proof.
      intros o o' Hn. apply F_cross. intros Ho. apply Hn. cbn. rewrite Ho. reflexivity.
    Qed.

    Lemma positional_opt : forall IT ic Wu r0 u0,
      IInv VE M IT ic -> ic_queue VE ic = [] ->
      (forall e, In e (ic_calls VE ic) -> ce_cell F e = DeadCall) ->
      rel_lin_witness BL.usel IT (semi_independent E)
        (BL.nuE_all opt_dec (fun _ => None) (fun c l => if opt_dec c None then nuJE l else True)) Wu ->
      exists lpc, PositionalJ VE keyE_dec keyF_dec opt_dec (fun o => Some (compF o)) nuJ
                    catE catF wlo whi IT ic Wu r0 u0 lpc.
    Proof.
      intros IT ic Wu r0 u0 Hinv Hq Hd HWu.
      apply (rel_lin_witness_nu_mono _ _ _ _ _ _
               (fun w => proj1 (nuE_all_const opt_dec None nuJE w))) in HWu.
      destruct (positional_JE IT ic Wu r0 u0 Hinv Hq Hd HWu) as (lpc & [Hinj Hwin HS1 Hord]).
      exists lpc. constructor; [exact Hinj | exact Hwin | exact HS1 |].
      intros s s' Hs Hs' Hc. apply Hord; [exact Hs | exact Hs' |].
      injection Hc as Hc. exact Hc.
    Qed.

    Theorem window_link_table_J_jointE q0 T c :
      module_execution_tagged VE M (initial_tagged_module VE q0) T c ->
      tm_queue c = [] ->
      (forall e, In e (tm_calls c) -> ce_cell F e = DeadCall) ->
      rel_lin BL.under_sel T (semi_independent E) nuJE ->
      rel_lin BL.over_sel T (semi_independent F) nuJ.
    Proof.
      intros Hexec Hqc Hdc Hunder.
      apply (window_link_table_J VE M keyE_dec keyF_dec opt_dec (fun _ => None)
               (fun o => Some (compF o)) (fun c l => if opt_dec c None then nuJE l else True)
               nuJ to catE catF E_compat F_cross_opt nuJ_nil wlo whi window_bodies
               positional_opt q0 T c Hexec Hqc Hdc).
      apply (rel_lin_nu_mono BL.under_sel T (semi_independent E) _ _
               (fun w => proj2 (nuE_all_const opt_dec None nuJE w))).
      exact Hunder.
    Qed.
  End JointUnderlay.
End WindowLinkTableJ.
