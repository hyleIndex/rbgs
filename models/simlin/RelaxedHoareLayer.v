(** * RLHL, part 10: layering foundations (RLHL-3c.1)

    Purpose.  The first of three files for latest-review M-22
    ("absorption, linking and [mtraces_mono] are missing").  This file
    provides the semantic tools that a vertical-composition theorem for
    [RelaxedHoareCompLin.RCompLin] needs; absorption is in
    [RelaxedHoareAbsorb], linking is planned for [RelaxedHoareLink]
    (plan: [.rocq-review/tasks/RLHL-3c.md], sub-task 3c.1).

    ** Results

    - Trace-determinedness.  [LPaths V v u]: [u] labels a path of [V]
      from [v].  [mtraces_mono]: if every path of [V1] from [v1] is a
      path of [V2] from [v2], then every overlay trace of a module [M]
      over [V1] is one over [V2].  So [MTraces V M v] depends on the
      underlay only through its path language from [v] ([mtraces_ext]),
      and [RCompLin] is antitone in the underlay's path language
      ([complin_mono_under]) and monotone in the overlay's
      ([complin_mono_over], via the copy-cat instance [rtraces_mono]).
      [lpaths_prefix]: path languages are prefix-closed.  The proof of
      [mtraces_mono] is the transport of
      [ViewLHL.exec_underlay_path] / [ViewLHL.exec_transport]: only the
      underlay steps of an execution look at the underlay.
    - [FreeLTS E]: the chaos LTS ([Step := True]).  [mtraces_free]: an
      execution over [V] is an execution over [FreeLTS] whose underlay
      trace is a path of [V].
    - [exec_app]: concatenation of tagged module executions.
    - The module as an LTS.  [ModLTS VE M : LTS F] has the tagged module
      configurations of [M] over [VE] as states; one step [mod_step] is
      a block of underlay steps of the module followed by one overlay
      event.  [modlts_paths]: the paths of [ModLTS VE M] from
      [initial_tagged_module VE σ0] are exactly [MTraces VE M σ0].
      Underlay steps that are pending at the end of an execution are
      invisible; they do not change the overlay trace.  [ModLTS] nests:
      [ModLTS (ModLTS VE M1) M2] is the composite "M2 over M1 over VE".
    - The trace set as an LTS.  [TrLTS T]: states are traces, a step
      appends one event and stays in [T].  [trlts_paths]: for a
      prefix-closed [T] containing [[]], the paths of [TrLTS T] from
      [[]] are exactly [T].  [mtraces_nil]: [MTraces] contains [[]].
      [modlts_trlts]: running [M2] over the operational composite
      [ModLTS VE M1] or over the trace set [TrLTS (MTraces VE M1 σ0)]
      gives the same overlay traces.  So the composite is determined by
      the trace set of the lower layer (the interaction-and-hiding
      reading of layering).
    - Sanity check: [hlift_drop_via_mono] re-derives the [⊇] half of
      [RelaxedHoareCompLinSpec.hlift] (dropping the handle-linearity
      list) from [mtraces_mono].

    ** K / S / P / R

    - K: every result below is closed under the global context
      ([Print Assumptions]).  No axiom, no [classic], no [eq_rect_eq].
    - S: generic in the signatures, the underlay LTSs, the module and
      the initial states; every execution, complete or not.
      [trlts_paths] assumes [T []] and prefix-closure of [T] (both hold
      for every [MTraces] set: [mtraces_nil], [RelaxedHoareCompLin.mtraces_prefix]).
    - P: these are prerequisites; the paper has no statement of its own
      for them.  The composition they support is the paper's vertical
      composition (relaxedlin.tex:56-71: interaction-and-hiding [S;T],
      inlining, associativity; relaxedlin.tex:88, prop:vertical-composition)
      and the saturation proposition (Appendix/relaxedlin.tex:53-56,
      [RelaxedHoareAbsorb]); see D1 below for what is not covered.
      [modlts_trlts] is the operational reading of [S;T]
      (relaxedlin.tex:57-61): [M2] run over the trace set of [M1].
    - R: latest-review M-22 item (1) ([mtraces_mono]) and the module
      trace-LTS that items (2)-(3) (absorption, linking) are stated
      over.  Absorption and linking themselves are not here.

    ** Provisional research-level choices (research-intent.md §7, not yet
       decided by the author)

    - D1 (semantic layering): the composite "N over M" is the LTS
      [ModLTS VE M] (with [N] run over it), not a syntactic inlining of
      [N]'s calls into [M]'s bodies.  [RelaxedLang] has no module-call
      construct.  Consequence: relaxedlin.tex:62-70 (inlining,
      ⟦M;N⟧ = ⟦M⟧;⟦N⟧, associativity) cannot be cited as mechanized;
      [modlts_trlts] is the semantic substitute.
    - D2 (saturation only on the E-side, over specification
      presentations) and D3 (verimpl in copy-cat form) concern
      [RelaxedHoareAbsorb] and [RelaxedHoareLink]; nothing in this file
      depends on them.

    ** Known limitations

    - [ModLTS]'s [Error] is [False]: module errors are not modelled (the
      tagged module semantics has no error rule; latest-review m-8).
    - [ModLTS VE M] hides the module's internal steps but keeps its
      configuration as the state; two configurations with the same
      future behaviour are not identified.  Only path languages matter
      for the results here ([mtraces_ext]).

    Name clashes: [ViewLHL] and [RelaxedHoareCompLin] both define
    [vf_path_cons_inv], and [RelaxedHoareCompLinSpec] defines [lift_step]
    and [lift_exec].  This file imports [RelaxedHoareCompLin] but neither
    [ViewLHL] nor [RelaxedHoareCompLinSpec]: it uses the qualified names
    [ViewLHL.exec_underlay_path], [ViewLHL.exec_transport],
    [ViewLHL.underlay_events], [RelaxedHoareCompLinSpec.HL], and defines
    no [vf_path_cons_inv] and no [lift_*] names. *)

Require Import Stdlib.Lists.List.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedGSim.
Require Import models.view.ViewLHL.
Require Import models.simlin.RelaxedHoareSpec.
Require Import models.simlin.RelaxedHoareCompLin.
Require Import models.simlin.RelaxedHoareCompLinSpec.

Import ListNotations.


Module RelaxedHoareLayer.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedModuleSemantics.
  Import RelaxedGSim.
  Import RelaxedHoareCompLin.

  (** ** Path languages *)

  (** [u] labels a path of [V] from [v]. *)
  Definition LPaths {F : RelaxedSig.t} (V : LTS F) (v : State V) (u : list (ThreadEvent F)) : Prop :=
    exists v', vf_path V v u v'.

  Lemma lpaths_nil {F : RelaxedSig.t} (V : LTS F) (v : State V) : LPaths V v [].
  Proof. exists v. constructor. Qed.

  Lemma lpaths_prefix {F : RelaxedSig.t} (V : LTS F) (v : State V) u1 u2 :
    LPaths V v (u1 ++ u2) -> LPaths V v u1.
  Proof.
    intros (v' & Hp). destruct (RelaxedHoareSpec.vf_path_app_inv V v u1 u2 v' Hp) as (v1 & H1 & _).
    exists v1. exact H1.
  Qed.

  (** ** Trace-determinedness (M-22 item 1) *)

  (** The overlay traces of a module over an underlay depend on the
      underlay only through its path language: an execution over [V1]
      moves to [V2] along its underlay trace. *)
  Theorem mtraces_mono {E F : RelaxedSig.t} (V1 V2 : LTS E) (M : RelaxedModuleImpl E F)
      (v1 : State V1) (v2 : State V2) :
    (forall u, LPaths V1 v1 u -> LPaths V2 v2 u) ->
    forall s, MTraces V1 M v1 s -> MTraces V2 M v2 s.
  Proof.
    intros Hp s (evs & c & Hex & Hov).
    pose proof (ViewLHL.exec_underlay_path M V1 _ _ _ Hex) as Hu.
    destruct (Hp _ (ex_intro _ _ Hu)) as (v2f & Hv2).
    destruct (ViewLHL.exec_transport M V1 V2 _ _ _ Hex v2 v2f Hv2) as (d & Hd & _).
    exists evs, d. split; [exact Hd | exact Hov].
  Qed.

  Corollary mtraces_ext {E F : RelaxedSig.t} (V1 V2 : LTS E) (M : RelaxedModuleImpl E F)
      (v1 : State V1) (v2 : State V2) :
    (forall u, LPaths V1 v1 u <-> LPaths V2 v2 u) ->
    forall s, MTraces V1 M v1 s <-> MTraces V2 M v2 s.
  Proof.
    intros Hp s. split; apply mtraces_mono; intros u; apply Hp.
  Qed.

  (** The copy-cat instance. *)
  Corollary rtraces_mono {F : RelaxedSig.t} (V1 V2 : LTS F) (v1 : State V1) (v2 : State V2) :
    (forall u, LPaths V1 v1 u -> LPaths V2 v2 u) ->
    forall s, RTraces V1 v1 s -> RTraces V2 v2 s.
  Proof. exact (mtraces_mono V1 V2 idF v1 v2). Qed.

  (** Copy-cat inclusion is antitone in the path language of the
      underlay: a module verified over a larger underlay is correct over
      a smaller one. *)
  Corollary complin_mono_under {E F : RelaxedSig.t} (M : RelaxedModuleImpl E F) (V1 V2 : LTS E)
      (v1 : State V1) (v2 : State V2) (VF : LTS F) (w : State VF) :
    (forall u, LPaths V1 v1 u -> LPaths V2 v2 u) ->
    RCompLin M V2 v2 VF w -> RCompLin M V1 v1 VF w.
  Proof.
    intros Hp HC s Hs. apply HC. exact (mtraces_mono V1 V2 M v1 v2 Hp s Hs).
  Qed.

  (** And monotone in the path language of the overlay specification. *)
  Corollary complin_mono_over {E F : RelaxedSig.t} (M : RelaxedModuleImpl E F) (VE : LTS E)
      (σ0 : State VE) (W1 W2 : LTS F) (w1 : State W1) (w2 : State W2) :
    (forall u, LPaths W1 w1 u -> LPaths W2 w2 u) ->
    RCompLin M VE σ0 W1 w1 -> RCompLin M VE σ0 W2 w2.
  Proof.
    intros Hp HC s Hs. exact (rtraces_mono W1 W2 w1 w2 Hp s (HC s Hs)).
  Qed.

  (** ** The chaos LTS *)

  Definition FreeLTS (E : RelaxedSig.t) : LTS E :=
    {| State := unit; Step := fun _ _ _ => True; Error := fun _ _ => False |}.

  Lemma free_path {E : RelaxedSig.t} (u : list (ThreadEvent E)) : vf_path (FreeLTS E) tt u tt.
  Proof.
    induction u as [| e u IH]; [constructor |]. econstructor; [exact Logic.I | exact IH].
  Qed.

  (** An execution over [V] is an execution over the chaos LTS whose
      underlay trace is a path of [V]. *)
  Theorem mtraces_free {E F : RelaxedSig.t} (V : LTS E) (M : RelaxedModuleImpl E F) (σ0 : State V) s :
    MTraces V M σ0 s <->
    exists evs c, module_execution_tagged (FreeLTS E) M (initial_tagged_module (FreeLTS E) tt) evs c /\
                  LPaths V σ0 (ViewLHL.underlay_events evs) /\ overlay_events evs = s.
  Proof.
    split.
    - intros (evs & c & Hex & Hov).
      pose proof (ViewLHL.exec_underlay_path M V _ _ _ Hex) as Hu.
      destruct (ViewLHL.exec_transport M V (FreeLTS E) _ _ _ Hex tt tt (free_path _)) as (d & Hd & _).
      exists evs, d. split; [exact Hd |]. split; [exists (tm_lts_state c); exact Hu | exact Hov].
    - intros (evs & c & Hex & (v' & Hp) & Hov).
      destruct (ViewLHL.exec_transport M (FreeLTS E) V _ _ _ Hex σ0 v' Hp) as (d & Hd & _).
      exists evs, d. split; [exact Hd | exact Hov].
  Qed.

  (** ** Module executions *)

  Lemma exec_app {E F : RelaxedSig.t} (VE : LTS E) (M : RelaxedModuleImpl E F) c1 evs1 c2 evs2 c3 :
    module_execution_tagged VE M c1 evs1 c2 -> module_execution_tagged VE M c2 evs2 c3 ->
    module_execution_tagged VE M c1 (evs1 ++ evs2) c3.
  Proof.
    induction 1 as [c | c1 c2 c2' ev evs Hst Hex IH]; intros H2; [exact H2 |].
    cbn. econstructor; [exact Hst | exact (IH H2)].
  Qed.

  Lemma overlay_events_underlay {E F : RelaxedSig.t} (us : list (ThreadEvent E)) :
    overlay_events (map (@UnderlayEvent E F) us) = [].
  Proof. induction us as [| e us IH]; [reflexivity | exact IH]. Qed.

  (** ** The module as an LTS *)

  (** One step of the composite: a block of underlay steps of the
      module, then one overlay event (an invocation or a return of [M]). *)
  Definition mod_step {E F : RelaxedSig.t} (VE : LTS E) (M : RelaxedModuleImpl E F) (ev : ThreadEvent F)
      (c c' : @TaggedModuleConfig E F VE) : Prop :=
    exists us c1, module_execution_tagged VE M c (map (@UnderlayEvent E F) us) c1 /\
                  module_step_tagged VE M (OverlayEvent ev) c1 c'.

  Definition ModLTS {E F : RelaxedSig.t} (VE : LTS E) (M : RelaxedModuleImpl E F) : LTS F :=
    {| State := @TaggedModuleConfig E F VE; Step := mod_step VE M; Error := fun _ _ => False |}.

  Section ModLTSPaths.
    Context {E F : RelaxedSig.t} (VE : LTS E) (M : RelaxedModuleImpl E F).

    Lemma modlts_path_exec c u c' :
      vf_path (ModLTS VE M) c u c' ->
      exists evs, module_execution_tagged VE M c evs c' /\ overlay_events evs = u.
    Proof.
      induction 1 as [c | c ev c1 u c' Hs Hp IH].
      - exists []. split; [constructor | reflexivity].
      - destruct Hs as (us & c0 & Hus & Hov). destruct IH as (evs & Hex & Hu).
        exists (map (@UnderlayEvent E F) us ++ OverlayEvent ev :: evs). split.
        + apply (exec_app VE M _ _ _ _ _ Hus). econstructor; [exact Hov | exact Hex].
        + rewrite overlay_events_app, overlay_events_underlay, <- Hu. reflexivity.
    Qed.

    Lemma exec_modlts_path c us c1 evs c' :
      module_execution_tagged VE M c (map (@UnderlayEvent E F) us) c1 ->
      module_execution_tagged VE M c1 evs c' ->
      exists c'', vf_path (ModLTS VE M) c (overlay_events evs) c''.
    Proof.
      intros Hus Hex. revert c us Hus.
      induction Hex as [c1 | c1 c2 c3 ev evs Hst Hex IH]; intros c us Hus.
      - exists c. constructor.
      - destruct ev as [e | e].
        + destruct (IH c (us ++ [e])) as (c'' & Hp).
          { rewrite map_app. exact (exec_snoc VE M _ _ _ _ _ Hus Hst). }
          exists c''. exact Hp.
        + destruct (IH c2 [] (tagged_module_execution_refl VE M c2)) as (c'' & Hp).
          exists c''. cbn. econstructor; [| exact Hp].
          exists us, c1. split; [exact Hus | exact Hst].
    Qed.

    (** The paths of the composite from the initial configuration are
        the overlay traces of the module. *)
    Theorem modlts_paths (σ0 : State VE) u :
      LPaths (ModLTS VE M) (initial_tagged_module VE σ0) u <-> MTraces VE M σ0 u.
    Proof.
      split.
      - intros (c' & Hp). destruct (modlts_path_exec _ _ _ Hp) as (evs & Hex & Hu).
        exists evs, c'. split; [exact Hex | exact Hu].
      - intros (evs & c & Hex & Hu). rewrite <- Hu.
        exact (exec_modlts_path _ [] _ _ _ (tagged_module_execution_refl VE M _) Hex).
    Qed.
  End ModLTSPaths.

  (** ** The trace set as an LTS *)

  Definition TrLTS {F : RelaxedSig.t} (T : list (ThreadEvent F) -> Prop) : LTS F :=
    {| State := list (ThreadEvent F); Step := fun e u u' => u' = u ++ [e] /\ T u';
       Error := fun _ _ => False |}.

  Lemma mtraces_nil {E F : RelaxedSig.t} (VE : LTS E) (M : RelaxedModuleImpl E F) (σ0 : State VE) :
    MTraces VE M σ0 [].
  Proof. exists [], (initial_tagged_module VE σ0). split; [constructor | reflexivity]. Qed.

  Section TrLTSPaths.
    Context {F : RelaxedSig.t} (T : list (ThreadEvent F) -> Prop).

    Lemma trlts_path_gen w u w' : vf_path (TrLTS T) w u w' -> w' = w ++ u /\ (T w -> T w').
    Proof.
      induction 1 as [w | w e w1 u w' Hs Hp IH].
      - rewrite app_nil_r. auto.
      - destruct Hs as (-> & HT). destruct IH as (-> & HT').
        rewrite <- app_assoc. split; [reflexivity | intros _; rewrite app_assoc; exact (HT' HT)].
    Qed.

    Theorem trlts_paths :
      T [] -> (forall s1 s2, T (s1 ++ s2) -> T s1) ->
      forall u, LPaths (TrLTS T) [] u <-> T u.
    Proof.
      intros Hnil Hpre u. split.
      - intros (w' & Hp). destruct (trlts_path_gen _ _ _ Hp) as (Hw & HT). rewrite Hw in HT. exact (HT Hnil).
      - induction u as [| e u IH] using rev_ind; intros Hu.
        + exists []. constructor.
        + destruct (IH (Hpre _ _ Hu)) as (w' & Hp).
          destruct (trlts_path_gen _ _ _ Hp) as (-> & _).
          exists (u ++ [e]). apply (vf_path_snoc (TrLTS T) _ _ _ _ _ Hp). split; [reflexivity | exact Hu].
    Qed.
  End TrLTSPaths.

  (** Running [M2] over the operational composite or over the trace set
      of the lower layer gives the same overlay traces. *)
  Corollary modlts_trlts {E F G : RelaxedSig.t} (VE : LTS E) (M1 : RelaxedModuleImpl E F) (σ0 : State VE)
      (M2 : RelaxedModuleImpl F G) s :
    MTraces (ModLTS VE M1) M2 (initial_tagged_module VE σ0) s <->
    MTraces (TrLTS (MTraces VE M1 σ0)) M2 [] s.
  Proof.
    apply mtraces_ext. intros u.
    rewrite (modlts_paths VE M1 σ0 u).
    rewrite (trlts_paths (MTraces VE M1 σ0) (mtraces_nil VE M1 σ0) (mtraces_prefix VE M1 σ0) u).
    reflexivity.
  Qed.

  (** ** Sanity check: the [⊇] half of [hlift] from [mtraces_mono] *)

  Lemma hl_path_base {E : RelaxedSig.t} (VE : LTS E) σ u σ' :
    vf_path (RelaxedHoareCompLinSpec.HL VE) σ u σ' -> vf_path VE (fst σ) u (fst σ').
  Proof.
    induction 1 as [σ | σ ev σ1 u σ' Hs Hp IH]; [constructor |].
    econstructor; [exact (RelaxedHoareCompLinSpec.hl_step_base VE ev σ σ1 Hs) | exact IH].
  Qed.

  Corollary hlift_drop_via_mono {E G : RelaxedSig.t} (VE : LTS E) (M : RelaxedModuleImpl E G)
      (σ0 : State VE) s :
    MTraces (RelaxedHoareCompLinSpec.HL VE) M (σ0, []) s -> MTraces VE M σ0 s.
  Proof.
    apply mtraces_mono. intros u (σ' & Hp). exists (fst σ'). exact (hl_path_base VE _ _ _ Hp).
  Qed.
End RelaxedHoareLayer.
