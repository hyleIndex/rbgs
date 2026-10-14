(** * Window composition over an ordering table, for a joint overlay specification

    [WindowTable.window_composition] concludes with the product of the
    component specifications: the overlay witness [ow] satisfies [nuF c]
    on its projection to every component [c] ([WindowTable.Conclusion]).
    This file replaces the specification part by a single predicate
    [nuJ] on the whole overlay witness (a joint specification) and keeps
    the ordering part unchanged:

    - [Hyps0J to S nuJ] has the fields of [WindowTable.Hyps0], except that
      the per-component obligation [h_S1] is replaced by one joint
      obligation [h_S1J]: [nuJ] holds of the overlay labels of the
      operations of all components, sorted by linearization point;
    - [ConclusionJ to S nuJ]: a permutation [ow] of the operations that
      respects the overlay order (the clause of [WindowTable.Conclusion])
      with [nuJ (map ovl ow)];
    - [window_composition_J] (with [WindowTable.Inherit]) and
      [window_composition_sequential_J] (a client that never overlaps its
      own operations).

    Outside Section [Product], the field [nuF] of the setting [S] is not
    read.

    Reuse.  The proofs of [WindowTable] are applied, not copied:
    - the ordering argument is [WindowTable.lp_before], applied to
      [triv S] ([S] with the trivial component specification), whose
      [Hyps0] follows from [Hyps0J] ([hyps0_triv]); see [lp_before_J];
    - the sorting argument is [WindowTable.conclusion_of_lp_before],
      applied to [joint S nuJ]: [S] read as a single component ([unit]),
      whose component-internal semi-independence is the whole
      table-induced [IF] / [IE] of [S] and whose component specification
      is [nuJ].  A joint specification is a product with one factor; see
      [conclusionJ_of_lp_before].
    The only proof lines taken from [WindowTable] are the six-line [lp]
    ordering step of [window_composition_sequential_J], which is inline
    (not a lemma) in [WindowTable.window_composition_sequential].  The
    fields of [Hyps0J] and the order clause of [ConclusionJ] are those of
    [WindowTable.Hyps0] and [WindowTable.Conclusion].

    [Hyps0J] is a record of its own, not [Hyps0 to (triv S)] plus
    [h_S1J], so that its statement does not mention the unused [nuF] of
    [S]; the two forms are equivalent ([hyps0_triv], [hyps0J_of_triv]).

    Modularity.  The ordering argument stays component-wise, as in
    [WindowTable]: each component orders its own pairs ([h_S1_ord]), and
    cross-component pairs are ordered through the windows, dominance,
    [h_ord] and [h_rt] (positions in the underlay witness).  The
    specification obligation does not: [h_S1J]
    is one obligation about the lp-sorted list of the operations of all
    components, not one obligation per component.  So
    [window_composition_J] is a composition theorem for the ordering, not
    for the specifications.

    Section [Product] (conservativity): if the component of an operation
    is read off its overlay label ([comp_ovl]; true in the module setting
    of [WindowLinkTable], where it is [compF] of the overlay operation),
    the product [nu_prod] of the component specifications is a joint
    specification; [WindowTable.Hyps0] gives [Hyps0J] for it
    ([hyps0J_prod]), [ConclusionJ] for it gives [WindowTable.Conclusion]
    ([conclusion_of_J_prod]), and [window_composition_of_J] rederives
    [WindowTable.window_composition] from [window_composition_J] (under
    [comp_ovl]).  Section [ProductAny] removes [comp_ovl]: [lift S] is [S]
    with the operations themselves as overlay labels (so [nuJ] ranges over
    lists of operations, and [comp_ovl] holds by [eq_refl]), and
    [window_composition_of_J_any] rederives [WindowTable.window_composition]
    from [window_composition_J] for every setting, with no side condition
    ([window_composition_of_J_any_statement] checks the statement in the
    kernel).

    Relation to the paper: Section [Product] has the overlay-specification
    shape of the paper's Horizontal Composition (overview.tex
    [prop:locality], relaxedlin.tex [prop:tensor-impl]): the product
    [ν_F1 ⊗ ν_F2] (trace.tex [def:spec-tensor], by projection).  It is
    not that proposition: this file is the abstract ordering-and-sorting
    argument for one setting, with no implementations, executions or
    underlay semantics.  The module-level counterpart, and the gaps of the
    concern-matrix row "Horizontal composition / compatibility" that still
    apply there, are in [WindowLinkTableJ].  The joint version is new
    relative to the paper. *)

From Stdlib Require Import List Sorting.Sorted Sorting.Permutation.
From Stdlib Require Import Arith.PeanoNat micromega.Lia.
Require Import examples.Relaxed.WindowComposition.
Require Import examples.Relaxed.WindowTable.

Import ListNotations.

Module WindowTableJ.
  Module WC := WindowComposition.WindowComposition.
  Module WT := WindowTable.WindowTable.

  (** ** Helpers *)

  Lemma filter_all_true {A} (f : A -> bool) (l : list A) :
    (forall x, In x l -> f x = true) -> filter f l = l.
  Proof.
    induction l as [|x l IH]; intros Hf; cbn; [reflexivity|].
    rewrite (Hf x (or_introl eq_refl)). f_equal.
    apply IH. intros y Hy. apply Hf. right. exact Hy.
  Qed.

  Lemma filter_all_false {A} (f : A -> bool) (l : list A) :
    (forall x, In x l -> f x = false) -> filter f l = [].
  Proof.
    induction l as [|x l IH]; intros Hf; cbn; [reflexivity|].
    rewrite (Hf x (or_introl eq_refl)).
    apply IH. intros y Hy. apply Hf. right. exact Hy.
  Qed.

  (** Decidable equality on [unit]; [unit_dec tt tt] computes to [left _]. *)
  Definition unit_dec (c c' : unit) : {c = c'} + {c <> c'}.
  Proof. destruct c, c'. left. reflexivity. Defined.

  (** ** The joint theorem *)

  Section Window.
    Context {Cat : Type} (to : Cat -> Cat -> Prop) (S : WT.Setting Cat).

    (** [S] with the trivial component specification. *)
    Definition triv : WT.Setting Cat := {|
      WT.Op := WT.Op S; WT.Call := WT.Call S; WT.OvOp := WT.OvOp S;
      WT.Comp := WT.Comp S; WT.comp_dec := WT.comp_dec S; WT.comp := WT.comp S;
      WT.ovl := WT.ovl S; WT.cF := WT.cF S; WT.IFc := WT.IFc S;
      WT.ucomp := WT.ucomp S; WT.cE := WT.cE S; WT.IEc := WT.IEc S;
      WT.lo := WT.lo S; WT.hi := WT.hi S; WT.lpc := WT.lpc S; WT.pos := WT.pos S;
      WT.ops := WT.ops S; WT.po := WT.po S; WT.rt := WT.rt S;
      WT.nuF := fun _ _ => True |}.

    Context (nuJ : list (WT.OvOp S) -> Prop).

    (** [WindowTable.Hyps0] with the joint obligation [h_S1J] in place of
        the per-component [h_S1]. *)
    Record Hyps0J : Prop := {
      h_nodup : NoDup (WT.ops S);
      h_lp_inj : forall q q', In q (WT.ops S) -> In q' (WT.ops S) ->
                              WT.lp S q = WT.lp S q' -> q = q';
      h_lo_comp : forall q, In q (WT.ops S) -> WT.ucomp S (WT.lo S q) = WT.comp S q;
      h_hi_comp : forall q, In q (WT.ops S) -> WT.ucomp S (WT.hi S q) = WT.comp S q;
      h_window : forall q, In q (WT.ops S) ->
                           WT.pos S (WT.lo S q) <= WT.lp S q <= WT.pos S (WT.hi S q);
      h_ord : forall q q', In q (WT.ops S) -> In q' (WT.ops S) -> WT.po S q q' ->
                           ~ WT.IE to S (WT.hi S q) (WT.lo S q') ->
                           WT.pos S (WT.hi S q) < WT.pos S (WT.lo S q');
      h_rt : forall q q', In q (WT.ops S) -> In q' (WT.ops S) -> WT.rt S q q' ->
                          WT.pos S (WT.hi S q) < WT.pos S (WT.lo S q');
      h_S1J : nuJ (map (WT.ovl S) (WC.isort (WT.lp S) (WT.ops S)));
      h_S1_ord : forall q q', In q (WT.ops S) -> In q' (WT.ops S) ->
                              WT.comp S q = WT.comp S q' ->
                              WT.po S q q' -> ~ WT.IFc S q q' -> WT.lp S q < WT.lp S q';
    }.

    Definition ConclusionJ : Prop :=
      exists ow : list (WT.Op S),
        Permutation ow (WT.ops S) /\
        (forall q q', In q (WT.ops S) -> In q' (WT.ops S) ->
           (WT.po S q q' /\ ~ WT.IF to S q q') \/ WT.rt S q q' ->
           exists l1 l2, ow = l1 ++ q :: l2 /\ In q' l2) /\
        nuJ (map (WT.ovl S) ow).

    (** [S] read as one component: the component-internal
        semi-independence is the whole table-induced [IF] / [IE] of [S],
        and the component specification is [nuJ]. *)
    Definition joint : WT.Setting Cat := {|
      WT.Op := WT.Op S; WT.Call := WT.Call S; WT.OvOp := WT.OvOp S;
      WT.Comp := unit; WT.comp_dec := unit_dec; WT.comp := fun _ => tt;
      WT.ovl := WT.ovl S; WT.cF := WT.cF S; WT.IFc := WT.IF to S;
      WT.ucomp := fun _ => tt; WT.cE := WT.cE S; WT.IEc := WT.IE to S;
      WT.lo := WT.lo S; WT.hi := WT.hi S; WT.lpc := WT.lpc S; WT.pos := WT.pos S;
      WT.ops := WT.ops S; WT.po := WT.po S; WT.rt := WT.rt S;
      WT.nuF := fun _ l => nuJ l |}.

    (** [Hyps0J] is [Hyps0] of the trivial-specification setting plus
        [h_S1J] (both directions). *)
    Lemma hyps0_triv (H : Hyps0J) : WT.Hyps0 to triv.
    Proof.
      constructor.
      - exact (h_nodup H).
      - exact (h_lp_inj H).
      - exact (h_lo_comp H).
      - exact (h_hi_comp H).
      - exact (h_window H).
      - exact (h_ord H).
      - exact (h_rt H).
      - intros c. exact I.
      - exact (h_S1_ord H).
    Qed.

    Lemma hyps0J_of_triv :
      WT.Hyps0 to triv -> nuJ (map (WT.ovl S) (WC.isort (WT.lp S) (WT.ops S))) -> Hyps0J.
    Proof.
      intros H HJ. constructor.
      - exact (WT.h_nodup _ _ H).
      - exact (WT.h_lp_inj _ _ H).
      - exact (WT.h_lo_comp _ _ H).
      - exact (WT.h_hi_comp _ _ H).
      - exact (WT.h_window _ _ H).
      - exact (WT.h_ord _ _ H).
      - exact (WT.h_rt _ _ H).
      - exact HJ.
      - exact (WT.h_S1_ord _ _ H).
    Qed.

    (** From [Hyps0] of [S] itself (its [h_S1] is dropped). *)
    Lemma hyps0J_intro :
      WT.Hyps0 to S -> nuJ (map (WT.ovl S) (WC.isort (WT.lp S) (WT.ops S))) -> Hyps0J.
    Proof.
      intros H HJ. constructor.
      - exact (WT.h_nodup _ _ H).
      - exact (WT.h_lp_inj _ _ H).
      - exact (WT.h_lo_comp _ _ H).
      - exact (WT.h_hi_comp _ _ H).
      - exact (WT.h_window _ _ H).
      - exact (WT.h_ord _ _ H).
      - exact (WT.h_rt _ _ H).
      - exact HJ.
      - exact (WT.h_S1_ord _ _ H).
    Qed.

    (** Sorting by [lp] gives [ConclusionJ] as soon as [lp] respects the
        overlay order: [WindowTable.conclusion_of_lp_before] for [joint]. *)
    Lemma conclusionJ_of_lp_before (H : Hyps0J) :
      (forall q q', In q (WT.ops S) -> In q' (WT.ops S) ->
                    (WT.po S q q' /\ ~ WT.IF to S q q') \/ WT.rt S q q' ->
                    WT.lp S q < WT.lp S q') ->
      ConclusionJ.
    Proof.
      intros Hlpb.
      assert (Hj : WT.Hyps0 to joint).
      { constructor.
        - exact (h_nodup H).
        - exact (h_lp_inj H).
        - intros q _. reflexivity.
        - intros q _. reflexivity.
        - exact (h_window H).
        - exact (h_ord H).
        - exact (h_rt H).
        - intros [].
          change (nuJ (map (WT.ovl S)
                    (WC.isort (WT.lp S) (filter (WT.in_comp joint tt) (WT.ops S))))).
          rewrite filter_all_true by (intros q _; reflexivity).
          exact (h_S1J H).
        - intros q q' Hq Hq' _ Hpo HnIF.
          exact (Hlpb q q' Hq Hq' (or_introl (conj Hpo HnIF))). }
      destruct (WT.conclusion_of_lp_before to joint Hj Hlpb) as (ow & Hp & Ho & Hs).
      exists ow. split; [exact Hp|]. split; [exact Ho|].
      specialize (Hs tt).
      change (nuJ (map (WT.ovl S) (filter (WT.in_comp joint tt) ow))) in Hs.
      rewrite filter_all_true in Hs by (intros q _; reflexivity).
      exact Hs.
    Qed.

    (** The ordering argument of [WindowTable.window_composition]:
        [WindowTable.lp_before] for [triv]. *)
    Lemma lp_before_J (H : Hyps0J) (Hinh : WT.Inherit to S) q q' :
      In q (WT.ops S) -> In q' (WT.ops S) ->
      (WT.po S q q' /\ ~ WT.IF to S q q') \/ WT.rt S q q' -> WT.lp S q < WT.lp S q'.
    Proof. exact (WT.lp_before to triv (hyps0_triv H) Hinh q q'). Qed.

    Theorem window_composition_J (H : Hyps0J) (Hinh : WT.Inherit to S) : ConclusionJ.
    Proof. apply (conclusionJ_of_lp_before H). exact (lp_before_J H Hinh). Qed.

    (** A client that never overlaps its own operations needs no
        inheritance (as [WindowTable.window_composition_sequential]). *)
    Theorem window_composition_sequential_J (H : Hyps0J) :
      (forall q q', In q (WT.ops S) -> In q' (WT.ops S) -> WT.po S q q' -> WT.rt S q q') ->
      ConclusionJ.
    Proof.
      intros Hseq. apply (conclusionJ_of_lp_before H).
      intros q q' Hq Hq' Hord.
      pose proof (h_window H q Hq) as [_ W1].
      pose proof (h_window H q' Hq') as [W2 _].
      assert (Hrt : WT.rt S q q')
        by (destruct Hord as [[Hpo _]|Hrt]; [apply Hseq|]; assumption).
      assert (WT.pos S (WT.hi S q) < WT.pos S (WT.lo S q')) by (apply (h_rt H); assumption).
      lia.
    Qed.
  End Window.

  Arguments Hyps0J {Cat} to S nuJ.
  Arguments ConclusionJ {Cat} to S nuJ.

  (** ** Conservativity: the product is a joint specification *)

  Section Product.
    Context {Cat : Type} (to : Cat -> Cat -> Prop) (S : WT.Setting Cat).

    (** The component of an operation is read off its overlay label. *)
    Context (compOv : WT.OvOp S -> WT.Comp S).
    Hypothesis comp_ovl : forall q, In q (WT.ops S) -> WT.comp S q = compOv (WT.ovl S q).

    Definition in_compOv (c : WT.Comp S) (o : WT.OvOp S) : bool :=
      if WT.comp_dec S (compOv o) c then true else false.

    (** The product of the component specifications [WT.nuF S], by
        projection on overlay labels. *)
    Definition nu_prod (l : list (WT.OvOp S)) : Prop :=
      forall c, WT.nuF S c (filter (in_compOv c) l).

    Lemma filter_map_ovl c l : (forall q, In q l -> In q (WT.ops S)) ->
      filter (in_compOv c) (map (WT.ovl S) l) = map (WT.ovl S) (filter (WT.in_comp S c) l).
    Proof.
      intros Hl. rewrite filter_map_swap. f_equal. apply filter_ext_in.
      intros q Hq. unfold in_compOv, WT.in_comp. rewrite (comp_ovl q (Hl q Hq)). reflexivity.
    Qed.

    Lemma hyps0J_prod : WT.Hyps0 to S -> Hyps0J to S nu_prod.
    Proof.
      intros H. apply (hyps0J_intro to S nu_prod H).
      intros c. rewrite filter_map_ovl.
      - rewrite WC.filter_isort by (exact (WT.h_lp_inj _ _ H) || exact (WT.h_nodup _ _ H)).
        exact (WT.h_S1 _ _ H c).
      - intros q Hq. exact (Permutation_in _ (WC.isort_perm _ _) Hq).
    Qed.

    Lemma conclusion_of_J_prod : ConclusionJ to S nu_prod -> WT.Conclusion to S.
    Proof.
      intros (ow & Hp & Ho & Hs). exists ow. split; [exact Hp|]. split; [exact Ho|].
      intros c. rewrite <- filter_map_ovl.
      - exact (Hs c).
      - intros q Hq. exact (Permutation_in _ Hp Hq).
    Qed.

    (** [WindowTable.window_composition], from the joint theorem. *)
    Theorem window_composition_of_J : WT.Hyps0 to S -> WT.Inherit to S -> WT.Conclusion to S.
    Proof.
      intros H Hinh. apply conclusion_of_J_prod.
      exact (window_composition_J to S nu_prod (hyps0J_prod H) Hinh).
    Qed.
  End Product.

  (** ** Unconditional conservativity: overlay labels := operations *)

  Section ProductAny.
    Context {Cat : Type} (to : Cat -> Cat -> Prop) (S : WT.Setting Cat).

    (** [S] with the operations as overlay labels; its component
        specification reads the labels of [S]. *)
    Definition lift : WT.Setting Cat := {|
      WT.Op := WT.Op S; WT.Call := WT.Call S; WT.OvOp := WT.Op S;
      WT.Comp := WT.Comp S; WT.comp_dec := WT.comp_dec S; WT.comp := WT.comp S;
      WT.ovl := fun q => q; WT.cF := WT.cF S; WT.IFc := WT.IFc S;
      WT.ucomp := WT.ucomp S; WT.cE := WT.cE S; WT.IEc := WT.IEc S;
      WT.lo := WT.lo S; WT.hi := WT.hi S; WT.lpc := WT.lpc S; WT.pos := WT.pos S;
      WT.ops := WT.ops S; WT.po := WT.po S; WT.rt := WT.rt S;
      WT.nuF := fun c l => WT.nuF S c (map (WT.ovl S) l) |}.

    Lemma hyps0_lift : WT.Hyps0 to S -> WT.Hyps0 to lift.
    Proof.
      intros H. constructor.
      - exact (WT.h_nodup _ _ H).
      - exact (WT.h_lp_inj _ _ H).
      - exact (WT.h_lo_comp _ _ H).
      - exact (WT.h_hi_comp _ _ H).
      - exact (WT.h_window _ _ H).
      - exact (WT.h_ord _ _ H).
      - exact (WT.h_rt _ _ H).
      - intros c.
        change (WT.nuF S c (map (WT.ovl S) (map (fun q => q)
                  (WC.isort (WT.lp S) (filter (WT.in_comp S c) (WT.ops S)))))).
        rewrite map_id. exact (WT.h_S1 _ _ H c).
      - exact (WT.h_S1_ord _ _ H).
    Qed.

    Lemma conclusion_unlift : WT.Conclusion to lift -> WT.Conclusion to S.
    Proof.
      intros (ow & Hp & Ho & Hs). exists ow. split; [exact Hp|]. split; [exact Ho|].
      intros c. specialize (Hs c).
      change (WT.nuF S c (map (WT.ovl S) (map (fun q => q) (filter (WT.in_comp S c) ow)))) in Hs.
      rewrite map_id in Hs. exact Hs.
    Qed.

    (** [WindowTable.window_composition], from the joint theorem, for
        every setting. *)
    Theorem window_composition_of_J_any :
      WT.Hyps0 to S -> WT.Inherit to S -> WT.Conclusion to S.
    Proof.
      intros H Hinh. apply conclusion_unlift.
      exact (window_composition_of_J to lift (WT.comp S) (fun q _ => eq_refl)
               (hyps0_lift H) Hinh).
    Qed.
  End ProductAny.

  (** [window_composition_of_J_any] has literally the statement of
      [WindowTable.window_composition]. *)
  Example window_composition_of_J_any_statement :
    ltac:(let T := type of @WT.window_composition in exact T).
  Proof. exact @window_composition_of_J_any. Qed.
End WindowTableJ.
