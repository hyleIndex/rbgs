(** * Prelude: relations, acyclicity and linear extensions of finite relations.

    Generic material used by the buffered-memory development
    ([memory/Cell.v], [memory/Declarative.v], [memory/Equivalence.v]).
    Nothing here is specific to memory models.

    Conventions (Appendix L of the paper, "Conventions"): a relation [R]
    is acyclic if its transitive closure is irreflexive.

    This file uses classical logic ([Coq.Logic.Classical]).  All
    concrete relations of the development are decidable, so the
    axiom could be traded for decidability hypotheses; we do not
    bother, in line with the usual practice for memory-model
    formalizations. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Sorting.Permutation.
Require Import Stdlib.Relations.Relation_Definitions.
Require Import Stdlib.Relations.Relation_Operators.
Require Import Stdlib.Relations.Operators_Properties.
Require Import Stdlib.Logic.Classical.

Import ListNotations.

Set Implicit Arguments.

(** ** Relation algebra *)

Section Relations.
  Variable A : Type.

  Definition rel_union (R S : relation A) : relation A :=
    fun x y => R x y \/ S x y.
  Definition rel_inter (R S : relation A) : relation A :=
    fun x y => R x y /\ S x y.
  Definition rel_minus (R S : relation A) : relation A :=
    fun x y => R x y /\ ~ S x y.
  Definition rel_seq (R S : relation A) : relation A :=
    fun x z => exists y, R x y /\ S y z.
  Definition rel_dom (P : A -> Prop) (R : relation A) : relation A :=
    fun x y => P x /\ R x y.
  Definition rel_cod (R : relation A) (P : A -> Prop) : relation A :=
    fun x y => R x y /\ P y.
  Definition rel_incl (R S : relation A) : Prop :=
    forall x y, R x y -> S x y.
  Definition tc (R : relation A) : relation A := clos_trans A R.
  Definition acyclic (R : relation A) : Prop := forall x, ~ tc R x x.
  Definition irreflexive (R : relation A) : Prop := forall x, ~ R x x.

  Lemma rel_incl_refl R : rel_incl R R.
  Proof. firstorder. Qed.

  Lemma rel_incl_trans R S T : rel_incl R S -> rel_incl S T -> rel_incl R T.
  Proof. firstorder. Qed.

  Lemma rel_union_incl_l R S : rel_incl R (rel_union R S).
  Proof. firstorder. Qed.

  Lemma rel_union_incl_r R S : rel_incl S (rel_union R S).
  Proof. firstorder. Qed.

  Lemma rel_union_lub R S T :
    rel_incl R T -> rel_incl S T -> rel_incl (rel_union R S) T.
  Proof. firstorder. Qed.

  Lemma tc_incl R S : rel_incl R S -> rel_incl (tc R) (tc S).
  Proof.
    intros H x y Hxy. induction Hxy.
    - apply t_step. auto.
    - eapply t_trans; eauto.
  Qed.

  Lemma tc_step R x y : R x y -> tc R x y.
  Proof. apply t_step. Qed.

  Lemma tc_trans R x y z : tc R x y -> tc R y z -> tc R x z.
  Proof. apply t_trans. Qed.

  Lemma tc_idem R : rel_incl (tc (tc R)) (tc R).
  Proof.
    intros x y H. induction H.
    - assumption.
    - eapply t_trans; eauto.
  Qed.

  Lemma tc_union_tc_l R S : rel_incl (tc (rel_union (tc R) S)) (tc (rel_union R S)).
  Proof.
    intros x y H. induction H.
    - destruct H as [H | H].
      + eapply tc_incl; [| exact H]. apply rel_union_incl_l.
      + apply t_step. right. assumption.
    - eapply t_trans; eauto.
  Qed.

  Lemma acyclic_incl R S : rel_incl R S -> acyclic S -> acyclic R.
  Proof.
    intros H Hac x Hx. apply (Hac x). eapply tc_incl; eauto.
  Qed.

  Lemma acyclic_irreflexive R : acyclic R -> irreflexive R.
  Proof.
    intros H x Hx. apply (H x). apply t_step. assumption.
  Qed.

  Lemma acyclic_tc R : acyclic R -> acyclic (tc R).
  Proof.
    intros H x Hx. apply (H x). apply tc_idem. assumption.
  Qed.

  (** An acyclic relation is contained in a strict order given by a
      "potential" into a well-ordered set: if some [f : A -> B] strictly
      increases along [R] for an irreflexive transitive [lt], then [R] is
      acyclic. *)
  Lemma acyclic_by_potential (B : Type) (lt : relation B) (f : A -> B) (R : relation A) :
    (forall x y, R x y -> lt (f x) (f y)) ->
    (forall b1 b2 b3, lt b1 b2 -> lt b2 b3 -> lt b1 b3) ->
    (forall b, ~ lt b b) ->
    acyclic R.
  Proof.
    intros Hmono Htrans Hirr x Hx.
    assert (Hlt : forall x y, tc R x y -> lt (f x) (f y)).
    { intros a b H. induction H; eauto. }
    apply (Hirr (f x)). auto.
  Qed.

  (** The same with a potential given as a total relation rather than a
      function (the potentials of the memory proofs are specified, not
      computed). *)
  Lemma acyclic_by_rel_potential (B : Type) (lt : relation B) (val : A -> B -> Prop) (R : relation A) :
    (forall x, exists b, val x b) ->
    (forall x y bx by', R x y -> val x bx -> val y by' -> lt bx by') ->
    (forall b1 b2 b3, lt b1 b2 -> lt b2 b3 -> lt b1 b3) ->
    (forall b, ~ lt b b) ->
    acyclic R.
  Proof.
    intros Htot Hmono Htrans Hirr x Hx.
    assert (Hlt : forall x y, tc R x y -> forall bx by', val x bx -> val y by' -> lt bx by').
    { intros a b H. induction H as [a b Hab | a b c Hab IH1 Hbc IH2]; intros bx by' Hx' Hy'.
      - eapply Hmono; eauto.
      - destruct (Htot b) as [bb Hb]. eapply Htrans; eauto. }
    destruct (Htot x) as [bx Hbx].
    apply (Hirr bx). eapply Hlt; eauto.
  Qed.

  (** Every edge of a relation increases a natural-number potential:
      then the relation is acyclic. *)
  Lemma acyclic_by_nat_potential (f : A -> nat) (R : relation A) :
    (forall x y, R x y -> f x < f y) -> acyclic R.
  Proof.
    intros H. eapply acyclic_by_potential with (lt := lt) (f := f); auto; lia.
  Qed.

End Relations.

Arguments tc {A} R.
Arguments acyclic {A} R.
Arguments irreflexive {A} R.
Arguments rel_incl {A} R S.

Declare Scope rel_scope.
Delimit Scope rel_scope with rel.
Bind Scope rel_scope with relation.

Infix "∪" := rel_union (at level 50, left associativity) : rel_scope.
Infix "∩" := rel_inter (at level 40, left associativity) : rel_scope.
Infix "\" := rel_minus (at level 40, left associativity) : rel_scope.
Infix ";;" := rel_seq (at level 45, right associativity) : rel_scope.
Notation "⦗ P ⦘ ;; R" := (rel_dom P R) (at level 45, right associativity) : rel_scope.
Notation "R ;; ⦗ P ⦘" := (rel_cod R P) (at level 45, right associativity) : rel_scope.
Infix "⊆" := rel_incl (at level 70) : rel_scope.
Notation "R ⁺" := (tc R) (at level 30, format "R ⁺") : rel_scope.

Open Scope rel_scope.

(** Lexicographic order on triples of naturals, the potential used in
    the realization proof. *)
Definition lex3 (p q : nat * nat * nat) : Prop :=
  let '(a1, b1, c1) := p in
  let '(a2, b2, c2) := q in
  a1 < a2 \/ (a1 = a2 /\ (b1 < b2 \/ (b1 = b2 /\ c1 < c2))).

Lemma lex3_trans p q r : lex3 p q -> lex3 q r -> lex3 p r.
Proof.
  destruct p as [[a1 b1] c1], q as [[a2 b2] c2], r as [[a3 b3] c3].
  unfold lex3. lia.
Qed.

Lemma lex3_irrefl p : ~ lex3 p p.
Proof.
  destruct p as [[a b] c]. unfold lex3. lia.
Qed.

Lemma acyclic_by_lex3 (A : Type) (f : A -> nat * nat * nat) (R : relation A) :
  (forall x y, R x y -> lex3 (f x) (f y)) -> acyclic R.
Proof.
  intros H. eapply acyclic_by_potential with (lt := lex3) (f := f).
  - assumption.
  - apply lex3_trans.
  - apply lex3_irrefl.
Qed.

Lemma acyclic_by_rel_lex3 (A : Type) (val : A -> nat * nat * nat -> Prop) (R : relation A) :
  (forall x, exists p, val x p) ->
  (forall x y px py, R x y -> val x px -> val y py -> lex3 px py) ->
  acyclic R.
Proof.
  intros Htot Hmono. eapply acyclic_by_rel_potential with (lt := lex3) (val := val); auto.
  - apply lex3_trans.
  - apply lex3_irrefl.
Qed.

Lemma acyclic_by_rel_nat (A : Type) (val : A -> nat -> Prop) (R : relation A) :
  (forall x, exists n, val x n) ->
  (forall x y nx ny, R x y -> val x nx -> val y ny -> nx < ny) ->
  acyclic R.
Proof.
  intros Htot Hmono. eapply acyclic_by_rel_potential with (lt := lt) (val := val); auto; lia.
Qed.

(** ** Positions in lists *)

Section Positions.
  Variable A : Type.

  (** [x] occurs strictly before [y] in [l]. *)
  Definition before (l : list A) (x y : A) : Prop :=
    exists i j, i < j /\ nth_error l i = Some x /\ nth_error l j = Some y.

  Lemma before_In_l l x y : before l x y -> In x l.
  Proof.
    intros (i & j & _ & Hi & _). eapply nth_error_In; eauto.
  Qed.

  Lemma before_In_r l x y : before l x y -> In y l.
  Proof.
    intros (i & j & _ & _ & Hj). eapply nth_error_In; eauto.
  Qed.

  Lemma before_irrefl l x : NoDup l -> ~ before l x x.
  Proof.
    intros Hnd (i & j & Hij & Hi & Hj).
    rewrite NoDup_nth_error in Hnd.
    assert (i = j).
    { apply Hnd.
      - apply nth_error_Some. rewrite Hi. discriminate.
      - congruence. }
    lia.
  Qed.

  Lemma before_trans l x y z : NoDup l -> before l x y -> before l y z -> before l x z.
  Proof.
    intros Hnd (i & j & Hij & Hi & Hj) (j' & k & Hjk & Hj' & Hk).
    rewrite NoDup_nth_error in Hnd.
    assert (j = j').
    { apply Hnd.
      - apply nth_error_Some. rewrite Hj. discriminate.
      - congruence. }
    subst j'. exists i, k. split; [lia | auto].
  Qed.

  Lemma before_total l x y :
    NoDup l -> In x l -> In y l -> x <> y -> before l x y \/ before l y x.
  Proof.
    intros Hnd Hx Hy Hxy.
    apply In_nth_error in Hx. destruct Hx as [i Hi].
    apply In_nth_error in Hy. destruct Hy as [j Hj].
    destruct (lt_eq_lt_dec i j) as [[Hlt | Heq] | Hgt].
    - left. exists i, j. auto.
    - subst. congruence.
    - right. exists j, i. auto.
  Qed.

  (** Variants for elements that occur at a unique position. *)
  Definition unique_occ (l : list A) (x : A) : Prop :=
    forall i j, nth_error l i = Some x -> nth_error l j = Some x -> i = j.

  Lemma NoDup_unique_occ l x : NoDup l -> unique_occ l x.
  Proof.
    intros Hnd i j Hi Hj. rewrite NoDup_nth_error in Hnd. apply Hnd.
    - apply nth_error_Some. congruence.
    - congruence.
  Qed.

  Lemma before_irrefl_u l x : unique_occ l x -> ~ before l x x.
  Proof.
    intros Hu (i & j & Hij & Hi & Hj). specialize (Hu i j Hi Hj). lia.
  Qed.

  Lemma before_trans_u l x y z : unique_occ l y -> before l x y -> before l y z -> before l x z.
  Proof.
    intros Hu (i & j & Hij & Hi & Hj) (j' & k & Hjk & Hj' & Hk).
    specialize (Hu j j' Hj Hj'). subst j'. exists i, k. split; [lia | auto].
  Qed.

  Lemma before_asym_u l x y : unique_occ l x -> unique_occ l y -> before l x y -> before l y x -> False.
  Proof.
    intros Hx Hy H1 H2. apply (before_irrefl_u Hx). eapply before_trans_u; eauto.
  Qed.

  Lemma before_total_u l x y :
    unique_occ l x -> unique_occ l y -> In x l -> In y l -> x <> y -> before l x y \/ before l y x.
  Proof.
    intros _ _ Hx Hy Hxy.
    apply In_nth_error in Hx. destruct Hx as [i Hi].
    apply In_nth_error in Hy. destruct Hy as [j Hj].
    destruct (lt_eq_lt_dec i j) as [[Hlt | Heq] | Hgt].
    - left. exists i, j. auto.
    - subst. congruence.
    - right. exists j, i. auto.
  Qed.

  Lemma before_cons l x y a : before l x y -> before (a :: l) x y.
  Proof.
    intros (i & j & Hij & Hi & Hj). exists (S i), (S j). cbn. auto with arith.
  Qed.

  Lemma before_cons_head l a y : In y l -> before (a :: l) a y.
  Proof.
    intros Hy. apply In_nth_error in Hy. destruct Hy as [j Hj].
    exists 0, (S j). cbn. auto with arith.
  Qed.

  Lemma before_cons_inv l a x y :
    NoDup (a :: l) -> before (a :: l) x y ->
    (x = a /\ In y l) \/ before l x y.
  Proof.
    intros Hnd (i & j & Hij & Hi & Hj).
    destruct i as [| i]; destruct j as [| j]; cbn in *; try lia.
    - left. inversion Hi; subst. split; auto. eapply nth_error_In; eauto.
    - right. exists i, j. auto with arith.
  Qed.

  Lemma before_app_l l1 l2 x y : before l1 x y -> before (l1 ++ l2) x y.
  Proof.
    intros (i & j & Hij & Hi & Hj). exists i, j.
    split; [auto |]. split; rewrite nth_error_app1; auto;
      apply nth_error_Some; congruence.
  Qed.

  Lemma before_app_lr l1 l2 x y : In x l1 -> In y l2 -> before (l1 ++ l2) x y.
  Proof.
    intros Hx Hy.
    apply In_nth_error in Hx. destruct Hx as [i Hi].
    apply In_nth_error in Hy. destruct Hy as [j Hj].
    exists i, (length l1 + j). split; [| split].
    - assert (i < length l1) by (apply nth_error_Some; congruence). lia.
    - rewrite nth_error_app1; auto. apply nth_error_Some; congruence.
    - rewrite nth_error_app2; [| lia]. replace (length l1 + j - length l1) with j by lia. auto.
  Qed.

  Lemma before_app_r l1 l2 x y : before l2 x y -> before (l1 ++ l2) x y.
  Proof.
    intros (i & j & Hij & Hi & Hj).
    exists (length l1 + i), (length l1 + j). split; [lia |].
    split; rewrite nth_error_app2; try lia;
      [replace (length l1 + i - length l1) with i by lia
      | replace (length l1 + j - length l1) with j by lia]; auto.
  Qed.

  Lemma before_app_inv l1 l2 x y :
    before (l1 ++ l2) x y ->
    before l1 x y \/ before l2 x y \/ (In x l1 /\ In y l2).
  Proof.
    intros (i & j & Hij & Hi & Hj).
    destruct (lt_dec i (length l1)) as [Hi1 | Hi1];
      destruct (lt_dec j (length l1)) as [Hj1 | Hj1].
    - left. exists i, j. rewrite nth_error_app1 in Hi, Hj; auto.
    - right. right. rewrite nth_error_app1 in Hi; auto. rewrite nth_error_app2 in Hj; [| lia].
      split; eapply nth_error_In; eauto.
    - lia.
    - right. left. rewrite nth_error_app2 in Hi, Hj; try lia.
      exists (i - length l1), (j - length l1). split; [lia | auto].
  Qed.

  (** Filtering preserves relative order. *)
  Lemma before_filter (f : A -> bool) l x y :
    before l x y -> f x = true -> f y = true -> before (filter f l) x y.
  Proof.
    induction l as [| a l IH]; intros Hb Hx Hy.
    - destruct Hb as (i & j & _ & Hi & _). destruct i; discriminate.
    - destruct Hb as (i & j & Hij & Hi & Hj).
      destruct i as [| i]; cbn in Hi.
      + inversion Hi; subst a. destruct j as [| j]; [lia |]. cbn in Hj.
        cbn. rewrite Hx. apply before_cons_head. apply filter_In. split; auto.
        eapply nth_error_In; eauto.
      + destruct j as [| j]; [lia |]. cbn in Hj.
        assert (Hb' : before l x y) by (exists i, j; auto with arith).
        specialize (IH Hb' Hx Hy).
        cbn. destruct (f a); auto. apply before_cons; auto.
  Qed.

  Lemma before_filter_inv (f : A -> bool) l x y :
    before (filter f l) x y -> before l x y.
  Proof.
    induction l as [| a l IH]; intros Hb.
    - destruct Hb as (i & j & _ & Hi & _). destruct i; discriminate.
    - cbn in Hb. destruct (f a) eqn:Hfa.
      + assert (Hnd_case : (x = a /\ In y (filter f l)) \/ before (filter f l) x y).
        { destruct Hb as (i & j & Hij & Hi & Hj).
          destruct i as [| i]; destruct j as [| j]; cbn in *; try lia.
          - left. inversion Hi; subst. split; auto. eapply nth_error_In; eauto.
          - right. exists i, j. auto with arith. }
        destruct Hnd_case as [[-> Hy] | Hb'].
        * apply before_cons_head. apply filter_In in Hy. tauto.
        * apply before_cons. auto.
      + apply before_cons. auto.
  Qed.

  Lemma before_Permutation_nth l x y i j :
    nth_error l i = Some x -> nth_error l j = Some y -> i < j -> before l x y.
  Proof.
    intros Hi Hj Hij. exists i, j. auto.
  Qed.

  Lemma nth_error_firstn_iff l n i (x : A) :
    nth_error (firstn n l) i = Some x <-> (i < n /\ nth_error l i = Some x).
  Proof.
    revert n i. induction l as [| a l IH]; intros n i.
    - rewrite firstn_nil. destruct i; cbn; split; intros H; try discriminate; destruct H; discriminate.
    - destruct n as [| n]; cbn.
      + destruct i; cbn; split; intros H; try discriminate; destruct H; lia.
      + destruct i as [| i]; cbn.
        * split; intros H; auto. split; [lia | tauto]. tauto.
        * rewrite IH. split; intros [H1 H2]; split; auto; lia.
  Qed.

End Positions.

Lemma before_map (A B : Type) (f : A -> B) (l : list A) (x y : A) :
  before l x y -> before (map f l) (f x) (f y).
Proof.
  intros (i & j & Hij & Hi & Hj). exists i, j. split; auto.
  split; apply map_nth_error; auto.
Qed.

Lemma before_map_inv (A B : Type) (f : A -> B) (l : list A) (u v : B) :
  before (map f l) u v -> exists x y, before l x y /\ u = f x /\ v = f y.
Proof.
  intros (i & j & Hij & Hi & Hj).
  rewrite nth_error_map in Hi, Hj.
  destruct (nth_error l i) as [x |] eqn:Hx; [| discriminate].
  destruct (nth_error l j) as [y |] eqn:Hy; [| discriminate].
  cbn in Hi, Hj. inversion Hi; inversion Hj; subst.
  exists x, y. split; auto. exists i, j. auto.
Qed.


(** ** Existence of duplicates in long lists *)

Section Pigeonhole.
  Variable A : Type.

  Lemma NoDup_of_pairwise (c : list A) :
    (forall i j x y, i < j -> nth_error c i = Some x -> nth_error c j = Some y -> x <> y) ->
    NoDup c.
  Proof.
    induction c as [| a c IH]; intros H.
    - constructor.
    - constructor.
      + intros Hin. apply In_nth_error in Hin. destruct Hin as [j Hj].
        apply (H 0 (S j) a a); cbn; auto with arith.
      + apply IH. intros i j x y Hij Hi Hj.
        apply (H (S i) (S j) x y); cbn; auto with arith.
  Qed.

  Lemma long_list_has_duplicate (c l : list A) :
    NoDup l -> incl c l -> length l < length c ->
    exists i j x, i < j /\ nth_error c i = Some x /\ nth_error c j = Some x.
  Proof.
    intros Hnd Hincl Hlen.
    apply NNPP. intros Hno.
    assert (HndC : NoDup c).
    { apply NoDup_of_pairwise. intros i j x y Hij Hi Hj Heq. subst y.
      apply Hno. exists i, j, x. auto. }
    pose proof (NoDup_incl_length HndC Hincl). lia.
  Qed.
End Pigeonhole.

(** ** Linear extensions of acyclic relations on finite lists *)

Section LinearExtension.
  Variable A : Type.
  Variable R : relation A.

  (** The restriction of [R] to the elements of a list. *)
  Definition restr (l : list A) : relation A :=
    fun x y => In x l /\ In y l /\ R x y.

  Lemma restr_incl l l' : incl l l' -> rel_incl (restr l) (restr l').
  Proof. firstorder. Qed.

  (** A backward chain: consecutive elements are related by [R] backwards,
      i.e. [c = [x0; x1; x2; ...]] with [R x1 x0], [R x2 x1], ... *)
  Definition bchain (l : list A) (c : list A) : Prop :=
    forall i a b, nth_error c i = Some a -> nth_error c (S i) = Some b -> restr l b a.

  Lemma bchain_app_last l c y z :
    bchain l c -> nth_error c (length c - 1) = Some z -> c <> [] ->
    restr l y z -> bchain l (c ++ [y]).
  Proof.
    intros Hc Hlast Hne Hyz i a b Ha Hb.
    destruct (lt_dec (S i) (length c)) as [Hlt | Hge].
    - rewrite nth_error_app1 in Ha, Hb; try lia. eapply Hc; eauto.
    - assert (HSi : S i < length (c ++ [y])) by (apply nth_error_Some; congruence).
      rewrite length_app in HSi. cbn in HSi.
      assert (S i = length c) by lia.
      rewrite nth_error_app1 in Ha; [| lia].
      rewrite nth_error_app2 in Hb; [| lia].
      replace (S i - length c) with 0 in Hb by lia. cbn in Hb. inversion Hb; subst b.
      replace i with (length c - 1) in Ha by lia. rewrite Hlast in Ha. inversion Ha; subst a.
      assumption.
  Qed.

  Lemma bchain_tc l c i j a b :
    bchain l c -> i < j -> nth_error c i = Some a -> nth_error c j = Some b ->
    tc (restr l) b a.
  Proof.
    intros Hc Hij. revert a b. induction Hij as [| j Hij IH]; intros a b Ha Hb.
    - apply t_step. eapply Hc; eauto.
    - assert (Hj : exists m, nth_error c j = Some m).
      { destruct (nth_error c j) eqn:Hm; [eauto |].
        apply nth_error_None in Hm.
        assert (S j < length c) by (apply nth_error_Some; congruence). lia. }
      destruct Hj as [m Hm].
      eapply t_trans.
      + apply t_step. eapply Hc; eauto.
      + apply IH; auto.
  Qed.

  Lemma chains_exist (l : list A) :
    (forall x, In x l -> exists y, In y l /\ R y x) ->
    forall n x, In x l ->
      exists c, length c = S n /\ nth_error c 0 = Some x /\ incl c l /\ bchain l c.
  Proof.
    intros Hpred n. induction n as [| n IH]; intros x Hx.
    - exists [x]. split; [reflexivity |]. split; [reflexivity |]. split.
      + intros y [Hy | []]. subst. auto.
      + intros k a b Ha Hb. destruct k; cbn in *; discriminate.
    - destruct (IH x Hx) as (c & Hlen & Hhd & Hincl & Hc).
      assert (Hne : c <> []) by (destruct c; cbn in Hlen; congruence).
      assert (Hz : exists z, nth_error c (length c - 1) = Some z).
      { destruct (nth_error c (length c - 1)) eqn:Hz; [eauto |].
        apply nth_error_None in Hz. destruct c; cbn in *; [congruence | lia]. }
      destruct Hz as [z Hz].
      assert (Hzl : In z l) by (apply Hincl; eapply nth_error_In; eauto).
      destruct (Hpred z Hzl) as (y & Hy & Hyz).
      exists (c ++ [y]). split; [| split; [| split]].
      + rewrite length_app. cbn. lia.
      + rewrite nth_error_app1; auto. destruct c; cbn in *; [congruence | lia].
      + intros a Ha. apply in_app_or in Ha. destruct Ha as [Ha | [Ha | []]]; subst; auto.
      + eapply bchain_app_last; eauto. repeat split; auto.
  Qed.

  (** A nonempty finite acyclic relation has a minimal element. *)
  Lemma minimal_exists (l : list A) :
    NoDup l -> acyclic (restr l) -> l <> [] ->
    exists m, In m l /\ forall y, In y l -> ~ R y m.
  Proof.
    intros Hnd Hac Hne.
    apply NNPP. intros Hno.
    assert (Hpred : forall x, In x l -> exists y, In y l /\ R y x).
    { intros x Hx. apply NNPP. intros Hnone. apply Hno. exists x. split; auto.
      intros y Hy Hyx. apply Hnone. eauto. }
    destruct l as [| x0 l0] eqn:Hl; [congruence |].
    rewrite <- Hl in *.
    assert (Hx0 : In x0 l) by (subst; left; auto).
    destruct (@chains_exist l Hpred (length l) x0 Hx0) as (c & Hlen & _ & Hincl & Hc).
    destruct (@long_list_has_duplicate A c l Hnd Hincl) as (i & j & x & Hij & Hi & Hj); [lia |].
    apply (Hac x). eapply bchain_tc; eauto.
  Qed.

  (** Main result: every finite acyclic relation has a linear extension,
      i.e. an enumeration of the carrier in which each edge goes forward. *)
  Theorem linear_extension (l : list A) :
    NoDup l -> acyclic (restr l) ->
    exists l', Permutation l l' /\ forall x y, restr l x y -> before l' x y.
  Proof.
    remember (length l) as n eqn:Hn. revert l Hn.
    induction n as [n IH] using lt_wf_ind; intros l Hn Hnd Hac.
    destruct (classic (l = [])) as [-> | Hne].
    - exists []. split; [constructor |]. intros x y (Hx & _ & _). inversion Hx.
    - destruct (minimal_exists Hnd Hac Hne) as (m & Hm & Hmin).
      apply in_split in Hm. destruct Hm as (l1 & l2 & Hsplit).
      set (rest := l1 ++ l2).
      assert (Hperm : Permutation l (m :: rest)).
      { rewrite Hsplit. unfold rest. symmetry. apply Permutation_middle. }
      assert (Hnd' : NoDup (m :: rest)) by (eapply Permutation_NoDup; eauto).
      apply NoDup_cons_iff in Hnd'. destruct Hnd' as [Hmrest Hndrest].
      assert (Hincl : incl rest l).
      { intros y Hy. eapply Permutation_in; [symmetry; exact Hperm |]. right. auto. }
      assert (Hac' : acyclic (restr rest)).
      { eapply acyclic_incl; [| exact Hac]. apply restr_incl. assumption. }
      assert (Hlen : length rest < n).
      { apply Permutation_length in Hperm. cbn in Hperm. lia. }
      destruct (IH (length rest) Hlen rest eq_refl Hndrest Hac') as (l' & Hperm' & Hbefore).
      exists (m :: l'). split.
      + eapply Permutation_trans; [exact Hperm |]. constructor. assumption.
      + intros x y (Hx & Hy & Hxy).
        assert (Hym : y <> m).
        { intros ->. exact (Hmin x Hx Hxy). }
        assert (Hy' : In y l').
        { eapply Permutation_in; [exact Hperm' |].
          eapply Permutation_in in Hy; [| exact Hperm]. destruct Hy; [congruence | auto]. }
        destruct (classic (x = m)) as [-> | Hxm].
        * apply before_cons_head. assumption.
        * apply before_cons. apply Hbefore.
          assert (Hx' : In x rest).
          { eapply Permutation_in in Hx; [| exact Hperm]. destruct Hx; [congruence | auto]. }
          assert (Hy'' : In y rest).
          { eapply Permutation_in in Hy; [| exact Hperm]. destruct Hy; [congruence | auto]. }
          repeat split; auto.
  Qed.

End LinearExtension.

(** ** Maxima of finite families *)

Section FiniteMax.
  Variable A : Type.

  (** A classical statement: the (possibly empty) image of a list under a
      partial function has a maximum. *)
  Lemma finite_max (l : list A) (P : A -> Prop) (f : A -> nat) :
    exists m, (forall x, In x l -> P x -> f x <= m) /\
              (m = 0 \/ exists x, In x l /\ P x /\ f x = m).
  Proof.
    induction l as [| a l IH].
    - exists 0. split; [intros x [] | left; auto].
    - destruct IH as (m & Hub & Hatt).
      destruct (classic (P a)) as [Ha | Ha].
      + exists (Nat.max (f a) m). split.
        * intros x [-> | Hx] Hx'; [lia |]. specialize (Hub x Hx Hx'). lia.
        * destruct (le_ge_dec (f a) m) as [Hle | Hge].
          -- rewrite Nat.max_r by lia.
             destruct Hatt as [-> | (x & Hx & HPx & Hfx)]; [left; auto |].
             right. exists x. split; [right | ]; auto.
          -- rewrite Nat.max_l by lia. right. exists a. auto with datatypes.
      + exists m. split.
        * intros x [-> | Hx] Hx'; [contradiction |]. auto.
        * destruct Hatt as [-> | (x & Hx & HPx & Hfx)]; [left; auto |].
          right. exists x. split; [right | ]; auto.
  Qed.
End FiniteMax.

(** A relational version, for a value given as a functional relation. *)
Lemma finite_max_rel (A : Type) (l : list A) (P : A -> Prop) (g : A -> nat -> Prop) :
  (forall x n n', g x n -> g x n' -> n = n') ->
  exists m, (forall x n, In x l -> P x -> g x n -> n <= m) /\
            (m = 0 \/ exists x n, In x l /\ P x /\ g x n /\ m = n).
Proof.
  intros Hfun. induction l as [| a l IH].
  - exists 0. split; [intros x n [] | left; auto].
  - destruct IH as (m & Hub & Hatt).
    destruct (classic (P a /\ exists n, g a n)) as [[Ha [na Hna]] | Hna].
    + exists (Nat.max na m). split.
      * intros x n [-> | Hx] Hx' Hg.
        -- assert (n = na) by (eapply Hfun; eauto). lia.
        -- specialize (Hub x n Hx Hx' Hg). lia.
      * destruct (le_ge_dec na m) as [Hle | Hge].
        -- rewrite Nat.max_r by lia.
           destruct Hatt as [-> | (x & n & Hx & HPx & Hg & ->)]; [left; auto |].
           right. exists x, n. split; [right | ]; auto.
        -- rewrite Nat.max_l by lia. right. exists a, na. split; [left; auto | auto].
    + exists m. split.
      * intros x n [-> | Hx] Hx' Hg; [exfalso; apply Hna; eauto | eauto].
      * destruct Hatt as [-> | (x & n & Hx & HPx & Hg & ->)]; [left; auto |].
        right. exists x, n. split; [right | ]; auto.
Qed.

(** ** Miscellaneous list facts *)

Section ListFacts.
  Variable A : Type.

  Lemma fold_left_app_single (f : list A -> A -> list A) (s : list A) (b : A) (acc : list A) :
    fold_left f (s ++ [b]) acc = f (fold_left f s acc) b.
  Proof.
    rewrite fold_left_app. reflexivity.
  Qed.

  Lemma filter_app_single (f : A -> bool) (s : list A) (b : A) :
    filter f (s ++ [b]) = filter f s ++ (if f b then [b] else []).
  Proof.
    rewrite filter_app. reflexivity.
  Qed.

  Lemma last_app_single (l : list A) (x d : A) : last (l ++ [x]) d = x.
  Proof.
    induction l as [| a l IH]; cbn; auto.
    destruct (l ++ [x]) eqn:Hl; [destruct l; discriminate | auto].
  Qed.

  Lemma hd_error_app_single (l : list A) (x : A) :
    hd_error (l ++ [x]) = match l with [] => Some x | a :: _ => Some a end.
  Proof.
    destruct l; reflexivity.
  Qed.

  (** A decomposition of [l ++ [b]] around a distinguished element is
      either at the new last element or inside [l]. *)
  Lemma snoc_split (l : list A) (b c : A) (l1 l2 : list A) :
    l ++ [b] = l1 ++ c :: l2 ->
    (l2 = [] /\ l1 = l /\ c = b) \/ (exists l2', l2 = l2' ++ [b] /\ l = l1 ++ c :: l2').
  Proof.
    intros H. destruct l2 as [| d l2] using rev_ind.
    - left. apply app_inj_tail in H. destruct H as [<- <-]. auto.
    - right. exists l2. rewrite app_comm_cons in H. rewrite app_assoc in H.
      apply app_inj_tail in H. destruct H as [<- <-]. auto.
  Qed.

  Lemma nth_error_split (l : list A) i x :
    nth_error l i = Some x -> l = firstn i l ++ x :: skipn (S i) l.
  Proof.
    revert i. induction l as [| a l IH]; intros i Hi.
    - destruct i; discriminate.
    - destruct i as [| i]; cbn in *.
      + inversion Hi; subst. reflexivity.
      + f_equal. apply IH. auto.
  Qed.

  Lemma firstn_length_le_nth (l : list A) i x :
    nth_error l i = Some x -> length (firstn i l) = i.
  Proof.
    intros H. apply firstn_length_le. apply Nat.lt_le_incl. apply nth_error_Some. congruence.
  Qed.

  Lemma firstn_S_nth (l : list A) k b :
    nth_error l k = Some b -> firstn (S k) l = firstn k l ++ [b].
  Proof.
    revert k. induction l as [| a l IH]; intros k Hk.
    - destruct k; discriminate.
    - destruct k as [| k]; cbn in *.
      + inversion Hk; subst. reflexivity.
      + f_equal. auto.
  Qed.

  Lemma NoDup_app_disjoint (l1 l2 : list A) x :
    NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
  Proof.
    induction l1 as [| a l1 IH]; intros Hnd H1 H2.
    - inversion H1.
    - cbn in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Ha Hnd].
      destruct H1 as [-> | H1].
      + apply Ha. apply in_or_app. auto.
      + eapply IH; eauto.
  Qed.

  Lemma NoDup_app (l1 l2 : list A) :
    NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> In x l2 -> False) -> NoDup (l1 ++ l2).
  Proof.
    induction l1 as [| a l1 IH]; intros H1 H2 Hdisj; cbn; auto.
    apply NoDup_cons_iff in H1. destruct H1 as [Ha H1].
    constructor.
    - intros H. apply in_app_or in H. destruct H as [H | H]; [contradiction |].
      eapply Hdisj; [left; auto | exact H].
    - apply IH; auto. intros x Hx Hx'. eapply Hdisj; [right; exact Hx | exact Hx'].
  Qed.

  Lemma NoDup_snoc (l : list A) x : NoDup l -> ~ In x l -> NoDup (l ++ [x]).
  Proof.
    induction l as [| a l IH]; intros Hnd Hx; cbn.
    - constructor; [intros [] | constructor].
    - apply NoDup_cons_iff in Hnd. destruct Hnd as [Ha Hnd].
      constructor.
      + intros H. apply in_app_or in H. destruct H as [H | [H | []]]; auto.
        apply Hx. left. auto.
      + apply IH; auto. intros H. apply Hx. right. auto.
  Qed.

  Lemma hd_error_rev_iff (l : list A) x :
    hd_error (rev l) = Some x <-> exists l', l = l' ++ [x].
  Proof.
    split.
    - intros H. destruct (rev l) as [| y l'] eqn:Hr; [discriminate |].
      cbn in H. inversion H; subst y. exists (rev l').
      rewrite <- (rev_involutive l). rewrite Hr. cbn. reflexivity.
    - intros [l' ->]. rewrite rev_app_distr. reflexivity.
  Qed.

  Lemma NoDup_map_on (B : Type) (f : A -> B) (l : list A) :
    NoDup l -> (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup (map f l).
  Proof.
    induction l as [| a l IH]; intros Hnd Hinj; cbn; [constructor |].
    apply NoDup_cons_iff in Hnd. destruct Hnd as [Ha Hnd].
    constructor.
    - intros H. apply in_map_iff in H. destruct H as (y & Hy & Hin).
      assert (y = a) by (apply Hinj; auto; [right; auto | left; auto]). subst y. contradiction.
    - apply IH; auto. intros x y Hx Hy. apply Hinj; right; auto.
  Qed.

  Lemma Permutation_filter (f : A -> bool) (l l' : list A) :
    Permutation l l' -> Permutation (filter f l) (filter f l').
  Proof.
    intros H. induction H as [| x l1 l2 H IH | x y l | l1 l2 l3 H1 IH1 H2 IH2].
    - constructor.
    - cbn. destruct (f x); auto.
    - cbn. destruct (f x), (f y); auto. constructor.
    - eapply Permutation_trans; eauto.
  Qed.

  Lemma Permutation_filter_partition (f : A -> bool) (l : list A) :
    Permutation l (filter f l ++ filter (fun x => negb (f x)) l).
  Proof.
    induction l as [| a l IH]; cbn; [constructor |].
    destruct (f a); cbn.
    - constructor. auto.
    - eapply Permutation_trans; [apply perm_skip; exact IH |]. apply Permutation_middle.
  Qed.

  Lemma filter_const_true (l : list A) : filter (fun _ => true) l = l.
  Proof. induction l; cbn; congruence. Qed.

  Lemma filter_const_false (l : list A) : filter (fun _ => false) l = [].
  Proof. induction l; cbn; congruence. Qed.

  Lemma In_firstn (l : list A) n x : In x (firstn n l) -> In x l.
  Proof.
    revert n. induction l as [| a l IH]; intros n H.
    - rewrite firstn_nil in H. inversion H.
    - destruct n as [| n]; cbn in H; [inversion H |].
      destruct H as [-> | H]; [left; auto | right; eauto].
  Qed.

End ListFacts.
