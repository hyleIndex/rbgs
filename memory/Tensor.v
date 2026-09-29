(** * Composite memory: the contract tensor (Appendix L, "Composite memory")

    This file defines the tensor product of Def. mem:def:tensor,

      ν_A ⊗ ν_B  =  { s ∈ ConcPlays_{Cell[A ∪ B]} | Pc(s) ∧ s↾A ∈ ν_A ∧ s↾B ∈ ν_B },

    parametrized by a predicate [Pc] on traces (the flush contract), and
    proves the facts the paper uses about it:

    - with [Pc] identically true it is the specification tensor of
      Def. def:spec-tensor (ordinary projection);
    - it is commutative, and associative and unital whenever [Pc] is
      closed under projection, so that the iterated tensor
      [⊗_{ℓ ∈ Locs} VBuf_ℓ] does not depend on the bracketing or on the
      order of enumeration of [Locs];
    - the flush contract [contract I] of Def. mem:def:contract is closed
      under projection ([contract_proj_closed]), for every [I];
    - consequently the memory of Def. mem:def:model decomposes exactly:
      [V_I[A ∪ B] = V_I[A] ⊗ V_I[B]] ([memory_tensor]) and
      [V_I[Locs] = ⊗_{ℓ ∈ Locs} VBuf_ℓ] ([memory_is_tensor_of_cells],
      [V_big]), and the hidden specification is [nu_I = hide(⊗_ℓ VBuf_ℓ)]
      ([nu_big]);
    - the contract is what makes [⊗] differ from the product of its
      factors: [contract_matters] exhibits a trace of
      [VBuf_x ⊗_True VBuf_y] that is not in [V_RC[{x,y}]]; and the
      difference survives hiding: [Litmus.MP.hidden_tensor_is_not_a_product]
      (message passing with release/acquire) shows
      [ν_RC[{x,y}] ⊊ ν_RC[{x}] ⊗_True ν_RC[{y}]], so the hidden
      specification of the composite memory is a tensor of its cells
      only through the contract, i.e. as [hide(⊗_{Pc} VBuf_ℓ)].

    Location sets are decidable predicates [Loc -> bool]; a trace is
    "over" a set when all of its blocks are at locations in the set, and
    [proj_set A s] is the projection [s↾A].  Disjointness of the two
    factors is the intended reading of Def. mem:def:tensor but none of
    the equations below needs it. *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Require Import Coq.PArith.PArith.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import memory.Prelude.
Require Import memory.Cell.

Import ListNotations.

Module Tensor.

  Import Cell.

  Section Tensor.
    Context (C : Cfg).

    Notation Loc := (Loc C).
    Notation block := (block C).
    Notation trace := (trace C).
    Notation proj := (proj (C := C)).
    Notation at_loc := (at_loc (C := C)).
    Notation loc_eqb := (loc_eqb (C := C)).

    (** ** Location sets *)

    Definition lset : Type := Loc -> bool.

    Definition lempty : lset := fun _ => false.
    Definition lfull : lset := fun _ => true.
    Definition lsingle (x : Loc) : lset := fun y => loc_eqb y x.
    Definition lunion (A B : lset) : lset := fun x => A x || B x.
    Definition lset_of (ls : list Loc) : lset := fun x => existsb (loc_eqb x) ls.

    Definition lsub (A B : lset) : Prop := forall x, A x = true -> B x = true.
    Definition ldisjoint (A B : lset) : Prop :=
      forall x, A x = true -> B x = true -> False.

    Lemma lsub_refl A : lsub A A.
    Proof. intros x H. exact H. Qed.

    Lemma lsub_union_l A B : lsub A (lunion A B).
    Proof. intros x H. unfold lunion. rewrite H. reflexivity. Qed.

    Lemma lsub_union_r A B : lsub B (lunion A B).
    Proof. intros x H. unfold lunion. rewrite H. apply orb_true_r. Qed.

    Lemma lsub_union_mono_r A B B' : lsub B B' -> lsub (lunion A B) (lunion A B').
    Proof.
      intros H x Hx. unfold lunion in *. apply orb_true_iff in Hx.
      apply orb_true_iff. destruct Hx as [Hx | Hx]; auto.
    Qed.

    Lemma lsub_union_mono_l A A' B : lsub A A' -> lsub (lunion A B) (lunion A' B).
    Proof.
      intros H x Hx. unfold lunion in *. apply orb_true_iff in Hx.
      apply orb_true_iff. destruct Hx as [Hx | Hx]; auto.
    Qed.

    Lemma lset_of_In ls x : lset_of ls x = true <-> In x ls.
    Proof.
      unfold lset_of. rewrite existsb_exists. split.
      - intros (y & Hy & Heq). apply loc_eqb_true in Heq. subst. exact Hy.
      - intros H. exists x. split; [exact H | apply loc_eqb_refl].
    Qed.

    Lemma lsingle_true x y : lsingle x y = true <-> y = x.
    Proof. unfold lsingle. apply loc_eqb_true. Qed.

    Lemma lsub_single_of x ls : In x ls -> lsub (lsingle x) (lset_of ls).
    Proof.
      intros Hx y Hy. apply lsingle_true in Hy. subst. apply lset_of_In. exact Hx.
    Qed.

    Lemma lset_of_cons x ls y :
      lset_of (x :: ls) y = lunion (lsingle x) (lset_of ls) y.
    Proof. reflexivity. Qed.

    (** ** Traces over a location set and projections *)

    Definition in_set (A : lset) (b : block) : bool := A (b_loc b).

    (** [over A s]: every block of [s] is at a location in [A]; this is
        membership in [ConcPlays_{Cell[A]}] as far as locations go. *)
    Definition over (A : lset) (s : trace) : Prop :=
      forall b, In b s -> A (b_loc b) = true.

    (** [proj_set A s] is the projection [s↾A]. *)
    Definition proj_set (A : lset) (s : trace) : trace := filter (in_set A) s.

    Lemma proj_set_single x s : proj_set (lsingle x) s = proj x s.
    Proof. reflexivity. Qed.

    Lemma proj_set_app A s1 s2 :
      proj_set A (s1 ++ s2) = proj_set A s1 ++ proj_set A s2.
    Proof. apply filter_app. Qed.

    Lemma proj_set_cons A b s :
      proj_set A (b :: s) = if in_set A b then b :: proj_set A s else proj_set A s.
    Proof. reflexivity. Qed.

    Lemma In_proj_set A b s : In b (proj_set A s) <-> In b s /\ A (b_loc b) = true.
    Proof. unfold proj_set, in_set. apply filter_In. Qed.

    Lemma over_proj_set A s : over A (proj_set A s).
    Proof. intros b Hb. apply In_proj_set in Hb. tauto. Qed.

    Lemma over_nil A : over A [].
    Proof. intros b []. Qed.

    Lemma over_app A s1 s2 : over A (s1 ++ s2) <-> over A s1 /\ over A s2.
    Proof.
      unfold over. split.
      - intros H. split; intros b Hb; apply H; apply in_or_app; auto.
      - intros [H1 H2] b Hb. apply in_app_or in Hb. destruct Hb; auto.
    Qed.

    Lemma over_sub A B s : lsub A B -> over A s -> over B s.
    Proof. intros HAB H b Hb. apply HAB. apply H. exact Hb. Qed.

    Lemma over_union_comm A B s : over (lunion A B) s <-> over (lunion B A) s.
    Proof.
      unfold over, lunion. split; intros H b Hb; rewrite orb_comm; apply H; exact Hb.
    Qed.

    Lemma over_union_assoc A B D s :
      over (lunion (lunion A B) D) s <-> over (lunion A (lunion B D)) s.
    Proof.
      unfold over, lunion. split; intros H b Hb;
        [rewrite orb_assoc | rewrite <- orb_assoc]; apply H; exact Hb.
    Qed.

    Lemma over_empty s : over lempty s <-> s = [].
    Proof.
      split.
      - intros H. destruct s as [| b s]; [reflexivity |].
        specialize (H b (or_introl eq_refl)). discriminate.
      - intros ->. apply over_nil.
    Qed.

    Lemma proj_set_over A s : over A s -> proj_set A s = s.
    Proof.
      induction s as [| b s IH]; intros H; [reflexivity |].
      rewrite proj_set_cons. unfold in_set.
      rewrite (H b (or_introl eq_refl)). f_equal. apply IH.
      intros b' Hb'. apply H. right. exact Hb'.
    Qed.

    Lemma proj_set_empty s : proj_set lempty s = [].
    Proof. induction s as [| b s IH]; cbn; auto. Qed.

    Lemma proj_set_full s : proj_set lfull s = s.
    Proof. apply proj_set_over. intros b _. reflexivity. Qed.

    (** Projecting twice: the inner set wins when it is the smaller one. *)
    Lemma proj_set_proj_set A B s :
      lsub A B -> proj_set A (proj_set B s) = proj_set A s.
    Proof.
      intros HAB. induction s as [| b s IH]; [reflexivity |].
      rewrite !proj_set_cons. unfold in_set.
      destruct (A (b_loc b)) eqn:HA.
      - rewrite (HAB _ HA). rewrite proj_set_cons. unfold in_set. rewrite HA. f_equal. exact IH.
      - destruct (B (b_loc b)); [rewrite proj_set_cons; unfold in_set; rewrite HA |]; exact IH.
    Qed.

    Lemma proj_proj_set_in A x s : A x = true -> proj x (proj_set A s) = proj x s.
    Proof.
      intros Hx. rewrite <- proj_set_single. apply proj_set_proj_set.
      intros y Hy. apply lsingle_true in Hy. subst. exact Hx.
    Qed.

    Lemma proj_proj_set_out A x s : A x = false -> proj x (proj_set A s) = [].
    Proof.
      intros Hx. induction s as [| b s IH]; [reflexivity |].
      rewrite proj_set_cons. unfold in_set.
      destruct (A (b_loc b)) eqn:HA; [| exact IH].
      rewrite proj_cons. destruct (at_loc x b) eqn:Hb; [| exact IH].
      apply at_loc_true in Hb. congruence.
    Qed.

    Lemma proj_over_out A x s : over A s -> A x = false -> proj x s = [].
    Proof.
      intros Hs Hx. rewrite <- (proj_set_over A s Hs). apply proj_proj_set_out. exact Hx.
    Qed.

    Lemma proj_set_ext A B s : (forall x, A x = B x) -> proj_set A s = proj_set B s.
    Proof.
      intros H. apply filter_ext. intros b. unfold in_set. apply H.
    Qed.

    Lemma over_ext A B s : (forall x, A x = B x) -> over A s -> over B s.
    Proof. intros H HA b Hb. rewrite <- H. apply HA. exact Hb. Qed.

    (** Factorizations of a projection lift to factorizations of the
        trace. *)
    Lemma proj_set_split A s l1 b l2 :
      proj_set A s = l1 ++ b :: l2 ->
      exists s1 s2, s = s1 ++ b :: s2 /\ proj_set A s1 = l1 /\ proj_set A s2 = l2
                    /\ A (b_loc b) = true.
    Proof.
      revert l1. induction s as [| c s IH]; intros l1 H.
      - destruct l1; discriminate.
      - rewrite proj_set_cons in H. destruct (in_set A c) eqn:Hc.
        + destruct l1 as [| c' l1].
          * cbn in H. injection H as <- <-. exists [], s. repeat split; auto.
          * cbn in H. injection H as <- H. apply IH in H.
            destruct H as (s1 & s2 & -> & H1 & H2 & Hb).
            exists (c :: s1), s2. repeat split; auto.
            rewrite proj_set_cons, Hc, H1. reflexivity.
        + apply IH in H. destruct H as (s1 & s2 & -> & H1 & H2 & Hb).
          exists (c :: s1), s2. repeat split; auto.
          rewrite proj_set_cons, Hc, H1. reflexivity.
    Qed.

    (** ** The contract tensor (Def. mem:def:tensor) *)

    (** [tens Pc A B nuA nuB] is [ν_A ⊗ ν_B]: the traces over [A ∪ B]
        satisfying [Pc] whose projections lie in the factors. *)
    Definition tens (Pc : trace -> Prop) (A B : lset)
        (nuA nuB : trace -> Prop) (s : trace) : Prop :=
      over (lunion A B) s /\ Pc s /\ nuA (proj_set A s) /\ nuB (proj_set B s).

    (** The specification tensor of Def. def:spec-tensor (ordinary
        projection, no contract). *)
    Definition spec_tens (A B : lset) (nuA nuB : trace -> Prop) (s : trace) : Prop :=
      over (lunion A B) s /\ nuA (proj_set A s) /\ nuB (proj_set B s).

    (** The unit: the only trace over no location. *)
    Definition unit_spec (s : trace) : Prop := s = [].

    (** [Pc] is closed under projection. *)
    Definition proj_closed (Pc : trace -> Prop) : Prop :=
      forall A s, Pc s -> Pc (proj_set A s).

    (** With [Pc] identically true, [⊗] is the specification tensor. *)
    Lemma tens_true A B nuA nuB s :
      tens (fun _ => True) A B nuA nuB s <-> spec_tens A B nuA nuB s.
    Proof. unfold tens, spec_tens. tauto. Qed.

    (** In general [⊗] is the specification tensor cut down by [Pc]. *)
    Lemma tens_spec_tens Pc A B nuA nuB s :
      tens Pc A B nuA nuB s <-> Pc s /\ spec_tens A B nuA nuB s.
    Proof. unfold tens, spec_tens. tauto. Qed.

    Lemma tens_mono Pc Pc' A B nuA nuA' nuB nuB' s :
      (forall s, Pc s -> Pc' s) ->
      (forall s, nuA s -> nuA' s) ->
      (forall s, nuB s -> nuB' s) ->
      tens Pc A B nuA nuB s -> tens Pc' A B nuA' nuB' s.
    Proof.
      intros HP HA HB (Ho & Hc & H1 & H2). repeat split; auto.
    Qed.

    (** Commutativity. *)
    Lemma tens_comm Pc A B nuA nuB s :
      tens Pc A B nuA nuB s <-> tens Pc B A nuB nuA s.
    Proof.
      unfold tens. rewrite over_union_comm. tauto.
    Qed.

    (** Associativity, under closure of [Pc] under projection. *)
    Lemma tens_assoc Pc A B D nuA nuB nuD s :
      proj_closed Pc ->
      tens Pc (lunion A B) D (tens Pc A B nuA nuB) nuD s <->
      tens Pc A (lunion B D) nuA (tens Pc B D nuB nuD) s.
    Proof.
      intros HPc. unfold tens.
      rewrite over_union_assoc.
      rewrite (proj_set_proj_set A (lunion A B) s (lsub_union_l A B)).
      rewrite (proj_set_proj_set B (lunion A B) s (lsub_union_r A B)).
      rewrite (proj_set_proj_set B (lunion B D) s (lsub_union_l B D)).
      rewrite (proj_set_proj_set D (lunion B D) s (lsub_union_r B D)).
      split.
      - intros (Ho & Hc & (_ & _ & HA & HB) & HD).
        repeat split; auto using over_proj_set.
      - intros (Ho & Hc & HA & (_ & _ & HB & HD)).
        repeat split; auto using over_proj_set.
    Qed.

    (** Units. *)
    Lemma tens_unit_l Pc A nuA s :
      tens Pc lempty A unit_spec nuA s <-> over A s /\ Pc s /\ nuA (proj_set A s).
    Proof.
      unfold tens, unit_spec. rewrite proj_set_empty.
      (* [lunion lempty A] is convertible to [A]. *)
      split; [intros (Ho & Hc & _ & HA) | intros (Ho & Hc & HA)]; repeat split; auto.
    Qed.

    Lemma tens_unit_r Pc A nuA s :
      tens Pc A lempty nuA unit_spec s <-> over A s /\ Pc s /\ nuA (proj_set A s).
    Proof.
      rewrite tens_comm. apply tens_unit_l.
    Qed.

    (** The factors may be replaced by extensionally equal ones, and the
        location sets by extensionally equal ones. *)
    Lemma tens_ext Pc A A' B B' nuA nuA' nuB nuB' s :
      (forall x, A x = A' x) -> (forall x, B x = B' x) ->
      (forall s, nuA s <-> nuA' s) -> (forall s, nuB s <-> nuB' s) ->
      tens Pc A B nuA nuB s <-> tens Pc A' B' nuA' nuB' s.
    Proof.
      intros HA HB HnA HnB. unfold tens.
      rewrite (proj_set_ext A A' s HA), (proj_set_ext B B' s HB).
      rewrite HnA, HnB.
      assert (Ho : over (lunion A B) s <-> over (lunion A' B') s).
      { split; apply over_ext; intros x; unfold lunion; rewrite HA, HB; reflexivity. }
      rewrite Ho. tauto.
    Qed.

    (** ** The iterated tensor [⊗_{ℓ ∈ ls} fam ℓ] *)

    (** Folded from the right along an enumeration [ls] of locations:
        [⊗_{ℓ ∈ x :: ls} fam ℓ = fam x ⊗ (⊗_{ℓ ∈ ls} fam ℓ)]. *)
    Fixpoint big (Pc : trace -> Prop) (fam : Loc -> trace -> Prop)
        (ls : list Loc) : trace -> Prop :=
      match ls with
      | [] => unit_spec
      | x :: ls' => tens Pc (lsingle x) (lset_of ls') (fam x) (big Pc fam ls')
      end.

    (** The characterization that makes the bracketing irrelevant: when
        [Pc] is closed under projection, the iterated tensor is the set
        of traces over [ls] satisfying [Pc] whose projection at each
        [ℓ ∈ ls] lies in [fam ℓ]. *)
    Theorem big_iff Pc fam ls s :
      proj_closed Pc -> Pc [] ->
      big Pc fam ls s <->
      over (lset_of ls) s /\ Pc s /\ forall x, In x ls -> fam x (proj x s).
    Proof.
      intros HPc Hnil. revert s. induction ls as [| x ls IH]; intros s; cbn.
      - unfold unit_spec.
        assert (Ho : over (lset_of []) s <-> s = []) by apply over_empty.
        rewrite Ho. split.
        + intros ->. repeat split; auto. intros y [].
        + tauto.
      - unfold tens. rewrite proj_set_single. rewrite IH.
        split.
        + intros (Ho & Hc & Hx & _ & _ & Hls).
          repeat split; auto.
          intros y [-> | Hy]; [exact Hx |].
          rewrite <- (proj_proj_set_in (lset_of ls) y s); [apply Hls; exact Hy |].
          apply lset_of_In. exact Hy.
        + intros (Ho & Hc & Hall).
          repeat split; auto using over_proj_set.
          intros y Hy. rewrite proj_proj_set_in; [apply Hall; right; exact Hy |].
          apply lset_of_In. exact Hy.
    Qed.

    (** Consequently the enumeration order does not matter. *)
    Corollary big_perm Pc fam ls ls' s :
      proj_closed Pc -> Pc [] -> Permutation ls ls' ->
      big Pc fam ls s <-> big Pc fam ls' s.
    Proof.
      intros HPc Hnil Hperm. rewrite !big_iff by assumption.
      assert (Hset : forall x, lset_of ls x = lset_of ls' x).
      { intros x. destruct (lset_of ls x) eqn:H1; destruct (lset_of ls' x) eqn:H2; auto.
        - apply lset_of_In in H1. eapply Permutation_in in H1; [| exact Hperm].
          apply lset_of_In in H1. congruence.
        - apply lset_of_In in H2. eapply Permutation_in in H2; [| symmetry; exact Hperm].
          apply lset_of_In in H2. congruence. }
      assert (Ho : over (lset_of ls) s <-> over (lset_of ls') s).
      { split; apply over_ext; intros x; [apply Hset | symmetry; apply Hset]. }
      rewrite Ho.
      assert (HIn : forall x, In x ls <-> In x ls').
      { intros x. split; intros H.
        - eapply Permutation_in; [exact Hperm | exact H].
        - eapply Permutation_in; [symmetry; exact Hperm | exact H]. }
      split; intros (H1 & H2 & H3); repeat split; auto; intros x Hx; apply H3; apply HIn; exact Hx.
    Qed.

    (** Splitting an enumeration splits the tensor. *)
    Corollary big_app Pc fam ls1 ls2 s :
      proj_closed Pc -> Pc [] ->
      big Pc fam (ls1 ++ ls2) s <->
      tens Pc (lset_of ls1) (lset_of ls2) (big Pc fam ls1) (big Pc fam ls2) s.
    Proof.
      intros HPc Hnil. unfold tens. rewrite !big_iff by assumption.
      assert (Hset : forall x, lset_of (ls1 ++ ls2) x = lunion (lset_of ls1) (lset_of ls2) x).
      { intros x. unfold lset_of, lunion. apply existsb_app. }
      assert (Ho : over (lset_of (ls1 ++ ls2)) s <-> over (lunion (lset_of ls1) (lset_of ls2)) s).
      { split; apply over_ext; intros x; [apply Hset | symmetry; apply Hset]. }
      rewrite Ho.
      split.
      - intros (Hov & Hc & Hall). repeat split; auto.
        + apply over_proj_set.
        + intros x Hx. rewrite proj_proj_set_in; [apply Hall; apply in_or_app; auto |].
          apply lset_of_In. exact Hx.
        + apply over_proj_set.
        + intros x Hx. rewrite proj_proj_set_in; [apply Hall; apply in_or_app; auto |].
          apply lset_of_In. exact Hx.
      - intros (Hov & Hc & (_ & _ & H1) & (_ & _ & H2)). repeat split; auto.
        intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx | Hx].
        + rewrite <- (proj_proj_set_in (lset_of ls1) x s); [apply H1; exact Hx |].
          apply lset_of_In. exact Hx.
        + rewrite <- (proj_proj_set_in (lset_of ls2) x s); [apply H2; exact Hx |].
          apply lset_of_In. exact Hx.
    Qed.

    (** ** The flush contract is closed under projection *)

    Section Contract.
      Notation pend := (pend (C := C)).
      Notation remove_first_at := (remove_first_at (C := C)).

      Lemma proj_set_remove_first_at A x l :
        proj_set A (remove_first_at x l) =
        if A x then remove_first_at x (proj_set A l) else proj_set A l.
      Proof.
        induction l as [| c l IH].
        - cbn. destruct (A x); reflexivity.
        - rewrite remove_first_at_cons. destruct (at_loc x c) eqn:Hc.
          + apply at_loc_true in Hc.
            rewrite proj_set_cons. unfold in_set. rewrite Hc.
            destruct (A x); [| reflexivity].
            rewrite remove_first_at_cons. unfold at_loc. rewrite Hc, loc_eqb_refl. reflexivity.
          + rewrite !proj_set_cons. unfold in_set. destruct (A (b_loc c)) eqn:HAc.
            * rewrite IH. destruct (A x); [| reflexivity].
              rewrite remove_first_at_cons, Hc. reflexivity.
            * exact IH.
      Qed.

      (** Pending writes commute with projection: the pending writes of
          a thread in [s↾A] are its pending writes in [s] at locations in
          [A] (Lemma mem:lem:book, set version). *)
      Lemma pend_proj_set A t s :
        pend t (proj_set A s) = proj_set A (pend t s).
      Proof.
        induction s as [| b s IH] using rev_ind; [reflexivity |].
        rewrite proj_set_app, pend_app. rewrite pend_snoc.
        rewrite proj_set_cons. cbn [proj_set filter].
        unfold pend_step at 2.
        destruct b as [u h y v a | u h y a v | u h y]; unfold in_set; cbn [b_loc].
        - (* write *)
          destruct (A y) eqn:HAy; cbn [fold_left].
          + unfold pend_step. rewrite IH.
            destruct (Pos.eq_dec u t); [| reflexivity].
            rewrite proj_set_app, proj_set_cons. unfold in_set. cbn [b_loc]. rewrite HAy. reflexivity.
          + rewrite IH.
            destruct (Pos.eq_dec u t); [| reflexivity].
            rewrite proj_set_app, proj_set_cons. unfold in_set. cbn [b_loc]. rewrite HAy.
            rewrite app_nil_r. reflexivity.
        - (* read *)
          destruct (A y); cbn [fold_left]; [unfold pend_step |]; exact IH.
        - (* flush *)
          destruct (A y) eqn:HAy; cbn [fold_left].
          + unfold pend_step. rewrite IH.
            destruct (Pos.eq_dec u t); [| reflexivity].
            rewrite proj_set_remove_first_at. rewrite HAy. reflexivity.
          + rewrite IH.
            destruct (Pos.eq_dec u t); [| reflexivity].
            rewrite proj_set_remove_first_at. rewrite HAy. reflexivity.
      Qed.

      (** Def. mem:def:contract is closed under projection: at a flush
          of [s↾A], the published write is the same as in [s], and the
          pending writes quantified over are a subset. *)
      Theorem contract_proj_closed (I : cell_op C -> cell_op C -> Prop) :
        proj_closed (contract I).
      Proof.
        intros A s Hc s1 t h x s2 m Hs Hm m' Hm' Hlt.
        apply proj_set_split in Hs.
        destruct Hs as (s1' & s2' & -> & H1 & H2 & Hx). cbn [b_loc] in Hx.
        subst s1 s2.
        rewrite pend_proj_set in Hm, Hm'.
        rewrite proj_proj_set_in in Hm by exact Hx.
        apply In_proj_set in Hm'. destruct Hm' as [Hm' _].
        eapply Hc; eauto.
      Qed.

    End Contract.

    (** ** The memory over a set of locations (Def. mem:def:model) *)

    Section Memory.
      Context (I : cell_op C -> cell_op C -> Prop).

      (** [V_on A] is [V_I[A]]: the traces over [A] satisfying the
          contract whose projection at every [ℓ ∈ A] is a behaviour of
          [Buf_ℓ].  [V I] of [Cell.v] is [V_on lfull]. *)
      Definition V_on (A : lset) (s : trace) : Prop :=
        over A s /\ contract I s /\ forall x, A x = true -> VBuf x (proj x s).

      Definition nu_on (A : lset) (s : trace) : Prop :=
        exists s', V_on A s' /\ hide s' = s.

      Lemma VBuf_nil (x : Loc) : VBuf x [].
      Proof. exists init_state. constructor. Qed.

      Lemma V_on_iff A s : V_on A s <-> over A s /\ V I s.
      Proof.
        unfold V_on, V. split.
        - intros (Ho & Hc & Hb). repeat split; auto.
          intros x. destruct (A x) eqn:Hx; [apply Hb; exact Hx |].
          rewrite (proj_over_out A x s Ho Hx). apply VBuf_nil.
        - intros (Ho & Hc & Hb). repeat split; auto.
      Qed.

      Lemma V_on_full s : V_on lfull s <-> V I s.
      Proof.
        rewrite V_on_iff. split; [tauto |]. intros H. split; [| exact H].
        intros b _. reflexivity.
      Qed.

      Lemma nu_on_full s : nu_on lfull s <-> nu I s.
      Proof.
        unfold nu_on, nu. split; intros (s' & H & <-); exists s'; split; auto;
          apply V_on_full; exact H.
      Qed.

      (** Projecting a memory trace onto a subset of its locations gives
          a memory trace over that subset. *)
      Lemma V_on_proj A B s : lsub B A -> V_on A s -> V_on B (proj_set B s).
      Proof.
        intros HBA (Ho & Hc & Hb). repeat split.
        - apply over_proj_set.
        - apply contract_proj_closed. exact Hc.
        - intros x Hx. rewrite proj_proj_set_in by exact Hx. apply Hb. apply HBA. exact Hx.
      Qed.

      (** *** Binary decomposition: [V_I[A ∪ B] = V_I[A] ⊗ V_I[B]] *)
      Theorem memory_tensor A B s :
        V_on (lunion A B) s <-> tens (contract I) A B (V_on A) (V_on B) s.
      Proof.
        unfold tens. split.
        - intros HV. destruct HV as (Ho & Hc & Hb).
          assert (HV : V_on (lunion A B) s) by (repeat split; auto).
          split; [exact Ho | split; [exact Hc | split]].
          + exact (V_on_proj (lunion A B) A s (lsub_union_l A B) HV).
          + exact (V_on_proj (lunion A B) B s (lsub_union_r A B) HV).
        - intros (Ho & Hc & (_ & _ & HA) & (_ & _ & HB)).
          repeat split; auto.
          intros x Hx. unfold lunion in Hx. apply orb_true_iff in Hx.
          destruct Hx as [Hx | Hx].
          + rewrite <- (proj_proj_set_in A x s Hx). apply HA. exact Hx.
          + rewrite <- (proj_proj_set_in B x s Hx). apply HB. exact Hx.
      Qed.

      (** *** The cells.  [V_I[{ℓ}] ⊆ VBuf_ℓ]; the factors of the
          decomposition below are the cells [VBuf_ℓ] themselves, as in
          the paper, and the contract is applied once, to the composite
          trace.  (At a single location the contract is not vacuous: for
          an [I] that relates no same-location pair it says that the
          published write has the least handle among the thread's
          pending writes at [ℓ], i.e. that issue order agrees with
          handle order there.) *)
      Lemma V_on_single_VBuf x s :
        V_on (lsingle x) s -> VBuf x s.
      Proof.
        intros (Ho & _ & Hb). specialize (Hb x (loc_eqb_refl C x)).
        rewrite <- proj_set_single in Hb. rewrite proj_set_over in Hb by exact Ho. exact Hb.
      Qed.

      (** *** The memory is the iterated tensor of its cells:
          [V_I[ls] = ⊗_{ℓ ∈ ls} VBuf_ℓ], with the contract as the [Pc]
          of Def. mem:def:tensor, for every enumeration [ls]. *)
      Theorem memory_is_tensor_of_cells (ls : list Loc) s :
        V_on (lset_of ls) s <-> big (contract I) (fun x => VBuf x) ls s.
      Proof.
        rewrite big_iff; [| apply contract_proj_closed | apply contract_nil].
        unfold V_on. split.
        - intros (Ho & Hc & Hb). repeat split; auto.
          intros x Hx. apply Hb. apply lset_of_In. exact Hx.
        - intros (Ho & Hc & Hb). repeat split; auto.
          intros x Hx. apply Hb. apply lset_of_In. exact Hx.
      Qed.

      (** For a complete enumeration of [Loc]: [V_I[Locs] = ⊗_ℓ VBuf_ℓ]. *)
      Theorem V_big (ls : list Loc) (Hls : forall x, In x ls) s :
        V I s <-> big (contract I) (fun x => VBuf x) ls s.
      Proof.
        rewrite <- memory_is_tensor_of_cells. rewrite V_on_iff.
        split; [| tauto]. intros H. split; [| exact H].
        intros b _. apply lset_of_In. apply Hls.
      Qed.

      (** And the hidden specification: [ν_I[Locs] = hide(⊗_ℓ VBuf_ℓ)]. *)
      Corollary nu_big (ls : list Loc) (Hls : forall x, In x ls) s :
        nu I s <-> exists s', big (contract I) (fun x => VBuf x) ls s' /\ hide s' = s.
      Proof.
        unfold nu. split; intros (s' & H & <-); exists s'; split; auto;
          apply (V_big ls Hls); exact H.
      Qed.

      Corollary nu_on_big (ls : list Loc) s :
        nu_on (lset_of ls) s <->
        exists s', big (contract I) (fun x => VBuf x) ls s' /\ hide s' = s.
      Proof.
        unfold nu_on. split; intros (s' & H & <-); exists s'; split; auto;
          apply memory_is_tensor_of_cells; exact H.
      Qed.

      (** The tensor of two memories is associative and commutative in
          the sense of Def. mem:def:tensor: instances of [tens_assoc]
          and [tens_comm] with [Pc = contract I]. *)
      Corollary memory_tensor_assoc A B D s :
        tens (contract I) (lunion A B) D (tens (contract I) A B (V_on A) (V_on B)) (V_on D) s <->
        tens (contract I) A (lunion B D) (V_on A) (tens (contract I) B D (V_on B) (V_on D)) s.
      Proof. apply tens_assoc. apply contract_proj_closed. Qed.

    End Memory.

  End Tensor.

  Arguments lset _ : clear implicits.
  Arguments lempty {C} _.
  Arguments lfull {C} _.
  Arguments lsingle {C} _ _.
  Arguments lunion {C} _ _ _.
  Arguments lset_of {C} _ _.
  Arguments lsub {C} _ _.
  Arguments ldisjoint {C} _ _.
  Arguments in_set {C} _ _.
  Arguments over {C} _ _.
  Arguments proj_set {C} _ _.
  Arguments tens {C} _ _ _ _ _ _.
  Arguments spec_tens {C} _ _ _ _ _.
  Arguments unit_spec {C} _.
  Arguments proj_closed {C} _.
  Arguments big {C} _ _ _ _.
  Arguments V_on {C} _ _ _.
  Arguments nu_on {C} _ _ _.

  Notation "nuA ⊗[ Pc ; A ; B ] nuB" := (tens Pc A B nuA nuB)
    (at level 40, Pc at next level, A at next level, B at next level, left associativity).

  (** ** The contract is what makes [⊗] differ from the product of its
      factors

      Over the release/acquire instance with two locations, a thread
      issues a relaxed write at [y], then a release write at [x], and
      the memory publishes the release write while the relaxed write is
      still pending.  Each projection is a behaviour of its cell, so the
      trace lies in [VBuf_x ⊗_True VBuf_y] (Def. def:spec-tensor), but
      the contract rejects the flush: a release write is published only
      after every pending write of smaller handle
      (Prop. mem:prop:instances (c)). *)
  Module ContractMatters.

    Import Instances.

    Definition C2 : Cfg := RC_cfg Bool.bool_dec.
    Definition x : Loc C2 := true.
    Definition y : Loc C2 := false.
    Definition I2 := mode_indep (C := C2).

    Definition s : trace C2 :=
      [ BW 1%positive 1 y 1 wrlx;
        BW 1%positive 2 x 1 rel;
        BF 1%positive 0 x ].

    Lemma proj_x : proj_set (lsingle x) s = [BW 1%positive 2 x 1 rel; BF 1%positive 0 x].
    Proof. reflexivity. Qed.

    Lemma proj_y : proj_set (lsingle y) s = [BW 1%positive 1 y 1 wrlx].
    Proof. reflexivity. Qed.

    Lemma s_in_product :
      spec_tens (lsingle x) (lsingle y) (VBuf x) (VBuf y) s.
    Proof.
      split; [| split].
      - intros b Hb. cbn in Hb. destruct Hb as [<- | [<- | [<- | []]]]; reflexivity.
      - rewrite proj_x.
        exists (next (BF 1%positive 0 x) (next (BW 1%positive 2 x 1 rel) init_state)).
        econstructor.
        { apply cell_step_iff. split; [reflexivity | split; [exact I | reflexivity]]. }
        econstructor.
        { apply cell_step_iff. split; [reflexivity | split; [| reflexivity]].
          vm_compute. discriminate. }
        constructor.
      - rewrite proj_y.
        exists (next (BW 1%positive 1 y 1 wrlx) init_state).
        econstructor.
        { apply cell_step_iff. split; [reflexivity | split; [exact I | reflexivity]]. }
        constructor.
    Qed.

    Lemma s_violates_contract : ~ contract I2 s.
    Proof.
      intros H.
      specialize (H [BW 1%positive 1 y 1 wrlx; BW 1%positive 2 x 1 rel]
                    1%positive 0 x [] (BW 1%positive 2 x 1 rel) eq_refl eq_refl
                    (BW 1%positive 1 y 1 wrlx) (or_introl eq_refl) (le_n 2)).
      destruct H as (_ & _ & H). exact H.
    Qed.

    Theorem contract_matters :
      spec_tens (lsingle x) (lsingle y) (VBuf x) (VBuf y) s /\
      ~ tens (contract I2) (lsingle x) (lsingle y) (VBuf x) (VBuf y) s.
    Proof.
      split; [apply s_in_product |].
      intros (_ & Hc & _). apply s_violates_contract. exact Hc.
    Qed.

    (** The same trace, read through [memory_tensor]: it is not in
        [V_RC[{x,y}]] although its projections are in [V_RC[{x}]] and
        [V_RC[{y}]]. *)
    Corollary not_in_memory : ~ V_on I2 (lunion (lsingle x) (lsingle y)) s.
    Proof.
      intros (_ & Hc & _). apply s_violates_contract. exact Hc.
    Qed.

  End ContractMatters.

End Tensor.
