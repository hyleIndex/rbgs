(** * Declarative characterization (Theorem mem:thm:decl)

    For an execution candidate [X] and an admissible [pre]:
    [X] is [I]-OMCA-consistent with respect to [pre] iff some trace of
    the hidden buffered memory [ν_E[Locs]] presents [X] and respects [pre].

    The semi-independence relation [I] is any relation on invocations
    that relates no two invocations at the same location; by
    Lemma mem:lem:shape this covers [RC.I], and also [TSO.I] and [PSO.I]
    (Def. mem:def:instances), so the theorem is stated for the mode-induced
    relation of every instance ([declarative_instances]). *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Relations.Relation_Definitions.

Require Import models.RelaxedSignature.
Require Import memory.Prelude.
Require Import memory.Cell.
Require Import memory.Declarative.
Require Import memory.Pending.
Require Import memory.Extraction.
Require Import memory.Realization.

Module Equivalence.

  Import Cell Decl.

  Section Equivalence.
    Context (C : Cfg).

    Variable I : cell_op C -> cell_op C -> Prop.
    Hypothesis HI : forall m m', I m m' -> op_loc m <> op_loc m'.

    Variable X : cand C.
    Hypothesis HX : wf_cand X.

    Variable pre : relation (block C).
    Hypothesis Hadm : admissible X I pre.

    Theorem declarative_characterization :
      (exists w, wf_witness X w /\ consistent X I w pre) <->
      (exists s, nu I s /\ presents s X /\ respects s pre).
    Proof.
      split.
      - intros (w & Hw & HD1 & HD2).
        apply (Realization.realization C I HI X HX pre Hadm w Hw HD1 HD2).
      - intros (s & Hnu & Hpres & Hresp).
        apply (Extraction.extraction C I HI X HX pre Hadm s Hpres Hresp Hnu).
    Qed.

  End Equivalence.

  (** ** The instances *)

  Section Instances.
    Import Cell.Instances.
    Context (Loc : Type) (dec : forall x y : Loc, {x = y} + {x <> y}).

    (** The mode-induced relations of all three instances relate no two
        invocations at the same location. *)
    Lemma mode_indep_cross (Cf : Cfg) m m' :
      mode_indep (C := Cf) m m' -> op_loc m <> op_loc m'.
    Proof. intros (H & _ & _). exact H. Qed.

    Theorem declarative_RC (X : cand (RC_cfg dec)) (HX : wf_cand X)
        (pre : relation (block (RC_cfg dec))) (Hadm : admissible X (mode_indep (C := RC_cfg dec)) pre) :
      (exists w, wf_witness X w /\ consistent X (mode_indep (C := RC_cfg dec)) w pre) <->
      (exists s, nu (mode_indep (C := RC_cfg dec)) s /\ presents s X /\ respects s pre).
    Proof. apply declarative_characterization; auto. apply mode_indep_cross. Qed.

    Theorem declarative_TSO (X : cand (TSO_cfg dec)) (HX : wf_cand X)
        (pre : relation (block (TSO_cfg dec))) (Hadm : admissible X (mode_indep (C := TSO_cfg dec)) pre) :
      (exists w, wf_witness X w /\ consistent X (mode_indep (C := TSO_cfg dec)) w pre) <->
      (exists s, nu (mode_indep (C := TSO_cfg dec)) s /\ presents s X /\ respects s pre).
    Proof. apply declarative_characterization; auto. apply mode_indep_cross. Qed.

    Theorem declarative_PSO (X : cand (PSO_cfg dec)) (HX : wf_cand X)
        (pre : relation (block (PSO_cfg dec))) (Hadm : admissible X (mode_indep (C := PSO_cfg dec)) pre) :
      (exists w, wf_witness X w /\ consistent X (mode_indep (C := PSO_cfg dec)) w pre) <->
      (exists s, nu (mode_indep (C := PSO_cfg dec)) s /\ presents s X /\ respects s pre).
    Proof. apply declarative_characterization; auto. apply mode_indep_cross. Qed.

  End Instances.

End Equivalence.
