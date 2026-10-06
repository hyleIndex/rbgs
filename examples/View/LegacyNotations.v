(** Assertion notations of the CSL-Lin simlin framework, for the proofs
    ported from CSL-Lin.

    rbgs's [models/logics/Logics.v] declares [//\\] and [\\//] right
    associative (levels 45/46), [==>>] at level 55 and [⊨ P] at level 80.
    CSL-Lin declared them at levels 40/50/70/100 with the default (left)
    associativity, and the ported proof scripts destruct conjunction chains
    in that shape.  The notations below denote the same rbgs constants
    ([Logics.Conj], [Logics.Disj], [Logics.Imply]); only parsing differs.
    A file importing this module must not also import [Logics]. *)

Require models.logics.Logics.

Module LegacyAssertionNotations.
  Abbreviation Assertion := Logics.Assertion.
  Abbreviation Conj := Logics.Conj.
  Abbreviation Disj := Logics.Disj.
  Abbreviation Imply := Logics.Imply.
  Delimit Scope assertion_scope with Assertion.
  Notation "P //\\ Q" := (Logics.Conj P Q) (at level 40) : assertion_scope.
  Notation "P \\// Q" := (Logics.Disj P Q) (at level 50) : assertion_scope.
  Notation "P ==>> Q" := (Logics.Imply P Q) (at level 70) : assertion_scope.
  Notation "⊨ P" := (forall s, P s) (at level 100) : assertion_scope.
End LegacyAssertionNotations.
