Require Import Stdlib.Lists.List.
Require Import models.EffectSignatures models.RelaxedSignature models.LinCCAL models.simlin.RelaxedLTS models.simlin.RelaxedLang models.simlin.RelaxedSemantics.
Module S33.
  Import RelaxedLang RelaxedSemantics.
  Section S.
    Context {E : RelaxedSig.t} {R : Type}.
    CoFixpoint spin : Prog E R := Tau spin.
    Lemma spin_eq : spin = Tau spin.
    Proof. rewrite (PPid spin) at 1. reflexivity. Qed.
    Definition SpinInv (p : Prog E R) : Prop :=
      p = spin \/ match p with Future _ k => forall f, k f = spin | _ => False end.
    Lemma step_inv t a c c' : program_step_tagged t a c c' -> SpinInv (pc_prog c) -> SpinInv (pc_prog c').
    Proof.
      intros Hs Hp. unfold SpinInv in *. destruct Hs; cbn [pc_prog] in *.
      - left. destruct Hp as [Hp | Hp]; [rewrite spin_eq in Hp; discriminate Hp | apply Hp].
      - destruct Hp as [Hp | []]. rewrite spin_eq in Hp. discriminate Hp.
      - destruct Hp as [Hp | []]. rewrite spin_eq in Hp. discriminate Hp.
      - destruct Hp as [Hp | []]. rewrite spin_eq in Hp. discriminate Hp.
      - exact Hp.
      - left. destruct Hp as [Hp | []]. rewrite spin_eq in Hp. injection Hp as Hp. exact Hp.
    Qed.
    Lemma exec_inv t c tr c' : program_execution_tagged t c tr c' -> SpinInv (pc_prog c) -> SpinInv (pc_prog c').
    Proof.
      induction 1 as [c | c1 c2 c3 tr Hs He IH | c1 c2 c3 m tr Hs He IH]; intros Hp.
      - exact Hp.
      - apply IH. exact (step_inv _ _ _ _ Hs Hp).
      - apply IH. exact (step_inv _ _ _ _ Hs Hp).
    Qed.
    Theorem never_produced t op tr (r : R) :
      ~ program_produces_tagged t (Future op (fun _ => spin)) tr r.
    Proof.
      intros (c' & Hex & Hterm).
      assert (H0 : SpinInv (pc_prog (initial_program (Future op (fun _ => spin))))).
      { right. cbn. intros _. reflexivity. }
      pose proof (exec_inv _ _ _ _ Hex H0) as Hc.
      destruct Hterm as [H r' Hall]. unfold SpinInv in Hc. cbn [pc_prog] in Hc.
      destruct Hc as [Hc | []]. rewrite spin_eq in Hc. discriminate Hc.
    Qed.
  End S.
End S33.
Print Assumptions S33.never_produced.
