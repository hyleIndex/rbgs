Require Import examples.Relaxed.RelaxedHoareSL2Read. Require Import examples.Relaxed.RelaxedHoareSL2Exec.
Import RelaxedHoareSL2Prog.RelaxedHoareSL2Prog RelaxedHoareSL2Read.RelaxedHoareSL2Read RelaxedHoareSL2Exec.RelaxedHoareSL2Exec.
Lemma sl2_no_mp rc tw s : RelaxedHoareCompLin.RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.RelaxedHoareSpec.EI (F := E_S rc) δS) (M2w rc slRA tw) (regs0, nil) s -> PrefixView.PrefixView.complete s -> ~ mp_shaped s.
Proof. intros Htr Hc Hmp. apply (mp2_not_rel_lin slRA slRA s slRA_slsi Hmp). exact (sl2_rel_lin rc slRA tw s (fun o o2 H => H) Htr Hc). Qed.
Lemma sl2_complin_unguarded rc si tw s : (forall o o2, slRA o o2 -> si o o2) -> RelaxedHoareCompLin.RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.RelaxedHoareSpec.EI (F := E_S rc) δS) (M2 rc si) (regs0, nil) s -> P1 tw s -> RelaxedHoareCompLin.RelaxedHoareCompLin.RTraces (RelaxedHoareSpec.RelaxedHoareSpec.EI (F := F2 si) δF) (A0, nil) s.
Proof. intros Hsi Htr HP. apply (sl2_complin rc si tw Hsi). exact (mtraces_guard rc si tw _ _ s Htr HP). Qed.
Print Assumptions sl2_no_mp.
Print Assumptions sl2_complin_unguarded.
