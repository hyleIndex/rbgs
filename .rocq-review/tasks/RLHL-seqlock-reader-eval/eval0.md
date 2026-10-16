**Verdict on option (A).** Tagging the reader's two barriers is cheap at the program and witness level. Writer B's hand check holds up when re-traced against the frozen `SL2Inv` definitions. The weak point is faithfulness, not soundness:
- **rmb_a ← rd Sq_i:** this is the Linux spin's control dependency, but the model folds the parity test into the final `rok`, so the paper's policy does not produce the tag for the current `rnext`.
- **rmb_b ← rd Sx_i, rd Sy_i:** no dependency rule in `impl.tex` produces this tag. It also contradicts the author's "dependency-only waits" principle (`research-intent.md:129`).
- **What saves it:** both tags are observationally inert over `EI δS` for complete traces. The argument is below; its key lemmas are kernel-checked, the full theorem is not mechanized. They are not shown inert for incomplete prefixes.

All scripts are in §6 and every result there is closed. They are run through `rocq repl` on stdin; no file was written.

## 1. Faithfulness

**What the paper's policy says (`impl.tex:118-139`, formula at :131).**
- An invocation's tag is the handles its arguments were computed from (data and address dependencies), plus κ if the operation is control-ordered.
- κ accumulates the handles of earlier branch conditions.
- For memory, every operation except a plain read is control-ordered. Under the natural instantiation for `E_S`, `sRmb` is therefore control-ordered and receives κ. `sRd` receives nothing.

**rmb_a ← rd Sq_i (tag `[n]`).**
- Linux `read_seqcount_begin` loops on `seq & 1` before `smp_rmb()`. So the policy tags `smp_rmb` with the handle of the seq load: a control dependency.
- `rnext` does not branch on `s` before rmb_a; the parity test is folded into `rok s s'` at the end. Under the policy, rmb_a gets no tag in the first iteration. In later iterations κ holds only the previous iterations' rd Sq handles.
- Making the tag policy-derived would need a spinning reader (`rd Sq; if odd then retry`). That changes the call shape, and with it the frozen `RdShape`/`Osl`, so I do not recommend it.
- Conclusion: the tag is justified as the Linux spin's control dependency, folded into the final check. This is an argued correspondence, not a derivation from the policy.

**rmb_b ← rd Sx_i, rd Sy_i (tags `[n+2; n+3]`).**
- In Linux, `a` and `c` reach no branch and no argument before `read_seqcount_retry`'s `smp_rmb()`.
- The policy gives rmb_b only κ (the G handle, plus G/T handles of earlier iterations), never X or Y.
- No construct of the paper's language yields this tag. Its only justification is barrier semantics: "a read barrier waits for earlier loads to complete".

**Is "rmb waits for prior loads to complete" a faithful barrier model here?**
- In `EI`, a read's value is fixed at its invocation (`ei_step`, `RelaxedHoareSpec.v:307-313`); the response only delivers it.
- The ordering content of `smp_rmb` (read, then rmb, then read, in program order) is already given by the invocation–invocation entries: `~sindep (sRd _) sRmb` and `~sindep sRmb (sRd _)` (`rd_order`, `SL2Prog.v:686`).
- A response tag adds a constraint only on local delivery. §2 shows that, on complete traces, this removes nothing.
- So on `EI δS` the tag is faithful in the sense of being inert. On an underlay whose values are fixed at the response, it would be a real completion fence (like `dmb ld` or `lfence`), stronger than what the paper's policy expresses.

**Final rd Sq_i, the branch, the return.**
- The final rd Sq_i is a plain read with no data dependency, so the policy gives it no tag.
- It is not needed either: s' is identified in the precondition of the final read's own response, which is enough (§4).
- The return is not an event. `ret` already requires every handle to be resolved (the Im(H) side condition), and `run` waits for each call.
- The policy would also tag the next iteration's rmbs with κ (earlier G and T handles). That is harmless and unneeded.

**Recommended tags:** rmb_a `[n]`, rmb_b `[n+2; n+3]`, nothing else. Because `dix` indices are absolute positions, the machine needs a call counter: `RG n`, …, with retry going to `RG (n+6)`. `rnextT` in §6 is exactly this, and it typechecks with the existing interpreter (`RelaxedHoareRun.v:206-245`).

## 2. Effect on traces

**Frontier rules, checked in the code.**
- `must_precede` (`RelaxedModuleSemantics.v:252-259`), for same-thread pairs:
  - response then response: never ordered;
  - invocation of h then response of h': ordered only if h = h';
  - response of h then a later invocation: ordered only if that invocation's tag contains h.
- Events of different threads always cross (`tagged_can_cross`).
- The `EI` response step removes the matching record from anywhere in the pending list. The handle-linear wrapper (`hlx_step`, `CompLinSpec.v:980-986`) adds nothing to responses.
- So a response is never blocked except by its own invocation.

**Insensitivity argument ("eager responses").**
1. Take any untagged execution. Each emitted response can be moved left until it sits right after its own invocation; the overlay events are unchanged.
   - Selection: the response crosses every earlier queue entry except its own invocation (`res_crosses`, `res_select_eager`). Events that used to cross it now face a shorter prefix (`select_sub`).
   - Underlay state: an `EI` response commutes left past an invocation of another key (`ei_res_inv_commute`). It commutes past another response by the same list argument, given key uniqueness, which module freshness provides (`trace_fresh` against `used`, as in `hlift`'s `LiftOK`).
   - Overlay invocations append to the end of the queue, and overlay returns of other calls are unaffected, so both commute trivially.
   - All four named lemmas are closed (§6).
2. Every tag source is an F2 predecessor of the tagged invocation: rd Sq_i before rmb_a, and rd Sx_i, rd Sy_i before rmb_b, all `~sindep`. So in the eager execution the source response is emitted right after an invocation that precedes the tagged one.
3. The tagged and untagged readers produce the same untagged events: `rdT_prod` and `rdT_retry_prod_gen` give exactly `rd_iter_evs`. A generic simulation between `run` machines that differ only in `dix` is straightforward but not written.
4. Conversely, tagged ⊆ untagged trivially: extra tags only add `must_precede` constraints.

**Scope.** The argument works whenever every tag-source response is eventually emitted. That holds for complete traces: `PrefixView.complete` means every call returned, so every response was emitted. Hence `sl2rd_relin_target`, which is stated for complete traces, transfers from the tagged program to the untagged one.

**It does not cover incomplete prefixes.** In the untagged module a reader whose response of rd Sq_i has a wrong prophecy stays stuck forever, yet it can still emit its rmbs. That unblocks a younger write on the same thread, since `lb_blocking` makes only the reader's pending rmb block that write's rd Sq_j, and the write can complete.
- The tagged module cannot replay this with the same reader trace. It must choose a different reader prophecy; the reader's result is unobserved, and the writer's events could be delayed.
- That is plausible for this module but unproved, and false in general.
- So copy-cat inclusion over all prefixes (`RCompLin`) for the untagged reader does not follow from this argument.

## 3. The SB witness

`sb2_exec_rd_mtraces_ij` already emits every reader response immediately after its invocation, so the same schedule works for the tagged module without rescheduling. I replayed it in Rocq and it is closed. The only changes:
- the production lemma now bounds tags to a range (`h ≤ q ≤ h+5`) instead of "no tags";
- in `cross_ok_ij`, the `~ tev_deps` case is replaced by a range case discharged by `lia`. A reader's rmb crossing its own thread's pending writer responses: reader tags lie in 10..15 / 30..35, writer handles are 0..6 / 20..26.

`sl2_read_overtakes_write` has the same crossing pattern and needs the same tactic case. `sl2_write_read_mtraces` has no rmb crossing a pending response; only its destructuring of the production lemma changes.

## 4. Does the derivation go through with the frozen `SL2Inv`? Yes, by hand trace

Notation: G, A, X, Y, B, T are the iteration's six calls (rd Sq_i, rmb, rd Sx_i, rd Sy_i, rmb, rd Sq_i). κ_G, κ_X, κ_T are the underlay call keys of G, X, T.

**Positions.** By `dprec_run`, call j has its invocation slot at 2j and its response slot at 2j+1. The tags add the edges 2n+1 → 2n+2 (G's response into A) and 2n+5, 2n+7 → 2n+8 (X's and Y's responses into B). The invariant needs `n = length cs` at `RG n`.

**Slot trace (one iteration).**
- **Inv G:** `read_inv_mine`, so ∃ r0, `KMine κ_G (Sq, r0)` ∧ r0 ≤ seq_i. Stable by the `kmine` and `kseqge` stability lemmas.
- **Res G (value s):** `eihl_mine_res` gives r0 = s. Post `KSeqGe i s`, which no longer mentions the record.
- **Edge Res G → Inv A (new F3 edge):** carries `KSeqGe i s`. `ns_if_new_in` ranges over earlier responses not before Res G; all have frame guarantees, and `kseqge_stable_g` covers them. Inv A then carries it to Inv X (Rmb before DR edge).
- **Inv X:** with s ≤ seq_i, `JEven` gives ∃ a_rec, `KMine κ_X (Sx, a_rec)` ∧ `KRdVal i s fst a_rec`.
- **Res X (value a):** a_rec = a. Post `KRdVal i s fst a`. Y is symmetric.
- **Edges Res X, Res Y → Inv B (new F3 edges):** at the linearization point (LP), `s ≤ seq_i` and (`seq_i = s` ∧ s even → `A i = (a, c)`).
- **Inv B, last rmb (`~Owns k isRmb`):** `isl_read_lp` always linearizes with `A i` (`RecNB` of G is carried along the invocation chain by the `krecnb` lemmas). Post: `KRec (Op k (fR i) p)` ∧ (p = (a, c) ∨ s < seq_i ∨ s odd), plus `KNotOwns k isRmb`.
- **Inv T, then Res T (value s'):** T's record r' = seq_i ≥ seq at the LP. Res T gives r' = s'. Post: `KRec … p` ∧ (p = (a, c) ∨ s' ≠ s ∨ s odd), which is pure plus `krec`.
  - If `rok s s'`: p = (a, c), so `Qsl` holds at `Close`.
  - Otherwise the machine loops, and the next rmb invocation's `ghost_emit` is impossible because k owns no rmb (`knotowns_stable`, and own events only remove their own entries).
- **Non-final iterations:** no LP. A return with rmbs still owned contradicts `NoOwn` at `RetCond`.

**Why the tags are the fix.** Every fact the LP needs relates a machine value to the current state. It is identified in a response's own precondition and carried forward along an F3 edge, so no consumed record is needed later. Without those edges the facts reach only the return, where seq_i has moved on; connecting them there would need the value history of option (B).

**Derivation-side obligations (not frozen-definition changes).**
- Each slot's guarantee must be finer than `Gsl k`: poss unchanged and the ghost minus the own event (`isl_response` and `isl_inv_noreg` already give the poss-unchanged part). This keeps `KRec`, `KLook` and `KOwns` of k stable under `ns_if_*`. It is the tagged-case remnant of M-24 (iii).
- Edge assertions that are live across the LP may mention k's phase only as a disjunction.

**Edits in `SL2Inv`:** only `m2w_read_body` and `sl2_read_run_provable` (`RG` becomes `RG 0`, new state type), plus the "OPEN" section of the header. `Isl`/`Rsl`/`Gsl`/`Osl`/`Qsl` do not depend on tags.

## 5. Cost and risks

**Effort.**
- **`SL2Prog`, about half a day.** New state type and `rnext`; `rd_prod`, `rd_retry_prod_gen` and `rd_retry_prod` with range bounds (the scratch proofs in §6 are drop-ins); one extra `cross_ok` case; `sl2_read_overtakes_write`; header (:39-43, :114-117).
- **`SL2Exec`, under a quarter day.** One tactic case, verified by the sed recipe in §6; header.
- **`SL2Inv` entry points, under a quarter day.**
- **The read derivation (task .5), 5-8 days, about 1,500-2,500 lines.** This is the first multi-call use of `rp_run`. It needs 6 calls × 2 slots, each with the nine `NewSlotOK` fields, and an invariant that summarises an unbounded number of earlier iterations uniformly.
- **Optional, recommended: insensitivity theorem for complete traces, 2-3 days, about 400-700 lines.** Response-left-commutation at module level, a `run` simulation for machines differing only in `dix`, and the instance.
- The writer derivation (task .6) is unaffected.

**Risks.**
1. **Author acceptance.** The rmb_b tag is outside both `impl.tex`'s policy and `research-intent.md:129`. Mitigation: describe it as a completion-barrier annotation, backed by the insensitivity theorem.
2. **Derivation size and the guarantee design.** Medium risk.
3. **Prefix copy-cat inclusion (`RCompLin`) for the untagged program is not obtained by this argument (§2).**
4. **Layering over a non-`EI` underlay** would make the response tags semantically active, so faithfulness would have to be argued again.
5. **`implex.tex:3` ("RLHL is complete").** Option (A) derives the proof for an observationally equivalent program, not the given one. It documents rather than resolves the rule-level incompleteness, so the SeqLock must not be cited for completeness.
6. **Records to update:** plan §2.3 ("no dependency tags anywhere") and plan :246 ("tags question moot") become false.

## 6. Scripts (run from `/Users/index/Documents/GitHub/rbgs-rlhl`; all 7 `Print Assumptions` report "Closed under the global context")

```sh
export PATH=/opt/homebrew/bin:$PATH; X=examples/Relaxed/RelaxedHoareSL2Exec.v
{ cat <<'EOF'
From Stdlib Require Import List Bool Arith.PeanoNat PArith.PArith micromega.Lia.
Require Import models.EffectSignatures models.RelaxedSignature models.LinCCAL.
Require Import models.simlin.RelaxedLTS models.simlin.RelaxedLang models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics models.simlin.RelaxedTraceLin models.simlin.RelaxedHoareRun.
Require Import models.simlin.RelaxedHoareSpec models.simlin.RelaxedHoareCompLin.
From examples.Relaxed Require Import RelaxedHoareSL2Prog RelaxedHoareSL2Exec.
Import ListNotations.
Import RelaxedHoareSL2Prog RelaxedHoareSL2Exec.
Import LinCCALBase RelaxedSig RelaxedLTSSpec RelaxedLang RelaxedSemantics RelaxedHoareRun.
Inductive RStT : Type :=
| TG (n : nat) | TA (n s : nat) | TX (n s : nat) | TY (n s a : nat)
| TB (n s a c : nat) | TT (n s a c : nat) | TD (a c : nat).
Definition rnextT (i : nat) (st : RStT) : SStep SSig RStT (nat * nat) :=
  match st with
  | TG n => SCall (sRd (Sq i)) [] (fun s => TA n s)
  | TA n s => SCall sRmb [n] (fun _ => TX n s)
  | TX n s => SCall (sRd (Sx i)) [] (fun a => TY n s a)
  | TY n s a => SCall (sRd (Sy i)) [] (fun c => TB n s a c)
  | TB n s a c => SCall sRmb [n + 2; n + 3] (fun _ => TT n s a c)
  | TT n s a c => SCall (sRd (Sq i)) [] (fun s' => if rok s s' then TD a c else TG (n + 6))
  | TD a c => SDone (a, c)
  end.
Definition M2T (rc : bool) (si : FOp -> FOp -> Prop) : RelaxedModuleImpl (E_S rc) (F2 si) :=
  fun op _ => match op as o return Prog (E_S rc) (far o) with
    | fW i vx vy => run (G := E_S rc) (wnext i vx vy) [] W0
    | fR i => run (G := E_S rc) (rnextT i) [] (TG 0) end.
Definition M2wT (rc : bool) (si : FOp -> FOp -> Prop) (tw : nat -> tid) : RelaxedModuleImpl (E_S rc) (F2 si) :=
  fun op t => match op as o return Prog (E_S rc) (far o) with
    | fW i vx vy => if Pos.eqb t (tw i) then M2T rc si (fW i vx vy) t else div
    | fR i => M2T rc si (fR i) t end.
Ltac deps_range :=
  apply Forall_forall; intros m Hm q Hq; cbn in Hm;
  repeat (destruct Hm as [<- | Hm]; [cbn in Hq; unfold no_deps in Hq;
    first [ contradiction
          | destruct Hq as [(ix & Hi & Hn) _]; cbn in Hi;
            repeat (destruct Hi as [<- | Hi]; [cbn in Hn; injection Hn as <-; lia |]); destruct Hi ] |]);
  destruct Hm.
Lemma rdT_prod rc si t i h s a c :
  Nat.even s = true ->
  exists tr, program_produces_tagged t (M2T rc si (fR i) t) tr (a, c) /\
    map untag tr = rd_iter_evs rc t i h s a c s /\
    Forall (fun m : TaggedEvent (E_S rc) => forall q, tev_deps m q -> h <= q <= h + 5) tr.
Proof.
  intros Hs. eexists. split; [eexists; split |].
  - unfold initial_program. cbn [M2T].
    ex_step h s. ex_step (h + 1) tt. ex_step (h + 2) a. ex_step (h + 3) c. ex_step (h + 4) tt. ex_step (h + 5) s.
    rewrite (rok_true s Hs). ex_done.
  - constructor. repeat constructor.
  - split; [reflexivity | deps_range].
Qed.
Lemma rdT_retry_prod_gen rc si t i h s1 a1 c1 s1' s a c :
  rok s1 s1' = false -> Nat.even s = true ->
  exists tr, program_produces_tagged t (M2T rc si (fR i) t) tr (a, c) /\
    map untag tr = rd_iter_evs rc t i h s1 a1 c1 s1' ++ rd_iter_evs rc t i (h + 6) s a c s /\
    Forall (fun m : TaggedEvent (E_S rc) => forall q, tev_deps m q -> h <= q <= h + 11) tr.
Proof.
  intros Hf Hs. eexists. split; [eexists; split |].
  - unfold initial_program. cbn [M2T].
    ex_step h s1. ex_step (h + 1) tt. ex_step (h + 2) a1. ex_step (h + 3) c1. ex_step (h + 4) tt. ex_step (h + 5) s1'.
    rewrite Hf.
    ex_step (h + 6) s. ex_step (h + 6 + 1) tt. ex_step (h + 6 + 2) a. ex_step (h + 6 + 3) c. ex_step (h + 6 + 4) tt.
    ex_step (h + 6 + 5) s.
    rewrite (rok_true s Hs). ex_done.
  - constructor. repeat constructor.
  - split; [reflexivity | deps_range].
Qed.
Lemma rdT_tags rc si t i h s a c :
  Nat.even s = true ->
  exists tr, program_produces_tagged t (M2T rc si (fR i) t) tr (a, c) /\
    map untag tr = rd_iter_evs rc t i h s a c s /\
    (forall d q, tev_deps (nth 2 tr d) q <-> q = h) /\
    (forall d q, tev_deps (nth 8 tr d) q <-> q = h + 2 \/ q = h + 3).
Proof.
  intros Hs. eexists. split; [eexists; split |].
  - unfold initial_program. cbn [M2T].
    ex_step h s. ex_step (h + 1) tt. ex_step (h + 2) a. ex_step (h + 3) c. ex_step (h + 4) tt. ex_step (h + 5) s.
    rewrite (rok_true s Hs). ex_done.
  - constructor. repeat constructor.
  - split; [reflexivity |]. cbn. split.
    + intros d q. split.
      * intros [(ix & [<- | []] & Hn) _]. cbn in Hn. injection Hn as <-. reflexivity.
      * intros ->. split; [exists 0; split; [left; reflexivity | reflexivity] |].
        exists (sRd (Sq i)), s. left. reflexivity.
    + intros d q. split.
      * intros [(ix & [<- | [<- | []]] & Hn) _]; cbn in Hn; injection Hn as <-; [left | right]; reflexivity.
      * intros [-> | ->].
        -- split; [exists 2; split; [left; reflexivity | reflexivity] |].
           exists (sRd (Sx i)), a. right. left. reflexivity.
        -- split; [exists 3; split; [right; left; reflexivity | reflexivity] |].
           exists (sRd (Sy i)), c. left. reflexivity.
Qed.
Lemma wrT_guard_prod rc si tw t i h v vx vy :
  tw i = t ->
  exists tr, program_produces_tagged t (M2wT rc si tw (fW i vx vy) t) tr tt /\
    map untag tr = wr_evs rc t i h v vx vy /\ Forall (fun m : TaggedEvent (E_S rc) => forall q, tev_deps m q -> q = h) tr.
Proof.
  intros Ht. destruct (wr_prod rc si t i h v vx vy) as (tr & Hp & Hm & Hd).
  exists tr. split; [| split; assumption]. cbn [M2wT]. rewrite Ht, Pos.eqb_refl. exact Hp.
Qed.
EOF
sed -n '521,546p' $X | sed -e 's/Local Ltac/Ltac/' -e 's/forall q, ~ tev_deps ?m q |- ~ tev_deps ?m _ => apply Hd end/forall q, tev_deps ?m q -> _ <= q <= _ |- ~ tev_deps ?m _ => let H := fresh in intros H; apply Hd in H; lia end/'
sed -n '548,641p' $X | sed -e 's/sb2_exec_rd_mtraces_ij/sb2T_exec_rd_mtraces_ij/' -e 's/(M2w rc si tw)/(M2wT rc si tw)/' -e 's/(wr_guard_prod /(wrT_guard_prod /g' -e 's/(rd_prod /(rdT_prod /g'
cat <<'EOF'
Import RelaxedModuleSemantics RelaxedTraceLin RelaxedHoareSpec.
Section Eager.
  Context {E F : RelaxedSig.t}.
  Lemma select_of_split (cand : TaggedScheduledEvent E F) pre post :
    Forall (fun e => tagged_can_cross (ts_event e) (ts_event cand)) pre ->
    select_frontier_tagged cand (pre ++ cand :: post) (pre ++ post).
  Proof.
    induction pre as [| e pre IH]; intros Hall; cbn; [apply tagged_select_here |].
    inversion Hall as [| ? ? He Hall']; subst. apply tagged_select_next; [exact He | exact (IH Hall')].
  Qed.
  Lemma res_crosses (e cand : TaggedEvent E) t h o (r : Sig.ar o) :
    untag cand = Build_ThreadEvent t (@ResEv E h o r) ->
    (forall o', untag e <> Build_ThreadEvent t (@InvEv E h o')) -> tagged_can_cross e cand.
  Proof.
    intros Hc He. unfold tagged_can_cross, must_precede. rewrite Hc. cbn.
    destruct (untag e) as [t' ev'] eqn:Hue. cbn.
    destruct (Pos.eq_dec t' t) as [-> | Hne]; [right | left; exact Hne].
    split; [reflexivity |]. destruct ev' as [h' o' | h' o' r']; cbn.
    - intros ->. exact (He o' eq_refl).
    - intros [].
  Qed.
  Lemma res_select_eager (cand : TaggedScheduledEvent E F) pre post t h o (r : Sig.ar o) :
    untag (ts_event cand) = Build_ThreadEvent t (@ResEv E h o r) ->
    (forall e o', In e pre -> untag (ts_event e) <> Build_ThreadEvent t (@InvEv E h o')) ->
    select_frontier_tagged cand (pre ++ cand :: post) (pre ++ post).
  Proof.
    intros Hc Hpre. apply select_of_split. apply Forall_forall. intros e He.
    apply (res_crosses _ _ t h o r Hc). intros o'. exact (Hpre e o' He).
  Qed.
  Lemma select_sub (cand : TaggedScheduledEvent E F) A1 x A2 B :
    Forall (fun e => tagged_can_cross (ts_event e) (ts_event cand)) (A1 ++ x :: A2) ->
    select_frontier_tagged cand ((A1 ++ A2) ++ cand :: B) ((A1 ++ A2) ++ B).
  Proof.
    intros Hall. apply select_of_split. apply Forall_app in Hall as [H1 H2].
    inversion H2; subst. apply Forall_app. split; assumption.
  Qed.
End Eager.
Section EICommute.
  Context {F : RelaxedSig.t} {St : Type}.
  Context (δ : St -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> St -> Prop).
  Lemma ei_res_inv_commute t1 h1 o1 t h o (r : Sig.ar o) s s1 s2 :
    (t1, h1) <> (t, h) ->
    ei_step δ (Build_ThreadEvent t1 (@InvEv F h1 o1)) s s1 ->
    ei_step δ (Build_ThreadEvent t (@ResEv F h o r)) s1 s2 ->
    exists s1', ei_step δ (Build_ThreadEvent t (@ResEv F h o r)) s s1' /\
                ei_step δ (Build_ThreadEvent t1 (@InvEv F h1 o1)) s1' s2.
  Proof.
    intros Hk (r1 & st' & Hd & ->) (P1 & P2 & HP & ->). cbn in *.
    destruct P1 as [| y P1]; cbn in HP.
    - exfalso. apply (f_equal (fun l => option_map (@op_key F) (hd_error l))) in HP. cbn in HP.
      apply Hk. congruence.
    - apply (f_equal (@tl _)) in HP as HP'. cbn in HP'.
      apply (f_equal (@hd_error _)) in HP. cbn in HP. injection HP as Hy. subst y.
      exists (fst s, P1 ++ P2). split.
      + exists P1, P2. split; [exact HP' | reflexivity].
      + exists r1, st'. split; [exact Hd | reflexivity].
  Qed.
End EICommute.
Print Assumptions rdT_prod. Print Assumptions rdT_retry_prod_gen. Print Assumptions rdT_tags.
Print Assumptions sb2T_exec_rd_mtraces_ij. Print Assumptions res_select_eager.
Print Assumptions select_sub. Print Assumptions ei_res_inv_commute.
EOF
} | rocq repl -q -R coqrel coqrel -R structures structures -R models models -R examples examples -R interfaces interfaces -R memory memory
```

The sed lines take `SL2Exec.v:521-546` (the local tactics, with the `~tev_deps` case replaced by the range case) and `:548-641` (the SB theorem with `M2w`, `wr_guard_prod`, `rd_prod` substituted). The replay takes about 10 seconds.

### Critical Files for Implementation
- /Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareSL2Prog.v
- /Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareSL2Inv.v
- /Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareSL2Exec.v
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareRun.v
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedModuleSemantics.v