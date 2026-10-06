# View-based (timestamped) specifications and proofs

Ported from CSL-Lin (`hyleIndex/CSL-Lin`, `master` at `3f7baaa`, 2026-06-16). These are the Rocq proofs that §6.3 of the paper cites: the exchanger (1,195 → 1,503 lines) and the elimination-backoff stack over TSO-style view specifications.

## Files

| rbgs file | CSL-Lin source | Content |
|---|---|---|
| `ViewSpecs.v` | `examples/Specs.v` (only the modules below) | `CASRegTSOSpec`, a CAS register with a timeline `cas_mem : Time → A` and per-thread views `cas_view : tid → Time`. `TryStackSpec` and `StackSpec`. `SeqLockUnderlaySpec`: x, y and a ticket lock in one LTS, with per-thread, per-location views and a ghost owner. `SeqLock`, the overlay, with a scalar per-thread frontier. |
| `LegacyNotations.v` | (new) | CSL-Lin's assertion notations, see below |
| `ExchangerTSO.v` | `examples/Exchanger.v` | Exchanger over `VCASRegTSO` → `VExch` (SC), with the `Tail` adapter |
| `TryStackTSO.v` | `examples/TryStackTSO.v` | `OwnedMemTSOSpec`; try-stack over `VCASRegTSO ⊗ VMemTSO` → `VTryStack` (SC) |
| `SeqLockTSO.v` | `examples/seqlock.v` | SeqLock over `VSeqLockUL` → `VSeqLock` |
| `EBStackTSO.v` | `examples/EBStackTSO.v` | The EB stack tower: `ECombo` (`VComboTSO`, a hand-built global view over the three objects) → `Fmid = VTryStack ⊗ VExch` → `VStack`. It includes the bridge `tpsim_combo_of_tensor` from the global view to the tensor of the per-object views. |

Not ported: CSL-Lin's `Exchangersc.v`, `TryStack.v` and `EBStackSC.v` (rbgs already has newer versions of them in `examples/Exchanger` and `examples/Stacks`), and the non-view modules of `Specs.v` (FAI, Lock, Reg, Ticket).

## Proof framework

The proofs use rbgs's unchanged SC simlin logic: `AssertionsSingle`, `RGILogic.soundness`, `TPSimulation.cal`. The view lives entirely in the LTS specifications of the underlays. Possibility states carry no timestamps.

## Changes from the CSL-Lin sources

Each file starts with a banner naming its source. Apart from that, the changes are limited to the following.

- **Imports:**
  - `Stdlib.*` paths;
  - `examples.Common.AtomicLTS`, which is identical to CSL-Lin's `AtomicLTS`;
  - `examples.Exchanger.ExchangerSpec`, which differs from CSL-Lin's only in its imports.
- **Assertion API:**
  - `Assertions` → `AssertionsSingle`;
  - `@Assertion _ _ VE VF` → `@Assertion (@ProofState _ _ VE VF)`;
  - `Build_ProofState` → `Build_ProofStateSingle`;
  - `Assertions.Conj` → `Logics.Conj`.
- **`ModuleImpl` argument order:** `li_impl t m` / `fun t m` → `li_impl m t` / `fun m t` (rbgs: `forall m, tid -> Prog`).
- **Notations:** `TryStackTSO.v`, `SeqLockTSO.v` and `EBStackTSO.v` import `LegacyAssertionNotations` instead of `Logics`. It restores CSL-Lin's parsing of `//\\` (level 40, left associative), `\\//`, `==>>` and `⊨`, over the same rbgs constants. rbgs makes `//\\` right associative, and the proof scripts destruct conjunction chains in the left-nested shape. `ExchangerTSO.v` builds with rbgs's notations unchanged.
- **Rocq 9.2:**
  - `Context {A : Type}` outside a section → `#[local] Parameter A : Type` (`EBStackTSO.v`). This is what Coq 8 did implicitly.
  - Two `replace … by exact Hfind` → `by exact (eq_sym Hfind)` (`EBStackTSO.v`).
  - One `apply ImplRefl` → `all: apply ImplRefl` (`SeqLockTSO.v`), because rbgs's `solve_conj_impl` already closes that goal.

`ViewSpecs.v`'s modules are character-for-character identical to the corresponding modules of CSL-Lin's `Specs.v`.

## Assumptions

No `Admitted`, `admit` or `Axiom`. `Print Assumptions` on `ExchangerImpl.Mexchanger`, `TryStackTSOImpl.Mtrystack`, `SeqLockImpl.Mseqlock` and `EBStackTSOImpl.{components_correct_tensor, components_correct, ebstack_mid_correct, Mcomponents, MebstackMid}` shows three things:

- `eq_rect_eq` and `classic`, which come from the simlin framework;
- the opaque element type of the functor instantiation: `ExchangerImplParam.A`, `TryStackTSOImplParam.A`, `EBStackTSOImpl.A`.

`SeqLockImpl.Mseqlock` has only the first two.

## Known limitations (input for improving views)

- **The views are hand-written into each specification.** They are part of the layer interfaces (`li_lts`). Nothing relates them to a relaxed specification `(ν, I)` (`RelaxedSig`), or relates `cal` to `RelaxedTraceLin.rel_lin`.
- **The overlays are SC** (`VExch`, `VTryStack`, `VStack`). `VSeqLock`'s timestamps do not affect its state.
- **Composing view specifications is not modular.** `EBStackTSO.v` needs the hand-built `VComboTSO` and a bridge of about 1,000 lines (`tensor_view_le`, `tpsim_combo_of_tensor`).
- **Duplicated specs.** `ViewSpecs.TryStackSpec` / `StackSpec` duplicate `examples/Stacks/StackSpec.v`, using CSL-Lin's older constructor shapes.
