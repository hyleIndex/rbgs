# herd7 tests for task G-3 (ARMv8 check of the buffered-cell redesign)

**Status: UNVERIFIED.** These files were written by hand. herd7 was not
installed on the machine where they were written, so no file here has
been parsed or run. Every expected verdict comes from one of two places:

- a theorem of `memory/ARMBar.v`, which is relative to that file's reading of
  `aarch64.cat`; or
- a hand derivation for x86-TSO (or, for `x86/SB+rfi`, a Coq trace of the
  x86-TSO machine of `memory/TSO.v`).

A herd7 run is the check of both.

## Commands

Run from this directory (`memory/herd/`).

```sh
herd7 -version                      # record the herdtools7 version with the results
for f in x86/*.litmus;     do herd7 -model x86tso.cat  "$f"; done
for f in aarch64/*.litmus; do herd7 -model aarch64.cat "$f"; done
```

To run a single test:

```sh
herd7 -model aarch64.cat aarch64/RSW+obj.litmus
herd7 -model x86tso.cat  x86/SeqLockZ+rfi.litmus
```

Each file has an `exists` condition. herd7 prints `Observation <name> Never`
when no consistent execution satisfies it. This is reported as **Forbidden**
below. It prints `Sometimes` or `Always` when some execution satisfies it.
This is reported as **Allowed**. Each file's first line after the name is a
quoted string that gives the expected verdict and its source.

When you report results, please also record:
- the herdtools7 version;
- which `aarch64.cat` herd7 loaded (for example, by passing its full path to `-model`).

The ARMv8 verdicts in `memory/ARMBar.v` are stated for three variants of the
model. A herd7 run tells which variant matches the shipped `aarch64.cat`:

- **POPL18**: the shape of `memory/ARM.v`, with the `coi` clauses and no `lws`. The
  name refers to those clauses only. The variant also has ARMBar's fence and RMW
  clauses, including the AL clause, which postdates POPL 2018;
- **Cur**: this file's reading of the current `aarch64.cat`, with `lws` and `si` = identity;
- **CurSI**: a hypothetical variant in which `si` relates the read and the write
  of an RMW, so that `obs; si` continues from an RMW's write to its read.

The model has two flags:

- **F1**: the AL clause `po; ([A]; amo; [L]); po` is read as *not* ordering the
  atomic's own write before later accesses. This is the literal reading
  (strict `po` on both sides). The G-3.1 review agrees, so F1 is not the open
  question.
- **F2**: does `si` relate an RMW's read and write? This is the open question.
  If herd7 shows CurSI-like behaviour, `VW+ldadda` and `VW+ldaddal` are
  Forbidden; the G-3.1 reviewer predicts Forbidden for `VW+ldaddal`.

## Expected verdicts: AArch64 (`herd7 -model aarch64.cat`)

The mapping is rmb = `DMB LD`, wmb = `DMB ST`, acq/rel = `SWP`/`LDADD` with the
flavour in the file name, and get_ticket/test_ticket = `LDR`.

| File | Expected | Source (`memory/ARMBar.v`, module `ARMBar`) | Notes |
|---|---|---|---|
| `SB+rfi` | Allowed | `SBrfi.sbrfi_allowed` | Reviewer A's test |
| `SB+rfi+dmb.ld` | Allowed | `SBrfi.sbrfi_dmbld_allowed` | |
| `SeqLockZ+rfi` | Allowed | `SeqLockZ.full_allowed` | the Q6 outcome; every SWP flavour |
| `SeqLockZ+rfi-core` | Allowed | `SeqLockZ.core_allowed` | |
| `MP+dmb.st+dmb.ld` | Forbidden | `MPBar.mp_dmbst_dmbld_forbidden` | |
| `RSW+obj` | **Forbidden** | `RSWObj.rsw_obj_forbidden` | G-3 (c); every RMW flavour and value |
| `RSW+obj-core` | Forbidden | `RSWObjCore.rsw_obj_core_forbidden` | |
| `RSW+obj-core+ldar` | Allowed | `RSWObjCore.rsw_obj_core_ldar_allowed` | the Δ2 shape: the order is carried by `LDAR` on the last read only |
| `RSW+rel+acq` | Allowed | `CrossCheck.rsw_allowed` | `memory/Litmus.v` `RSW.arm_allow`; Mem.tex Δ2 |
| `SB+rel+acq` | Forbidden | `CrossCheck.sb_relacq_forbidden` | `memory/Litmus.v` `SB.arm_forbid`; Mem.tex Δ1 |
| `AC+dmb.st+ldadd+dmb.ld` | Forbidden | `AtomicClause.ac_ldadd_ldr_forbidden` | G-3 (d); relaxed `LDADD`, plain `LDR` get |
| `AC+dmb.st+ldadd+ldadd` | Forbidden | `AtomicClause.ac_rmw_observer_forbidden` | the observer is an RMW |
| `AC+po+ldadd+dmb.ld` | Allowed | `AtomicClause.ac_nodmbst_allowed` | no wmb; dto(DW, DRMW) = false |
| `AC+po+ldaddl+dmb.ld` | Forbidden | `AtomicClause.ac_nodmbst_rel_forbidden` | |
| `AC+dmb.st+ldadd+po` | Allowed | `AtomicClause.ac_ldr_nodmbld_allowed` | no rmb, `LDR` get |
| `AC+dmb.st+ldadd+ldar` | Forbidden | `AtomicClause.ac_ldar_nodmbld_forbidden` | no rmb, `LDAR` get |
| `VW+ldaddl` | Allowed | `VW.vw_allowed` | version word, item 3; all variants |
| `VW+ldadda` | **Allowed** in POPL18/Cur, **Forbidden** in CurSI | `VW.vw_allowed`, `VW.vw_acq_si_forbidden` | **KEY: decides F2** |
| `VW+ldaddal` | **Allowed** in POPL18/Cur, **Forbidden** in CurSI | `VW.vw_allowed`, `VW.vw_acq_si_forbidden` | **KEY: F1 and F2** |
| `VW+ldadd+data` | **Allowed** in POPL18/Cur, **Forbidden** in CurSI | `VW.vw_data_allowed`, `VW.vw_data_si_forbidden` | **KEY: decides F2** |
| `VW+ldaddl+dmb.st` | Forbidden | `VW.vw_dmbst_forbidden` | |
| `VW+ldaddl+dmb.sy` | Forbidden | `VW.vw_dmbsy_forbidden` | |
| `VW+ldaddl+stlr` | Forbidden | `VW.vw_stlr_forbidden` | |
| `VW-SeqLock+swpl` | Allowed | `VW.vw_seqlock_allowed` | all variants |
| `VW-SeqLock+swpal` | **Allowed** in POPL18/Cur, **Forbidden** in CurSI | `VW.vw_seqlock_allowed`, `VW.vw_seqlock_acq_si_forbidden` | **KEY: F1 and F2** |
| `VW-SeqLock+swpl+dmb.st` | Forbidden | `VW.vw_seqlock_dmbst_forbidden` | |
| `RT-get+swpl+dmb.st` | Allowed | `RTGet.rt_get_ldr_allowed` | reader side, M-15: `LDR z; LDR s` |
| `RT-get+swpl+dmb.st+ldar` | Allowed | `RTGet.rt_get_ldar_allowed` | LDAR orders later accesses, not earlier ones |
| `RT-get+swpl+dmb.st+ctrl` | Allowed | `RTGet.rt_get_ctrl_allowed` | `CBNZ` without ISB |
| `RT-get+swpl+dmb.st+ctrl+isb` | Forbidden | derivation only: ARMBar has no ISB; aarch64.cat's `(ctrl \| (addr; po)); [ISB]; po; [R]` | |
| `RT-get+swpl+dmb.st+dmb.ld` | Forbidden | `RTGet.rt_get_dmbld_forbidden` | |
| `MP-obj+ldadd` | **Forbidden** | `MPObj.mp_obj_forbidden` | read() = (0,0) after zr() = 1, TicketLock inlined; the DMB LD after get_ticket also orders the earlier z load before the data loads |
| `MP-obj+ldadd+stale-get` | Allowed | `MPObj.mp_obj_stale_get_allowed` | M-15 in a full run: get_ticket = 0 after zr() = 1, then a retry |
| `MP-obj+ldadd+dmb.ld` | Forbidden | `MPObj.mp_obj_forbidden` (with the prologue) | rmb at the start of read() |
| `MP-obj+ldadd+dmb.ld+stale-get` | Forbidden | `MPObj.mp_obj_prologue_stale_get_forbidden` | the prologue removes the stale get_ticket |

## Expected verdicts: x86 (`herd7 -model x86tso.cat`)

rmb and wmb are compiler barriers, so they produce no instruction. acq and rel
are `XCHG`.

| File | Expected | Source | Notes |
|---|---|---|---|
| `SB+rfi` | Allowed | Coq: `examples/Relaxed/SeqLockQ6Mem.v` `sbrfi_x86_trace` (a trace of the machine of `memory/TSO.v`) | Reviewer A's test |
| `SeqLockZ+rfi` | Allowed | derivation (`.rocq-review/buffered-cell-plan.md`, "Q6 status"); its cell image is `SeqLockQ6Mem.q6_cells_x86_trace`, where XCHG is a locked R;W;flush triple, which is itself a derivation | the Q6 outcome |
| `SeqLockZ+rfi-core` | Allowed | derivation: P0's store of z stays buffered | |
| `MP` | Forbidden | derivation: TSO keeps W→W and R→R | |
| `RSW+obj` | Forbidden | derivation: W x before W z (W→W), R z before R x (R→R) | |
| `AC+xchg` | Forbidden | derivation: XCHG drains the buffer | atomic clause |
| `VW+xchg` | Forbidden | derivation: XCHG writes s to memory before z is stored | version word |
| `VW-SeqLock+xchg` | Forbidden | derivation | version word |
| `RT-get+xchg` | Forbidden | derivation: the reader's loads stay in order, and XCHG writes s before z is stored | M-15 counterpart |
| `MP-obj+xchg` | Forbidden | derivation: W x before W z, R z before R x | |
| `MP-obj+xchg+stale-get` | Forbidden | derivation: acq's XCHG writes own = 1 before z is stored, and the loads stay in order | |

## What the results decide

- **`RSW+obj` (and `-core`)** settle G-3 (c). The Coq verdict is Forbidden in
  all three variants. The cycle uses only the `DMB ST` and `DMB LD` clauses.
  If herd7 says Allowed, the reading of those clauses in `ARMBar` is wrong.
- **`RSW+rel+acq`** confirms Mem.tex Δ2 against the shipped `aarch64.cat`.
- **The KEY tests** decide flag F2:
  - *All four Allowed*: the model is Cur.
  - *All four Forbidden*: the model is CurSI, at least for acquire RMWs. The
    read and the write of an RMW then act as one point in `ob`.
  - *A mixed result*, for example `VW+ldaddal` Forbidden but `VW+ldadda`
    Allowed: the AL clause would order the atomic's own write, contrary to its
    literal reading (F1). `ARMBar` would then need a fourth variant.

### The writer side (finding M-16; a module-trace argument, not a theorem)

A VW outcome says that an RMW's write can become visible after a later store of
the same thread. It refutes an atomic TicketLock specification only if the
module semantics orders that later store's invocation after the RMW's response.
That requires a `Wait` on the RMW, or a data dependency on its result
(`must_precede`, F3).

Otherwise the store may be invoked before the RMW responds: Rel and WrZ are
semi-independent, since dto(DRMW, DW) = false. A witness of the hybrid underlay
Hν can then place Rel after the observer's get_ticket.

- In the SeqLock as coded (`SeqLockProg.write`), the only such Wait is
  `Wait fa` on acq. The DMB ST that follows already orders acq's write before
  every later store. So `VW-SeqLock+swpl` does not by itself refute the atomic
  TicketLock.
- The genuine writer-side violation is `VW+ldadd+data` under Cur. F3 forces the
  dependent store after the RMW's response, and the store becomes visible
  before the RMW's write.
- Consequence for F-2: a publication point for RMWs (option R1 of the G-3.1
  report) may be unnecessary for the SeqLock. It would be needed only for code
  that waits on, or data-depends on, an RMW result and then publishes without
  a barrier.

### The reader side (finding M-15)

A client `while (zr() != 1) {}; read()` waits on zr. The module semantics
therefore invokes read, and so get_ticket, after zr's response.

ARMv8 does not order `LDR z` before get_ticket's `LDR own`. The `RT-get` tests
show this with an LDR get, an LDAR get, and a control dependency without ISB.

In a full run (`MP-obj+ldadd+stale-get`), get_ticket returns the value from
before acq, and the read retries. The SeqLock behaves correctly, and the
client-visible MP outcome is forbidden (`MP-obj+ldadd`): the DMB LD after
get_ticket also orders the z load. The stale get_ticket is removed by a DMB LD
at the start of read() (`MP-obj+ldadd+dmb.ld+stale-get`), or by ctrl+ISB
(derivation).

**Derivation (not kernel-checked; F-2 is to check it once Hν exists): Hν
rejects the underlay trace of the stale-get run.** In any Hν witness:

- Acq < wmb1, since dto(DRMW, Wmb) = true.
- wmb1 < wmb2 < WrZ, since dto(Wmb, Wmb) and dto(Wmb, DW) are true.
- WrZ is published before RdZ = 1, which reads the only write of 1 to z.
- RdZ < GT, by real time (the client's Wait).

So Acq < GT, and the atomic TicketLock answers GT ≥ 1. GT = 0 has no witness.

This is a failure of the underlay hypothesis on a correct SeqLock run, as for
the registers x and y in Q6-2. It is not a client-visible violation. Whether
ARMv8 is claimed is the author's decision:
- x86 only; or
- ARMv8 under a stated compilation scheme in which a Wait on a load compiles to
  a DMB LD, or ctrl+ISB, before the next underlay load.
