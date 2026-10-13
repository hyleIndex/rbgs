# Iteration log: /rocq-loop

Append-only. Each `/rocq-loop` iteration adds one entry in the format given in `.claude/skills/rocq-loop/SKILL.md` (Step 11). Do not rewrite past entries. Record corrections as new entries.

## 2026-10-13 — setup — iteration 0 (baseline; no Rocq changes)

- **HEAD:** `dcccce0` (relaxed-lin), plus 19 uncommitted files (unchanged by this session).
- **Task:** create the Writer–Reviewer configuration and a baseline audit. No `.v` file was edited.
- **Files created:**
  - `.claude/agents/rocq-writer.md`
  - `.claude/agents/rocq-research-reviewer.md`
  - `.claude/skills/rocq-loop/SKILL.md`
  - `.rocq-review/{research-intent,concern-matrix,latest-review,iteration-log,popl2027-reviews}.md`
  - `.rocq-review/.gitignore`
  - `CLAUDE.md` (new; none existed)
- **Verification:**
  - Clean build with Rocq 9.2.0 / Stdlib 9.2.0 (from source) in a cloud container, with the uncommitted files overlaid: 171/171 files, 251 s at -j2.
  - No admits.
  - `Print Assumptions` of 109 key theorems ⊆ {`eq_rect_eq`, `classic`, `Parameter A` (3 view examples)}.
  - `rocqchk` crashes on `models/Sets.v`.
  - The author's machine was **not** built: the session's shell on that computer has no Rocq toolchain installed.
- **Review:** baseline by the orchestrator, not by `rocq-research-reviewer`. BLOCKER 4, MAJOR 9, MINOR 7. Verdict: continue; the RLHL judgement needs redesign.
- **Escalated to the author:** Q1–Q5 in `research-intent.md` §7, and the missing `claude/…` notes cited by `todo-oopsla.md`.
- **Concern-matrix rows changed:** all rows created.

## 2026-10-13 — author decisions (no Rocq changes)

- Scope fixed to oMCA. Priority: LatchSet + write snapshot, SeqLock on COH.
- Q1 clarified: the RLHL issue is the Coq encoding (one-path Wait rule, global queue equality, no rely, no soundness theorem) and the paper's existential OStep, not the paper's EStep rule. Recorded in research-intent.md §8; queue updated in concern-matrix.md §6.

