# Next week: get the paper onto arXiv

Goal: post the current work as a preprint. arXiv is **not** prior
publication for PLDI, OOPSLA or POPL, so this costs nothing in venue
eligibility and buys priority in a field that produced five relevant
papers in twelve months. Check the specific CFP before submitting later
— double-blind venues typically ask you not to *publicize* during
review, but posting is fine.

Not in scope this week: the GPU work (Path A), and the remaining Coq
items. Neither blocks the preprint. See the bottom of this file.

---

## Blockers — the preprint should not go up without these

### 1. The artifact link points at code that does not exist yet
`paper/layout-algebra.tex:2140` footnotes
`https://github.com/annp0/simplified-layout`. `origin/main` is at
`3e9b63b`: no `coq/`, no `study/`, no generated numbers. A reader who
follows the link sees none of what the paper claims.

**Decision needed:** merge `paper-integration` into `main`, or retarget
the footnote at the branch. Merging is cleaner; the branch is 9 commits
and the two parent branches (`reproducible-eval-numbers`,
`coq-formalization`) are still local if you want to split it into
reviewable PRs first.

### 2. Author list
The paper lists Nan An alone (`layout-algebra.tex:50`). **Decision
needed** on whether this is right for the preprint.

### 3. Date is stale
`\date{September 9, 2026}` — pin it to the posting date.

### 4. The abstract undersells two of the three contributions
It mentions Coq once, at the end, and does not mention the CuTe
measurement at all. As of now the contributions are:
  - the algebra, and the conditions it dissolves;
  - a decision procedure, mechanized end to end and extracted, agreeing
    with the implementation on 186,293 maps;
  - a measurement showing CuTe's conditions are unchecked and fail
    silently.
The abstract should say all three. Also update "roughly 1,000 lines of
OCaml" — there are ~1,960 lines of Coq alongside it now.

### 5. Section 9 reads as unfinished
"The DSL this serves" is six lines promising a system that does not
exist. To a reviewer — and to anyone reading the preprint — that signals
an incomplete paper.

**Decision needed:** cut it, or fold one sentence into the conclusion.
Recommend cutting.

---

## Should do — worth the time before posting

### 6. Related work needs depth, not coverage
All the right papers are cited and each gets a sentence or two. What is
missing is the *delta*, and this is the part most likely to be attacked,
by reviewers and by the preprint's own readers:

- **Axe** is the biggest novelty threat. The paper already concedes that
  its Appendix A.2.1 uses the same floor expansion and first differences
  — but the concession is a trailing clause in a long sentence. Move it
  up and state precisely what is ours: existence *decided* for an
  arbitrary map on a finite box, in linear time, with a fallback when
  the answer is no, versus uniqueness of a normalized form assuming one
  exists.
- **Linear layouts** deserve the strongest available defence, which the
  section does not currently make: $\mathbb{F}_2$ cannot represent
  non-power-of-2 modes at all, and size-3 and size-6 modes appear
  throughout the tests. Give a concrete example from a real kernel.
- A **capability table** would carry all of this compactly: rows for
  CuTe / Shah / Carlisle / linear layouts / ISL / Axe / this work,
  columns for non-power-of-2, replication, swizzle, decides-composite-
  is-a-layout, generic conversion, solver-free.

### 7. Point the paper at the reproduction instructions
`README.md` documents `paper/eval.sh`, `coq/extract.sh`, `study/run.sh`
and their `--check` modes. The paper should say so where it quotes
generated figures, so a reader knows the numbers regenerate.

### 8. arXiv metadata
Categories (cs.PL primary; cs.DC or cs.MS secondary) and a license.
**Decision needed** on the license.

---

## If there is time

- **Composition sweep**, the counterpart of `study/complement_sweep.cpp`.
  Composition has four conditions to complement's two, and its runtime
  assertion for the dynamic case is commented out entirely, so the
  dynamic path is wholly unguarded. Likely a richer result than the
  complement sweep. Classify on all four conditions from the start —
  the complement sweep initially classified on one of two and had to be
  redone.
- An architecture figure. The paper has no diagram of the pipeline from
  layout to emitted expression.

---

## Pre-flight

All four must pass, in two different opam switches:

    eval $(opam env --switch=$PWD)          # project deps
    dune test
    ./paper/eval.sh --check
    ./coq/extract.sh --check

    eval $(opam env --switch=vst-audit)     # Coq
    make -C coq

and, with CUTLASS and CCCL checkouts:

    CUTLASS_DIR=... CCCL_DIR=... ./study/run.sh --check

Then rebuild the PDF and confirm every generated macro resolved — a
missing `\input` shows up as `??` rather than an error.

---

## Deliberately deferred

**Path A (the GPU work).** Not needed for the preprint; needed for PLDI.
Three tiers, only one of which needs a GPU:
  - *no CUDA at all* — source-level CUTLASS study. Done, and `study/`
    shows the rest can be done here too.
  - *CUDA toolkit, no device* — `ptxas -v` register and instruction
    counts, `cuobjdump` for the SASS. This is most of the evidence, and
    it needs only a machine with the toolkit installed.
  - *a real GPU* — the timed GEMM mainloop against a CUTLASS baseline.

**Remaining Coq.** Coarsest-chain minimality; `s_j = g(w_j)`; the
nested-to-flat shape regrouping; mode permutation for Lemma 1. All
listed in `coq/README.md`. The decision procedure is proved and
extracted without them.
