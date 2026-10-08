# An inductive approach to the Erdős–Hajnal property for fixed induced paths

**Yuwen Zhou** — University of British Columbia Okanagan  
Preprint, 7 October 2026.

The proof has been formally verified in Lean 4, relative to the published inputs listed
below. It has not yet been reviewed by specialists.

## Claim

For every integer s ≥ 1 there is δ_s > 0 such that every P_s-free graph G on n vertices
has a clique or a stable set of size at least n^{δ_s}. The same holds for graphs that
exclude the complement of P_s.

The proof is an induction on the path length. From EH(P_{s−1}) it derives the following,
in order:

1. a homogeneity statement for lightly mixed blocks, through a finite "forcing template";
2. rooted Tooth contracts T_5, T_6, …, T_{s−2} inside the fixed class of graphs whose
   complement is P_s-free;
3. a local oracle and generalized niceness, which give EH(P_s).

## What the result depends on

The final Lean theorem is

```lean
theorem AllPathsLocal.eh_all_paths
    (hRodl : ∀ s : ℕ, 7 ≤ s → RodlCo s) (hcomb : EHP6.NssComb) (hE6 : EHforPath 6) :
    ∀ s : ℕ, EHforPath s
```

It depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
Its three hypotheses are inputs taken from elsewhere:

| Hypothesis | Content | Source |
|---|---|---|
| `RodlCo s` (s ≥ 7) | Rödl's theorem for the complement of P_s, in maximum-degree form | Rödl 1986; Nguyen–Scott–Seymour VII, Thm 1.3 |
| `EHP6.NssComb` | the comb lemma | Nguyen–Scott–Seymour, *Induced subgraph density VII* ([arXiv:2312.15333](https://arxiv.org/abs/2312.15333)), Lemma 4.3 |
| `EHforPath 6` | EH(P_6) | Theorem A of [machine-qed/erdos-hajnal-six-vertex-path](https://github.com/machine-qed/erdos-hajnal-six-vertex-path/tree/v1.0-proof), tag v1.0-proof |

The theorem `eh_all_paths_of_rodl` fills in the last two hypotheses from the P6 project. It
therefore also depends on that project's three axioms: Rödl's theorem for the complement of
P_6 (`rodl_coP6`), EH(P_5) (`eh_P5`, NSS VII Thm 1.2), and the comb lemma (`nss_comb`).

**The P6 project is itself unrefereed.** Its source is included here unchanged (see below),
but it is not re-derived or re-verified independently.

A machine check proves that the Lean conclusion follows from the Lean hypotheses. Whether
those hypotheses say exactly what the cited papers prove needs a human reader. In particular:

- compare the constant 20 in `NssComb` with Lemma 4.3 of NSS VII;
- check that `RodlCo s` is what Rödl's theorem gives; its maximum-degree form follows from
  the edge-density form by deleting high-degree vertices;
- check the definitions `EHforPath`, `Free`, `pathGraph'`, `IsCliqueF` and `IsStableF`
  against the intended statement.

## Files

- `paper/All_paths_EH.pdf`, `paper/All_paths_EH.tex`: the manuscript (40 pages).
- `lean/`: the Lean 4 development.
  - `AllPaths*.lean`, `RP5*.lean`: the all-paths proof (137 files, 439 audited declarations).
  - `FinalAllLocal439.lean`: imports everything and prints the statements and axioms of the
    main theorems.
  - `AllPathsMain.lean`: the induction (`tooth_all`, `eh_path_step`, `eh_all_paths`).
  - `EHP6/`, `EHP6.lean`: the P6 base project, copied unchanged from
    machine-qed/erdos-hajnal-six-vertex-path at tag v1.0-proof (Apache-2.0, see
    `lean/EHP6/LICENSE`).
- `CHANGES.md`: revision notes.

## Building the Lean proof

Requirements: [elan](https://github.com/leanprover/elan). The toolchain is pinned in
`lean/lean-toolchain` (Lean 4.34.1), and mathlib is pinned to v4.34.1 in
`lean/lake-manifest.json`.

```sh
cd lean
lake exe cache get        # download prebuilt mathlib
lake build                # builds every module (default target AllPathsEH)
lake env lean FinalAllLocal439.lean   # prints statements and axioms
```

Expected output for the main theorem:

```
'AllPathsLocal.eh_all_paths' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The manuscript builds with `latexmk -pdf paper/All_paths_EH.tex`.

Generative AI (Claude) and Lean were used to produce the manuscript and the formalization.
The author is responsible for the contents.

## Feedback

Corrections, counterexamples, reports of build problems and pointers to errors are very
welcome. Please open an issue.
