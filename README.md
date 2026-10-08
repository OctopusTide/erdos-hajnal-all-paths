# An inductive approach to the Erdős–Hajnal property for fixed induced paths

**Author:** Yuwen Zhou
**Status:** preprint, 7 October 2026. **Not refereed. No specialist has reviewed it yet.**
The argument has been formalized in Lean 4. The formal proof is conditional on the inputs
listed below. Its full build has so far been run only by the author.

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

## Verification status

| Item | Status |
|---|---|
| Whole chain from the three inputs to all s (Lean) | formalized: 0 `sorry`, 0 `admit`, no new axioms (`lean/AllPaths*.lean`, `lean/RP5*.lean`) |
| Build of `lean/` with Lean 4.34.1 and mathlib v4.34.1 | `lake build` completed (3664 jobs) in the author's cloud environment |
| Kernel replay (`leanchecker --fresh FinalAllLocal439`) | exit code 0 in the author's environment |
| Independent audit of statement fidelity (AI-assisted) | no escape hatches found; the points above were flagged for human checking |
| Review by a specialist | **not yet done** |
| Manuscript `paper/All_paths_EH.pdf` | previous draft; does **not** yet follow the formalized route (see below) |

### Where the formal proof differs from the manuscript

The Lean development proves the same theorem, but in a few places by a different route.
A revised manuscript that follows the formal route is in preparation.

1. **Terminal step.** The leaf-fibre / virality / product argument (App. J–K) is not used,
   so the Bucić–Fox–Pham EH ⇒ viral theorem is no longer an input. Instead, generalized
   niceness of a class is turned into polynomial homogeneous sets by the P6 project's
   argument (NSS VII round two, Crux, Lemma 8.1/8.2, polynomial Rödl). Its one P̄6-specific
   step, the house lemma, is replaced by the forcing-template homogeneity statement.
2. **No specialized RP6 step.** The appendices on RP6 frontiers and the RP6 tree are not
   used. T_6 comes from the general RPq recurrence, with T_4 taken from T_5: a root with no
   rooted P_4 has no rooted P_5.
3. **No Hayward theorem.** In the RP5 negative branch, partial transversals ordered by layer
   have no induced P_4 whose earliest vertex is an endpoint. A greedy ordered stable set then
   gives a proper colouring together with a clique of the same size, so αω ≥ |T|. Perfection
   of weakly chordal graphs is not used.
4. **Comb input.** Combs are extracted from NSS VII Lemma 4.3, as in the P6 project, and
   not from Huang–Ju–Zhou Lemma 2.10. The sparse-path input (NSS V, Statement 3.1) is
   proved in the P6 project rather than assumed.
5. **Smaller changes.** A forward tower construction homogenizes only consecutive fibres,
   and diagonal pairs in two-labelled lifts may be chosen independently. Integer constants
   are chosen for convenience and differ from the manuscript's.

## Files

- `paper/All_paths_EH.pdf`, `paper/All_paths_EH.tex`: the manuscript (previous draft, 40 pages).
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
