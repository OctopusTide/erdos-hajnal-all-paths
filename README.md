# The Erdős–Hajnal property for paths

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23270286.svg)](https://doi.org/10.5281/zenodo.23270286)

**Yuwen Zhou** — University of British Columbia Okanagan

## Main result

For every integer s ≥ 1 there is δ_s > 0 such that every P_s-free graph G on n vertices
has a clique or a stable set of size at least n^{δ_s}. The same holds for graphs that
exclude the complement of P_s.

The proof is an induction on the path length. From EH(P_{s−1}) it derives, in order:

1. a homogeneity statement for lightly mixed blocks, through a finite "forcing template";
2. rooted Tooth contracts T_5, T_6, …, T_{s−2} inside the fixed class of graphs whose
   complement is P_s-free;
3. a local oracle and generalized niceness, which give EH(P_s).

## Formal verification

The result is formalized in Lean 4 with Mathlib. The main theorem is

```lean
theorem AllPathsLocal.eh_all_paths
    (hRodl : ∀ s : ℕ, 7 ≤ s → RodlCo s) (hcomb : EHP6.NssComb) (hE6 : EHforPath 6) :
    ∀ s : ℕ, EHforPath s
```

and it depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
Its hypotheses are:

| Hypothesis | Content | Source |
|---|---|---|
| `RodlCo s` (s ≥ 7) | Rödl's theorem for the complement of P_s | Rödl 1986; Nguyen–Scott–Seymour VII, Thm 1.3 |
| `EHP6.NssComb` | the comb lemma | Nguyen–Scott–Seymour, *Induced subgraph density VII* ([arXiv:2312.15333](https://arxiv.org/abs/2312.15333)), Lemma 4.3 |
| `EHforPath 6` | EH(P_6) | [machine-qed/erdos-hajnal-six-vertex-path](https://github.com/machine-qed/erdos-hajnal-six-vertex-path/tree/v1.0-proof), Theorem A |

`eh_all_paths_of_rodl` fills in the last two from the P6 project, whose axioms are Rödl's
theorem for the complement of P_6, EH(P_5) (NSS VII, Thm 1.2) and the comb lemma.

## Repository

- `paper/` — the manuscript (`ErdosHajnalPaths.pdf`, `ErdosHajnalPaths.tex`).
- `lean/` — the Lean 4 development.
  - `AllPathsMain.lean` — the induction (`tooth_all`, `eh_path_step`, `eh_all_paths`).
  - `AllPaths*.lean`, `RP5*.lean` — the rest of the proof.
  - `FinalAllLocal439.lean` — imports everything and prints the main statements and axioms.
  - `EHP6/`, `EHP6.lean` — the P6 project, unchanged from tag v1.0-proof (Apache-2.0, see
    `lean/EHP6/LICENSE`).
- `CHANGES.md` — revision notes.

## Building

Lean (toolchain and Mathlib v4.34.1 are pinned in `lean/`; requires
[elan](https://github.com/leanprover/elan)):

```sh
cd lean
lake exe cache get
lake build
lake env lean FinalAllLocal439.lean   # prints statements and axioms
```

Paper: `latexmk -pdf paper/ErdosHajnalPaths.tex`.

## Citation

```bibtex
@misc{Zhou2026ErdosHajnalPaths,
  author    = {Zhou, Yuwen},
  title     = {The {Erd\H{o}s}--{Hajnal} property for paths},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.23270286},
  url       = {https://doi.org/10.5281/zenodo.23270286},
  note      = {Preprint}
}
```

## Notes

This is a preprint and has not yet been peer reviewed. Comments and corrections are welcome;
please open an issue.

Generative AI (Claude) was used in writing the manuscript and the Lean formalization.
