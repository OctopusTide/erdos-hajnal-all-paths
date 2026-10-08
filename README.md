# An inductive approach to the Erdős–Hajnal property for fixed induced paths

**Author:** Yuwen Zhou  
**Status:** preprint draft, 7 October 2026. **Not refereed. Not fully verified.**

## Claim

For every integer s ≥ 1 there is δ_s > 0 such that every P_s-free graph G on n vertices
has a clique or stable set of size at least n^{δ_s}; the same holds for graphs excluding
the complement of P_s.

The manuscript gives an induction on the path length: from EH(P_{s−1}) it derives a strong
"wonderfulness" statement for P_s, a family of rooted Tooth statements inside the fixed
class Forb(P_s), and then EH(P_s).

## What this result depends on

- **Base case.** EH(P_6) is taken from Theorem A of
  [machine-qed/erdos-hajnal-six-vertex-path](https://github.com/machine-qed/erdos-hajnal-six-vertex-path/tree/v1.0-proof)
  (v1.0-proof). That proof is a Lean 4 formalization conditional on three literature
  results (Rödl's theorem for the complement of P_6, EH(P_5), and a comb lemma of
  Nguyen–Scott–Seymour). It is itself unrefereed. Nothing here re-verifies it.
- **Cited inputs.** Fixed-precision Rödl; sparse induced-path extraction
  (Nguyen–Scott–Seymour, arXiv:2307.15032, Statement 3.1); EH ⇒ viral
  (Bucić–Fox–Pham, arXiv:2403.08303); comb extraction (Huang–Ju–Zhou, arXiv:2606.06258,
  Lemma 2.10); weakly chordal graphs are perfect (Hayward 1985).

## Verification status — please read before relying on anything

| Part of the manuscript | Formal (Lean 4) | Text review |
|---|---|---|
| App. A, general Tooth lemma | formalized | read line by line |
| App. B, thin-layer sampling | formalized, conditional on perfection of partial transversals (Hayward) | read line by line |
| App. C, RP5 Tooth | clean / frontier / positive branches formalized; negative branch not yet integrated | read line by line |
| App. D–G (EH bridge, RP6, RPq recurrence) | **not formalized** | read line by line |
| Part I, Sections 7–12, App. H–K, final induction | **not formalized** | read |

The text review was carried out with AI assistance (several independent adversarial
passes that recomputed the inequalities and looked for counterexamples). It found no
fatal error, but **an AI reading is not a proof check**, and no specialist in the area
has read the manuscript yet. The all-paths theorem should be regarded as **unverified**.

Generative AI and Lean were used in producing the manuscript. The author is responsible
for its contents.

## Files

- `paper/All_paths_EH.pdf` — the manuscript (40 pages).
- `paper/All_paths_EH.tex` — standalone LaTeX source (`article`, standard packages).
- `CHANGES.md` — what was corrected in the last two revision rounds.

Build: `tectonic -X compile paper/All_paths_EH.tex` or `latexmk -xelatex paper/All_paths_EH.tex`.

## Feedback

Corrections, counterexamples and pointers to errors are very welcome — please open an issue.
