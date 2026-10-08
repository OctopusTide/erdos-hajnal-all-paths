# Revision notes

## 7 October 2026 (evening): Lean formalization added

- Added `lean/`: a Lean 4 / mathlib (v4.34.1) formalization of the whole induction.
  `AllPathsLocal.eh_all_paths` proves EH(P_s) for every s from three displayed hypotheses:
  Rödl's theorem for the complement of P_s (s ≥ 7), the comb lemma (NSS VII Lemma 4.3) and
  EH(P_6). It uses only the standard axioms. The P6 base project
  (machine-qed/erdos-hajnal-six-vertex-path, v1.0-proof, Apache-2.0) is included unchanged
  under `lean/EHP6/`.
- The formal proof follows a modified route; README.md lists the differences. In short:
  - the leaf-fibre / virality / product terminal argument is replaced by the P6 project's
    niceness ⇒ EH chain, with the house lemma replaced by the forcing template;
  - the specialized RP6 appendices are replaced by the general RPq recurrence starting at
    q = 6;
  - Hayward's theorem is replaced by an ordered clique/colouring certificate;
  - combs come from NSS VII Lemma 4.3.
  The Bucić–Fox–Pham, Huang–Ju–Zhou and Hayward results are no longer inputs.
- README.md updated: dependencies, verification status, build instructions.
- The manuscript in `paper/` is unchanged (the previous draft). It does not yet follow
  the formalized route; a revised text is in preparation.

## 7 October 2026: revised draft

Numbering of theorems, lemmas and contracts is unchanged from the earlier draft.

### Mathematical corrections

1. **Contract 2.6** (sparse induced-path extraction): added `k ≥ 2` and `|J| ≥ z^{-2}`.
   Blocks are nonempty in this paper, so the source statement (which allows empty blocks)
   cannot be quoted without an order hypothesis. The hypothesis is verified at each of
   the three uses (proof of Theorem H.2, Appendix H.1, Appendix J.1).
2. **Weak vs. directed semisparsity**: Hypothesis H.1 (O2), Theorem H.2, Lemma I.1 and
   Appendix J.1 are stated for *weakly* semisparse blockades, which is what Section 10's
   all-clean branch supplies and all that the proofs use. (O3) and the clean-root
   condition stay directed.
3. **Host class**: Hypothesis H.1, Theorem H.2 and Lemma I.1 are stated for a fixed
   hereditary class C of co-P_h-free graphs, so that they apply both to Forb(co-P_s)
   and to the relative class C_{r,s}.
4. **Appendix G.5**: added the conversion of (L3) early blockade outputs to (F2), and
   the length/width check of the main output.
5. **Lemma B.1 / Theorem D.1**: the degree bound ε(|T|−1) and "partial transversal" are
   now explicit in the statements; the container encoding in D.1 states its stopping rule.
6. Smaller points: parameter range in Lemma A.1; location of output sets in T2/T3,
   (L2)/(L3), Lemmas E.1 and G.1; self-contained hypothesis of Lemma G.1; `m ≥ m_0`
   in Theorem G.2; corrected numerical closure in C.8.
7. The introduction states that the main theorem is conditional on the unrefereed
   EH(P_6) result.

### Presentation

Substitution arrow, implication arrows, subscripted constants, numbered key displays
(A.1, G.1–G.5, H.1–H.3, K.1–K.2), local size cutoff renamed `s_cut`, output lists set as
enumerations, path notation, calligraphic ambient class, a definition of generalized
niceness before Lemma I.1, uniform spelling, bibliography URLs.
