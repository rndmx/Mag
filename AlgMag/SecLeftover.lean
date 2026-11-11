/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SecLeftoverFPR
import AlgMag.SecLeftover1615
import AlgMag.SecLeftover158
import AlgMag.SecLeftoverQCoh
import AlgMag.SecLeftoverQCohB
import AlgMag.SecLeftover1510

/-!
# Leftover statements of §§6, 9, 15, 16 of *Algebraic Magnetism*

Corrected statements:

* **Remark 6.5.** Printed: `S = Spec ℤ`, `U = D(ℤ/2)`, "`U → S` is smooth of relative dimension zero and
  so it is étale". This is false at the prime `2` (`AlgMag.Leftover.not_etale_printed_rem65`). Corrected:
  `|M|` invertible on `S`, for instance `S = Spec ℤ[1/2]` (`rem65`, `rem65_zmod2`).
* **Remark 6.6.** Printed: `Z ≠ M`, `M/Z` finite, "`f : D(M) → D(Z)` is étale" and
  "`U^{D(M)} = X^{D(M)} = ∅`". Corrected (`rem66`): `[M : Z]` invertible on `S`, needed for étale, and
  `Z ≠ 0`, needed for `X^{D(M)} = ∅`: for `Z = 0`, `X = S` has `X^{D(M)} = X`. `M` finitely generated is
  added, for finite presentation of `R[M]` over `R[Z]`.
* **Proposition 16.15 (ii).** `prop1615_ii`, as printed, with the attractors assumed to be schemes
  (as in Corollary 11.10 for schemes).
  For algebraic spaces: `prop1615_ii_spaces` in `AlgMag.SecLeftover1615Spaces` (not imported here),
  with the attractors assumed to be algebraic spaces.
* **Example 15.10 (ii).** `ex1510_ii`, `S` any nonempty scheme.
* **Remark 15.8.** `rem158_printed`, with Conjecture 6.9 (ii) as printed; `S` quasi-compact.
* **Quasi-coherent modules, §9.** `isQCoh_assocPMod`: a Stacks quasi-coherent module on a scheme `S`
  gives an `AlgMag.S9.IsQCoh` module. `isQCoh_restr`: a module with `AlgMag.S9.IsQCoh` on `Over Y`
  restricts to one with `AlgMag.S9B.IsQCoh` on `SB Bsp`, given a natural map from the objects to `Y`.
-/
