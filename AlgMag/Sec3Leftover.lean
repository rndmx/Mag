/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Leftover328
import AlgMag.Sec3Leftover33
import AlgMag.Sec3Leftover26
import AlgMag.Sec3Leftover26Sh
import AlgMag.Sec3Leftover12
import AlgMag.Sec3Leftover313
import AlgMag.Sec3LeftoverFace
import AlgMag.Sec3Leftover221Eq

/-!
# Algebraic Magnetism, §§2-3: leftovers

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026).

* Proposition 3.28 over an arbitrary scheme: `AlgMag.VB.vAction`, `AlgMag.VB.vAttractorEquiv` (functor
  of points) and, in `Sec3Leftover328V` (needs the full Stacks build), `AlgMag.VB.prop328`.
* Example 3.33 as printed: `AlgMag.GB.ex333_axis_points`, `ex333_zero_points`, `ex333_iter`.
* Example 3.21 on points: `AlgMag.GB.exists_att_A_iff`.
* Fact 2.6: `AlgMag.OverB.flat_str`, `isFlat_pr`, `exists_affine_chart_pr`.
* Fact 2.6 (i), `q_* 𝒪 (U) = 𝒪_S(U)[N]`, `U` affine open: `AlgMag.GB.fact26_i_sections`.
* Example 1.2 over an arbitrary scheme: `AlgMag.VB.ex12_general`.
* Remark 3.13, second assertion, `X` affine over `S`: `AlgMag.GB.rem313`.
* Fact 3.16 for algebraic spaces: `AlgMag.fact316_spaces`. Definition 2.11: `AlgMag.OverB.eS`, `eB`.
* Definition 2.20 with `W(F) = p^* F`: `AlgMag.W.AModule`, in `Sec3LeftoverW` (needs one more Stacks module).
-/
