/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Table.Groups
import AlgMag.Table.Link

/-! Table 1, `SL4mu2`: 3 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`.
Light version of `LinkRows` (see `Link_SL2`). -/

namespace AlgMag.Table
open AlgMag.Rooted
set_option maxRecDepth 100000

theorem SL4mu2_checkAll : SL4mu2.checkAll = true := by decide +kernel
theorem SL4mu2_repsG : SL4mu2.repsG.length = 3 := by decide +kernel

theorem SL4mu2_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin SL4mu2.n → ℤ) | ∃ w, Z = weylMagnet (SL4mu2.actG w) ∧
      weylMagnet (SL4mu2.actG w) ≠ weylMagnetLower SL4mu2.PhiG SL4mu2.actG w} = 3 :=
  (RD.nonRed_ncard SL4mu2_checkAll).trans SL4mu2_repsG

end AlgMag.Table

#print axioms AlgMag.Table.SL4mu2_nonRed_ncard
