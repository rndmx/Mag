/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Table.Groups
import AlgMag.Table.Link

/-! Table 1, `Spin5`: 0 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`.
Light version of `LinkRows` (see `Link_SL2`). -/

namespace AlgMag.Table
open AlgMag.Rooted
set_option maxRecDepth 100000

theorem Spin5_checkAll : Spin5.checkAll = true := by decide +kernel
theorem Spin5_repsG : Spin5.repsG.length = 0 := by decide +kernel

theorem Spin5_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin Spin5.n → ℤ) | ∃ w, Z = weylMagnet (Spin5.actG w) ∧
      weylMagnet (Spin5.actG w) ≠ weylMagnetLower Spin5.PhiG Spin5.actG w} = 0 :=
  (RD.nonRed_ncard Spin5_checkAll).trans Spin5_repsG

end AlgMag.Table

#print axioms AlgMag.Table.Spin5_nonRed_ncard
