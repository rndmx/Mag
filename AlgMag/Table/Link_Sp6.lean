/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Table.Groups
import AlgMag.Table.Link

/-! Table 1, `Sp6`: 0 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`.
Light version of `LinkRows` (see `Link_SL2`). -/

namespace AlgMag.Table
open AlgMag.Rooted
set_option maxRecDepth 100000

theorem Sp6_checkAll : Sp6.checkAll = true := by decide +kernel
theorem Sp6_repsG : Sp6.repsG.length = 0 := by decide +kernel

theorem Sp6_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin Sp6.n → ℤ) | ∃ w, Z = weylMagnet (Sp6.actG w) ∧
      weylMagnet (Sp6.actG w) ≠ weylMagnetLower Sp6.PhiG Sp6.actG w} = 0 :=
  (RD.nonRed_ncard Sp6_checkAll).trans Sp6_repsG

end AlgMag.Table

#print axioms AlgMag.Table.Sp6_nonRed_ncard
