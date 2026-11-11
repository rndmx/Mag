/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Table.Groups
import AlgMag.Table.Link

/-! Table 1, `Spin4`: 0 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`.
Light version of `LinkRows` (see `Link_SL2`). -/

namespace AlgMag.Table
open AlgMag.Rooted
set_option maxRecDepth 100000

theorem Spin4_checkAll : Spin4.checkAll = true := by decide +kernel
theorem Spin4_repsG : Spin4.repsG.length = 0 := by decide +kernel

theorem Spin4_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin Spin4.n → ℤ) | ∃ w, Z = weylMagnet (Spin4.actG w) ∧
      weylMagnet (Spin4.actG w) ≠ weylMagnetLower Spin4.PhiG Spin4.actG w} = 0 :=
  (RD.nonRed_ncard Spin4_checkAll).trans Spin4_repsG

end AlgMag.Table

#print axioms AlgMag.Table.Spin4_nonRed_ncard
