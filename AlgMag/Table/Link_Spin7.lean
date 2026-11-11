/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Table.Groups
import AlgMag.Table.Link

/-! Table 1, `Spin7`: 1 non-redundant Weyl magnet, in the sense of `joinIrreducibles_reductive`.
Light version of `LinkRows` (see `Link_SL2`). -/

namespace AlgMag.Table
open AlgMag.Rooted
set_option maxRecDepth 100000

theorem Spin7_checkAll : Spin7.checkAll = true := by decide +kernel
theorem Spin7_repsG : Spin7.repsG.length = 1 := by decide +kernel

theorem Spin7_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin Spin7.n → ℤ) | ∃ w, Z = weylMagnet (Spin7.actG w) ∧
      weylMagnet (Spin7.actG w) ≠ weylMagnetLower Spin7.PhiG Spin7.actG w} = 1 :=
  (RD.nonRed_ncard Spin7_checkAll).trans Spin7_repsG

end AlgMag.Table

#print axioms AlgMag.Table.Spin7_nonRed_ncard
