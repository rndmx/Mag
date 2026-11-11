/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Table.Groups
import AlgMag.Table.Link

/-! Table 1, `G2`: 1 non-redundant Weyl magnet, in the sense of `joinIrreducibles_reductive`.
Light version of `LinkRows` (see `Link_SL2`). -/

namespace AlgMag.Table
open AlgMag.Rooted
set_option maxRecDepth 100000

theorem G2_checkAll : G2.checkAll = true := by decide +kernel
theorem G2_repsG : G2.repsG.length = 1 := by decide +kernel

theorem G2_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin G2.n → ℤ) | ∃ w, Z = weylMagnet (G2.actG w) ∧
      weylMagnet (G2.actG w) ≠ weylMagnetLower G2.PhiG G2.actG w} = 1 :=
  (RD.nonRed_ncard G2_checkAll).trans G2_repsG

end AlgMag.Table

#print axioms AlgMag.Table.G2_nonRed_ncard
