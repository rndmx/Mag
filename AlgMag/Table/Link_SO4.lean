/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Table.Groups
import AlgMag.Table.Link

/-! Table 1, `SO4`: 1 non-redundant Weyl magnet, in the sense of `joinIrreducibles_reductive`.
Light version of `LinkRows` (see `Link_SL2`). -/

namespace AlgMag.Table
open AlgMag.Rooted
set_option maxRecDepth 100000

theorem SO4_checkAll : SO4.checkAll = true := by decide +kernel
theorem SO4_repsG : SO4.repsG.length = 1 := by decide +kernel

theorem SO4_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin SO4.n → ℤ) | ∃ w, Z = weylMagnet (SO4.actG w) ∧
      weylMagnet (SO4.actG w) ≠ weylMagnetLower SO4.PhiG SO4.actG w} = 1 :=
  (RD.nonRed_ncard SO4_checkAll).trans SO4_repsG

end AlgMag.Table

#print axioms AlgMag.Table.SO4_nonRed_ncard
