/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Table.Groups
import AlgMag.Table.Link

/-! Table 1, `SO7`: 3 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`.
Light version of `LinkRows` (see `Link_SL2`). -/

namespace AlgMag.Table
open AlgMag.Rooted
set_option maxRecDepth 100000

theorem SO7_checkAll : SO7.checkAll = true := by decide +kernel
theorem SO7_repsG : SO7.repsG.length = 3 := by decide +kernel

theorem SO7_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin SO7.n → ℤ) | ∃ w, Z = weylMagnet (SO7.actG w) ∧
      weylMagnet (SO7.actG w) ≠ weylMagnetLower SO7.PhiG SO7.actG w} = 3 :=
  (RD.nonRed_ncard SO7_checkAll).trans SO7_repsG

end AlgMag.Table

#print axioms AlgMag.Table.SO7_nonRed_ncard
