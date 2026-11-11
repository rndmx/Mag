/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Table.Groups
import AlgMag.Table.Link

/-! Table 1, `SO5`: 2 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`.
Light version of `LinkRows` (see `Link_SL2`). -/

namespace AlgMag.Table
open AlgMag.Rooted
set_option maxRecDepth 100000

theorem SO5_checkAll : SO5.checkAll = true := by decide +kernel
theorem SO5_repsG : SO5.repsG.length = 2 := by decide +kernel

theorem SO5_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin SO5.n → ℤ) | ∃ w, Z = weylMagnet (SO5.actG w) ∧
      weylMagnet (SO5.actG w) ≠ weylMagnetLower SO5.PhiG SO5.actG w} = 2 :=
  (RD.nonRed_ncard SO5_checkAll).trans SO5_repsG

end AlgMag.Table

#print axioms AlgMag.Table.SO5_nonRed_ncard
