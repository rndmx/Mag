/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Table.Groups
import AlgMag.Table.Link

/-! Table 1, `SL3`: 0 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`.
Light version of `LinkRows` (see `Link_SL2`). -/

namespace AlgMag.Table
open AlgMag.Rooted
set_option maxRecDepth 100000

theorem SL3_checkAll : SL3.checkAll = true := by decide +kernel
theorem SL3_repsG : SL3.repsG.length = 0 := by decide +kernel

theorem SL3_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin SL3.n → ℤ) | ∃ w, Z = weylMagnet (SL3.actG w) ∧
      weylMagnet (SL3.actG w) ≠ weylMagnetLower SL3.PhiG SL3.actG w} = 0 :=
  (RD.nonRed_ncard SL3_checkAll).trans SL3_repsG

end AlgMag.Table

#print axioms AlgMag.Table.SL3_nonRed_ncard
