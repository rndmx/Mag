/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Table.Groups
import AlgMag.Table.Link

/-! Table 1, `SL4`: 0 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`.
Light version of `LinkRows` (see `Link_SL2`). -/

namespace AlgMag.Table
open AlgMag.Rooted
set_option maxRecDepth 100000

theorem SL4_checkAll : SL4.checkAll = true := by decide +kernel
theorem SL4_repsG : SL4.repsG.length = 0 := by decide +kernel

theorem SL4_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin SL4.n → ℤ) | ∃ w, Z = weylMagnet (SL4.actG w) ∧
      weylMagnet (SL4.actG w) ≠ weylMagnetLower SL4.PhiG SL4.actG w} = 0 :=
  (RD.nonRed_ncard SL4_checkAll).trans SL4_repsG

end AlgMag.Table

#print axioms AlgMag.Table.SL4_nonRed_ncard
