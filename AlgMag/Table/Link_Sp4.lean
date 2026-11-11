/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Table.Groups
import AlgMag.Table.Link

/-! Table 1, `Sp4`: 0 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`.
Light version of `LinkRows` (see `Link_SL2`). -/

namespace AlgMag.Table
open AlgMag.Rooted
set_option maxRecDepth 100000

theorem Sp4_checkAll : Sp4.checkAll = true := by decide +kernel
theorem Sp4_repsG : Sp4.repsG.length = 0 := by decide +kernel

theorem Sp4_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin Sp4.n → ℤ) | ∃ w, Z = weylMagnet (Sp4.actG w) ∧
      weylMagnet (Sp4.actG w) ≠ weylMagnetLower Sp4.PhiG Sp4.actG w} = 0 :=
  (RD.nonRed_ncard Sp4_checkAll).trans Sp4_repsG

end AlgMag.Table

#print axioms AlgMag.Table.Sp4_nonRed_ncard
