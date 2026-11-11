/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Table.Groups
import AlgMag.Table.Link

/-! Table 1, `PGL2`: 1 non-redundant Weyl magnet, in the sense of `joinIrreducibles_reductive`.
Light version of `LinkRows` (see `Link_SL2`). -/

namespace AlgMag.Table
open AlgMag.Rooted
set_option maxRecDepth 100000

theorem PGL2_checkAll : PGL2.checkAll = true := by decide +kernel
theorem PGL2_repsG : PGL2.repsG.length = 1 := by decide +kernel

theorem PGL2_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin PGL2.n → ℤ) | ∃ w, Z = weylMagnet (PGL2.actG w) ∧
      weylMagnet (PGL2.actG w) ≠ weylMagnetLower PGL2.PhiG PGL2.actG w} = 1 :=
  (RD.nonRed_ncard PGL2_checkAll).trans PGL2_repsG

end AlgMag.Table

#print axioms AlgMag.Table.PGL2_nonRed_ncard
