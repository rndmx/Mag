/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Table.Groups
import AlgMag.Table.Link

/-! Table 1, `PGL3`: 1 non-redundant Weyl magnet, in the sense of `joinIrreducibles_reductive`.
Light version of `LinkRows` (see `Link_SL2`). -/

namespace AlgMag.Table
open AlgMag.Rooted
set_option maxRecDepth 100000

theorem PGL3_checkAll : PGL3.checkAll = true := by decide +kernel
theorem PGL3_repsG : PGL3.repsG.length = 1 := by decide +kernel

theorem PGL3_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin PGL3.n → ℤ) | ∃ w, Z = weylMagnet (PGL3.actG w) ∧
      weylMagnet (PGL3.actG w) ≠ weylMagnetLower PGL3.PhiG PGL3.actG w} = 1 :=
  (RD.nonRed_ncard PGL3_checkAll).trans PGL3_repsG

end AlgMag.Table

#print axioms AlgMag.Table.PGL3_nonRed_ncard
