/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Table.Groups
import AlgMag.Table.Link

/-! Table 1, `PGL4`: 6 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`.
Light version of `LinkRows` (see `Link_SL2`). -/

namespace AlgMag.Table
open AlgMag.Rooted
set_option maxRecDepth 100000

theorem PGL4_checkAll : PGL4.checkAll = true := by decide +kernel
theorem PGL4_repsG : PGL4.repsG.length = 6 := by decide +kernel

theorem PGL4_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin PGL4.n → ℤ) | ∃ w, Z = weylMagnet (PGL4.actG w) ∧
      weylMagnet (PGL4.actG w) ≠ weylMagnetLower PGL4.PhiG PGL4.actG w} = 6 :=
  (RD.nonRed_ncard PGL4_checkAll).trans PGL4_repsG

end AlgMag.Table

#print axioms AlgMag.Table.PGL4_nonRed_ncard
