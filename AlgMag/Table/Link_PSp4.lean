/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Table.Groups
import AlgMag.Table.Link

/-! Table 1, `PSp4`: 2 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`.
Light version of `LinkRows` (see `Link_SL2`). -/

namespace AlgMag.Table
open AlgMag.Rooted
set_option maxRecDepth 100000

theorem PSp4_checkAll : PSp4.checkAll = true := by decide +kernel
theorem PSp4_repsG : PSp4.repsG.length = 2 := by decide +kernel

theorem PSp4_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin PSp4.n → ℤ) | ∃ w, Z = weylMagnet (PSp4.actG w) ∧
      weylMagnet (PSp4.actG w) ≠ weylMagnetLower PSp4.PhiG PSp4.actG w} = 2 :=
  (RD.nonRed_ncard PSp4_checkAll).trans PSp4_repsG

end AlgMag.Table

#print axioms AlgMag.Table.PSp4_nonRed_ncard
