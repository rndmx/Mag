/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Table.Groups
import AlgMag.Table.Link

/-! Table 1, `PSp6`: 7 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`.
Light version of `LinkRows` (see `Link_SL2`). -/

namespace AlgMag.Table
open AlgMag.Rooted
set_option maxRecDepth 100000

theorem PSp6_checkAll : PSp6.checkAll = true := by decide +kernel
theorem PSp6_repsG : PSp6.repsG.length = 7 := by decide +kernel

theorem PSp6_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin PSp6.n → ℤ) | ∃ w, Z = weylMagnet (PSp6.actG w) ∧
      weylMagnet (PSp6.actG w) ≠ weylMagnetLower PSp6.PhiG PSp6.actG w} = 7 :=
  (RD.nonRed_ncard PSp6_checkAll).trans PSp6_repsG

end AlgMag.Table

#print axioms AlgMag.Table.PSp6_nonRed_ncard
