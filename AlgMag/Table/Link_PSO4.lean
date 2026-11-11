/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Table.Groups
import AlgMag.Table.Link

/-! Table 1, `PSO4`: 2 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`.
Light version of `LinkRows` (see `Link_SL2`). -/

namespace AlgMag.Table
open AlgMag.Rooted
set_option maxRecDepth 100000

theorem PSO4_checkAll : PSO4.checkAll = true := by decide +kernel
theorem PSO4_repsG : PSO4.repsG.length = 2 := by decide +kernel

theorem PSO4_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin PSO4.n → ℤ) | ∃ w, Z = weylMagnet (PSO4.actG w) ∧
      weylMagnet (PSO4.actG w) ≠ weylMagnetLower PSO4.PhiG PSO4.actG w} = 2 :=
  (RD.nonRed_ncard PSO4_checkAll).trans PSO4_repsG

end AlgMag.Table

#print axioms AlgMag.Table.PSO4_nonRed_ncard
