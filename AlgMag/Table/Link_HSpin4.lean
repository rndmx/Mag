/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Table.Groups
import AlgMag.Table.Link

/-! Table 1, `HSpin4`: 1 non-redundant Weyl magnet, in the sense of `joinIrreducibles_reductive`.
Light version of `LinkRows` (see `Link_SL2`). -/

namespace AlgMag.Table
open AlgMag.Rooted
set_option maxRecDepth 100000

theorem HSpin4_checkAll : HSpin4.checkAll = true := by decide +kernel
theorem HSpin4_repsG : HSpin4.repsG.length = 1 := by decide +kernel

theorem HSpin4_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin HSpin4.n → ℤ) | ∃ w, Z = weylMagnet (HSpin4.actG w) ∧
      weylMagnet (HSpin4.actG w) ≠ weylMagnetLower HSpin4.PhiG HSpin4.actG w} = 1 :=
  (RD.nonRed_ncard HSpin4_checkAll).trans HSpin4_repsG

end AlgMag.Table

#print axioms AlgMag.Table.HSpin4_nonRed_ncard
