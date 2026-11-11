/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Table.Groups
import AlgMag.Table.Link

/-! Table 1, `SL2`: 0 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`.
Light version of `LinkRows`: two kernel checks, then the generic bridge `RD.nonRed_ncard`
composed with `Eq.trans` (no `▸`, so the elaborator never unfolds the computation). -/

namespace AlgMag.Table
open AlgMag.Rooted
set_option maxRecDepth 100000

theorem SL2_checkAll : SL2.checkAll = true := by decide +kernel
theorem SL2_repsG : SL2.repsG.length = 0 := by decide +kernel

theorem SL2_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin SL2.n → ℤ) | ∃ w, Z = weylMagnet (SL2.actG w) ∧
      weylMagnet (SL2.actG w) ≠ weylMagnetLower SL2.PhiG SL2.actG w} = 0 :=
  (RD.nonRed_ncard SL2_checkAll).trans SL2_repsG

end AlgMag.Table

#print axioms AlgMag.Table.SL2_nonRed_ncard
