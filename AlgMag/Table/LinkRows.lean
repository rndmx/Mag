/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Table.Groups
import AlgMag.Table.Link

/-!
# Table 1, column "non-redundant Weyl magnets", as a statement about `weylMagnet`

For each root datum `G` of rank ≤ 3: `Set.ncard {Z | ∃ w, Z = Z_w ∧ Z_w ≠ weylMagnetLower Φ act w}`
equals the table entry, with `Z_w = weylMagnet (act w)` and `weylMagnetLower` from
`AlgMag/Rooted/MinimalRootReductive.lean` (so, by `joinIrreducibles_reductive`, the minimal root has
`|Φ|` + this many elements). The certificate check `checkAll` and the count are evaluated by the
kernel (`decide +kernel`); `RD.nonRed_ncard` is the verified bridge. `numNonRed_eq` ties the
count to the column function `RD.numNonRed` of `AlgMag.Table.Rows`.
-/

namespace AlgMag.Table

open AlgMag.Rooted

set_option maxRecDepth 100000

theorem SL2_checkAll : SL2.checkAll = true := by decide +kernel
theorem SL2_repsG : SL2.repsG.length = 0 := by decide +kernel
theorem SL2_numNonRed_eq : SL2.numNonRed = SL2.repsG.length := by decide +kernel
/-- Table 1, `SL2`: 0 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`. -/
theorem SL2_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin SL2.n → ℤ) | ∃ w, Z = weylMagnet (SL2.actG w) ∧
      weylMagnet (SL2.actG w) ≠ weylMagnetLower SL2.PhiG SL2.actG w} = 0 :=
  SL2_repsG ▸ RD.nonRed_ncard SL2_checkAll

theorem PGL2_checkAll : PGL2.checkAll = true := by decide +kernel
theorem PGL2_repsG : PGL2.repsG.length = 1 := by decide +kernel
theorem PGL2_numNonRed_eq : PGL2.numNonRed = PGL2.repsG.length := by decide +kernel
/-- Table 1, `PGL2`: 1 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`. -/
theorem PGL2_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin PGL2.n → ℤ) | ∃ w, Z = weylMagnet (PGL2.actG w) ∧
      weylMagnet (PGL2.actG w) ≠ weylMagnetLower PGL2.PhiG PGL2.actG w} = 1 :=
  PGL2_repsG ▸ RD.nonRed_ncard PGL2_checkAll

theorem SL3_checkAll : SL3.checkAll = true := by decide +kernel
theorem SL3_repsG : SL3.repsG.length = 0 := by decide +kernel
theorem SL3_numNonRed_eq : SL3.numNonRed = SL3.repsG.length := by decide +kernel
/-- Table 1, `SL3`: 0 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`. -/
theorem SL3_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin SL3.n → ℤ) | ∃ w, Z = weylMagnet (SL3.actG w) ∧
      weylMagnet (SL3.actG w) ≠ weylMagnetLower SL3.PhiG SL3.actG w} = 0 :=
  SL3_repsG ▸ RD.nonRed_ncard SL3_checkAll

theorem PGL3_checkAll : PGL3.checkAll = true := by decide +kernel
theorem PGL3_repsG : PGL3.repsG.length = 1 := by decide +kernel
theorem PGL3_numNonRed_eq : PGL3.numNonRed = PGL3.repsG.length := by decide +kernel
/-- Table 1, `PGL3`: 1 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`. -/
theorem PGL3_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin PGL3.n → ℤ) | ∃ w, Z = weylMagnet (PGL3.actG w) ∧
      weylMagnet (PGL3.actG w) ≠ weylMagnetLower PGL3.PhiG PGL3.actG w} = 1 :=
  PGL3_repsG ▸ RD.nonRed_ncard PGL3_checkAll

theorem Spin5_checkAll : Spin5.checkAll = true := by decide +kernel
theorem Spin5_repsG : Spin5.repsG.length = 0 := by decide +kernel
theorem Spin5_numNonRed_eq : Spin5.numNonRed = Spin5.repsG.length := by decide +kernel
/-- Table 1, `Spin5`: 0 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`. -/
theorem Spin5_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin Spin5.n → ℤ) | ∃ w, Z = weylMagnet (Spin5.actG w) ∧
      weylMagnet (Spin5.actG w) ≠ weylMagnetLower Spin5.PhiG Spin5.actG w} = 0 :=
  Spin5_repsG ▸ RD.nonRed_ncard Spin5_checkAll

theorem SO5_checkAll : SO5.checkAll = true := by decide +kernel
theorem SO5_repsG : SO5.repsG.length = 2 := by decide +kernel
theorem SO5_numNonRed_eq : SO5.numNonRed = SO5.repsG.length := by decide +kernel
/-- Table 1, `SO5`: 2 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`. -/
theorem SO5_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin SO5.n → ℤ) | ∃ w, Z = weylMagnet (SO5.actG w) ∧
      weylMagnet (SO5.actG w) ≠ weylMagnetLower SO5.PhiG SO5.actG w} = 2 :=
  SO5_repsG ▸ RD.nonRed_ncard SO5_checkAll

theorem Sp4_checkAll : Sp4.checkAll = true := by decide +kernel
theorem Sp4_repsG : Sp4.repsG.length = 0 := by decide +kernel
theorem Sp4_numNonRed_eq : Sp4.numNonRed = Sp4.repsG.length := by decide +kernel
/-- Table 1, `Sp4`: 0 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`. -/
theorem Sp4_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin Sp4.n → ℤ) | ∃ w, Z = weylMagnet (Sp4.actG w) ∧
      weylMagnet (Sp4.actG w) ≠ weylMagnetLower Sp4.PhiG Sp4.actG w} = 0 :=
  Sp4_repsG ▸ RD.nonRed_ncard Sp4_checkAll

theorem PSp4_checkAll : PSp4.checkAll = true := by decide +kernel
theorem PSp4_repsG : PSp4.repsG.length = 2 := by decide +kernel
theorem PSp4_numNonRed_eq : PSp4.numNonRed = PSp4.repsG.length := by decide +kernel
/-- Table 1, `PSp4`: 2 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`. -/
theorem PSp4_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin PSp4.n → ℤ) | ∃ w, Z = weylMagnet (PSp4.actG w) ∧
      weylMagnet (PSp4.actG w) ≠ weylMagnetLower PSp4.PhiG PSp4.actG w} = 2 :=
  PSp4_repsG ▸ RD.nonRed_ncard PSp4_checkAll

theorem Spin4_checkAll : Spin4.checkAll = true := by decide +kernel
theorem Spin4_repsG : Spin4.repsG.length = 0 := by decide +kernel
theorem Spin4_numNonRed_eq : Spin4.numNonRed = Spin4.repsG.length := by decide +kernel
/-- Table 1, `Spin4`: 0 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`. -/
theorem Spin4_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin Spin4.n → ℤ) | ∃ w, Z = weylMagnet (Spin4.actG w) ∧
      weylMagnet (Spin4.actG w) ≠ weylMagnetLower Spin4.PhiG Spin4.actG w} = 0 :=
  Spin4_repsG ▸ RD.nonRed_ncard Spin4_checkAll

theorem SO4_checkAll : SO4.checkAll = true := by decide +kernel
theorem SO4_repsG : SO4.repsG.length = 1 := by decide +kernel
theorem SO4_numNonRed_eq : SO4.numNonRed = SO4.repsG.length := by decide +kernel
/-- Table 1, `SO4`: 1 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`. -/
theorem SO4_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin SO4.n → ℤ) | ∃ w, Z = weylMagnet (SO4.actG w) ∧
      weylMagnet (SO4.actG w) ≠ weylMagnetLower SO4.PhiG SO4.actG w} = 1 :=
  SO4_repsG ▸ RD.nonRed_ncard SO4_checkAll

theorem PSO4_checkAll : PSO4.checkAll = true := by decide +kernel
theorem PSO4_repsG : PSO4.repsG.length = 2 := by decide +kernel
theorem PSO4_numNonRed_eq : PSO4.numNonRed = PSO4.repsG.length := by decide +kernel
/-- Table 1, `PSO4`: 2 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`. -/
theorem PSO4_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin PSO4.n → ℤ) | ∃ w, Z = weylMagnet (PSO4.actG w) ∧
      weylMagnet (PSO4.actG w) ≠ weylMagnetLower PSO4.PhiG PSO4.actG w} = 2 :=
  PSO4_repsG ▸ RD.nonRed_ncard PSO4_checkAll

theorem HSpin4_checkAll : HSpin4.checkAll = true := by decide +kernel
theorem HSpin4_repsG : HSpin4.repsG.length = 1 := by decide +kernel
theorem HSpin4_numNonRed_eq : HSpin4.numNonRed = HSpin4.repsG.length := by decide +kernel
/-- Table 1, `HSpin4`: 1 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`. -/
theorem HSpin4_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin HSpin4.n → ℤ) | ∃ w, Z = weylMagnet (HSpin4.actG w) ∧
      weylMagnet (HSpin4.actG w) ≠ weylMagnetLower HSpin4.PhiG HSpin4.actG w} = 1 :=
  HSpin4_repsG ▸ RD.nonRed_ncard HSpin4_checkAll

theorem G2_checkAll : G2.checkAll = true := by decide +kernel
theorem G2_repsG : G2.repsG.length = 1 := by decide +kernel
theorem G2_numNonRed_eq : G2.numNonRed = G2.repsG.length := by decide +kernel
/-- Table 1, `G2`: 1 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`. -/
theorem G2_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin G2.n → ℤ) | ∃ w, Z = weylMagnet (G2.actG w) ∧
      weylMagnet (G2.actG w) ≠ weylMagnetLower G2.PhiG G2.actG w} = 1 :=
  G2_repsG ▸ RD.nonRed_ncard G2_checkAll

theorem SL4_checkAll : SL4.checkAll = true := by decide +kernel
theorem SL4_repsG : SL4.repsG.length = 0 := by decide +kernel
theorem SL4_numNonRed_eq : SL4.numNonRed = SL4.repsG.length := by decide +kernel
/-- Table 1, `SL4`: 0 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`. -/
theorem SL4_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin SL4.n → ℤ) | ∃ w, Z = weylMagnet (SL4.actG w) ∧
      weylMagnet (SL4.actG w) ≠ weylMagnetLower SL4.PhiG SL4.actG w} = 0 :=
  SL4_repsG ▸ RD.nonRed_ncard SL4_checkAll

theorem SL4mu2_checkAll : SL4mu2.checkAll = true := by decide +kernel
theorem SL4mu2_repsG : SL4mu2.repsG.length = 3 := by decide +kernel
theorem SL4mu2_numNonRed_eq : SL4mu2.numNonRed = SL4mu2.repsG.length := by decide +kernel
/-- Table 1, `SL4mu2`: 3 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`. -/
theorem SL4mu2_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin SL4mu2.n → ℤ) | ∃ w, Z = weylMagnet (SL4mu2.actG w) ∧
      weylMagnet (SL4mu2.actG w) ≠ weylMagnetLower SL4mu2.PhiG SL4mu2.actG w} = 3 :=
  SL4mu2_repsG ▸ RD.nonRed_ncard SL4mu2_checkAll

theorem PGL4_checkAll : PGL4.checkAll = true := by decide +kernel
theorem PGL4_repsG : PGL4.repsG.length = 6 := by decide +kernel
theorem PGL4_numNonRed_eq : PGL4.numNonRed = PGL4.repsG.length := by decide +kernel
/-- Table 1, `PGL4`: 6 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`. -/
theorem PGL4_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin PGL4.n → ℤ) | ∃ w, Z = weylMagnet (PGL4.actG w) ∧
      weylMagnet (PGL4.actG w) ≠ weylMagnetLower PGL4.PhiG PGL4.actG w} = 6 :=
  PGL4_repsG ▸ RD.nonRed_ncard PGL4_checkAll

theorem Spin7_checkAll : Spin7.checkAll = true := by decide +kernel
theorem Spin7_repsG : Spin7.repsG.length = 1 := by decide +kernel
theorem Spin7_numNonRed_eq : Spin7.numNonRed = Spin7.repsG.length := by decide +kernel
/-- Table 1, `Spin7`: 1 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`. -/
theorem Spin7_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin Spin7.n → ℤ) | ∃ w, Z = weylMagnet (Spin7.actG w) ∧
      weylMagnet (Spin7.actG w) ≠ weylMagnetLower Spin7.PhiG Spin7.actG w} = 1 :=
  Spin7_repsG ▸ RD.nonRed_ncard Spin7_checkAll

theorem SO7_checkAll : SO7.checkAll = true := by decide +kernel
theorem SO7_repsG : SO7.repsG.length = 3 := by decide +kernel
theorem SO7_numNonRed_eq : SO7.numNonRed = SO7.repsG.length := by decide +kernel
/-- Table 1, `SO7`: 3 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`. -/
theorem SO7_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin SO7.n → ℤ) | ∃ w, Z = weylMagnet (SO7.actG w) ∧
      weylMagnet (SO7.actG w) ≠ weylMagnetLower SO7.PhiG SO7.actG w} = 3 :=
  SO7_repsG ▸ RD.nonRed_ncard SO7_checkAll

theorem Sp6_checkAll : Sp6.checkAll = true := by decide +kernel
theorem Sp6_repsG : Sp6.repsG.length = 0 := by decide +kernel
theorem Sp6_numNonRed_eq : Sp6.numNonRed = Sp6.repsG.length := by decide +kernel
/-- Table 1, `Sp6`: 0 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`. -/
theorem Sp6_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin Sp6.n → ℤ) | ∃ w, Z = weylMagnet (Sp6.actG w) ∧
      weylMagnet (Sp6.actG w) ≠ weylMagnetLower Sp6.PhiG Sp6.actG w} = 0 :=
  Sp6_repsG ▸ RD.nonRed_ncard Sp6_checkAll

theorem PSp6_checkAll : PSp6.checkAll = true := by decide +kernel
theorem PSp6_repsG : PSp6.repsG.length = 7 := by decide +kernel
theorem PSp6_numNonRed_eq : PSp6.numNonRed = PSp6.repsG.length := by decide +kernel
/-- Table 1, `PSp6`: 7 non-redundant Weyl magnets, in the sense of `joinIrreducibles_reductive`. -/
theorem PSp6_nonRed_ncard :
    Set.ncard {Z : AddSubmonoid (Fin PSp6.n → ℤ) | ∃ w, Z = weylMagnet (PSp6.actG w) ∧
      weylMagnet (PSp6.actG w) ≠ weylMagnetLower PSp6.PhiG PSp6.actG w} = 7 :=
  PSp6_repsG ▸ RD.nonRed_ncard PSp6_checkAll

#print axioms SL2_nonRed_ncard
#print axioms PGL2_nonRed_ncard
#print axioms SL3_nonRed_ncard
#print axioms PGL3_nonRed_ncard
#print axioms Spin5_nonRed_ncard
#print axioms SO5_nonRed_ncard
#print axioms Sp4_nonRed_ncard
#print axioms PSp4_nonRed_ncard
#print axioms Spin4_nonRed_ncard
#print axioms SO4_nonRed_ncard
#print axioms PSO4_nonRed_ncard
#print axioms HSpin4_nonRed_ncard
#print axioms G2_nonRed_ncard
#print axioms SL4_nonRed_ncard
#print axioms SL4mu2_nonRed_ncard
#print axioms PGL4_nonRed_ncard
#print axioms Spin7_nonRed_ncard
#print axioms SO7_nonRed_ncard
#print axioms Sp6_nonRed_ncard
#print axioms PSp6_nonRed_ncard

end AlgMag.Table
