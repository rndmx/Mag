/-
The Borel route to T2, T3, step 0 and condition (i)  (plan: equivalence-reductive/T2-plan.md).

STATUS (2026-11-10).  Tau Ceti's `Borel/*` files are not compiled in this repo yet
(port: `Borel.Basic` blocked on `Solvable.Basic`, see equivalence-reductive/port-log.md).
Hence the Borel notion enters through the hypothesis structure `BorelBridge`, whose fields
are exactly the Tau Ceti facts used, each tagged with the declaration that will discharge
it once the port compiles.  Nothing here is an axiom and there is no `sorry`: every theorem
is proved from its explicitly named hypotheses.

Conventions.  Closed subgroups of `G = Spec H` are Hopf ideals of `H`; the order is reversed:
`I ≤ J` (ideals) iff `V(J) ⊆ V(I)` (subgroups); `I ⊔ J` is the intersection `V(I) ∩ V(J)`.
-/
import AlgMag.Reductive.LieTorusZero
import AlgMag.Reductive.Prop1610
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Unipotent.Representability

open Magnetism TauCeti TauCeti.Cocharacter

namespace AlgMag.Reductive.BorelRoute

universe u

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]

/-- The parabolic `P(l)`, Levi `Z(l)`, unipotent `U(l)` Hopf ideals of a cocharacter. -/
noncomputable abbrev P (l : H →ₐc[k] LaurentPolynomial k) : HopfIdeal k H :=
  parabolicDefiningHopfIdeal l
noncomputable abbrev Z (l : H →ₐc[k] LaurentPolynomial k) : HopfIdeal k H :=
  leviDefiningHopfIdeal l
noncomputable abbrev U (l : H →ₐc[k] LaurentPolynomial k) : HopfIdeal k H :=
  BialgHom.unipotentDefiningHopfIdeal l

/-- `Z(l) = P(l) ∩ P(-l)` (Tau Ceti definition, D4). -/
theorem Z_eq (l : H →ₐc[k] LaurentPolynomial k) : Z l = P l ⊔ P l.oppositeCocharacter :=
  leviDefiningHopfIdeal_def l

/-- **Bridge to Tau Ceti's Borel theory** (pending the port).

* `IsBorelIn S B` stands for `S ≤ B ∧ IsBorelOverAlgClosed k (quotient H S) (B.map mk_S)`:
  `V(B)` is a Borel subgroup of `V(S)`.  `S = ⊥` is `G` itself.
* `Ru S` stands for the comap to `H` of `unipotentRadicalDefiningIdeal (quotient H S)`.
* `one` is the trivial subgroup (augmentation Hopf ideal). -/
structure BorelBridge (k : Type u) (H : Type u) [Field k] [CommRing H] [HopfAlgebra k H] where
  IsBorelIn : HopfIdeal k H → HopfIdeal k H → Prop
  Ru : HopfIdeal k H → HopfIdeal k H
  one : HopfIdeal k H
  /-- every Hopf ideal cuts out a subgroup containing `1`. -/
  le_one : ∀ I : HopfIdeal k H, I ≤ one
  /-- `IsBorelOverAlgClosed.map_of_le` (Borel/Subgroup.lean). -/
  map_of_le : ∀ {S B}, IsBorelIn ⊥ B → S ≤ B → IsBorelIn S B
  /-- (D) `IsBorelOverAlgClosed.le_unipotentRadicalDefiningIdeal` (Borel/Radical.lean),
  applied to the quotient `V(S)`: `R_u(V(S)) ⊆ B`. -/
  le_Ru : ∀ {S B}, IsBorelIn S B → B ≤ Ru S
  /-- **Lemma L1** (plan §3.1; math proved, char-free, no reductivity).  Lean proof: Levi
  quotient (Dynamic/Levi/Quotient.lean `limit_mem_levi`) + `map_of_le` + Solvable/Extension;
  pending the port of `Borel.Basic`.  A Borel `B ⊆ P(μ)` contains `U(μ)` and `B ∩ Z(μ)` is a
  Borel of `Z(μ)`. -/
  L1 : ∀ {B} (μ : H →ₐc[k] LaurentPolynomial k), IsBorelIn ⊥ B → P μ ≤ B →
    B ≤ U μ ∧ IsBorelIn (Z μ) (B ⊔ Z μ)

variable (bb : BorelBridge k H)

/-- `l` is regular: `Z_G(l) = C := Z_G(T)`, the latter as the magnet `G^0` (= `C`). -/
def IsRegular (C : HopfIdeal k H) (l : H →ₐc[k] LaurentPolynomial k) : Prop := Z l = C

/-- **(Bor)**: for `G` reductive and `ν` regular, `P_G(ν)` is a Borel subgroup of `G`.
Precise form, once the port compiles:
`reductiveCommHopfAlgProperty k G → ∀ ν, IsRegular C ν →
   IsBorelOverAlgClosed k G (parabolicDefiningHopfIdeal ν)`.
Here `hred` is the reductivity of `G`, kept abstract as a `Prop`. -/
def Bor (hred : Prop) (C : HopfIdeal k H) : Prop :=
  hred → ∀ ν : H →ₐc[k] LaurentPolynomial k, IsRegular C ν → bb.IsBorelIn ⊥ (P ν)

/-- `V(S)` is reductive: trivial unipotent radical
(`reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_eq_augmentation`). -/
def IsRed (S : HopfIdeal k H) : Prop := bb.Ru S = bb.one

/-! ### Steps 1–3 of T2 (plan §3.2): `R_u(Z(μ)) ⊆ C`, char-free. -/

/-- Opposite regular cocharacters are regular (same Levi). -/
theorem isRegular_opposite {C : HopfIdeal k H} {ν : H →ₐc[k] LaurentPolynomial k}
    (h : IsRegular C ν) : IsRegular C ν.oppositeCocharacter := by
  unfold IsRegular at *; rw [Z, leviDefiningHopfIdeal_oppositeCocharacter]; exact h

/-- **Residue of T2.** Under (Bor), if `ν'` is regular with `P(±ν') ⊆ P(±μ)`, then
`R_u(Z(μ)) ⊆ C`. -/
theorem C_le_Ru_levi {hred : Prop} {C : HopfIdeal k H} (hBor : Bor bb hred C) (hG : hred)
    (μ ν' : H →ₐc[k] LaurentPolynomial k) (hν' : IsRegular C ν')
    (hP : P μ ≤ P ν') (hPm : P μ.oppositeCocharacter ≤ P ν'.oppositeCocharacter) :
    C ≤ bb.Ru (Z μ) := by
  have hB := hBor hG ν' hν'
  have hBm := hBor hG _ (isRegular_opposite hν')
  have h1 := bb.le_Ru (bb.L1 μ hB hP).2
  have h2 := bb.le_Ru (bb.L1 μ.oppositeCocharacter hBm hPm).2
  rw [Z, leviDefiningHopfIdeal_oppositeCocharacter] at h2
  rw [← hν', Z_eq]
  exact sup_le (le_sup_left.trans h1) (le_sup_left.trans h2)

/-- **T2** (plan §3.2): with (i) (`C = T`) and "a unipotent radical inside `T` is trivial",
`Z(μ)` is reductive. -/
theorem reductive_levi {hred : Prop} {C T : HopfIdeal k H} (hBor : Bor bb hred C) (hG : hred)
    (hi : C = T) (μ ν' : H →ₐc[k] LaurentPolynomial k)
    (hTriv : T ≤ bb.Ru (Z μ) → bb.Ru (Z μ) = bb.one) (hν' : IsRegular C ν')
    (hP : P μ ≤ P ν') (hPm : P μ.oppositeCocharacter ≤ P ν'.oppositeCocharacter) :
    IsRed bb (Z μ) :=
  hTriv (hi ▸ C_le_Ru_levi bb hBor hG μ ν' hν' hP hPm)

/-! ### T3 (plan §5.1) -/

/-- **T3.** `Z_α = Z(μ)`, `λ` with `P_{Z_α}(λ) = P(ν') ∩ Z_α` (Lemma 4.1, `hlam`):
`P_{Z_α}(λ)` is a Borel of `Z_α`. -/
theorem T3 {hred : Prop} {C : HopfIdeal k H} (hBor : Bor bb hred C) (hG : hred)
    (μ ν' l : H →ₐc[k] LaurentPolynomial k) (hν' : IsRegular C ν') (hP : P μ ≤ P ν')
    (hlam : P ν' ⊔ Z μ = P l ⊔ Z μ) :
    bb.IsBorelIn (Z μ) (P l ⊔ Z μ) :=
  hlam ▸ (bb.L1 μ (hBor hG ν' hν') hP).2

/-! ### Step 0 (plan §5.2) -/

/-- **Step 0.** If `U^-_{Z_α} = 1`, so that `U^+ := U_{Z_α}(λ)` is normal in `Z_α` and lies in
`R_u(Z_α)` (`hnormal`), then `U^+ ⊆ P_{Z_α}(-λ) = C` (`hC`), contradicting `U^+ ∩ C = 1`
(`hUC`, D4) and `U^+ ≠ 1` (`hne`, D3: `𝔤_α ⊆ Lie U^+`). -/
theorem step0 {hred : Prop} {C Uplus : HopfIdeal k H} (hBor : Bor bb hred C) (hG : hred)
    (μ ν' : H →ₐc[k] LaurentPolynomial k) (hν' : IsRegular C ν')
    (hPm : P μ.oppositeCocharacter ≤ P ν'.oppositeCocharacter)
    (hnormal : bb.Ru (Z μ) ≤ Uplus)
    (hC : P ν'.oppositeCocharacter ⊔ Z μ = C)
    (hUC : Uplus ⊔ C = bb.one) (hne : Uplus ≠ bb.one) : False := by
  have hBm := hBor hG _ (isRegular_opposite hν')
  have h := bb.le_Ru (bb.L1 μ.oppositeCocharacter hBm hPm).2
  rw [Z, leviDefiningHopfIdeal_oppositeCocharacter] at h
  rw [hC] at h
  apply hne
  have : C ≤ Uplus := h.trans hnormal
  rw [← hUC, sup_eq_left.2 this]

/-! ### Condition (i) and `Lie Z_G(T) = Lie T` (plan §4.2) -/

/-- The named inputs of §4.2, for `C = Z_G(T)` with unipotent radical `Cu = R_u(C)`.
* `solv`: step 1, `C/C_u` is a torus; with `C_u = 1` and `T` maximal this gives `C = T`
  (`torus_coinvariants_unipotentRadical` + `IsMaximalTorus`); uses `C ⊆ P(ν)` Borel by (Bor).
* `T4` / `centralises`: steps 2–3, `V_α ≅ 𝔾_a` with weight `α` (T4 + `isRootGroup_rootGroupIdeal_of_finrank`)
  and the additive-polynomial rigidity, so `C_u` centralises every `V_α`.
* `Gen`: (Gen) `ParabolicGeneration` + `subset_of_isOpen_subset`: centralising every `V_α`
  and being normalised by `C` forces `C_u ⊲ G`.
* `normal_le`: step 5, `unipotentRadicalDefiningIdeal_le`: a normal smooth connected unipotent
  subgroup lies in `R_u(G)`. -/
structure CondIInputs (C T : HopfIdeal k H) (Roots : Type*) where
  T4 : Roots → Prop
  t4 : ∀ α, T4 α
  centralises : Roots → Prop
  centralises_of_T4 : ∀ α, T4 α → centralises α
  normal_of_centralises : (∀ α, centralises α) → (bb.Ru C).IsNormal
  normal_le : (bb.Ru C).IsNormal → bb.Ru ⊥ ≤ bb.Ru C
  solv : bb.Ru C = bb.one → C = T

/-- **(i)**: `C = T` from (Bor) (inside `solv`), T4 for all roots and (Gen). -/
theorem condI_of_borelRoute {C T : HopfIdeal k H} {Roots : Type*}
    (inp : CondIInputs bb C T Roots) (hred : IsRed bb ⊥) : C = T := by
  apply inp.solv
  have hn := inp.normal_of_centralises fun α => inp.centralises_of_T4 α (inp.t4 α)
  have h := inp.normal_le hn
  rw [show bb.Ru ⊥ = bb.one from hred] at h
  exact le_antisymm (bb.le_one _) h

variable {X : Type u} [CommGroup X] [DecidableEq X] (π : H →ₐc[k] MonoidAlgebra k X)

/-- **Corollary (Lie).** If `C = G^0 = magnetHopfIdeal π ⊥` equals `T` then
`𝔤_0 = Lie T` (`rootSpace_zero_eq_lieBot`). -/
theorem rootSpace_zero_eq_lieT {T : HopfIdeal k H} (hCT : magnetHopfIdeal π ⊥ = T) :
    rootSpace π 0 = (T.lieSubalgebra (B := k)).toSubmodule := by
  rw [rootSpace_zero_eq_lieBot, hCT]

end AlgMag.Reductive.BorelRoute
