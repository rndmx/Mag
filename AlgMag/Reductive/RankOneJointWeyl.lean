/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.R1Geometry
import AlgMag.Reductive.ForwardAssembly

/-!
# Joint rank-one argument, piece W: the Weyl element from the second `T`-fixed point

Notes: `equivalence-reductive/lean-joint.md` (sketch, steps W1–W3).

Setting: `G = Spec H` affine of finite type over `k = k̄`, `T = V(ker π)` a maximal torus,
`Y = G·x₀ ⊆ ℙ(M)` a closed orbit (FlagOrbit), `S = Stab(x₀)` (`hstab`), `T(k) ⊆ S(k)`.

* `FixedPointsNormalizer` (named): a `T`-fixed point `g·x₀` of `Y` is `n·x₀` with `n` normalising
  `T` (Lemma 1.2 of `centralizer-via-Q.md`, Step 4 of `rankone-m1.md`): `g⁻¹Tg` and `T` are
  maximal tori of the solvable `Stab(x₀)`, conjugate there by some `s`, and `n := g s⁻¹`.
* `exists_weyl_of_second_fixed` (proved): if `n` normalises `T` and `n·x₀ ≠ x₀`, then `n` acts on
  `X` by some `σ ≠ 1`. If `σ = 1`, `n` centralises `T`, so `n ∈ C(k) ⊆ B⁺(k) ⊆ S(k)` fixes `x₀`.
* `exists_weyl_of_opposite` (proved): the second fixed point is the `B⁻`-fixed point `x₁` of the
  Tau Ceti fixed-point theorem; `x₁ ≠ x₀` because otherwise `S(k) ⊇ ⟨B⁺(k), B⁻(k)⟩ = G(k)` is
  solvable (T2). With `FixedPointsNormalizer` this gives the Weyl element `n`, `σ ≠ 1`, `n·x₀ = x₁`,
  from T2 alone: no `BorelZMax`, no `dim U = 1`, no (ii′).

Nothing here uses reductivity, `ParabolicBorel`, `BorelZMax`, `rayDim ≤ 1` or `Z_G(T) = T`.
-/

suppress_compilation

open AlgebraicGeometry TauCeti TauCeti.Comodule WithConv AlgMag.Weyl

namespace AlgMag.Reductive.RankOneJoint

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable [Algebra.FiniteType k H]
variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- The rational points of the closed subgroup `V(S)`. -/
abbrev pts (S : HopfIdeal k H) : Subgroup (WithConv (H →ₐ[k] k)) :=
  CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) S (CommAlgCat.of k k)

section Orbit

variable {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

variable (H) in
/-- The point `a·x₀` of the orbit of `[m]`. -/
abbrev orbPt (m : M) (hm : Module.IsUnimodular k m) (a : WithConv (H →ₐ[k] k)) :=
  projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint a.ofConv)

variable (H) in
/-- `x₀ = 1·x₀`. -/
abbrev basePt (m : M) (hm : Module.IsUnimodular k m) :=
  projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H))

end Orbit

/-- **`T`-fixed points of a closed orbit are normaliser translates of the base point** (named).
Let `Y = G·x₀` be a closed orbit with stabiliser `S` (`hstab`), `S(k)` solvable, `T(k) ⊆ S(k)`.
If `g·x₀` is fixed by `T(k)`, then `g·x₀ = n·x₀` for some `n` normalising `T` as a Hopf ideal.
Classically `g⁻¹Tg` and `T` are maximal tori of the solvable group `Stab(x₀)`, hence conjugate
there (Tau Ceti `exists_conjugate_eq_of_isMaximalTorus`, with its `hcontain` input), and
`n := g s⁻¹`. True for `SL₂` (`Y = ℙ¹`, fixed points `0` and `∞ = n·0`) and `SL₃` (same in the
rank-one Levis, and `Y = G/B` with `Y^T = W·x₀` in general). Non-circular: no T2, no Borel
maximality, no `dim U = 1`, no `Z_G(T) = T`. -/
def FixedPointsNormalizer (hπ : Function.Surjective π) : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]
    (m : M) (hm : Module.IsUnimodular k m) (S : HopfIdeal k H),
    IsClosed (Set.range (projectiveOrbitMap (H := H) m hm)) →
    (∀ a : WithConv (H →ₐ[k] k), a ∈ pts S ↔ orbPt H m hm a = basePt H m hm) →
    Group.IsSolvable (pts S) →
    (∀ t ∈ pts (HopfIdeal.kerOfSurjective π hπ), t ∈ pts S) →
    ∀ g : WithConv (H →ₐ[k] k),
      (∀ t ∈ pts (HopfIdeal.kerOfSurjective π hπ), orbPt H m hm (t * g) = orbPt H m hm g) →
      ∃ n : WithConv (H →ₐ[k] k),
        (HopfIdeal.kerOfSurjective π hπ).conjugate n = HopfIdeal.kerOfSurjective π hπ ∧
        orbPt H m hm n = orbPt H m hm g

section Weyl

variable {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- **W2: the Weyl element acts nontrivially.** If `n` normalises `T` and moves `x₀`, while every
point centralising `T` (`σ = 1`) fixes `x₀` (`hC`: `C(k) ⊆ B⁺(k) ⊆ S(k)`), then `n` acts on `X`
by some `σ ≠ 1`. -/
theorem exists_weyl_of_second_fixed (hπ : Function.Surjective π)
    (m : M) (hm : Module.IsUnimodular k m) (S : HopfIdeal k H)
    (hstab : ∀ a : WithConv (H →ₐ[k] k), a ∈ pts S ↔ orbPt H m hm a = basePt H m hm)
    (hC : ∀ a : WithConv (H →ₐ[k] k), IsNormalizingWith π k a 1 → a ∈ pts S)
    (n : WithConv (H →ₐ[k] k))
    (hn : (HopfIdeal.kerOfSurjective π hπ).conjugate n = HopfIdeal.kerOfSurjective π hπ)
    (hne : orbPt H m hm n ≠ basePt H m hm) :
    ∃ σ : X ≃* X, IsNormalizingWith π k n σ ∧ σ ≠ 1 := by
  obtain ⟨σ, hσ⟩ := exists_isNormalizingWith_of_conjugate_eq π hπ hn
  refine ⟨σ, hσ, fun h1 => hne ?_⟩
  subst h1
  exact (hstab n).1 (hC n hσ)

/-- **W1 + W2.** From `FixedPointsNormalizer` and a `T`-fixed point `g·x₀ ≠ x₀`: a Weyl element
`n` with `σ ≠ 1` and `n·x₀ = g·x₀`. -/
theorem exists_weyl_of_fixed (hπ : Function.Surjective π) (hFN : FixedPointsNormalizer π hπ)
    (m : M) (hm : Module.IsUnimodular k m) (S : HopfIdeal k H)
    (hclosed : IsClosed (Set.range (projectiveOrbitMap (H := H) m hm)))
    (hstab : ∀ a : WithConv (H →ₐ[k] k), a ∈ pts S ↔ orbPt H m hm a = basePt H m hm)
    (hsolv : Group.IsSolvable (pts S))
    (hTS : ∀ t ∈ pts (HopfIdeal.kerOfSurjective π hπ), t ∈ pts S)
    (hC : ∀ a : WithConv (H →ₐ[k] k), IsNormalizingWith π k a 1 → a ∈ pts S)
    (g : WithConv (H →ₐ[k] k))
    (hfix : ∀ t ∈ pts (HopfIdeal.kerOfSurjective π hπ), orbPt H m hm (t * g) = orbPt H m hm g)
    (hne : orbPt H m hm g ≠ basePt H m hm) :
    ∃ (n : WithConv (H →ₐ[k] k)) (σ : X ≃* X), IsNormalizingWith π k n σ ∧ σ ≠ 1 ∧
      orbPt H m hm n = orbPt H m hm g := by
  obtain ⟨n, hn, hnx⟩ := hFN M m hm S hclosed hstab hsolv hTS g hfix
  obtain ⟨σ, hσ, hσ1⟩ := exists_weyl_of_second_fixed π hπ m hm S hstab hC n hn (hnx ▸ hne)
  exact ⟨n, σ, hσ, hσ1, hnx⟩

/-- **W3: the Weyl element from T2 and the opposite Borel**, Borel-free. Inputs: a closed orbit
`Y = G·x₀` with solvable stabiliser `S ⊇ B⁺` (`hK`, `f : k[G] ↠ k[B⁺]`), the opposite
`f' : k[G] → k[B⁻]` with `B⁻` reduced connected solvable containing `T(k)` (`hTB`), generation of
`G(k)` by `B⁺(k) ∪ B⁻(k)` (`hgen`, the open cell), `T2` (`G(k)` not solvable), `hC`
(`T`-centralising points fix `x₀`) and `FixedPointsNormalizer`. Conclusion: a Weyl element `n`
with `σ ≠ 1` whose translate `n·x₀` is the `B⁻`-fixed point. -/
theorem exists_weyl_of_opposite (hπ : Function.Surjective π) (hFN : FixedPointsNormalizer π hπ)
    {K : Type u} [CommRing K] [HopfAlgebra k K] [Algebra.FiniteType k K]
    (f : H →ₐc[k] K)
    {K' : Type u} [CommRing K'] [HopfAlgebra k K'] [Algebra.FiniteType k K'] [IsReduced K']
    [ConnectedSpace (PrimeSpectrum K')] [Group.IsSolvable (WithConv (K' →ₐ[k] k))]
    (f' : H →ₐc[k] K')
    (m : M) (hm : Module.IsUnimodular k m) (S : HopfIdeal k H)
    (hclosed : IsClosed (Set.range (projectiveOrbitMap (H := H) m hm)))
    (hstab : ∀ a : WithConv (H →ₐ[k] k), a ∈ pts S ↔ orbPt H m hm a = basePt H m hm)
    (hsolv : Group.IsSolvable (pts S))
    (hK : ∀ b : WithConv (K →ₐ[k] k), BialgHom.mapDomain f b ∈ pts S)
    (hTB : ∀ t ∈ pts (HopfIdeal.kerOfSurjective π hπ), t ∈ Set.range (BialgHom.mapDomain f'))
    (hgen : Subgroup.closure (Set.range (BialgHom.mapDomain (A := CommAlgCat.of k k) f) ∪
      Set.range (BialgHom.mapDomain (A := CommAlgCat.of k k) f')) = ⊤)
    (hT2 : ¬ Group.IsSolvable (WithConv (H →ₐ[k] k)))
    (hTS : ∀ t ∈ pts (HopfIdeal.kerOfSurjective π hπ), t ∈ pts S)
    (hC : ∀ a : WithConv (H →ₐ[k] k), IsNormalizingWith π k a 1 → a ∈ pts S) :
    ∃ (n : WithConv (H →ₐ[k] k)) (σ : X ≃* X), IsNormalizingWith π k n σ ∧ σ ≠ 1 ∧
      ∀ b : WithConv (K' →ₐ[k] k), orbPt H m hm (BialgHom.mapDomain f' b * n) = orbPt H m hm n := by
  -- the `B⁻`-fixed point `x₁ = g·x₀`
  obtain ⟨g, hg⟩ :=
    BialgHom.exists_projectiveOrbitMap_kernelPoint_fixed_of_isClosed_of_isSolvable f' m hm hclosed
  have hfix' : ∀ b : WithConv (K' →ₐ[k] k),
      orbPt H m hm (BialgHom.mapDomain f' b * g) = orbPt H m hm g := fun b ↦ by
    rw [orbPt, ← projectivePointTranslation_projectiveOrbitMap_kernelPoint]; exact hg b
  have hfix : ∀ t ∈ pts (HopfIdeal.kerOfSurjective π hπ), orbPt H m hm (t * g) = orbPt H m hm g := by
    intro t ht
    obtain ⟨b, rfl⟩ := hTB t ht
    exact hfix' b
  -- `x₁ ≠ x₀`: otherwise `S(k) = G(k)` is solvable
  have hne : orbPt H m hm g ≠ basePt H m hm := by
    intro heq
    apply hT2
    have hgS : g ∈ pts S := (hstab g).mpr heq
    have hB' : ∀ b, BialgHom.mapDomain f' b ∈ pts S := fun b ↦ by
      have h1 : BialgHom.mapDomain f' b * g ∈ pts S := (hstab _).mpr ((hfix' b).trans heq)
      simpa using (pts S).mul_mem h1 ((pts S).inv_mem hgS)
    have htop : pts S = ⊤ := by
      rw [eq_top_iff, ← hgen, Subgroup.closure_le]
      rintro _ (⟨b, rfl⟩ | ⟨b, rfl⟩)
      · exact hK b
      · exact hB' b
    have : Group.IsSolvable (⊤ : Subgroup (WithConv (H →ₐ[k] k))) := htop ▸ hsolv
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.topEquiv (G := WithConv (H →ₐ[k] k))).symm.toMonoidHom)
      (Subgroup.topEquiv (G := WithConv (H →ₐ[k] k))).symm.injective
  obtain ⟨n, σ, hσ, hσ1, hnx⟩ :=
    exists_weyl_of_fixed π hπ hFN m hm S hclosed hstab hsolv hTS hC g hfix hne
  refine ⟨n, σ, hσ, hσ1, fun b ↦ ?_⟩
  -- `n·x₀ = g·x₀` is `B⁻`-fixed, so `b n·x₀ = b g·x₀ = g·x₀ = n·x₀`
  have h1 : orbPt H m hm (BialgHom.mapDomain f' b * n) =
      (projectivePointTranslation (M := M) (BialgHom.mapDomain f' b)).hom (orbPt H m hm n) := by
    rw [orbPt, orbPt, projectivePointTranslation_projectiveOrbitMap_kernelPoint]
  have h2 : orbPt H m hm (BialgHom.mapDomain f' b * g) =
      (projectivePointTranslation (M := M) (BialgHom.mapDomain f' b)).hom (orbPt H m hm g) := by
    rw [orbPt, orbPt, projectivePointTranslation_projectiveOrbitMap_kernelPoint]
  rw [h1, hnx, ← h2, hfix' b]

end Weyl

end AlgMag.Reductive.RankOneJoint

#print axioms AlgMag.Reductive.RankOneJoint.exists_weyl_of_second_fixed
#print axioms AlgMag.Reductive.RankOneJoint.exists_weyl_of_fixed
#print axioms AlgMag.Reductive.RankOneJoint.exists_weyl_of_opposite
