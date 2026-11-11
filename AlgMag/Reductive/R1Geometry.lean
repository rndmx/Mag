/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.FlagOrbit
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.SolvableSubgroup
import TauCeti.Algebra.AlgebraicGroup.Torus.Conjugation
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Map

/-!
# Geometry for (R1): closed orbit with a Borel-fixed base point (G1-plan steps 2–3)

`exists_closedOrbit_fixed`: for an affine group `Z` of finite type over `k = k̄` and a reduced
connected solvable group `K → Z` (for (R1): `B⁺ = P_Z(λ) → Z`), there is a closed projective
orbit `Y = Z·[m]` whose stabiliser `S` satisfies `hstab` and has solvable rational points, with
`K(k)` contained in `S(k)` (`[m]` is the `K`-fixed point `x₀`).

`exists_second_fixed`: the point-level consequences of a second fixed point `x₁ = g·x₀ ≠ x₀`
under explicitly named inputs.
-/

open AlgebraicGeometry TauCeti TauCeti.Comodule

namespace AlgMag.Reductive.R1Geometry

universe u

variable {k H : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

section Translate

variable {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

theorem bpr_mul_apply (a g : WithConv (H →ₐ[k] k)) (m : M) :
    basePointsRepresentation (H := H) M a (basePointsRepresentation (H := H) M g m) =
      basePointsRepresentation (H := H) M (a * g) m := by
  rw [map_mul, Module.End.mul_apply]

/-- `a` fixes `[g·m]` iff the orbit map of `m` takes the same value at `a g` and at `g`. -/
theorem mem_lineStabilizer_bpr_iff (m : M) (hm : Module.IsUnimodular k m)
    (g a : WithConv (H →ₐ[k] k)) :
    a ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        (FlagOrbit.lineStabilizer (H := H) (basePointsRepresentation (H := H) M g m))
        (CommAlgCat.of k k) ↔
      projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint (a * g).ofConv) =
        projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint g.ofConv) := by
  have hm' := (isUnimodular_basePointsRepresentation_iff g m).mpr hm
  rw [FlagOrbit.mem_lineStabilizer_iff _ hm']
  have h1 := projectiveOrbitMap_kernelPoint_eq_iff_span_eq (H := H) _ hm' _ hm' a 1
  have hone : (1 : WithConv (H →ₐ[k] k)).ofConv = Bialgebra.counitAlgHom k H := rfl
  rw [hone] at h1
  rw [h1, projectiveOrbitMap_kernelPoint_eq_iff_span_eq (H := H) m hm m hm (a * g) g,
    bpr_mul_apply, map_one, Module.End.one_apply]

end Translate

variable {K : Type u} [CommRing K] [HopfAlgebra k K] [Algebra.FiniteType k K]
  [IsReduced K] [ConnectedSpace (PrimeSpectrum K)] [Group.IsSolvable (WithConv (K →ₐ[k] k))]

/-- **G1-plan steps 2–3 (first half).** A closed orbit with solvable stabiliser whose base point
is fixed by the image of a reduced connected solvable group. -/
theorem exists_closedOrbit_fixed (f : H →ₐc[k] K) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module k M) (_ : Comodule k H M)
      (_ : Module.Finite k M) (m : M) (hm : Module.IsUnimodular k m) (S : HopfIdeal k H),
      IsClosed (Set.range (projectiveOrbitMap (H := H) m hm)) ∧
      (∀ a : WithConv (H →ₐ[k] k),
        a ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) S
            (CommAlgCat.of k k) ↔
          projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint a.ofConv) =
            projectiveOrbitMap (H := H) m hm
              (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H))) ∧
      Group.IsSolvable (CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) S
        (CommAlgCat.of k k)) ∧
      ∀ b : WithConv (K →ₐ[k] k), BialgHom.mapDomain f b ∈
        CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) S
          (CommAlgCat.of k k) := by
  obtain ⟨M, _, _, _, _, m, hm, S₀, hclosed, hstab₀, hsolv₀⟩ :=
    FlagOrbit.exists_isClosed_projectiveOrbit_solvable_stabilizer (k := k) (H := H)
  obtain ⟨g, hg⟩ :=
    BialgHom.exists_projectiveOrbitMap_kernelPoint_fixed_of_isClosed_of_isSolvable f m hm hclosed
  set m' := basePointsRepresentation (H := H) M g m
  have hm' : Module.IsUnimodular k m' := (isUnimodular_basePointsRepresentation_iff g m).mpr hm
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, m', hm',
    FlagOrbit.lineStabilizer (H := H) m', ?_, FlagOrbit.mem_lineStabilizer_iff m' hm', ?_, ?_⟩
  · rw [range_projectiveOrbitMap_basePointsRepresentation]; exact hclosed
  · -- conjugation by `g⁻¹` embeds the stabiliser of `[g m]` into that of `[m]`
    let G := CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
      (FlagOrbit.lineStabilizer (H := H) m') (CommAlgCat.of k k)
    let G₀ := CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) S₀
      (CommAlgCat.of k k)
    have hmem : ∀ a : G, g⁻¹ * (a : WithConv (H →ₐ[k] k)) * g ∈ G₀ := by
      intro a
      have ha := (mem_lineStabilizer_bpr_iff m hm g a).mp a.2
      have h2 := congrArg (projectivePointTranslation (M := M) g⁻¹).hom ha
      rw [projectivePointTranslation_projectiveOrbitMap_kernelPoint,
        projectivePointTranslation_projectiveOrbitMap_kernelPoint, inv_mul_cancel] at h2
      rw [hstab₀, ← mul_assoc] at *
      exact h2
    let φ : G →* G₀ :=
      { toFun := fun a ↦ ⟨_, hmem a⟩
        map_one' := by ext1; simp
        map_mul' := by intro a b; ext1; simp [mul_assoc] }
    refine Group.isSolvable_of_isSolvable_injective (f := φ) fun a b hab ↦ ?_
    have := congrArg Subtype.val hab
    simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  · intro b
    rw [mem_lineStabilizer_bpr_iff m hm g, ← projectivePointTranslation_projectiveOrbitMap_kernelPoint]
    exact hg b

section SecondFixed

variable {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- **G1-plan step 3, point level.** Let `x₀ = [m]` be fixed by `K(k)` (via `f`), and let
`S(k) = Stab(x₀)(k)`. Assume the named inputs
* `hBor` (Bor): `Stab(x₀)(k) ⊆ f(K(k))`,
* `hC`: `C(k) ⊆ f(K(k))`,
and a second point `x₁ = g·x₀ ≠ x₀` fixed by a subgroup `T(k)` (`hfix`, `hne`). Then the
conjugate `g⁻¹ T(k) g` lies in `f(K(k))`, and `b·g ∉ C(k)` for every `b ∈ K(k)`. -/
theorem second_fixed_consequences (f : H →ₐc[k] K) (m : M) (hm : Module.IsUnimodular k m)
    (S : HopfIdeal k H)
    (hstab : ∀ a : WithConv (H →ₐ[k] k),
      a ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) S
          (CommAlgCat.of k k) ↔
        projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint a.ofConv) =
          projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)))
    (hK : ∀ b : WithConv (K →ₐ[k] k), BialgHom.mapDomain f b ∈
      CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) S (CommAlgCat.of k k))
    (hBor : ∀ a : WithConv (H →ₐ[k] k),
      a ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) S
        (CommAlgCat.of k k) → a ∈ Set.range (BialgHom.mapDomain f))
    (T C : Set (WithConv (H →ₐ[k] k))) (hC : C ⊆ Set.range (BialgHom.mapDomain f))
    (g : WithConv (H →ₐ[k] k))
    (hfix : ∀ t ∈ T, projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint (t * g).ofConv) =
      projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint g.ofConv))
    (hne : projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint g.ofConv) ≠
      projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H))) :
    (∀ t ∈ T, g⁻¹ * t * g ∈ Set.range (BialgHom.mapDomain f)) ∧
      ∀ b : WithConv (K →ₐ[k] k), BialgHom.mapDomain f b * g ∉ C := by
  have hone : Bialgebra.counitAlgHom k H = (1 : WithConv (H →ₐ[k] k)).ofConv := rfl
  refine ⟨fun t ht ↦ hBor _ ((hstab _).mpr ?_), fun b hb ↦ hne ?_⟩
  · have h2 := congrArg (projectivePointTranslation (M := M) g⁻¹).hom (hfix t ht)
    rw [projectivePointTranslation_projectiveOrbitMap_kernelPoint,
      projectivePointTranslation_projectiveOrbitMap_kernelPoint, inv_mul_cancel, ← mul_assoc] at h2
    rw [hone]; exact h2
  · obtain ⟨b', hb'⟩ := hC hb
    have hg : g = BialgHom.mapDomain f (b⁻¹ * b') := by
      rw [map_mul, hb', map_inv, inv_mul_cancel_left]
    exact hg ▸ (hstab _).mp (hK _)

end SecondFixed

section Torus

variable {K : Type u} [CommRing K] [HopfAlgebra k K] [Algebra.FiniteType k K]

theorem mapValue_ofId_self (g : WithConv (H →ₐ[k] k)) :
    AlgHom.mapValue (H := H) (Algebra.ofId k k) g = g := by
  apply WithConv.ofConv_injective
  ext x
  simp [AlgHom.mapValue_apply]

/-- Rational points killing `ker f` come from `K` (for `f` surjective). -/
theorem mem_range_mapDomain_of_mem (f : H →ₐc[k] K) (hf : Function.Surjective f)
    (a : WithConv (H →ₐ[k] k))
    (ha : a ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.kerOfSurjective f hf) (CommAlgCat.of k k)) :
    a ∈ Set.range (BialgHom.mapDomain f) := by
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at ha
  have hker : RingHom.ker (f : H →ₐ[k] K) ≤ RingHom.ker a.ofConv := fun x hx ↦
    ha x (by rw [HopfIdeal.mem_kerOfSurjective]; exact hx)
  let e := Ideal.quotientKerAlgEquivOfSurjective (f := (f : H →ₐ[k] K)) hf
  let τ : K →ₐ[k] k :=
    (Ideal.Quotient.liftₐ (RingHom.ker (f : H →ₐ[k] K)) a.ofConv fun x hx ↦ hker hx).comp
      e.symm.toAlgHom
  refine ⟨WithConv.toConv τ, ?_⟩
  apply WithConv.ofConv_injective
  ext x
  rw [BialgHom.mapDomain_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv]
  show (Ideal.Quotient.liftₐ (RingHom.ker (f : H →ₐ[k] K)) a.ofConv fun x hx ↦ hker hx)
    (e.symm (f x)) = _
  rw [show e.symm (f x) = Ideal.Quotient.mk _ x from e.symm_apply_eq.2 rfl]
  rfl

/-- **Torus plumbing for `SQ`.** If the rational points of `T^g = g T g⁻¹` lie in `f(K(k))`,
then `T^g` contains `ker f` scheme-theoretically (tori are reduced; separation by points), so it
descends to a Hopf ideal `SQ` of `K` with `comap SQ = T^g`, and `T^g` is a maximal torus.
(`isMaximalTorus_of_comapOfSurjective` in `ForwardAssembly.lean` then gives `hSQ`.) -/
theorem exists_SQ (T : HopfIdeal k H)
    (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) T)
    (f : H →ₐc[k] K) (hf : Function.Surjective f) (g : WithConv (H →ₐ[k] k))
    (hin : ∀ t ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) T
        (CommAlgCat.of k k), g * t * g⁻¹ ∈ Set.range (BialgHom.mapDomain f)) :
    ∃ SQ : HopfIdeal k K, SQ.comapOfSurjective f hf = T.conjugate g ∧
      HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H)
        (SQ.comapOfSurjective f hf) := by
  have hJ := hT.conjugate g
  have htor := ((HopfIdeal.isMaximalTorus_iff k _ _).1 hJ).1
  haveI : IsReduced (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) (T.conjugate g)) :=
    htor.geometricallyReduced.isReduced
  have hle : HopfIdeal.kerOfSurjective f hf ≤ T.conjugate g := by
    refine HopfIdeal.le_of_quotientPointsSubgroup_le (k := k) (K := k)
      (H := _root_.CommHopfAlgCat.of k H) (I := HopfIdeal.kerOfSurjective f hf)
      (J := T.conjugate g) fun x hx ↦ ?_
    have hx' : g⁻¹ * x * g ∈ CommHopfAlgCat.quotientPointsSubgroup
        (_root_.CommHopfAlgCat.of k H) T (CommAlgCat.of k k) := by
      rw [← CommHopfAlgCat.pointConjugation_mem_conjugate_iff T g, mapValue_ofId_self]
      simpa [mul_assoc] using hx
    have := hin _ hx'
    simp only [mul_assoc, mul_inv_cancel, mul_one, ← mul_assoc g, mul_inv_cancel, one_mul] at this
    obtain ⟨b, hb⟩ := this
    rw [← hb, ← HopfIdeal.comapOfSurjective_bot f hf]
    exact (BialgHom.mapDomain_mem_quotientPointsSubgroup_comapOfSurjective_iff f hf ⊥ (CommAlgCat.of k k) b).2
      (by
        rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
        intro y hy
        rw [HopfIdeal.mem_bot.1 hy]; exact map_zero _)
  haveI : RingHomSurjective (f : H →+* K) := ⟨hf⟩
  refine ⟨(T.conjugate g).map f, ?_, ?_⟩
  · rw [HopfIdeal.comapOfSurjective_map, sup_eq_left.2 hle]
  · rw [HopfIdeal.comapOfSurjective_map, sup_eq_left.2 hle]; exact hJ

end Torus

section Assembly

variable {K : Type u} [CommRing K] [HopfAlgebra k K] [Algebra.FiniteType k K]
  [IsReduced K] [ConnectedSpace (PrimeSpectrum K)]

/-- The named geometric input for (R1) on the closed orbit `Y = Z·x₀` of
`exists_closedOrbit_fixed`: (Bor-stab) `Stab(x₀)(k) ⊆ B⁺(k)` and (second fixed point) some
`g·x₀ ≠ x₀` fixed by `T(k)`. -/
def OrbitInput (f : H →ₐc[k] K) (T : HopfIdeal k H) : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]
      (m : M) (hm : Module.IsUnimodular k m) (S : HopfIdeal k H),
      IsClosed (Set.range (projectiveOrbitMap (H := H) m hm)) →
      (∀ a : WithConv (H →ₐ[k] k),
        a ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) S
            (CommAlgCat.of k k) ↔
          projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint a.ofConv) =
            projectiveOrbitMap (H := H) m hm
              (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H))) →
      (∀ b : WithConv (K →ₐ[k] k), BialgHom.mapDomain f b ∈
        CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) S
          (CommAlgCat.of k k)) →
      Group.IsSolvable (CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) S
        (CommAlgCat.of k k)) →
      -- (Bor) and (second fixed point)
      (∀ a : WithConv (H →ₐ[k] k),
        a ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) S
          (CommAlgCat.of k k) → a ∈ Set.range (BialgHom.mapDomain f)) ∧
      ∃ g : WithConv (H →ₐ[k] k),
        (∀ t ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) T
            (CommAlgCat.of k k),
          projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint (t * g).ofConv) =
            projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint g.ofConv)) ∧
        projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint g.ofConv) ≠
          projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H))

/-- **(R1) geometric fields, at the level of `Z`.** Here `H` is the coordinate algebra of `Z`,
`f : k[Z] ↠ k[B⁺]` and `T` is a maximal torus of `Z` with `T(k) ⊆ B⁺(k)`. Named inputs:
* `Bor` : `B⁺(k)` is solvable (instance argument);
* `hBor` : for the closed orbit of `exists_closedOrbit_fixed`, `Stab(x₀)(k) ⊆ B⁺(k)`;
* `hC` : `C(k) ⊆ B⁺(k)`;
* `hsecond` : a second `T`-fixed point `g·x₀ ≠ x₀` on that orbit.

Conclusion: there are `g` and `SQ ⊆ k[B⁺]` with `comap SQ = T^{g⁻¹}`, `T^{g⁻¹}` a maximal torus
of `Z`, and `b·g⁻¹ ∉ C(k)` for all `b ∈ B⁺(k)`. -/
theorem r1Geom_fields [Group.IsSolvable (WithConv (K →ₐ[k] k))]
    (f : H →ₐc[k] K) (hf : Function.Surjective f) (T : HopfIdeal k H)
    (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) T)
    (C : Set (WithConv (H →ₐ[k] k))) (hC : C ⊆ Set.range (BialgHom.mapDomain f))
    (hinput : OrbitInput f T) :
    ∃ (g : WithConv (H →ₐ[k] k)) (SQ : HopfIdeal k K),
      SQ.comapOfSurjective f hf = T.conjugate g ∧
      HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) (SQ.comapOfSurjective f hf) ∧
      ∀ b : WithConv (K →ₐ[k] k), BialgHom.mapDomain f b * g ∉ C := by
  obtain ⟨M, _, _, _, _, m, hm, S, hclosed, hstab, hsolv, hK⟩ := exists_closedOrbit_fixed (H := H) f
  obtain ⟨hBor, g, hfix, hne⟩ := hinput M m hm S hclosed hstab hK hsolv
  obtain ⟨hTg, -⟩ := second_fixed_consequences f m hm S hstab hK hBor
    (CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) T (CommAlgCat.of k k))
    C hC g hfix hne
  obtain ⟨SQ, hSQ, hmax⟩ := exists_SQ T hT f hf g⁻¹ fun t ht ↦ by
    simpa only [inv_inv] using hTg t ht
  refine ⟨g⁻¹, SQ, hSQ, hmax, fun b hb ↦ hne ?_⟩
  obtain ⟨b', hb'⟩ := hC hb
  have hg : g = BialgHom.mapDomain f (b'⁻¹ * b) := by
    rw [map_mul, map_inv, hb', mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
  have := (hstab _).mp (hK (b'⁻¹ * b))
  rw [← hg] at this
  exact this

/-- **The second fixed point from the opposite Borel** (G1-plan / T4: the `B⁻`-fixed point).
No Białynicki-Birula is needed. Named inputs:
* `f' : k[Z] → k[B⁻]`, `B⁻` reduced, connected, with solvable points (Bor⁻);
* `hTB` : `T(k) ⊆ B⁻(k)`;
* `hgen` : `Z(k)` is generated by `B⁺(k) ∪ B⁻(k)` (from the open cell `U⁻ × B⁺ ⊆ Z`);
* `hT2` : `Z(k)` is not solvable (T2);
* `hBorStab` : (Bor) `Stab(x₀)(k) ⊆ B⁺(k)` on every closed orbit through a `B⁺`-fixed point,
  for stabilisers whose points form a SOLVABLE group (without this premise the hypotheses are
  inconsistent with `hT2`: trivial comodule).

Proof: `B⁻` fixes some `x₁ = g·x₀` (Tau Ceti fixed-point theorem), and `T ⊆ B⁻` fixes it.
If `x₁ = x₀`, then `B⁺(k)` and `B⁻(k)` lie in `Stab(x₀)(k)`, so `Stab(x₀)(k) = Z(k)` is
solvable, contradicting T2. -/
theorem orbitInput_of_opposite (f : H →ₐc[k] K) (T : HopfIdeal k H)
    {K' : Type u} [CommRing K'] [HopfAlgebra k K'] [Algebra.FiniteType k K'] [IsReduced K']
    [ConnectedSpace (PrimeSpectrum K')] [Group.IsSolvable (WithConv (K' →ₐ[k] k))]
    (f' : H →ₐc[k] K')
    (hTB : ∀ t ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) T
      (CommAlgCat.of k k), t ∈ Set.range (BialgHom.mapDomain f'))
    (hgen : Subgroup.closure (Set.range (BialgHom.mapDomain (A := CommAlgCat.of k k) f) ∪
      Set.range (BialgHom.mapDomain (A := CommAlgCat.of k k) f')) = ⊤)
    (hT2 : ¬ Group.IsSolvable (WithConv (H →ₐ[k] k)))
    (hBorStab : ∀ (M : Type u) [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]
      (m : M) (hm : Module.IsUnimodular k m) (S : HopfIdeal k H),
      IsClosed (Set.range (projectiveOrbitMap (H := H) m hm)) →
      (∀ a : WithConv (H →ₐ[k] k),
        a ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) S
            (CommAlgCat.of k k) ↔
          projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint a.ofConv) =
            projectiveOrbitMap (H := H) m hm
              (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H))) →
      (∀ b : WithConv (K →ₐ[k] k), BialgHom.mapDomain f b ∈
        CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) S
          (CommAlgCat.of k k)) →
      Group.IsSolvable (CommHopfAlgCat.quotientPointsSubgroup
        (_root_.CommHopfAlgCat.of k (H)) S (CommAlgCat.of k k)) →
      ∀ a : WithConv (H →ₐ[k] k),
        a ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) S
          (CommAlgCat.of k k) → a ∈ Set.range (BialgHom.mapDomain f)) :
    OrbitInput f T := by
  intro M _ _ _ _ m hm S hclosed hstab hK hsolv
  refine ⟨hBorStab M m hm S hclosed hstab hK hsolv, ?_⟩
  obtain ⟨g, hg⟩ :=
    BialgHom.exists_projectiveOrbitMap_kernelPoint_fixed_of_isClosed_of_isSolvable f' m hm hclosed
  have hfix' : ∀ b : WithConv (K' →ₐ[k] k),
      projectiveOrbitMap (H := H) m hm
          (AlgHom.kernelPoint (BialgHom.mapDomain f' b * g).ofConv) =
        projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint g.ofConv) := fun b ↦ by
    rw [← projectivePointTranslation_projectiveOrbitMap_kernelPoint]; exact hg b
  refine ⟨g, fun t ht ↦ ?_, fun heq ↦ hT2 ?_⟩
  · obtain ⟨b, rfl⟩ := hTB t ht
    exact hfix' b
  · set G := CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) S
      (CommAlgCat.of k k)
    have hgS : g ∈ G := (hstab g).mpr heq
    have hB' : ∀ b, BialgHom.mapDomain f' b ∈ G := fun b ↦ by
      have h1 : BialgHom.mapDomain f' b * g ∈ G := (hstab _).mpr ((hfix' b).trans heq)
      simpa using G.mul_mem h1 (G.inv_mem hgS)
    have htop : G = ⊤ := by
      rw [eq_top_iff, ← hgen, Subgroup.closure_le]
      rintro _ (⟨b, rfl⟩ | ⟨b, rfl⟩)
      · exact hK b
      · exact hB' b
    have : Group.IsSolvable (⊤ : Subgroup (WithConv (H →ₐ[k] k))) := htop ▸ hsolv
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.topEquiv (G := WithConv (H →ₐ[k] k))).symm.toMonoidHom)
      (Subgroup.topEquiv (G := WithConv (H →ₐ[k] k))).symm.injective

end Assembly

end AlgMag.Reductive.R1Geometry
