/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RootDatumFromGFinal
import AlgMag.Reductive.DescentToField
import AlgMag.Reductive.TorusRigidity

/-!
# Split reductive data from properties of `G`

* `mem_roots_of_isNormalizingWith`: normalizing points preserve the roots;
* `barData`: split reductive data over `k̄`, `W` = image of `N_G(T)(k̄)` (finite by
  `finite_weylImage`), from `Z_G(T) = T` (`HypZ`);
* `mem_weylGroup_of_bar`: every `σ ∈ W` has a `k`-rational representative (chamber argument
  over `k̄`, reflections from (R1));
* `SplitReductiveData.ofR1R2`, `WithRootDatum.ofR1R2` and the §13 theorems `*_G` with hypotheses
  only on `G`: smooth, geometrically connected, finite type, (R1), (R2′) over `k̄`, (Z).
-/

suppress_compilation

open TensorProduct Magnetism TauCeti WithConv AlgMag.Weyl

namespace AlgMag.Reductive

universe u

section RootsStable

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- `torusCoact` is the orbit map of the universal point. -/
lemma torusCoact_eq_orbitHom (h : H) :
    torusCoact π h = (orbitHom π H (toConv (AlgHom.id k H))).ofConv h := by
  rw [orbitHom_apply]
  simp only [ofConv_toConv, Algebra.TensorProduct.map_id, AlgHom.id_apply]
  rfl

/-- **Conjugation by a normalizing point transports the grading**:
`ρ ∘ c_n = (c_n ⊗ σ_*) ∘ ρ`. -/
theorem torusCoact_pointConjugation {n : WithConv (H →ₐ[k] k)} {σ : X ≃* X}
    (hn : IsNormalizingWith π k n σ) (h : H) :
    torusCoact π (HopfAlgebra.pointConjugationAlgHom n h) =
      Algebra.TensorProduct.map (HopfAlgebra.pointConjugationAlgHom n)
        (MonoidAlgebra.mapDomainAlgHom k k σ.toMonoidHom) (torusCoact π h) := by
  set c := HopfAlgebra.pointConjugationAlgHom n
  set Φ : H ⊗[k] MonoidAlgebra k X →ₐ[k] H ⊗[k] MonoidAlgebra k X := Algebra.TensorProduct.map c (MonoidAlgebra.mapDomainAlgHom k k σ.toMonoidHom)
  set u : WithConv (H →ₐ[k] H) := toConv (AlgHom.id k H)
  set O := orbitHom π H u
  set nH := AlgHom.mapValue (Algebra.ofId k H) n
  set nB := AlgHom.mapValue (Algebra.ofId k (H ⊗[k] MonoidAlgebra k X)) n
  set iL := AlgHom.mapValue (H := H) (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := H)
    (B := MonoidAlgebra k X))
  have hnB : iL nH = nB := by
    apply WithConv.ext; ext x; simp [iL, nH, nB, AlgHom.mapValue_apply]
  have hnorm : nB * torusPoint π H * nB⁻¹ = twistPoint π H σ.toMonoidHom := by
    have := IsNormalizingWith.mapValue π (Algebra.ofId k H) hn
    rw [IsNormalizingWith, MulAut.conj_apply] at this
    rw [← hnB]; exact this
  have hΦt : AlgHom.mapValue Φ (torusPoint π H) = twistPoint π H σ.toMonoidHom := by
    apply WithConv.ext; ext x
    simp only [Φ, torusPoint, twistPoint, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
      Algebra.TensorProduct.includeRight_apply]
    erw [Algebra.TensorProduct.map_tmul, map_one]
  have hcu : toConv c = nH * u * nH⁻¹ := by
    have := HopfAlgebra.comp_pointConjugationAlgHom (A := H) n u
    rw [show u.ofConv = AlgHom.id k H from rfl, AlgHom.id_comp] at this
    exact this
  have hΦu : AlgHom.mapValue Φ (iL u) = nB * iL u * nB⁻¹ := by
    have : AlgHom.mapValue Φ (iL u) = iL (toConv c) := by
      apply WithConv.ext; ext x
      simp only [Φ, iL, u, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
        Algebra.TensorProduct.includeLeft_apply, AlgHom.id_apply]
      erw [Algebra.TensorProduct.map_tmul, map_one]
    rw [this, hcu, map_mul, map_mul, map_inv, hnB]
  have hO : O = torusPoint π H * iL u * (torusPoint π H)⁻¹ := rfl
  have key : AlgHom.mapValue Φ O = nB * O * nB⁻¹ := by
    rw [hO, map_mul, map_mul, map_inv (AlgHom.mapValue (H := H) Φ), hΦt, hΦu, ← hnorm]
    have hc : ∀ a : WithConv (H →ₐ[k] H ⊗[k] MonoidAlgebra k X), nB * a * nB⁻¹ = MulAut.conj nB a :=
      fun a => rfl
    rw [hc, hc, hc, ← map_inv, ← map_mul, ← map_mul]
  have hL := HopfAlgebra.comp_pointConjugationAlgHom (A := H ⊗[k] MonoidAlgebra k X) n O
  rw [torusCoact_eq_orbitHom, torusCoact_eq_orbitHom]
  have e1 : O.ofConv (c h) = (toConv (O.ofConv.comp c)).ofConv h := rfl
  rw [e1, hL, ← key]
  rfl

theorem pointConjugation_mem_torusGrading {n : WithConv (H →ₐ[k] k)} {σ : X ≃* X}
    (hn : IsNormalizingWith π k n σ) {χ : Additive X} {h : H} (hh : h ∈ torusGrading π χ) :
    HopfAlgebra.pointConjugationAlgHom n h ∈
      torusGrading π (Additive.ofMul (σ (Additive.toMul χ))) := by
  rw [mem_torusGrading] at hh ⊢
  rw [torusCoact_pointConjugation π hn, hh]
  simp

variable [Module.Finite k (Bialgebra.CotangentSpace k H)]

/-- **Normalizing points preserve the roots.** -/
theorem mem_roots_of_isNormalizingWith {n : WithConv (H →ₐ[k] k)} {σ : X ≃* X}
    (hn : IsNormalizingWith π k n σ) {α : Additive X} (hα : α ∈ roots π) :
    Additive.ofMul (σ (Additive.toMul α)) ∈ roots π := by
  have h0 : α ≠ 0 := ne_zero_of_mem_roots hα
  have h0' : Additive.ofMul (σ (Additive.toMul α)) ≠ 0 := by
    intro e
    apply h0
    have : σ (Additive.toMul α) = 1 := by simpa using congrArg Additive.toMul e
    simpa using (map_eq_one_iff σ σ.injective).1 this
  rw [← mem_tangentWeights_iff_mem_roots h0']
  obtain ⟨d, h, hh, hd⟩ := (mem_tangentWeights_iff_mem_roots h0).2 hα
  refine ⟨derivationComp (HopfAlgebra.pointConjugationBialgEquiv n⁻¹ : H →ₐc[k] H) d,
    HopfAlgebra.pointConjugationAlgHom n h, pointConjugation_mem_torusGrading π hn hh, ?_⟩
  rw [derivationComp_apply, HopfAlgebra.pointConjugationBialgEquiv_toAlgHom]
  have : HopfAlgebra.pointConjugationAlgHom n⁻¹ (HopfAlgebra.pointConjugationAlgHom n h) = h := by
    have := AlgHom.congr_fun (HopfAlgebra.pointConjugationAlgHom_mul n n⁻¹) h
    simpa using this.symm
  rw [this]; exact hd

end RootsStable

section Construction

open AlgMag.RootDatumBase

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable {π : H →ₐc[k] MonoidAlgebra k X}

/-- **(Z) gives `N_G(T)(A) = ⊔ n T(A)`**: two `A`-points normalizing `T` with the same
automorphism differ by a point of `T`, when `Z_G(T) = G^0 = T` (`J_0 = ker π`). -/
theorem exists_torus_of_normalizing_same (hπ : Function.Surjective π)
    (hZ : magnetIdeal (torusGrading π) ⊥ = RingHom.ker π.toAlgHom)
    {A : Type u} [CommRing A] [Algebra k A] [Nontrivial A] {y r : WithConv (H →ₐ[k] A)}
    {σ : X ≃* X} (hy : IsNormalizingWith π A y σ) (hr : IsNormalizingWith π A r σ) :
    ∃ t : MonoidAlgebra k X →ₐ[k] A, y = r * toConv (t.comp π.toAlgHom) := by
  have ht := IsNormalizingWith.mul π hy (IsNormalizingWith.inv π hr)
  rw [mul_inv_cancel] at ht
  have hbot : r⁻¹ * y ∈ attractorSubgroup π ⊥ A :=
    (mem_attractorSubgroup_iff_weylMagnet_le π hπ ht ⊥).2 weylMagnet_one_le_bot
  have hker : RingHom.ker π.toAlgHom ≤ RingHom.ker (r⁻¹ * y).ofConv := by
    rw [← hZ]; exact (mem_attractorSubgroup π).1 hbot
  have hs : Function.Surjective π.toAlgHom := hπ
  let e := Ideal.quotientKerAlgEquivOfSurjective (f := π.toAlgHom) hs
  refine ⟨(Ideal.Quotient.liftₐ (RingHom.ker π.toAlgHom) (r⁻¹ * y).ofConv
    fun a ha => hker ha).comp e.symm.toAlgHom, ?_⟩
  have h2 : toConv (((Ideal.Quotient.liftₐ (RingHom.ker π.toAlgHom) (r⁻¹ * y).ofConv
      fun a ha => hker ha).comp e.symm.toAlgHom).comp π.toAlgHom) = r⁻¹ * y := by
    apply WithConv.ofConv_injective
    ext x
    rw [ofConv_toConv]
    show (Ideal.Quotient.liftₐ (RingHom.ker π.toAlgHom) (r⁻¹ * y).ofConv fun a ha => hker ha)
      (e.symm (π.toAlgHom x)) = _
    rw [show e.symm (π.toAlgHom x) = Ideal.Quotient.mk _ x from e.symm_apply_eq.2 rfl]
    rfl
  rw [h2, mul_inv_cancel_left]

variable [Algebra.FiniteType k H]

local notation "K" => AlgebraicClosure k

/-- **Split reductive data over `k̄`** with `W` the image of `N_G(T)(k̄)` in `Aut X`. -/
def barData [Group.FG X] (hπ : Function.Surjective π)
    (hZ : magnetIdeal (torusGrading π) ⊥ = RingHom.ker π.toAlgHom) :
    SplitReductiveData (piBar π) where
  surjective := torusBaseChange_surjective _ hπ
  W := weylGroup π K
  finite := (finite_weylImage π hπ K).to_subtype
  rep w := bcPoints K K (Classical.choose w.2)
  rep_normalizing w := by
    rw [isNormalizingWith_baseChange_iff, MulEquiv.symm_apply_apply]
    exact Classical.choose_spec w.2
  normalizer_cover g σ hg := by
    let L := AlgebraicClosure K
    have h0 := (isNormalizingWith_baseChange_iff K π L g σ).1 hg
    let φ : L ≃ₐ[k] K := IsAlgClosure.equiv k L K
    have hσ : σ ∈ weylGroup π K := ⟨_, IsNormalizingWith.mapValue π φ.toAlgHom h0⟩
    refine ⟨hσ, ?_⟩
    set r := bcPoints K K (Classical.choose hσ)
    have hr : IsNormalizingWith (piBar π) K r σ := by
      rw [isNormalizingWith_baseChange_iff, MulEquiv.symm_apply_apply]
      exact Classical.choose_spec hσ
    have hr' := (isNormalizingWith_baseChange_iff K π L _ σ).1
      (IsNormalizingWith.mapValue (piBar π) (Algebra.ofId K L) hr)
    obtain ⟨t, ht⟩ := exists_torus_of_normalizing_same hπ hZ h0 hr'
    let χ : X →* L := t.toRingHom.toMonoidHom.comp (MonoidAlgebra.of k X)
    let t' : MonoidAlgebra K X →ₐ[K] L := MonoidAlgebra.lift K L X χ
    refine ⟨t', ?_⟩
    have hcomp : (t'.restrictScalars k).comp
        ((MonoidAlgebra.mapAlgHom X (Algebra.ofId k K)).restrictScalars k) = t := by
      apply MonoidAlgebra.algHom_ext
      · intro x
        simp [t', χ]
      · exact Subsingleton.elim _ _
    have ht' : ∀ p, t' (MonoidAlgebra.mapAlgHom X (Algebra.ofId k K) p) = t p :=
      fun p => by simpa using congrArg (fun F : MonoidAlgebra k X →ₐ[k] L => F p) hcomp
    apply (bcPoints (k := k) (H := H) K L).symm.injective
    rw [ht, map_mul]
    congr 1
    apply WithConv.ext
    ext h
    simp [torusPointOf, AlgHom.mapValue_apply]
    exact (ht' _).symm
  roots_stable w hw α hα := by
    obtain ⟨n, hn⟩ := hw
    have hn' : IsNormalizingWith (piBar π) K (bcPoints K K n) w := by
      rw [isNormalizingWith_baseChange_iff, MulEquiv.symm_apply_apply]; exact hn
    exact mem_roots_of_isNormalizingWith (piBar π) hn' hα

end Construction

section FromG

open AlgMag.RootDatumBase

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable {π : H →ₐc[k] MonoidAlgebra k X}
variable [Algebra.FiniteType k H] [Algebra.Smooth k H] [Monoid.FG X] [IsMulTorsionFree X]
  [Module.IsTorsionFree ℤ (Additive X)] [Module.Finite ℤ (Additive X)]

local notation "K" => AlgebraicClosure k

/-- **(R1)**: for every root `α`, a `k`-point of `N_{G^{ℤα}}(T)` acting by `σ ≠ 1`. -/
def HypR1 (π : H →ₐc[k] MonoidAlgebra k X) : Prop :=
  ∀ α ∈ roots π, ∃ (n : WithConv (H →ₐ[k] k)) (σ : X ≃* X), IsNormalizingWith π k n σ ∧
    n ∈ attractorSubgroup π (lineMagnet α) k ∧ σ ≠ 1

/-- **(R2′)** over `k̄`: for every root `α`, `O(U_α)` of `G_{k̄}` is monogenic. -/
def HypR2 (π : H →ₐc[k] MonoidAlgebra k X) : Prop :=
  ∀ (α : Additive X) (hα : α ∈ roots (piBar π)), ∃ y : K ⊗[k] H, Function.Surjective
    (Polynomial.aeval (R := K) (Ideal.Quotient.mk
      (rootGroupIdeal (piBar π) α (nsmul_eq_zero_of_mem_roots hα)).toIdeal y))

/-- **(Z)**: `Z_G(T) = G^0 = T`. -/
def HypZ (π : H →ₐc[k] MonoidAlgebra k X) : Prop :=
  magnetIdeal (torusGrading π) ⊥ = RingHom.ker π.toAlgHom

omit [Algebra.Smooth k H] [Monoid.FG X] [IsMulTorsionFree X] [Module.IsTorsionFree ℤ (Additive X)]
  [Module.Finite ℤ (Additive X)] in
lemma isNormalizingWith_bar {n : WithConv (H →ₐ[k] k)} {σ : X ≃* X}
    (hn : IsNormalizingWith π k n σ) :
    IsNormalizingWith (piBar π) K (bcPoints K K (toAlgClosure n)) σ := by
  rw [isNormalizingWith_baseChange_iff, MulEquiv.symm_apply_apply]
  exact IsNormalizingWith.mapValue π _ hn

omit [Algebra.Smooth k H] [Monoid.FG X] [IsMulTorsionFree X] [Module.IsTorsionFree ℤ (Additive X)]
  [Module.Finite ℤ (Additive X)] in
/-- (R1) for `G_{k̄}`. -/
theorem hypR1_bar (hπ : Function.Surjective π) (hR1 : HypR1 π) :
    ∀ α ∈ roots (piBar π), ∃ (n : WithConv (K ⊗[k] H →ₐ[K] K)) (σ : X ≃* X),
      IsNormalizingWith (piBar π) K n σ ∧ n ∈ attractorSubgroup (piBar π) (lineMagnet α) K ∧
        σ ≠ 1 := by
  intro α hα
  rw [roots_piBar] at hα
  obtain ⟨n, σ, hn, hnα, hσ⟩ := hR1 α hα
  have hn' := isNormalizingWith_bar hn
  exact ⟨_, σ, hn', (mem_lineAttractor_iff (torusBaseChange_surjective _ hπ) hn' α).2
    ((mem_lineAttractor_iff hπ hn α).1 hnα), hσ⟩

variable [ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] H))]

/-- **`W = W'`: every element of the image of `N_G(T)(k̄)` has a `k`-rational representative.**
Chamber argument over `k̄` (`WeylAlt.exists_weylGroup_rootPairing`), then each reflection
`s_α` is the automorphism of the `k`-point `n_α` of (R1). -/
theorem mem_weylGroup_of_bar (hπ : Function.Surjective π) (hZ : HypZ π) (hR1 : HypR1 π)
    (hR2 : HypR2 π) {σ : X ≃* X} (hσ : σ ∈ weylGroup π K) : σ ∈ weylGroup π k := by
  haveI : Group.FG X := Group.fg_iff_monoid_fg.mpr inferInstance
  let Db := barData hπ hZ
  let Dr := SplitReductiveData.WithReflections.ofLineAttractor Db (hypR1_bar hπ hR1)
  have hdr : ∀ α (hα : α ∈ roots (piBar π)), Module.finrank K (rootSpace (piBar π) α) = 1 ∧
      ∀ n : ℕ, 2 ≤ n → n • α ∉ roots (piBar π) := fun α hα =>
    (RankOne.finrank_rootSpace_eq_one_and_reduced_iff (nsmul_eq_zero_of_mem_roots hα) hα).mpr
      (hR2 α hα)
  haveI := Dr.isReduced_rootPairing fun α hα => (hdr α hα).2
  obtain ⟨g, hg⟩ := WeylAlt.exists_weylGroup_rootPairing Dr (baseInt _) ⟨σ, hσ⟩
  have key : ∀ g : Dr.rootPairing.weylGroup, ∃ τ ∈ weylGroup π k,
      ∀ m : Additive X, (g : Dr.rootPairing.Aut) • m = actW τ m := by
    rintro ⟨g, hg⟩
    induction hg using RootPairing.weylGroup.induction with
    | mem i =>
      have hi : (i : Additive X) ∈ roots π := by rw [← roots_piBar π]; exact i.2
      obtain ⟨n, τ, hn, hnα, hτ⟩ := hR1 _ hi
      have hn' := isNormalizingWith_bar hn
      have hnα' := (mem_lineAttractor_iff (torusBaseChange_surjective _ hπ) hn' _).2
        ((mem_lineAttractor_iff hπ hn _).1 hnα)
      have hrefl := isReflectionOn_of_mem_lineAttractor Db i.2 hn' hnα' hτ
      have hτW : τ ∈ Db.W := ⟨toAlgClosure n, IsNormalizingWith.mapValue π _ hn⟩
      have heq : (⟨τ, hτW⟩ : Dr.W) = Dr.refl i := Dr.refl_eq i hrefl.1 hrefl.2
      refine ⟨τ, ⟨n, hn⟩, fun m => ?_⟩
      have h1 : Dr.refl i • m = actW τ m := by rw [← heq]; rfl
      rw [← h1, ← Dr.reflection_rootPairing]
      rfl
    | one => exact ⟨1, one_mem _, fun m => by simp; rfl⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨τ, hτ, h⟩ := ihx
      obtain ⟨τ', hτ', h'⟩ := ihy
      exact ⟨τ * τ', mul_mem hτ hτ', fun m => by rw [mul_smul, h', h]; rfl⟩
  obtain ⟨τ, hτ, hτg⟩ := key g
  have : σ = τ := MulEquiv.ext fun x =>
    congrArg Additive.toMul ((hg (Additive.ofMul x)).symm.trans (hτg _))
  exact this ▸ hτ

/-- **Split reductive data from `G`**: `G` smooth, geometrically connected, of finite type over a
field `k`, `T = D(X)` split, with (R1), (R2′) and (Z). `W` is the image of `N_G(T)(k̄)` in
`Aut X` (finite by rigidity of tori). -/
def SplitReductiveData.ofR1R2 (hπ : Function.Surjective π) (hZ : HypZ π) (hR1 : HypR1 π)
    (hR2 : HypR2 π) : SplitReductiveData π where
  surjective := hπ
  W := weylGroup π K
  finite := by
    haveI : Group.FG X := Group.fg_iff_monoid_fg.mpr inferInstance
    exact (finite_weylImage π hπ K).to_subtype
  rep w := Classical.choose (mem_weylGroup_of_bar hπ hZ hR1 hR2 w.2)
  rep_normalizing w := Classical.choose_spec (mem_weylGroup_of_bar hπ hZ hR1 hR2 w.2)
  normalizer_cover g σ hg := by
    refine ⟨⟨g, hg⟩, ?_⟩
    obtain ⟨t, ht⟩ := exists_torus_of_normalizing_same hπ hZ hg (IsNormalizingWith.mapValue π
      (Algebra.ofId k K) (Classical.choose_spec (mem_weylGroup_of_bar hπ hZ hR1 hR2 ⟨g, hg⟩)))
    exact ⟨t, ht⟩
  roots_stable w hw α hα := by
    haveI : Group.FG X := Group.fg_iff_monoid_fg.mpr inferInstance
    have := (barData hπ hZ).roots_stable w hw α (by rwa [roots_piBar])
    rwa [roots_piBar] at this

end FromG

section Corollaries

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable {π : H →ₐc[k] MonoidAlgebra k X}
variable [Algebra.FiniteType k H] [Algebra.Smooth k H] [Monoid.FG X] [IsMulTorsionFree X]
  [Module.IsTorsionFree ℤ (Additive X)] [Module.Finite ℤ (Additive X)]
  [ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] H))]
variable (hπ : Function.Surjective π) (hZ : HypZ π) (hR1 : HypR1 π) (hR2 : HypR2 π)
include hπ hZ hR1 hR2

/-- Split reductive data with root spaces of dimension one for `G_{k̄}`, from `G`. -/
def SplitReductiveData.WithRootSpaces.barOfR1R2 : SplitReductiveData.WithRootSpaces (piBar π) :=
  haveI : Group.FG X := Group.fg_iff_monoid_fg.mpr inferInstance
  (barData hπ hZ).toWithRootSpacesOfRankOne (hypR1_bar hπ hR1) hR2

/-- **The root datum of `G`**, from (R1), (R2′), (Z): `WithRootDatum π` over `k`. -/
def SplitReductiveData.WithRootDatum.ofR1R2 : SplitReductiveData.WithRootDatum π :=
  let WR := (SplitReductiveData.WithRootSpaces.barOfR1R2 hπ hZ hR1 hR2).toWithRootDatum
  { SplitReductiveData.ofR1R2 hπ hZ hR1 hR2 with
    ι := WR.ι
    finite_ι := WR.finite_ι
    N := WR.N
    addCommGroup_N := WR.addCommGroup_N
    P := WR.P
    crystallographic := WR.crystallographic
    reduced := WR.reduced
    b := WR.b
    range_root := WR.range_root.trans (roots_piBar π)
    weyl_eq := WR.weyl_eq }

/-- **Theorem `thm:red-pure`** for `G` with (R1), (R2′), (Z). -/
theorem red_pure_G (N : AddSubmonoid (Additive X)) :
    Rooted.reductiveHull (roots π) (fun w : weylGroup π (AlgebraicClosure k) => actW (w : X ≃* X)) N =
      sInf {L | affineY (torusGrading π) L = affineY (torusGrading π) N} :=
  red_pure_field (SplitReductiveData.ofR1R2 hπ hZ hR1 hR2) N

/-- **Theorem `thm:red-classification` (i)**, finiteness of `Π(a)`, for `G`. -/
theorem finite_pure_G : {N | IsPure (affineY (torusGrading π)) N}.Finite :=
  finite_pure_field (SplitReductiveData.ofR1R2 hπ hZ hR1 hR2)

/-- **Theorem `thm:red-classification` (i)**, bijection, for `G`. -/
theorem red_classification_G :
    Set.BijOn (Rooted.pairOf (roots π)
          (fun w : weylGroup π (AlgebraicClosure k) => actW (w : X ≃* X)))
        {N | IsPure (affineY (torusGrading π)) N}
        {p | Rooted.IsCompatiblePair (roots π)
          (fun w : weylGroup π (AlgebraicClosure k) => actW (w : X ≃* X)) p} ∧
      Set.InvOn (fun p : Set (Additive X) × Set (weylGroup π (AlgebraicClosure k)) =>
          Rooted.pairMagnet (fun w : weylGroup π (AlgebraicClosure k) => actW (w : X ≃* X))
            p.1 p.2)
        (Rooted.pairOf (roots π)
          (fun w : weylGroup π (AlgebraicClosure k) => actW (w : X ≃* X)))
        {N | IsPure (affineY (torusGrading π)) N}
        {p | Rooted.IsCompatiblePair (roots π)
          (fun w : weylGroup π (AlgebraicClosure k) => actW (w : X ≃* X)) p} :=
  red_classification_i_field (SplitReductiveData.ofR1R2 hπ hZ hR1 hR2)

/-- **Theorem `thm:red-classification` (ii)** for `G`. -/
theorem red_classification_ii_G {R : Set (Additive X)} (hRΦ : R ⊆ roots π)
    (hR : (AddSubmonoid.closure R : Set (Additive X)) ∩ roots π = R) :
    IsPure (affineY (torusGrading π))
        (sInf {L | affineY (torusGrading π) L =
          affineY (torusGrading π) (AddSubmonoid.closure R)}) ∧
      ((sInf {L | affineY (torusGrading π) L =
          affineY (torusGrading π) (AddSubmonoid.closure R)} : AddSubmonoid (Additive X)) :
          Set (Additive X)) ∩ roots π = R :=
  classification_ii_field (SplitReductiveData.ofR1R2 hπ hZ hR1 hR2) hRΦ hR

/-- **Theorem `thm:red-rooted`** for `G`. -/
theorem reductive_joinDense_G :
    Rooted.IsJoinDense (IsPure (affineY (torusGrading π)))
      (Rooted.reductiveRoot (roots π)
        fun w : weylGroup π (AlgebraicClosure k) => actW (w : X ≃* X)) :=
  reductive_joinDense_field (SplitReductiveData.ofR1R2 hπ hZ hR1 hR2)

/-- **Theorem `thm:red-SL-Sp`** for `G`. -/
theorem red_SL_Sp_G :
    List.TFAE [Set.BijOn (fun N : AddSubmonoid (Additive X) => (N : Set (Additive X)) ∩
          roots π)
        {N | IsPure (affineY (torusGrading π)) N} {E | Rooted.IsStableElt (roots π) E},
      Rooted.IsJoinDense (IsPure (affineY (torusGrading π))) (Rooted.mono '' roots π),
      SLSp.JoinIrredWeylGenerated (roots π)
        (fun w : weylGroup π (AlgebraicClosure k) => actW (w : X ≃* X))] :=
  red_SL_Sp_field (SplitReductiveData.WithRootDatum.ofR1R2 hπ hZ hR1 hR2)

/-- **Corollary `cor:red-monogenic`** for `G`. -/
theorem red_mono_bijOn_G :
    Set.BijOn (fun a : Additive X => AddSubmonoid.closure {a}) (roots π)
      {N | IsPure (affineY (torusGrading π)) N ∧ (∃ x, N = AddSubmonoid.closure {x}) ∧
        N ≠ ⊥} :=
  red_mono_bijOn_field (SplitReductiveData.WithRootDatum.ofR1R2 hπ hZ hR1 hR2)

open TauCeti.Cocharacter in
/-- **Theorem `thm:red-parabolic`, `G^N = P_ξ`**, for `G`, with the base `B` of the root datum
`WithRootDatum.ofR1R2`. -/
theorem red_parabolic_G (ψ : X →* Multiplicative ℤ) {N : AddSubmonoid (Additive X)}
    (hBN : (SplitReductiveData.WithRootDatum.ofR1R2 hπ hZ hR1 hR2).P.root ''
      (SplitReductiveData.WithRootDatum.ofR1R2 hπ hZ hR1 hR2).b.support ⊆ N)
    (hξ : ∀ α ∈ Parabolic.xi ((SplitReductiveData.WithRootDatum.ofR1R2 hπ hZ hR1 hR2).P.root ''
      (SplitReductiveData.WithRootDatum.ofR1R2 hπ hZ hR1 hR2).b.support) N, pairingHom ψ α = 0)
    (hpos : ∀ α ∈ (SplitReductiveData.WithRootDatum.ofR1R2 hπ hZ hR1 hR2).P.root ''
        (SplitReductiveData.WithRootDatum.ofR1R2 hπ hZ hR1 hR2).b.support,
      α ∉ Parabolic.xi ((SplitReductiveData.WithRootDatum.ofR1R2 hπ hZ hR1 hR2).P.root ''
        (SplitReductiveData.WithRootDatum.ofR1R2 hπ hZ hR1 hR2).b.support) N →
          0 < pairingHom ψ α) :
    magnetIdeal (torusGrading π) N =
      (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal :=
  red_parabolic_field (SplitReductiveData.WithRootDatum.ofR1R2 hπ hZ hR1 hR2) ψ hBN hξ hpos

/-- **Proposition `prop:root-groups` (i)** for `G_{k̄}`: `U_α` is a root group. -/
theorem isRootGroup_G {α : Additive X} (hα : α ∈ roots (piBar π)) :
    IsRootGroup (piBar π) α (rootGroupIdeal (piBar π) α (nsmul_eq_zero_of_mem_roots hα)) :=
  isRootGroup_of_withRootSpaces (D := SplitReductiveData.WithRootSpaces.barOfR1R2 hπ hZ hR1 hR2) hα

end Corollaries

end AlgMag.Reductive

