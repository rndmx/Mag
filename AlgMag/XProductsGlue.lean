/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import AlgMag.GeneralBase

/-!
# X-products of attractors: the scheme `𝔸(𝒩)` (Proposition 3.1)

Mayeux, *Algebraic magnetism: X-products of attractors via F₁-geometry*, Semigroup Forum,
doi 10.1007/s00233-026-10695-7, §3.

`M` is a finitely generated abelian group and `𝒩 = {N_α}` is a family of fine submonoids of `M` with
common group completion `Z`. Then `D(Z) → 𝔸(N_α)` is an open immersion and the schemes `𝔸(N_α)` glue
along `D(Z)`.

## Main results

* `AlgMag.XP.MagnetFamily`: the data `𝒩`.
* `AlgMag.XP.isOpenImmersion_gpMap`: `D(Z) → 𝔸(N_α)` is an open immersion ("cf. [6, p. 67]").
* `AlgMag.XP.MagnetFamily.prop31`: **Proposition 3.1**.
* `AlgMag.XP.MagnetFamily.exists_factor_of_overlap`: `𝔸(N_α) ∩ 𝔸(N_β) = D(Z)` in `𝔸(𝒩)`, `α ≠ β`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

set_option linter.unusedSectionVars false

namespace AlgMag.XP

open GB

section Localization

variable {M : Type u} [AddCommGroup M]

/-- For a finitely generated submonoid `N`, the sum `s` of its generators is a common denominator of
the group completion: every `z ∈ N^gp` has `z + k s ∈ N` for some `k`. -/
theorem exists_denominator {N : AddSubmonoid M} (hN : N.FG) :
    ∃ s ∈ N, ∀ z ∈ AddSubgroup.closure (N : Set M), ∃ k : ℕ, z + k • s ∈ N := by
  classical
  obtain ⟨G, hG⟩ := hN
  have hGN : ∀ g ∈ G, g ∈ N := fun g hg => hG ▸ AddSubmonoid.subset_closure hg
  let s : M := ∑ g ∈ G, g
  have hs : s ∈ N := N.sum_mem hGN
  have hneg : ∀ g ∈ G, -g + s ∈ N := by
    intro g hg
    have e : -g + s = ∑ x ∈ G.erase g, x := by
      have hsum : s = g + ∑ x ∈ G.erase g, x := (Finset.add_sum_erase G (fun x => x) hg).symm
      rw [hsum]
      abel
    rw [e]
    exact N.sum_mem fun x hx => hGN x (Finset.mem_of_mem_erase hx)
  let H : AddSubgroup M :=
    { carrier := {z | (∃ k : ℕ, z + k • s ∈ N) ∧ ∃ k : ℕ, -z + k • s ∈ N}
      zero_mem' := ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩
      add_mem' := by
        rintro a b ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩ ⟨⟨l, hl⟩, ⟨l', hl'⟩⟩
        refine ⟨⟨k + l, ?_⟩, ⟨k' + l', ?_⟩⟩
        · have := N.add_mem hk hl
          rwa [show a + k • s + (b + l • s) = a + b + (k + l) • s by rw [add_nsmul]; abel] at this
        · have := N.add_mem hk' hl'
          rwa [show -a + k' • s + (-b + l' • s) = -(a + b) + (k' + l') • s by
            rw [add_nsmul]; abel] at this
      neg_mem' := by
        rintro a ⟨h1, h2⟩
        exact ⟨by simpa using h2, by simpa using h1⟩ }
  have hNH : N ≤ H.toAddSubmonoid := by
    rw [← hG, AddSubmonoid.closure_le]
    intro g hg
    refine ⟨⟨0, by simpa using hGN g hg⟩, ⟨1, by simpa using hneg g hg⟩⟩
  refine ⟨s, hs, fun z hz => ?_⟩
  have : AddSubgroup.closure (N : Set M) ≤ H := (AddSubgroup.closure_le _).mpr fun x hx => hNH hx
  exact (this hz).1

/-- `ℤ[N] → ℤ[N^gp]` is a localization at the monomial `X^s`, for `N` finitely generated. -/
theorem isLocalization_away_gp {N : AddSubmonoid M} {L : AddSubmonoid M} (h : N ≤ L) {s : M}
    (hs : s ∈ N) (hL : ∀ z ∈ L, ∃ k : ℕ, z + k • s ∈ N) (hn : ∀ z ∈ L, -z ∈ L) :
    letI := (AddMonoidAlgebra.mapDomainRingHom ℤ (AddSubmonoid.inclusion h)).toAlgebra
    IsLocalization.Away (AddMonoidAlgebra.single (⟨s, hs⟩ : N) (1 : ℤ)) (AddMonoidAlgebra ℤ L) := by
  let := (AddMonoidAlgebra.mapDomainRingHom ℤ (AddSubmonoid.inclusion h)).toAlgebra
  let θ := AddMonoidAlgebra.mapDomainRingHom ℤ (AddSubmonoid.inclusion h)
  have hmap : ∀ x, algebraMap (AddMonoidAlgebra ℤ N) (AddMonoidAlgebra ℤ L) x = θ x := fun _ => rfl
  have hsingle : ∀ (n : N) (r : ℤ), θ (AddMonoidAlgebra.single n r) =
      AddMonoidAlgebra.single (AddSubmonoid.inclusion h n) r := by
    intro n r; simp [θ]
  have hsL : s ∈ L := h hs
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, k, rfl⟩
    rw [map_pow, hmap, hsingle]
    refine IsUnit.pow k (IsUnit.of_mul_eq_one (AddMonoidAlgebra.single (⟨-s, hn s hsL⟩ : L) 1) ?_)
    rw [AddMonoidAlgebra.single_mul_single, one_mul]
    have : (AddSubmonoid.inclusion h ⟨s, hs⟩ + ⟨-s, hn s hsL⟩ : L) = 0 :=
      Subtype.ext (add_neg_cancel s)
    rw [this]
    rfl
  · intro z
    have key : ∃ k : ℕ, ∃ x : AddMonoidAlgebra ℤ N,
        z * (AddMonoidAlgebra.single (⟨s, hsL⟩ : L) 1) ^ k = θ x := by
      induction z using AddMonoidAlgebra.induction_linear with
      | zero => exact ⟨0, 0, by simp⟩
      | add a b ha hb =>
        obtain ⟨k, x, hx⟩ := ha
        obtain ⟨l, y, hy⟩ := hb
        let g : AddMonoidAlgebra ℤ N := AddMonoidAlgebra.single ⟨s, hs⟩ 1
        have hg : θ g = AddMonoidAlgebra.single (⟨s, hsL⟩ : L) 1 := hsingle _ _
        refine ⟨k + l, x * g ^ l + y * g ^ k, ?_⟩
        rw [map_add, map_mul, map_mul, map_pow, map_pow, hg, ← hx, ← hy, pow_add]
        ring
      | single n r =>
        obtain ⟨k, hk⟩ := hL n n.2
        refine ⟨k, AddMonoidAlgebra.single ⟨n + k • s, hk⟩ r, ?_⟩
        rw [hsingle, AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_mul_single,
          one_pow, mul_one]
        congr 1
    obtain ⟨k, x, hx⟩ := key
    refine ⟨⟨x, ⟨AddMonoidAlgebra.single (⟨s, hs⟩ : N) 1 ^ k, k, rfl⟩⟩, ?_⟩
    change z * algebraMap _ _ (AddMonoidAlgebra.single (⟨s, hs⟩ : N) 1 ^ k) = algebraMap _ _ x
    rw [hmap, hmap, hx.symm, map_pow, hsingle]
    rfl
  · intro x y hxy
    refine ⟨1, ?_⟩
    have hinj : Function.Injective θ := by
      intro a b hab
      apply AddMonoidAlgebra.coeff_injective
      exact Finsupp.mapDomain_injective (AddSubmonoid.inclusion_injective h)
        (congrArg AddMonoidAlgebra.coeff hab)
    rw [hinj hxy]

/-- **§3, "cf. [6, p. 67]"**: for a finitely generated submonoid `N` of `M`, with group completion the
subgroup `Z`, the morphism `D(Z) → 𝔸(N)` is an open immersion. -/
theorem isOpenImmersion_gpMap {N : AddSubmonoid M} (hN : N.FG) {Z : AddSubgroup M}
    (hZ : AddSubgroup.closure (N : Set M) = Z) (h : N ≤ Z.toAddSubmonoid) :
    IsOpenImmersion (AZmap (AddSubmonoid.inclusion h)) := by
  obtain ⟨s, hs, hk⟩ := exists_denominator hN
  letI := (AddMonoidAlgebra.mapDomainRingHom ℤ (AddSubmonoid.inclusion h)).toAlgebra
  haveI := isLocalization_away_gp h hs (fun z hz => hk z (by rw [hZ]; exact hz))
    (fun z hz => Z.neg_mem hz)
  exact IsOpenImmersion.of_isLocalization (AddMonoidAlgebra.single (⟨s, hs⟩ : N) (1 : ℤ))

end Localization

/-- §3. A family `𝒩 = {N_α}` of fine submonoids of the abelian group `M` with a common group
completion `Z = N_α^gp`. (Submonoids of a group are integral, so fine means finitely generated.) -/
structure MagnetFamily (M : Type u) [AddCommGroup M] (A : Type u) where
  /-- The submonoids. -/
  N : A → AddSubmonoid M
  /-- The common group completion `N^gp`. -/
  Z : AddSubgroup M
  fg : ∀ α, (N α).FG
  gp : ∀ α, AddSubgroup.closure (N α : Set M) = Z

variable {M : Type u} [AddCommGroup M] {A : Type u} (𝓝 : MagnetFamily M A)

namespace MagnetFamily

lemma le (α : A) : 𝓝.N α ≤ 𝓝.Z.toAddSubmonoid := by
  intro x hx
  change x ∈ 𝓝.Z
  rw [← 𝓝.gp α]
  exact AddSubgroup.subset_closure hx

/-- `D(Z) = 𝔸(Z)`, as a scheme. -/
noncomputable abbrev D : Scheme.{u} := AZ 𝓝.Z.toAddSubmonoid

/-- `h_α : D(Z) → 𝔸(N_α)`, dual to `N_α ⊆ Z`. -/
noncomputable def gpMap (α : A) : 𝓝.D ⟶ AZ (𝓝.N α) := AZmap (AddSubmonoid.inclusion (𝓝.le α))

instance (α : A) : IsOpenImmersion (𝓝.gpMap α) :=
  isOpenImmersion_gpMap (𝓝.fg α) (𝓝.gp α) (𝓝.le α)

/-- The diagram `D(Z) → 𝔸(N_α)`, `α ∈ A`, of Proposition 3.1. -/
noncomputable def diag : WidePushoutShape A ⥤ Scheme.{u} :=
  WidePushoutShape.wideSpan 𝓝.D (fun α => AZ (𝓝.N α)) 𝓝.gpMap

instance {i j : WidePushoutShape A} (f : i ⟶ j) : IsOpenImmersion (𝓝.diag.map f) := by
  cases f with
  | id => simp only [diag]; change IsOpenImmersion (𝟙 _); infer_instance
  | init α => exact inferInstanceAs (IsOpenImmersion (𝓝.gpMap α))

instance : Small.{u} (WidePushoutShape A) := inferInstanceAs (Small.{u} (Option A))

/-- **Proposition 3.1**: the diagram `D(N^gp) → 𝔸(N_α)` admits a colimit in the category of schemes. -/
theorem prop31 : HasColimit 𝓝.diag := inferInstance

instance : HasColimit 𝓝.diag := 𝓝.prop31

/-- The scheme `𝔸(𝒩)` of **Proposition 3.1**. -/
noncomputable def AN : Scheme.{u} := colimit 𝓝.diag

/-- The morphism `𝔸(N_α) → 𝔸(𝒩)`. -/
noncomputable def ι (α : A) : AZ (𝓝.N α) ⟶ 𝓝.AN := colimit.ι 𝓝.diag (some α)

/-- The morphism `D(Z) → 𝔸(𝒩)`. -/
noncomputable def ιD : 𝓝.D ⟶ 𝓝.AN := colimit.ι 𝓝.diag none

/-- The proof of **Proposition 3.1**: each `𝔸(N_α) → 𝔸(𝒩)` is an open immersion. -/
instance isOpenImmersion_ι (α : A) : IsOpenImmersion (𝓝.ι α) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι 𝓝.diag (some α)))

instance (α : A) : Mono (𝓝.ι α) := inferInstance

@[reassoc] lemma gpMap_ι (α : A) : 𝓝.gpMap α ≫ 𝓝.ι α = 𝓝.ιD :=
  colimit.w 𝓝.diag (WidePushoutShape.Hom.init α)

/-- **Proposition 3.1**, universal property: families of morphisms `𝔸(N_α) → Y` agreeing on `D(Z)` glue
uniquely. -/
noncomputable def desc {Y : Scheme.{u}} (f : ∀ α, AZ (𝓝.N α) ⟶ Y) (f₀ : 𝓝.D ⟶ Y)
    (hf : ∀ α, 𝓝.gpMap α ≫ f α = f₀) : 𝓝.AN ⟶ Y :=
  colimit.desc 𝓝.diag (WidePushoutShape.mkCocone (F := 𝓝.diag) f₀ f hf)

@[reassoc (attr := simp)] lemma ι_desc {Y : Scheme.{u}} (f : ∀ α, AZ (𝓝.N α) ⟶ Y) (f₀ : 𝓝.D ⟶ Y)
    (hf : ∀ α, 𝓝.gpMap α ≫ f α = f₀) (α : A) : 𝓝.ι α ≫ 𝓝.desc f f₀ hf = f α :=
  colimit.ι_desc (F := 𝓝.diag) (WidePushoutShape.mkCocone (F := 𝓝.diag) f₀ f hf) (some α : WidePushoutShape A)

/-- Every point of `𝔸(𝒩)` lies in some `𝔸(N_α)`, `A` being nonempty. -/
lemma exists_mem_range [Nonempty A] (x : 𝓝.AN) : ∃ α, x ∈ Set.range (𝓝.ι α) := by
  obtain ⟨i, xi, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective 𝓝.diag x
  cases i with
  | none =>
    obtain ⟨α⟩ := ‹Nonempty A›
    refine ⟨α, (𝓝.gpMap α) (show 𝓝.D from xi), ?_⟩
    exact congrArg (fun k : 𝓝.D ⟶ 𝓝.AN => k (show 𝓝.D from xi)) (𝓝.gpMap_ι α)
  | some α => exact ⟨α, xi, rfl⟩

/-- `𝔸(N_α) ∩ 𝔸(N_β) = D(Z)` inside `𝔸(𝒩)` for `α ≠ β`: two morphisms to `𝔸(N_α)`, `𝔸(N_β)` with the
same image in `𝔸(𝒩)` come from a morphism to `D(Z)`. -/
theorem exists_factor_of_overlap {W : Scheme.{u}} {α β : A} (hne : α ≠ β) (a : W ⟶ AZ (𝓝.N α))
    (b : W ⟶ AZ (𝓝.N β)) (e : a ≫ 𝓝.ι α = b ≫ 𝓝.ι β) :
    ∃ u : W ⟶ 𝓝.D, u ≫ 𝓝.gpMap α = a ∧ u ≫ 𝓝.gpMap β = b := by
  have hr : Set.range a ⊆ Set.range (𝓝.gpMap α) := by
    rintro _ ⟨w, rfl⟩
    have hw : colimit.ι 𝓝.diag (some α) (a w) = colimit.ι 𝓝.diag (some β) (b w) := by
      exact congrArg (fun k : W ⟶ 𝓝.AN => k w) e
    obtain ⟨k, fi, fj, x, hx, -⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff 𝓝.diag).mp hw
    cases fi with
    | id =>
      cases fj
      exact (hne rfl).elim
    | init =>
      exact ⟨x, hx⟩
  let u : W ⟶ 𝓝.D := IsOpenImmersion.lift (𝓝.gpMap α) a hr
  have hu : u ≫ 𝓝.gpMap α = a := IsOpenImmersion.lift_fac _ _ _
  refine ⟨u, hu, ?_⟩
  rw [← cancel_mono (𝓝.ι β), ← e, ← hu, Category.assoc, Category.assoc, gpMap_ι, gpMap_ι]

end MagnetFamily

end AlgMag.XP
