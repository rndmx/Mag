/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartPointRing
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Ring theory for Lemma 1.1 of the chart-lemma proof, step B

* `AlgMag.ChartPoint.surjective_of_epi_of_isField`: an epimorphism from a field is surjective.
* `AlgMag.ChartPoint.exists_away_flat_of_epi`: generic flatness of an injective finite type
  epimorphism onto a noetherian ring.
-/

open CategoryTheory TensorProduct

universe u

namespace AlgMag.ChartPoint

/-- An epimorphism from a field is surjective (`b ⊗ 1 = 1 ⊗ b` forces `b ∈ κ`). -/
theorem surjective_of_epi_of_field {κ C : Type u} [Field κ] [CommRing C] (i : κ →+* C)
    (he : ∀ (R : Type u) [CommRing R] (a b : C →+* R), a.comp i = b.comp i → a = b) :
    Function.Surjective i := by
  classical
  by_cases hC : Subsingleton C
  · exact fun c => ⟨0, Subsingleton.elim _ _⟩
  haveI : Nontrivial C := not_subsingleton_iff_nontrivial.1 hC
  letI : Algebra κ C := i.toAlgebra
  intro c
  by_contra hc
  have e := he (C ⊗[κ] C) (Algebra.TensorProduct.includeLeft : C →ₐ[κ] C ⊗[κ] C).toRingHom
    (Algebra.TensorProduct.includeRight : C →ₐ[κ] C ⊗[κ] C).toRingHom (by
      ext x
      change (i x) ⊗ₜ[κ] (1 : C) = (1 : C) ⊗ₜ[κ] (i x)
      have : i x = x • (1 : C) := by rw [Algebra.smul_def, mul_one]; rfl
      rw [this, TensorProduct.smul_tmul])
  have ec : c ⊗ₜ[κ] (1 : C) = (1 : C) ⊗ₜ[κ] c := congrArg (fun r => r c) e
  -- a linear form vanishing on `1` and not on `c`
  let W : Submodule κ C := Submodule.span κ {(1 : C)}
  have hcW : c ∉ W := by
    intro hm
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hm
    exact hc ⟨a, by rw [← ha, Algebra.smul_def, mul_one]; rfl⟩
  obtain ⟨φ, hφc, hφW⟩ := Submodule.exists_le_ker_of_notMem hcW
  have hφ1 : φ 1 = 0 := hφW (Submodule.mem_span_singleton_self _)
  let T : C ⊗[κ] C →ₗ[κ] C := (TensorProduct.lid κ C).toLinearMap ∘ₗ
    TensorProduct.map φ LinearMap.id
  have h1 : T (c ⊗ₜ[κ] (1 : C)) = φ c • (1 : C) := by simp [T]
  have h2 : T ((1 : C) ⊗ₜ[κ] c) = 0 := by simp [T, hφ1]
  rw [ec, h2] at h1
  have := (smul_eq_zero.1 h1.symm).resolve_right one_ne_zero
  exact hφc this

/-- **Lemma 1.1, step B**: `f : A → B` injective, of finite type, an epimorphism of rings, `B`
noetherian, `A ≠ 0`. There is `s ∈ A` with `f s` not nilpotent and `A → B[1/f s]` flat
(in fact `A[1/s] = B[1/f s]`). At a minimal prime `y` of `A`, `m_y` is nilpotent as `f` is injective
and `B` noetherian, the fibre is the residue field, Nakayama gives `A_y = B_y`, and finite type
spreads this out. -/
theorem exists_away_flat_of_epi {A Bb : Type u} [CommRing A] [CommRing Bb] [Nontrivial A]
    [IsNoetherianRing Bb] (f : A →+* Bb) (hinj : Function.Injective f) (hft : f.FiniteType)
    (he : ∀ (R : Type u) [CommRing R] (a b : Bb →+* R), a.comp f = b.comp f → a = b) :
    ∃ s : A, ¬ IsNilpotent (f s) ∧
      ((algebraMap Bb (Localization.Away (f s))).comp f).Flat := by
  classical
  letI : Algebra A Bb := f.toAlgebra
  have hfa : algebraMap A Bb = f := rfl
  obtain ⟨m0, hm0⟩ := Ideal.exists_maximal A
  obtain ⟨y, hy, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := m0) bot_le
  haveI hyp : y.IsPrime := hy.1.1
  let Sy := y.primeCompl
  let SB := Algebra.algebraMapSubmonoid Bb Sy
  let L := Localization.AtPrime y
  let L' := Localization SB
  letI : Algebra L L' := localizationAlgebra Sy Bb
  haveI : IsScalarTower A L L' := inferInstance
  let g : L →+* L' := algebraMap L L'
  have hgc : ∀ a : A, g (algebraMap A L a) = algebraMap Bb L' (f a) := fun a => by
    rw [← IsScalarTower.algebraMap_apply A L L', IsScalarTower.algebraMap_apply A Bb L', hfa]
  haveI : IsLocalization (Sy.map f) L' := inferInstanceAs (IsLocalization SB L')
  have hginj : Function.Injective g := by
    have := IsLocalization.map_injective_of_injective (M := Sy) (S := L) (Q := L') hinj
    convert this using 1
    refine congrArg _ (IsLocalization.ringHom_ext Sy (RingHom.ext fun a => ?_))
    simp [hgc, g, IsLocalization.map_eq, hfa]
  haveI : IsNoetherianRing L' := IsLocalization.isNoetherianRing SB L' inferInstance
  let m := IsLocalRing.maximalIdeal L
  have hcm : Ideal.comap (algebraMap A L) m = y := Localization.AtPrime.comap_maximalIdeal
  -- `m` is nilpotent
  have hnil : IsNilpotent m := by
    obtain ⟨n, hn⟩ := IsNoetherianRing.isNilpotent_nilradical L'
    refine ⟨n, ?_⟩
    have hle : m.map g ≤ nilradical L' := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have hxn : IsNilpotent x := by
        rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
        intro (Q : Ideal L) hQ
        haveI hQp : Q.IsPrime := hQ
        have h1 : Ideal.comap (algebraMap A L) Q ≤ y := by
          have hle := IsLocalRing.le_maximalIdeal hQp.ne_top
          have := Ideal.comap_mono (f := algebraMap A L) hle
          exact this.trans hcm.le
        have h2 : y ≤ Ideal.comap (algebraMap A L) Q := hy.2 ⟨Ideal.comap_isPrime _ _, bot_le⟩ h1
        have h3 : m ≤ Q := by
          rw [← IsLocalization.map_comap Sy L Q, ← IsLocalization.map_comap Sy L m]
          refine Ideal.map_mono ?_
          change Ideal.comap (algebraMap A L) m ≤ Ideal.comap (algebraMap A L) Q
          rw [hcm]; exact h2
        exact h3 hx
      exact hxn.map g
    have h2 : (m ^ n).map g = ⊥ := by
      rw [Ideal.map_pow, ← le_bot_iff]
      calc (m.map g) ^ n ≤ nilradical L' ^ n := Ideal.pow_right_mono hle n
        _ = ⊥ := hn
    change m ^ n = ⊥
    rw [eq_bot_iff]
    intro x hx
    have : g x ∈ (m ^ n).map g := Ideal.mem_map_of_mem _ hx
    rw [h2, Ideal.mem_bot] at this
    exact hginj (this.trans (map_zero g).symm)
  -- the residue map is an epimorphism
  letI : Field (L ⧸ m) := Ideal.Quotient.field m
  let C := L' ⧸ m.map g
  let i : L ⧸ m →+* C := Ideal.quotientMap (m.map g) g Ideal.le_comap_map
  have hi : ∀ a : L, i (Ideal.Quotient.mk m a) = Ideal.Quotient.mk (m.map g) (g a) := fun _ => rfl
  have hiepi : ∀ (R : Type u) [CommRing R] (a b : C →+* R), a.comp i = b.comp i → a = b := by
    intro R _ a b hab
    have h0 : (a.comp (Ideal.Quotient.mk (m.map g))).comp (algebraMap Bb L') =
        (b.comp (Ideal.Quotient.mk (m.map g))).comp (algebraMap Bb L') := by
      refine he R _ _ (RingHom.ext fun x => ?_)
      have := congrArg (fun r => r (Ideal.Quotient.mk m (algebraMap A L x))) hab
      simp only [RingHom.comp_apply, hi, hgc] at this ⊢
      exact this
    have h1 : a.comp (Ideal.Quotient.mk (m.map g)) = b.comp (Ideal.Quotient.mk (m.map g)) :=
      IsLocalization.ringHom_ext SB h0
    exact Ideal.Quotient.ringHom_ext h1
  have hisurj := surjective_of_epi_of_field i hiepi
  have hgsurj : Function.Surjective g := by
    refine surjective_of_residue_surjective g hnil fun b => ?_
    obtain ⟨c, hc⟩ := hisurj (Ideal.Quotient.mk _ b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨a, ?_⟩
    rw [← Ideal.Quotient.eq]
    exact hc.symm
  -- spreading out
  have hb : ∀ b : Bb, ∃ σ α : A, σ ∉ y ∧ f σ * b = f α := by
    intro b
    obtain ⟨l, hl⟩ := hgsurj (algebraMap Bb L' b)
    obtain ⟨⟨α, σ⟩, rfl⟩ := IsLocalization.mk'_surjective Sy l
    have h3 : g (IsLocalization.mk' L α σ) * algebraMap Bb L' (f σ) = algebraMap Bb L' (f α) := by
      rw [← hgc, ← hgc, ← map_mul, IsLocalization.mk'_spec]
    rw [hl, ← map_mul] at h3
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists SB L').1 h3
    obtain ⟨c0, hc0, hc1⟩ := c.2
    refine ⟨c0 * σ, c0 * α, y.primeCompl.mul_mem hc0 σ.2, ?_⟩
    rw [map_mul, map_mul]
    have hc1' : f c0 = (c : Bb) := hc1
    rw [← hc1'] at hc
    change f c0 * (b * f σ) = f c0 * f α at hc
    rw [← hc]; ring
  haveI : Algebra.FiniteType A Bb := (RingHom.finiteType_algebraMap).1 hft
  obtain ⟨t, ht⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra A Bb).FG)
  choose σ α hσ hα using hb
  let s : A := ∏ b ∈ t, σ b
  have hs : s ∉ y := by
    change s ∈ y.primeCompl
    exact Submonoid.prod_mem _ fun b _ => hσ b
  refine ⟨s, ?_, ?_⟩
  · intro hn
    have : IsNilpotent s := by
      obtain ⟨k, hk⟩ := hn
      exact ⟨k, hinj (by rw [map_pow, hk, map_zero])⟩
    obtain ⟨k, hk⟩ := this
    exact hs (hyp.mem_of_pow_mem k (by rw [hk]; exact y.zero_mem))
  -- `A[1/s] → B[1/f s]`
  let As := Localization.Away s
  let Bs := Localization.Away (f s)
  let j : As →+* Bs := Localization.awayMap f s
  have hj : ∀ a : A, j (algebraMap A As a) = algebraMap Bb Bs (f a) := fun a => by
    simp [j, Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
    rfl
  have hu : IsUnit (algebraMap Bb Bs (f s)) := IsLocalization.Away.algebraMap_isUnit (f s)
  have hjinj : Function.Injective j := by
    have : Algebra As Bs := j.toAlgebra
    exact IsLocalization.map_injective_of_injective (Submonoid.powers s) As Bs hinj
  have hrange : ∀ b : Bb, algebraMap Bb Bs b ∈ j.range := by
    have : ∀ b ∈ (⊤ : Subalgebra A Bb), algebraMap Bb Bs b ∈ j.range := by
      rw [← ht]
      intro b hb
      refine Algebra.adjoin_induction (p := fun b _ => algebraMap Bb Bs b ∈ j.range) ?_ ?_ ?_ ?_ hb
      · intro b hbt
        have hsb : IsUnit (algebraMap A As (σ b)) := by
          refine isUnit_of_dvd_unit ?_ (IsLocalization.Away.algebraMap_isUnit (R := A) (S := As) s)
          exact map_dvd _ (Finset.dvd_prod_of_mem _ hbt)
        obtain ⟨v, hv⟩ := hsb
        refine ⟨(v⁻¹ : Asˣ) * algebraMap A As (α b), ?_⟩
        have e1 : j (v : As) = algebraMap Bb Bs (f (σ b)) := by rw [hv, hj]
        have e2 : algebraMap Bb Bs (f (σ b)) * algebraMap Bb Bs b = algebraMap Bb Bs (f (α b)) := by
          rw [← map_mul, hα]
        rw [map_mul, hj, ← e2, ← e1, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
      · intro a; exact ⟨algebraMap A As a, hj a⟩
      · rintro x y _ _ hx hy; rw [map_add]; exact Subring.add_mem _ hx hy
      · rintro x y _ _ hx hy; rw [map_mul]; exact Subring.mul_mem _ hx hy
    exact fun b => this b trivial
  have hjsurj : Function.Surjective j := by
    intro z
    obtain ⟨⟨b, r⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (f s)) z
    obtain ⟨n, hn⟩ := r.2
    obtain ⟨w, hw⟩ := hrange b
    have hrs : j (algebraMap A As (s ^ n)) = algebraMap Bb Bs r := by
      rw [hj, map_pow, ← hn]
    have hus : IsUnit (algebraMap A As (s ^ n)) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit (R := A) (S := As) s).pow n
    obtain ⟨v, hv⟩ := hus
    refine ⟨(v⁻¹ : Asˣ) * w, ?_⟩
    rw [IsLocalization.eq_mk'_iff_mul_eq.symm.symm, map_mul, hw, mul_right_comm, ← hrs, ← hv,
      ← map_mul, Units.inv_mul, map_one, one_mul]
  have hc : (algebraMap Bb Bs).comp f = j.comp (algebraMap A As) :=
    RingHom.ext fun a => (hj a).symm
  rw [hc]
  have h1 : (algebraMap A As).Flat :=
    (RingHom.flat_algebraMap_iff).2 (IsLocalization.flat As (Submonoid.powers s))
  exact RingHom.Flat.comp h1 (RingHom.Flat.of_bijective ⟨hjinj, hjsurj⟩)

/-- `A → B`, `B → C` local maps of local rings, `B → C` flat, `A → C` flat: `A → B` is flat. -/
theorem flat_of_comp_flat_local {A₀ B₀ C₀ : Type u} [CommRing A₀] [CommRing B₀] [CommRing C₀]
    [IsLocalRing B₀] [IsLocalRing C₀] (a : A₀ →+* B₀) (b : B₀ →+* C₀) [IsLocalHom b]
    (hb : b.Flat) (hc : (b.comp a).Flat) : a.Flat := by
  letI := a.toAlgebra
  letI := b.toAlgebra
  letI := (b.comp a).toAlgebra
  haveI : IsScalarTower A₀ B₀ C₀ := .of_algebraMap_eq fun _ => rfl
  haveI : Module.Flat B₀ C₀ := hb
  haveI : Module.Flat A₀ C₀ := hc
  haveI : IsLocalHom (algebraMap B₀ C₀) := ‹IsLocalHom b›
  haveI : Module.FaithfullyFlat B₀ C₀ := Module.FaithfullyFlat.of_flat_of_isLocalHom
  change Module.Flat A₀ B₀
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ u hu
  have h1 : Function.Injective (LinearMap.lTensor C₀ u) :=
    Module.Flat.lTensor_preserves_injective_linearMap u hu
  have h2 : Function.Injective (LinearMap.lTensor C₀ (u.baseChange B₀)) := by
    let eN := TensorProduct.AlgebraTensorModule.cancelBaseChange A₀ B₀ B₀ C₀ N
    let eP := TensorProduct.AlgebraTensorModule.cancelBaseChange A₀ B₀ B₀ C₀ P
    have hc : ∀ z, eP (LinearMap.lTensor C₀ (u.baseChange B₀) z) = LinearMap.lTensor C₀ u (eN z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul c w =>
        induction w using TensorProduct.induction_on with
        | zero => simp
        | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
        | tmul b n => simp [eN, eP, TensorProduct.smul_tmul']
    intro z z' hzz
    apply eN.injective
    apply h1
    rw [← hc, ← hc, hzz]
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective B₀ C₀ (u.baseChange B₀)).1 h2

/-- An element of `E` dying in `E ⊗_A B`, for `E` flat over `A`, lies in `ker(A → B) E`. -/
theorem mem_map_ker_of_tmul_eq_zero {A₀ B₀ E₀ : Type u} [CommRing A₀] [CommRing B₀] [CommRing E₀]
    [Algebra A₀ B₀] [Algebra A₀ E₀] [Module.Flat A₀ E₀] (x : E₀)
    (hx : x ⊗ₜ[A₀] (1 : B₀) = 0) :
    x ∈ (RingHom.ker (algebraMap A₀ B₀)).map (algebraMap A₀ E₀) := by
  let I := RingHom.ker (algebraMap A₀ B₀)
  let u : I →ₗ[A₀] A₀ := Submodule.subtype I
  let v : A₀ →ₗ[A₀] B₀ := Algebra.linearMap A₀ B₀
  have hex : Function.Exact u v := by
    intro a
    constructor
    · intro h; exact ⟨⟨a, h⟩, rfl⟩
    · rintro ⟨b, rfl⟩; exact b.2
  have hex2 := Module.Flat.lTensor_exact E₀ hex
  have h0 : LinearMap.lTensor E₀ v (x ⊗ₜ[A₀] (1 : A₀)) = 0 := by
    simpa [v] using hx
  obtain ⟨z, hz⟩ := (hex2 _).1 h0
  have key : ∀ z : E₀ ⊗[A₀] I, TensorProduct.lift
      ((LinearMap.mul A₀ E₀).compl₂ ((Algebra.linearMap A₀ E₀) ∘ₗ u)) z ∈
      I.map (algebraMap A₀ E₀) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add]; exact Ideal.add_mem _ ha hb
    | tmul e i =>
      simp only [TensorProduct.lift.tmul, LinearMap.compl₂_apply, LinearMap.mul_apply']
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ i.2)
  have e2 : ∀ z : E₀ ⊗[A₀] I, TensorProduct.lift
      ((LinearMap.mul A₀ E₀).compl₂ ((Algebra.linearMap A₀ E₀) ∘ₗ u)) z =
      TensorProduct.rid A₀ E₀ (TensorProduct.map LinearMap.id
        (LinearMap.id) (LinearMap.lTensor E₀ u z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul e i => simp [Algebra.smul_def, mul_comm, u]
  have := key z
  rw [e2, hz] at this
  simpa using this

end AlgMag.ChartPoint
