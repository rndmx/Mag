/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR4Open

/-!
# Lemma D for algebraic spaces: `SDR3Asm_ChartInput`

For Props. 3.31 (ii), 3.32 (ii), 15.1 of `Algebraic Magnetism`, Steps 1-3. `SDR4_chartInput` connects
`SDR3Orbit_step1`, `SDR4_step2`, `SDR3Orbit_bcOrbit`, `SDR3Coact_main` to the fields of `SDR3Asm_Data`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct

universe u

namespace AlgMag.SD

open AlgMag AlgMag.SQ AlgMag.SDTorus

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

lemma SDR4_assoc4 {X₁ X₂ X₃ X₄ X₅ : Scheme.{u}} (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) (c : X₃ ⟶ X₄) (d : X₄ ⟶ X₅) :
    (a ≫ b) ≫ c ≫ d = (a ≫ b ≫ c) ≫ d := by simp

section Point

variable {P P₀ κ : Type u} [AddCommMonoid P] [Countable P] [AddCommMonoid P₀] [Countable P₀] [Field κ]
  {V' T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V')] [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  (j : P₀ →+ P) (t' : V' ⟶ T) (c' : APt (fppfO B S hS) P (op V')) (iV : (BigFppfOver.toScheme B S hS).obj V' ≅ Spec (.of κ))

/-- The point `q₀ : V' → 𝔸(P₀)_T`, read in `κ'`. -/
theorem SDR4_q₀  (φ₀ : gRing P₀ T →+* κ) (hmono : ∀ k : P₀, SDR4_E iV (SDR4_cast c' (Multiplicative.ofAdd (j k))) =
      φ₀ (AddMonoidAlgebra.single k 1))
    (ht : ∀ x, SDR4_E iV (((SCH).map t').appTop.hom x) = φ₀ (AddMonoidAlgebra.single 0 x)) :
    iV.inv ≫ (SCH).map (specLift t' (APt.along j c')) = sp φ₀ := by
  refine SDR4_spec_ext _ φ₀ fun a => ?_
  have h1 : (iV.inv ≫ (SCH).map (specLift t' (APt.along j c'))).appTop.hom ((Scheme.ΓSpecIso (.of (gRing P₀ T))).inv.hom a) =
      iV.inv.appTop.hom (specRing t' (APt.along j c') a) :=
    (SDR3Coact_app (f := iV.inv) (k := (SCH).map (specLift t' (APt.along j c'))) rfl _).symm.trans
      (congrArg iV.inv.appTop.hom (SDR4_specLift_app t' (APt.along j c') a))
  refine (congrArg (Scheme.ΓSpecIso (.of κ)).hom.hom h1).trans ?_
  clear h1
  change SDR4_E iV _ = _
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | single n x =>
    have e : (AddMonoidAlgebra.single n x : gRing P₀ T) = AddMonoidAlgebra.single 0 x * AddMonoidAlgebra.single n 1 := by
      rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
    rw [specRing_single, map_mul, ht, e, map_mul, ← hmono]
    rfl

end Point

/-- From the universal property of `W'`, two maps with equal projections agree. -/
lemma SDR4_uniq {U₁ U W W' : BigFppfOver B S hS} (f : yoneda.obj U ⟶ X) (i₁ : U₁ ⟶ U) {x : X.obj (op W)} (p : W' ⟶ W)
    (s : W' ⟶ U₁) (hfs : f.app (op W') (s ≫ i₁) = X.map p.op x)
    (hu : ∀ {T : BigFppfOver B S hS} (a : T ⟶ W) (b : T ⟶ U₁), X.map a.op x = f.app (op T) (b ≫ i₁) →
      ∃! l : T ⟶ W', l ≫ p = a ∧ l ≫ s = b) {T : BigFppfOver B S hS} (l₁ l₂ : T ⟶ W') (h1 : l₁ ≫ p = l₂ ≫ p)
    (h2 : l₁ ≫ s = l₂ ≫ s) : l₁ = l₂ := by
  obtain ⟨l, -, huq⟩ := hu (l₁ ≫ p) (l₁ ≫ s) (by
    have h := NatTrans.naturality_apply f l₁.op (s ≫ i₁ : W' ⟶ U)
    rw [hfs] at h
    rw [Category.assoc]
    refine Eq.trans ?_ h.symm
    rw [← Functor.map_comp_apply, ← op_comp])
  rw [huq l₁ ⟨rfl, rfl⟩, huq l₂ ⟨h1.symm, h2.symm⟩]

set_option maxHeartbeats 4000000 in
/-- **`SDR3Asm_ChartInput`**, the outcome of Steps 1-3 of Lemma D, for an algebraic space. -/
theorem SDR4_chartInput (hX : IsAlgebraicSpace B S hS X) (r : ℕ) : SDR3Asm_ChartInput X r := by
  classical
  intro P P₀ _ _ _ _ δ j hj hk T _ x hx q
  letI iRA : Algebra (gRing P₀ T) (gRing P T) := (monι j Γ((SCH).obj T, ⊤)).toAlgebra
  have halg : algebraMap (gRing P₀ T) (gRing P T) = monι j _ := rfl
  have hιA := monCoact_isInv (R := Γ((SCH).obj T, ⊤)) (δ := δ) hj hk
  have hcInv : ∀ r : gRing P₀ T, (monCoact (R := Γ((SCH).obj T, ⊤)) δ).σ (algebraMap _ (gRing P T) r) =
      AddMonoidAlgebra.single 0 (algebraMap _ (gRing P T) r) := fun r => (hιA.range _).2 ⟨r, rfl⟩
  have hk0 : ∀ k, δ (j k) = 0 := fun k => (hk _).2 ⟨k, rfl⟩
  have hfree : ∀ L : AddSubgroup (Lat.{u} r), Module.Free ℤ L := SDR3Orbit_lat_free r
  haveI : UniqueSums (Lat.{u} r) := SDLocS_uniqueSums_lat r
  haveI : q.asIdeal.IsPrime := q.isPrime
  obtain ⟨I, K, _, ρ, φ, hI, hIq, hmax, hφρ, hρ, hsurj, hφ, κ', _, _, h1, h2, L, V', hV'a, t', c', hL, U, f, u₀, hfe, hu₀,
    hconst, hLeq, iV, hiV, hic⟩ := SDR3Orbit_step1 hX hfree δ j hj hk T x hx q
  obtain ⟨R', _, _, hE, P', _, hP', τ, hτ, hτρ, hτs⟩ := SDR4_step2 (A₀ := gRing P₀ T) (K := K) (κ' := κ') (q := q.asIdeal) ρ hρ hsurj
  let φκ : gRing P T →+* κ' := (algebraMap K κ').comp φ
  have hinj : Function.Injective (algebraMap K κ') := (algebraMap K κ').injective
  have hφκ0 : ∀ a, φκ a = 0 ↔ φ a = 0 := fun a => map_eq_zero_iff _ hinj
  have hφκ : ∀ d a, (monCoact (R := Γ((SCH).obj T, ⊤)) δ).IsHom d a → (φκ a = 0 ↔ a ∈ I) := fun d a ha => by
    rw [hφκ0]
    exact hφ d a ha
  have hτφ : ∀ s, τ (algebraMap (gRing P₀ T) R' s) = φκ (algebraMap _ (gRing P T) s) := fun s => by
    rw [hτρ]
    change _ = algebraMap K κ' (φ (monι j _ s))
    rw [hφρ]
  obtain ⟨θ, I', hθ, hI'mem, hI'hom, hIq', hmax'⟩ := SDR3Orbit_bcOrbit (monCoact (R := Γ((SCH).obj T, ⊤)) δ) hcInv hιA hI hIq hmax
    φκ τ hτφ hφκ hτ
  have hC : B.Contains (Spec (.of R')) := SDR3Coact_contains_of_finiteType (R := gRing P₀ T) (contains_spec P₀ T)
  -- the field `κ'` as the functions on `V'`
  let E := SDR4_E iV
  have hEc : ∀ n : P, E (SDR4_cast c' (Multiplicative.ofAdd n)) = φκ (AddMonoidAlgebra.single n 1) := fun n => by
    have h := hic (Multiplicative.ofAdd n)
    change (Scheme.ΓSpecIso (.of κ')).hom.hom (iV.inv.appTop.hom (SDR4_cast c' (Multiplicative.ofAdd n))) = _
    refine (congrArg _ h).trans (SDR4_iso_app _ _)
  have hEt : ∀ y, E (((SCH).map t').appTop.hom y) = φκ (AddMonoidAlgebra.single 0 y) := fun y => by
    change (Scheme.ΓSpecIso (.of κ')).hom.hom (iV.inv.appTop.hom (((SCH).map t').appTop.hom y)) = _
    have h : iV.inv.appTop.hom (((SCH).map t').appTop.hom y) = (iV.inv ≫ (SCH).map t').appTop.hom y := by
      rw [Scheme.Hom.comp_appTop]
      rfl
    rw [h, hiV, Scheme.Hom.comp_appTop]
    change (Scheme.ΓSpecIso (.of κ')).hom.hom ((sp _).appTop.hom (((SCH).obj T).isoSpec.inv.appTop.hom y)) = _
    rw [SDR4_isoSpec_inv, appTop_sp_inv, SDR4_iso_app]
    rfl
  -- the affine chart
  let pt₀ : (SCH).obj V' := iV.inv (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum κ')
  obtain ⟨U₁, hU₁, i₁, hi₁, W', p, s, hy, hpe, hps, hfs, hu⟩ := SDR4_chart f hfe x ((SCH).map u₀ pt₀)
  obtain ⟨u₁, hu₁⟩ := SDR4_lift i₁ u₀ (by
    rintro _ ⟨z, rfl⟩
    have hz : z = pt₀ := by
      have h0 : iV.hom z = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum κ') := Subsingleton.elim _ _
      have h3 : iV.inv (iV.hom z) = z := by
        have := congrArg (fun m : (SCH).obj V' ⟶ (SCH).obj V' => m z) iV.hom_inv_id
        exact this
      rw [← h3, h0]
    rw [hz]
    exact hy)
  -- the action on `W'`
  let f₁ : yoneda.obj U₁ ⟶ X := yoneda.map i₁ ≫ f
  have hf₁ : ∀ {T' : BigFppfOver B S hS} (b : T' ⟶ U₁), f₁.app (op T') b = f.app (op T') (b ≫ i₁) := fun _ => rfl
  obtain ⟨act, hact⟩ := SDR3Coact_liftAction f₁ hx p s hfs (fun a b h => hu a b h)
  have hact1 : ∀ {T' : BigFppfOver B S hS} (g : APt (fppfO B S hS) (Lat.{u} r) (op T')) (l : T' ⟶ W'),
      act.smul (U := op T') g l ≫ p = SDR3Coact_smulW δ g (l ≫ p) := fun g l => (hact g l).1
  have huq := fun {T' : BigFppfOver B S hS} (l₁ l₂ : T' ⟶ W') => SDR4_uniq (X := X) f i₁ p s hfs hu l₁ l₂
  -- the orbit map
  let Orb : BigFppfOver B S hS := specObj (SDR3Orbit_OM L) V'
  let prV : Orb ⟶ V' := specPr (SDR3Orbit_OM L) V'
  let a₀ : Orb ⟶ specObj P T := specLift (prV ≫ t') (SDR3Orbit_c₀ L δ c' hL)
  obtain ⟨lw, ⟨hlwp, hlws⟩, -⟩ := hu a₀ (prV ≫ u₁) (by
    rw [Category.assoc, hu₁]
    exact hconst)
  -- the point of `Spec R'`
  let φ₀ : gRing P₀ T →+* κ' := τ.comp (algebraMap (gRing P₀ T) R')
  have hq₀ := SDR4_q₀ j t' c' iV φ₀ (fun k => by
      refine (hEc (j k)).trans ?_
      change _ = τ _
      rw [hτφ]
      change φκ _ = φκ (monι j _ _)
      rw [monι_single])
    (fun y => by
      refine (hEt y).trans ?_
      change _ = τ _
      rw [hτφ]
      change φκ _ = φκ (monι j _ _)
      rw [monι_single, map_zero])
  let q₀ : V' ⟶ specObj P₀ T := specLift t' (APt.along j c')
  have hq₀' : (SCH).map q₀ = iV.hom ≫ sp φ₀ := by
    exact (Iso.hom_inv_id_assoc iV _).symm.trans (congrArg (fun m => iV.hom ≫ m) hq₀)
  have hcomp : iV.hom ≫ sp τ ≫ sp (algebraMap (gRing P₀ T) R') = (SCH).map q₀ := by
    rw [hq₀']
    exact (congrArg (fun m => iV.hom ≫ m) (sp_comp (algebraMap (gRing P₀ T) R') τ)).symm
  let e₀ : V' ⟶ SDR4_Qr (P₀ := P₀) T hC := overHom (iV.hom ≫ sp τ) (by
    have h3 : (iV.hom ≫ sp τ ≫ sp (algebraMap (gRing P₀ T) R')) ≫ (specObj P₀ T).hom.hom = V'.hom.hom := by
      rw [hcomp]
      exact site_w q₀
    exact (SDR4_assoc4 iV.hom (sp τ) (sp (algebraMap (gRing P₀ T) R')) (specObj P₀ T).hom.hom).trans h3)
  have he₀ : e₀ ≫ SDR4_e (P₀ := P₀) T hC = q₀ :=
    toScheme_map_injective ((Functor.map_comp _ _ _).trans ((Category.assoc _ _ _).trans hcomp))
  have hcond : lw ≫ p ≫ specAlong T j = (prV ≫ e₀) ≫ SDR4_e (P₀ := P₀) T hC := by
    rw [← Category.assoc, hlwp, Category.assoc, he₀, SDR4_along]
    change specLift _ _ = prV ≫ specLift t' (APt.along j c')
    rw [SDR3Orbit_comp_specLift]
    have hpr : a₀ ≫ specPr P T = prV ≫ t' := specLift_pr _ _
    have hres : APt.res a₀.op (specPt P T) = SDR3Orbit_c₀ L δ c' hL := res_specLift _ _
    rw [hpr, hres]
    congr 1
    refine MonoidHom.ext fun n => ?_
    have hmem : δ (j n.toAdd) ∈ L := by
      rw [hk0]
      exact L.zero_mem
    have h3 := SDR3Orbit_c₀_pos L δ c' hL (Multiplicative.ofAdd (j n.toAdd)) hmem
    refine h3.trans ?_
    have hone : Multiplicative.ofAdd (SDR3Orbit_om L hmem) = 1 := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      refine Prod.ext rfl ?_
      exact hk0 _
    rw [hone, map_one, mul_one]
    rfl
  let Z := SDR4_Z j p hC
  let fstZ : Z ⟶ W' := pullback.fst _ _
  let sndZ : Z ⟶ SDR4_Qr (P₀ := P₀) T hC := pullback.snd _ _
  let lo : Orb ⟶ Z := pullback.lift lw (prV ≫ e₀) hcond
  have hlo1 : lo ≫ fstZ = lw := pullback.lift_fst _ _ _
  have hlo2 : lo ≫ sndZ = prV ≫ e₀ := pullback.lift_snd _ _ _
  let actZ := SDR4_actZ δ j p hC hk0 act hact1
  have hZ1 : ∀ {T' : BigFppfOver B S hS} (g : APt (fppfO B S hS) (Lat.{u} r) (op T')) (l : T' ⟶ Z),
      actZ.smul (U := op T') g l ≫ fstZ = act.smul (U := op T') g (l ≫ fstZ) := fun g l => pullback.lift_fst _ _ _
  have hZ2 : ∀ {T' : BigFppfOver B S hS} (g : APt (fppfO B S hS) (Lat.{u} r) (op T')) (l : T' ⟶ Z),
      actZ.smul (U := op T') g l ≫ sndZ = l ≫ sndZ := fun g l => pullback.lift_snd _ _ _
  haveI hOrbC : CompactSpace ((SCH).obj Orb) := inferInstanceAs (CompactSpace (Spec _))
  obtain ⟨Vo, k, actV, so, hkim, hso, heq, hVc, cV, hcV⟩ := SDR4_opening (W := specObj P T) actZ (fstZ ≫ p) lo
  haveI := hkim
  -- `f`
  have hf₀pb := SDR4_f₀_pb j p hC halg
  haveI hpe' : Etale ((SCH).map p) := hpe
  haveI hps' : IsSeparated ((SCH).map p) := hps
  haveI hf₀e : Etale (SDR4_f₀ j p hC halg) :=
    MorphismProperty.of_isPullback (P := @Etale) hf₀pb hpe'
  haveI hf₀s : IsSeparated (SDR4_f₀ j p hC halg) :=
    MorphismProperty.of_isPullback (P := @IsSeparated) hf₀pb hps'
  let fV : (SCH).obj Vo ⟶ Spec (.of (R' ⊗[gRing P₀ T] gRing P T)) := (SCH).map k ≫ SDR4_f₀ j p hC halg
  have hfVR : fV ≫ sp ((Algebra.TensorProduct.includeRight : gRing P T →ₐ[gRing P₀ T] R' ⊗[gRing P₀ T] gRing P T) :
      gRing P T →+* R' ⊗[gRing P₀ T] gRing P T) = (SCH).map (k ≫ fstZ ≫ p) := by
    change ((SCH).map k ≫ _) ≫ _ = _
    rw [Category.assoc, SDR4_f₀_R, Functor.map_comp, Functor.map_comp]
    rfl
  have hfVL : fV ≫ sp (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[gRing P₀ T] gRing P T) =
      (SCH).map (k ≫ sndZ) := by
    change ((SCH).map k ≫ _) ≫ _ = _
    rw [Category.assoc, SDR4_f₀_L, Functor.map_comp]
    rfl
  -- the ring map `Θ : R' ⊗ A → κ'[L]`
  let G := gRing (SDR3Orbit_OM L) V'
  have hmapSo : ∃ Θ' : CommRingCat.of (R' ⊗[gRing P₀ T] gRing P T) ⟶ CommRingCat.of G,
      Spec.map Θ' = (SCH).map so ≫ fV := Spec.map_surjective ((SCH).map so ≫ fV)
  obtain ⟨Θ', hΘ'⟩ := hmapSo
  let Θ : R' ⊗[gRing P₀ T] gRing P T →+* G := Θ'.hom
  have hspΘ : sp Θ = (SCH).map so ≫ fV := hΘ'
  let Ei : κ' →+* Γ((SCH).obj V', ⊤) := (E.symm : κ' →+* Γ((SCH).obj V', ⊤))
  let ΘL : R' →+* G := (algebraMap Γ((SCH).obj V', ⊤) G).comp (Ei.comp τ)
  let ΘA : gRing P T →+* G := (SDR4_toG _ V').comp (specRing (prV ≫ t') (SDR3Orbit_c₀ L δ c' hL))
  have hsoLo : (SCH).map so ≫ (SCH).map k = (SCH).map lo := by
    rw [← Functor.map_comp, hso]
  have hlegL : sp Θ ≫ sp (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[gRing P₀ T] gRing P T) =
      (SCH).map (prV ≫ e₀) := by
    refine (congrArg (fun m => m ≫ sp (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[gRing P₀ T] gRing P T)) hspΘ).trans
      ((Category.assoc _ _ _).trans ((congrArg (fun m => (SCH).map so ≫ m) hfVL).trans ?_))
    rw [← hlo2, ← hso]
    simp only [Category.assoc, Functor.map_comp]
    rfl
  have hlegR : sp Θ ≫ sp ((Algebra.TensorProduct.includeRight : gRing P T →ₐ[gRing P₀ T] R' ⊗[gRing P₀ T] gRing P T) :
      gRing P T →+* R' ⊗[gRing P₀ T] gRing P T) = (SCH).map a₀ := by
    refine (congrArg (fun m => m ≫ sp ((Algebra.TensorProduct.includeRight : gRing P T →ₐ[gRing P₀ T] R' ⊗[gRing P₀ T] gRing P T) :
      gRing P T →+* R' ⊗[gRing P₀ T] gRing P T)) hspΘ).trans
      ((Category.assoc _ _ _).trans ((congrArg (fun m => (SCH).map so ≫ m) hfVR).trans ?_))
    rw [← hlwp, ← hlo1, ← hso]
    simp only [Category.assoc, Functor.map_comp]
    rfl
  have hΘLeq : Θ.comp (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[gRing P₀ T] gRing P T) = ΘL := by
    refine SDR4_sp_inj ((sp_comp _ _).trans (hlegL.trans ?_))
    refine SDR4_spec_ext _ ΘL fun a => ?_
    change SDR4_toG _ V' (((SCH).map (prV ≫ e₀)).appTop.hom ((Scheme.ΓSpecIso (.of R')).inv.hom a)) = _
    have h3 : ((SCH).map e₀).appTop.hom ((Scheme.ΓSpecIso (.of R')).inv.hom a) = Ei (τ a) :=
      (SDR3Coact_app (f := iV.hom) (k := sp τ) rfl _).symm.trans (congrArg iV.hom.appTop.hom (appTop_sp_inv τ a))
    refine (congrArg _ (SDR4_app_comp prV e₀ _)).trans ?_
    refine (congrArg (fun y => SDR4_toG _ V' (((SCH).map prV).appTop.hom y)) h3).trans ?_
    exact SDR4_toG_pr _ V' _
  have hΘReq : Θ.comp ((Algebra.TensorProduct.includeRight : gRing P T →ₐ[gRing P₀ T] R' ⊗[gRing P₀ T] gRing P T) :
      gRing P T →+* R' ⊗[gRing P₀ T] gRing P T) = ΘA := by
    refine SDR4_sp_inj ((sp_comp _ _).trans (hlegR.trans ?_))
    refine SDR4_spec_ext _ ΘA fun a => ?_
    exact congrArg (SDR4_toG _ V') (SDR4_specLift_app (prV ≫ t') (SDR3Orbit_c₀ L δ c' hL) a)
  have hΘ : ∀ r a, Θ (r ⊗ₜ a) = ΘL r * ΘA a := by
    intro r a
    have h3 : r ⊗ₜ[gRing P₀ T] a = (Algebra.TensorProduct.includeLeftRingHom r : R' ⊗[gRing P₀ T] gRing P T) *
        ((Algebra.TensorProduct.includeRight : gRing P T →ₐ[gRing P₀ T] R' ⊗[gRing P₀ T] gRing P T) a) := by
      change _ = (r ⊗ₜ[gRing P₀ T] (1 : gRing P T)) * ((1 : R') ⊗ₜ[gRing P₀ T] a)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h3, map_mul, ← hΘLeq, ← hΘReq]
    rfl
  let ω := SDR4_ω L (E : Γ((SCH).obj V', ⊤) →+* κ')
  have hω : Function.Injective ω := SDR4_ω_inj L _ E.injective
  have hzero : SDR4_omι L 0 = 0 := map_zero _
  have hΘL : ∀ a, ω (ΘL a) = AddMonoidAlgebra.single 0 (τ a) := fun a => by
    change SDR4_ω L _ (AddMonoidAlgebra.single 0 (Ei (τ a))) = _
    rw [SDR4_ω_single, hzero]
    congr 1
    exact E.apply_symm_apply _
  have hΘA : ∀ a, ω (ΘA a) = AddMonoidAlgebra.mapRingHom _ φκ ((monCoact (R := Γ((SCH).obj T, ⊤)) δ).σ a) :=
    fun a => SDR4_formula L δ t' c' hL _ φκ hEc hEt a
  have hLdeg : ∀ d ∈ (L : Set (Lat.{u} r)), ∃ a, (monCoact (R := Γ((SCH).obj T, ⊤)) δ).IsHom d a ∧ φκ a ≠ 0 := by
    intro d hd
    refine SDR4_deg hιA hI hIq hmax φκ hφκ _ ?_ (d := d) (by rw [← hLeq]; exact hd)
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨AddMonoidAlgebra.single n.toAdd 1, monσ_single _ _ _, fun h0 => hn ((hφκ0 _).1 h0)⟩
  have hgen : ∀ Q : G → Prop, Q 0 → (∀ a b, Q a → Q b → Q (a + b)) →
      (∀ d ∈ (L : Set (Lat.{u} r)), ∀ (k : κ') (g : G), ω g = AddMonoidAlgebra.single d k → Q g) → ∀ g, Q g := by
    intro Q h0 hadd hs g
    induction g using AddMonoidAlgebra.induction_linear with
    | zero => exact h0
    | add a b ha hb => exact hadd _ _ ha hb
    | single x y => exact hs _ (SDR4_omι_mem L x) (E y) _ (SDR4_ω_single L _ x y)
  have hone : ∀ a : κ', ∃ g : G, ω g = AddMonoidAlgebra.single 0 a := fun a =>
    ⟨AddMonoidAlgebra.single 0 (Ei a), by
      refine (SDR4_ω_single L _ 0 _).trans ?_
      rw [hzero]
      congr 1
      exact E.apply_symm_apply _⟩
  let Sm : Submonoid ((R' ⊗[gRing P₀ T] gRing P T) ⧸ I') :=
    P'.primeCompl.map ((Ideal.Quotient.mk I').comp (algebraMap R' (R' ⊗[gRing P₀ T] gRing P T)))
  obtain ⟨hprime, e, he⟩ := SDR4_orbit_loc (monCoact (R := Γ((SCH).obj T, ⊤)) δ) hcInv φκ τ θ hθ I' hI'mem P' hτ hτs ω hω ΘL ΘA hΘL hΘA Θ hΘ
    (L : Set (Lat.{u} r)) hLdeg hgen hone Sm rfl
  let s₀ : Spec (.of (Localization Sm)) ⟶ (SCH).obj Vo := sp (e.symm : G →+* Localization Sm) ≫ (SCH).map so
  have hs₀ : s₀ ≫ fV = Spec.map (CommRingCat.ofHom (algebraMap (R' ⊗[gRing P₀ T] gRing P T) (Localization Sm))) := by
    refine (Category.assoc _ _ _).trans ((congrArg (fun m => sp (e.symm : G →+* Localization Sm) ≫ m) hspΘ.symm).trans
      ((sp_comp Θ (e.symm : G →+* Localization Sm)).symm.trans ?_))
    refine congrArg (fun ρ => sp ρ) (RingHom.ext fun b => ?_)
    change e.symm (Θ b) = _
    rw [← he, e.symm_apply_apply]
    rfl
  -- the translation
  let m : specObj (Lat.{u} r) Orb ⟶ Orb := SDR4_m L
  let prO : specObj (Lat.{u} r) Orb ⟶ Orb := specPr (Lat.{u} r) Orb
  let ptO : APt (fppfO B S hS) (Lat.{u} r) (op (specObj (Lat.{u} r) Orb)) := specPt (Lat.{u} r) Orb
  have hmpr : m ≫ prV = prO ≫ prV := SDR4_m_pr L
  have hmW : m ≫ a₀ = SDR3Coact_smulW δ ptO (prO ≫ a₀) := SDR4_m_W L δ t' c' hL
  have hmlo : m ≫ lo = actZ.smul (U := op (specObj (Lat.{u} r) Orb)) ptO (prO ≫ lo) := by
    refine pullback.hom_ext ?_ ?_
    · change (m ≫ lo) ≫ fstZ = actZ.smul (U := op (specObj (Lat.{u} r) Orb)) ptO (prO ≫ lo) ≫ fstZ
      rw [hZ1, Category.assoc, Category.assoc, hlo1]
      refine huq _ _ ?_ ?_
      · rw [Category.assoc, hlwp, hact1, Category.assoc, hlwp, hmW]
      · rw [Category.assoc, hlws, (hact _ _).2, Category.assoc, hlws, ← Category.assoc, hmpr, Category.assoc]
    · change (m ≫ lo) ≫ sndZ = actZ.smul (U := op (specObj (Lat.{u} r) Orb)) ptO (prO ≫ lo) ≫ sndZ
      rw [hZ2, Category.assoc, Category.assoc, hlo2, ← Category.assoc, hmpr, Category.assoc]
  have hm : m ≫ so = actV.smul (U := op (specObj (Lat.{u} r) Orb)) ptO (prO ≫ so) := by
    refine SDR4_cancel k ?_
    rw [heq, Category.assoc, Category.assoc, hso]
    exact hmlo
  have hs₀k : ∀ z, SDR3Asm_ev s₀ z = 0 → ∀ d, SDR3Asm_ev s₀ (cV.comp d z) = 0 := by
    intro z hz d
    have hev : ∀ y, SDR3Asm_ev s₀ y = e.symm (SDR4_toG _ V' (((SCH).map so).appTop.hom y)) := fun y =>
      SDR3Asm_ev_comp (e.symm : G →+* Localization Sm) ((SCH).map so) y
    rw [hev] at hz ⊢
    have h3 : ((SCH).map so).appTop.hom z = 0 := by
      have h4 := (map_eq_zero_iff _ e.symm.injective).1 hz
      rw [← SDR4_ofG_toG _ V' (((SCH).map so).appTop.hom z), h4, map_zero]
    rw [SDR4_ker_hom actV (k ≫ fstZ ≫ p) hcV so m hm z h3 d, map_zero, map_zero]
  -- `ψ`
  let u : X.obj (op U₁) := f.app (op U₁) i₁
  have hus : X.map s.op u = X.map p.op x := by
    have h := NatTrans.naturality_apply f s.op i₁
    exact h.symm.trans hfs
  have hHom0 : ∀ y : Γ((SCH).obj U₁, ⊤), cV.IsHom 0 (((SCH).map (k ≫ fstZ ≫ s)).appTop.hom y) := fun y =>
    SDR4_isHom_zero actV (k ≫ fstZ ≫ p) hcV (k ≫ fstZ ≫ s) (fun {T'} g t => by
      rw [← Category.assoc, heq, ← Category.assoc, hZ1, (hact _ _).2]
      simp only [Category.assoc]) y
  have hLeft : ∀ {T' : BigFppfOver B S hS} (g : APt (fppfO B S hS) (Lat.{u} r) (op T')) (t : T' ⟶ Vo),
      actV.smul (U := op T') g t ≫ k ≫ pullback.snd _ _ = t ≫ k ≫ pullback.snd _ _ := fun {T'} g t => by
    rw [← Category.assoc, heq]
    refine (hZ2 g _).trans ?_
    exact Category.assoc _ _ _
  have hRight : ∀ {T' : BigFppfOver B S hS} (g : APt (fppfO B S hS) (Lat.{u} r) (op T')) (t : T' ⟶ Vo),
      actV.smul (U := op T') g t ≫ k ≫ fstZ ≫ p = SDR3Coact_smulW δ g (t ≫ k ≫ fstZ ≫ p) := fun {T'} g t => by
    rw [← Category.assoc, heq, ← Category.assoc, hZ1, hact1]
    simp only [Category.assoc]
  have hψW : (SCH).map (k ≫ fstZ ≫ s) ≫ U₁.hom.hom = (SCH).map (k ≫ fstZ ≫ p) ≫ (specObj P T).hom.hom :=
    (site_w _).trans (site_w _).symm
  unfold SDR3Asm_Data
  refine ⟨R', inferInstance, inferInstance, hE, P', inferInstance, hP', I', hprime, hI'hom, hIq', hmax', Sm, rfl,
    (SCH).obj Vo, hVc, fV, inferInstance, inferInstance, cV, ?_, SDR4_acts actV (k ≫ fstZ ≫ p) hcV, s₀, hs₀, hs₀k, U₁, hU₁, u,
    (SCH).map (k ≫ fstZ ≫ s), hHom0, ?_, ?_⟩
  · exact fun d b => SDR4_hV δ j p hC halg hcInv k actV hLeft hRight hcV d b
  · refine hψW.trans ?_
    exact (congrArg (fun m => m ≫ (specObj P T).hom.hom) hfVR.symm).trans ((Category.assoc _ _ _).trans
      (congrArg (fun m => fV ≫ _ ≫ m) (Category.id_comp _).symm))
  · intro Z₀ a b z ha hb
    have hza : z ≫ (SCH).map (k ≫ fstZ ≫ p) = (SCH).map a := by
      refine ((congrArg (fun m => z ≫ m) hfVR.symm).trans ?_).trans ha.symm
      exact congrArg (fun m => z ≫ m) (congrArg (fun m => fV ≫ m) (Category.comp_id _).symm)
    let z' : Z₀ ⟶ Vo := overHom z (by
      have h1' : (SCH).map a ≫ (specObj P T).hom.hom = Z₀.hom.hom := site_w a
      have h2' : (SCH).map (k ≫ fstZ ≫ p) ≫ (specObj P T).hom.hom = Vo.hom.hom := site_w _
      rw [← h2', ← Category.assoc, hza, h1'])
    have hza' : a = z' ≫ k ≫ fstZ ≫ p := toScheme_map_injective (by rw [Functor.map_comp, map_overHom, hza])
    have hzb' : b = z' ≫ k ≫ fstZ ≫ s := toScheme_map_injective (by rw [Functor.map_comp, map_overHom, hb])
    rw [hza', hzb']
    have hl : ∀ {Y Y' Y'' : BigFppfOver B S hS} (m₁ : Y ⟶ Y') (n : Y' ⟶ Y'') (w : X.obj (op Y'')),
        X.map (m₁ ≫ n).op w = X.map m₁.op (X.map n.op w) := fun m₁ n w => by
      rw [op_comp, Functor.map_comp_apply]
    have e1 : z' ≫ k ≫ fstZ ≫ s = (z' ≫ k ≫ fstZ) ≫ s := by simp
    have e2 : z' ≫ k ≫ fstZ ≫ p = (z' ≫ k ≫ fstZ) ≫ p := by simp
    rw [e1, e2, hl _ s, hl _ p, hus]

end AlgMag.SD

#print axioms AlgMag.SD.SDR4_chartInput
