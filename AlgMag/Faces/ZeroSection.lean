/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Faces.Spaces

/-!
# Theorem 12.4 (ii) for faces: the isomorphism respects the zero section

Paper, Theorem 12.4 (ii) (`thm:BB`): the isomorphism `Sym_{A'_F}(I/I²) ≅ A'` makes `p_{N,F}` the
bundle projection **and** `ι_{F,N}` the zero section. On rings: the isomorphism `e` intertwines
`π : A' → A'_F` with the augmentation `Sym(I/I²) → A'_F`, and sends `p ∈ I/I²` (degree one) to an
element of `I = ker π` whose class in `I/I²` is `p`.

The printed proof builds `e = lift s` from a section `s : I/I² → I` of `I → I/I²`
(`Sec12Printed.exists_section`); both properties are read off `s`.

## Main results

* `Sec12Printed.printed_ring_zeroSection_smooth`: ring form, strengthening `printed_ring_smooth`.
* `Faces.face_sym_ring_zeroSection`: strengthening `Faces.face_sym_ring`.
* `Faces.FaceChartZero`, `Faces.faceChartZero_printed`: strengthening `FaceChart`, `faceChart_printed`.
* `Faces.bb_face_zeroSection`, `Faces.bb_face_attP_zeroSection`: Theorem A with `FaceChartZero`.
-/

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism

open scoped Classical

universe u

namespace AlgMag.Sec12Printed

/-- **Theorem 12.4**, ring statement, with the zero section: there is `e : Sym_{A₀}(I/I²) ≃ B` with
`π ∘ e` the augmentation of `Sym`, and `e(p) ∈ I` with class `p` in `I/I²` for `p` in degree one. -/
theorem printed_ring_zeroSection_smooth {A₀ B R Y : Type u} [CommRing A₀] [CommRing B] [CommRing R]
    [Algebra A₀ B] {π : B →ₐ[A₀] A₀} [AddCommMonoid Y] [DecidableEq Y]
    {𝒜 : Y → Submodule A₀ B} [GradedAlgebra 𝒜] {w : Y → ℕ}
    [Algebra R B] [Algebra R A₀] [Algebra.Smooth R B] [Algebra.Smooth R A₀]
    (φ : B →ₐ[R] A₀) (hφ : ∀ b, φ b = π b) (H : IsAug 𝒜 π w) :
    ∃ e : SymmetricAlgebra A₀ (Conormal π) ≃ₐ[A₀] B,
      π.comp e.toAlgHom = SymmetricAlgebra.algebraMapInv ∧
      ∀ p, e (SymmetricAlgebra.ι A₀ _ p) ∈ augI π ∧
        tMap π (e (SymmetricAlgebra.ι A₀ _ p)) = p := by
  have := projective_conormal_of_smooth φ hφ
  have hgr : GrInjective π := grInjective_of_isQRAt fun q hq => by
    have := hq.isPrime
    exact isQRAt_of_smooth φ hφ q
  obtain ⟨s, hts, hπs, hg⟩ := exists_section H
  let e := AlgEquiv.ofBijective (SymmetricAlgebra.lift s : SymmetricAlgebra A₀ (Conormal π) →ₐ[A₀] B)
    ⟨phi_injective_of_grInjective hgr hπs hts, phi_surjective H hts hπs hg⟩
  have he : ∀ p, e (SymmetricAlgebra.ι A₀ _ p) = s p := fun p => SymmetricAlgebra.lift_ι_apply s p
  refine ⟨e, SymmetricAlgebra.algHom_ext (LinearMap.ext fun p => ?_), fun p => ?_⟩
  · change π (e (SymmetricAlgebra.ι A₀ _ p)) = SymmetricAlgebra.algebraMapInv (SymmetricAlgebra.ι A₀ _ p)
    rw [he, hπs, SymmetricAlgebra.algebraMapInv_ι]
  · rw [he]
    exact ⟨hπs p, hts p⟩

#print axioms printed_ring_zeroSection_smooth

end AlgMag.Sec12Printed

namespace AlgMag.Faces

open AlgMag.GB AlgMag.Sec12Printed

section RingMain

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {M : Type u} [AddCommGroup M]
  (𝒜 : M → Submodule R A) [GradedAlgebra 𝒜] (N F : AddSubmonoid M)

/-- **Theorem A (ii), ring form, with the zero section.** As `face_sym_ring`, and the isomorphism
`e : Sym_{B₀}(I/I²) ≃ B` satisfies `π ∘ e = augmentation` and maps `I/I²` into `I` lifting classes. -/
theorem face_sym_ring_zeroSection (hF : IsFace F N) {Nc : AddSubmonoid M} (hle : Nc ≤ N)
    (hfg : Nc.FG) (hsupp : ∀ m, m ∉ Nc → ∀ a ∈ 𝒜 m, a ∈ magnetIdeal 𝒜 N)
    (s₁ : Algebra.Smooth R (A ⧸ magnetIdeal 𝒜 N)) (s₀ : Algebra.Smooth R (A ⧸ magnetIdeal 𝒜 F)) :
    letI := (rhoF (faceData_of_Nc 𝒜 N F hF hle hsupp)).toRingHom.toAlgebra
    Module.Finite (A ⧸ magnetIdeal 𝒜 F) (Conormal (piBF (faceData_of_Nc 𝒜 N F hF hle hsupp))) ∧
      Module.Projective (A ⧸ magnetIdeal 𝒜 F) (Conormal (piBF (faceData_of_Nc 𝒜 N F hF hle hsupp))) ∧
      ∃ e : SymmetricAlgebra (A ⧸ magnetIdeal 𝒜 F)
          (Conormal (piBF (faceData_of_Nc 𝒜 N F hF hle hsupp))) ≃ₐ[A ⧸ magnetIdeal 𝒜 F]
            (A ⧸ magnetIdeal 𝒜 N),
        (piBF (faceData_of_Nc 𝒜 N F hF hle hsupp)).comp e.toAlgHom =
            SymmetricAlgebra.algebraMapInv ∧
          ∀ p, e (SymmetricAlgebra.ι _ _ p) ∈ augI (piBF (faceData_of_Nc 𝒜 N F hF hle hsupp)) ∧
            tMap (piBF (faceData_of_Nc 𝒜 N F hF hle hsupp)) (e (SymmetricAlgebra.ι _ _ p)) = p := by
  set H := faceData_of_Nc 𝒜 N F hF hle hsupp with hH
  letI := (rhoF H).toRingHom.toAlgebra
  letI := gradedBF H
  haveI := s₁
  haveI := s₀
  obtain ⟨wZ, hw0, hwadd, -⟩ := exists_weight_nbar (isFace_inf hF hle) hfg
  have hzero : ∀ n ∈ Nc, n ∈ F ⊓ Nc → QuotientAddGroup.mk' (Fgp (F ⊓ Nc)) n = 0 :=
    fun n _ h => (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.subset_closure h)
  have hIs := isAug_face H wZ ?_ ?_
  · have hfin := Sec12SpacesThm.finite_conormal_of_smooth (R := R) (piBF H)
      (magnetQuotMap 𝒜 hF.le) (fun _ => rfl)
    have hp := projective_conormal_of_smooth (R := R) (π := piBF H) (magnetQuotMap 𝒜 hF.le) (fun _ => rfl)
    have hrest := printed_ring_zeroSection_smooth (R := R) (magnetQuotMap 𝒜 hF.le) (fun _ => rfl) hIs
    exact ⟨hfin, hp, hrest⟩
  · intro z a ha hne h0
    obtain ⟨n, hn, rfl⟩ := exists_mem_Nc 𝒜 N hsupp ha hne
    exact hzero n hn ((hw0 n hn).1 h0)
  · intro u a ha hne v b hb hne'
    obtain ⟨n, hn, rfl⟩ := exists_mem_Nc 𝒜 N hsupp ha hne
    obtain ⟨n', hn', rfl⟩ := exists_mem_Nc 𝒜 N hsupp hb hne'
    rw [← map_add]
    exact hwadd n hn n' hn'

end RingMain

section Chart

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M]
variable {X : Over S} [IsAffineHom X.hom] (act : AAction (overO S) M (yoneda.obj X))
variable (N : AddSubmonoid M) {F : AddSubmonoid M} (hF : IsFace F N)

attribute [local instance] gradedAlgebraOf

/-- `FaceChart` with the zero section: the isomorphism `e : Sym_{B₀}(I/I²) ≃ B` intertwines
`π` (`p_{N,F}`) with the augmentation of `Sym` (so `Spec ρ = i_{F,N}` is the zero section), and sends
`I/I²` (degree one) into `I = ker π`, lifting each class. -/
def FaceChartZero {V : S.Opens} (hV : IsAffineOpen V) : Prop :=
  ∃ ρ : Qalg act F hV →ₐ[Γ(S, V)] Qalg act N hV,
    IsPullback (iotaZ act N ⟨V, hV⟩).left (PhiMap hV ρ).left (faceZF act N hF).left
      (iotaZ act F ⟨V, hV⟩).left ∧
    (letI := ρ.toRingHom.toAlgebra
     ∃ π : Qalg act N hV →ₐ[Qalg act F hV] Qalg act F hV,
      (∀ x, π (ρ x) = x) ∧
      (∀ a : Aalg X V, π (qAlg act N hV a) = qAlg act F hV a) ∧
      Module.Finite (Qalg act F hV) (Conormal π) ∧
      Module.Projective (Qalg act F hV) (Conormal π) ∧
      ∃ e : SymmetricAlgebra (Qalg act F hV) (Conormal π) ≃ₐ[Qalg act F hV] Qalg act N hV,
        π.comp e.toAlgHom = SymmetricAlgebra.algebraMapInv ∧
        ∀ p, e (SymmetricAlgebra.ι _ _ p) ∈ augI π ∧ tMap π (e (SymmetricAlgebra.ι _ _ p)) = p)

lemma FaceChartZero.faceChart {V : S.Opens} {hV : IsAffineOpen V}
    (h : FaceChartZero act N hF hV) : FaceChart act N hF hV := by
  obtain ⟨ρ, hp, π, h1, h2, h3, h4, e, -⟩ := h
  exact ⟨ρ, hp, π, h1, h2, h3, h4, ⟨e⟩⟩

/-- **Theorem A (ii)** with the zero section, `X` affine smooth over `S`. -/
theorem faceChartZero_printed [Smooth X.hom] {V : S.Opens} (hV : IsAffineOpen V)
    (h : N.FG ∨ AddGroup.FG M) : FaceChartZero act N hF hV := by
  obtain ⟨Nc, hle, -, hfg, hsupp⟩ := exists_Nc act N (isFace_unitsOf N) hV h
  have s₁ := smooth_Qalg act ⟨V, hV⟩ N
  have s₀ := smooth_Qalg act ⟨V, hV⟩ F
  have hr := face_sym_ring_zeroSection (gradingOf hV act) N F hF hle hfg hsupp s₁ s₀
  refine ⟨rhoQ act N hV _ (faceData_of_Nc (gradingOf hV act) N F hF hle hsupp),
    isPullback_chart_squareF act N hF ⟨V, hV⟩ _
      (faceData_of_Nc (gradingOf hV act) N F hF hle hsupp), ?_⟩
  letI := (rhoQ act N hV _ (faceData_of_Nc (gradingOf hV act) N F hF hle hsupp)).toRingHom.toAlgebra
  exact ⟨piBF (faceData_of_Nc (gradingOf hV act) N F hF hle hsupp),
    piF_rhoF (faceData_of_Nc (gradingOf hV act) N F hF hle hsupp),
    fun _ => rfl, hr.1, hr.2.1, hr.2.2⟩

end Chart

open AlgMag.Sec12Spaces AlgMag.Sec12SpacesThm

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

section Thm

attribute [local instance] AlgMag.GB.gradedAlgebraOf

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actX : AAction (fppfO B S hS) M X}
  {A : Type u} {U : A → BigFppfOver B S hS}

/-- **Theorem A (Białynicki-Birula for faces)**, as `bb_face`, with the affine charts in the form
`FaceChartZero`: `p_{N,F}` is the bundle projection and `i_{F,N}` the zero section. -/
theorem bb_face_zeroSection (L : ZariskiLocallyLinearizable actX A U)
    (hsm : Space.IsSmooth B S hS (terminal.from X)) {N F : AddSubmonoid M}
    (hF : IsFace F N) {Zx Zf : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (rx : RepresentsAttractor actX N Zx) (rf : RepresentsAttractor actX F Zf)
    {T : BigFppfOver B S hS} (y : Zf.obj (op T)) (t : (SCH).obj T) :
    ∃ a : A, haveI : IsAffineHom (structMap (U a)) := L.isAffineHom a
      ∃ he : Space.IsOpenImmersion B S hS (repAttractorMap (jHom L a) F (repCh (L.act a) F) rf),
        Space.IsOpenImmersion B S hS (repAttractorMap (jHom L a) N (repCh (L.act a) N) rx) ∧
        t ∈ rangeOf he y ∧
        IsPullback (repAttractorMap (jHom L a) N (repCh (L.act a) N) rx)
          (yoneda.map (faceSF (L.act a) hF)) (repFace rx rf hF)
          (repAttractorMap (jHom L a) F (repCh (L.act a) F) rf) ∧
        (SCH).map (faceSF (L.act a) hF) = (faceZF (chA (L.act a)) N hF).left ∧
        ∀ (V : S.Opens) (hV : IsAffineOpen V), FaceChartZero (chA (L.act a)) N hF hV := by
  have : ∀ a, IsAffineHom (structMap (U a)) := L.isAffineHom
  obtain ⟨a, he, h1, h2, h3, h4, -⟩ := bb_face L hsm hF rx rf y t
  have hs : Smooth (chO (B := B) (S := S) (hS := hS) (U₀ := U a)).hom := smooth_chart L hsm a
  exact ⟨a, he, h1, h2, h3, h4,
    fun V hV => faceChartZero_printed (chA (L.act a)) N hF hV (Or.inr inferInstance)⟩

/-- `bb_face_zeroSection` for the attractor functors themselves. -/
theorem bb_face_attP_zeroSection (L : ZariskiLocallyLinearizable actX A U)
    (hsm : Space.IsSmooth B S hS (terminal.from X)) {N F : AddSubmonoid M} (hF : IsFace F N)
    {T : BigFppfOver B S hS} (y : (attP actX F).obj (op T)) (t : (SCH).obj T) :
    ∃ a : A, haveI : IsAffineHom (structMap (U a)) := L.isAffineHom a
      ∃ he : Space.IsOpenImmersion B S hS
          (repAttractorMap (jHom L a) F (repCh (L.act a) F) (attPRep actX F)),
        Space.IsOpenImmersion B S hS
          (repAttractorMap (jHom L a) N (repCh (L.act a) N) (attPRep actX N)) ∧
        t ∈ rangeOf he y ∧
        IsPullback (repAttractorMap (jHom L a) N (repCh (L.act a) N) (attPRep actX N))
          (yoneda.map (faceSF (L.act a) hF)) (repFace (attPRep actX N) (attPRep actX F) hF)
          (repAttractorMap (jHom L a) F (repCh (L.act a) F) (attPRep actX F)) ∧
        (SCH).map (faceSF (L.act a) hF) = (faceZF (chA (L.act a)) N hF).left ∧
        ∀ (V : S.Opens) (hV : IsAffineOpen V), FaceChartZero (chA (L.act a)) N hF hV :=
  bb_face_zeroSection L hsm hF (attPRep actX N) (attPRep actX F) y t

end Thm

#print axioms face_sym_ring_zeroSection
#print axioms faceChartZero_printed
#print axioms bb_face_zeroSection
#print axioms bb_face_attP_zeroSection

end AlgMag.Faces
