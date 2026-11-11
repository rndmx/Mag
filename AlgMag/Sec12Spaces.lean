/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec12GenericSmall
import AlgMag.Sec12Topology
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms

/-!
# Proposition 12.2 (i) for algebraic spaces

Mayeux, *Algebraic Magnetism*, Proposition 12.2 (i): if `f : X → Y` is an equivariant open immersion and
`X^N`, `Y^N` are represented, then `f^N` is an open immersion.

The printed proof goes through Corollary 11.2 and Tag 05W5. Here we use the direct route of
`AlgMag.Sec12Printed.exists_att_of_vertex_general`, which is stronger: `X^N = Y^N ×_Y X` along the vertex
maps `Y^N → Y`, evaluation at the point `n ↦ 1` on `F`, `n ↦ 0` off `F`, for a subgroup face `F` of `N`.
So `f^N` is a base change of `f`. `X`, `Y` are arbitrary presheaves. `M` is countable (site cutoff: `𝔸(N)_K`
and the field `L` of `exists_generic_point_small` must lie in the site).
-/

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

open scoped Classical

universe u

namespace AlgMag.Sec12Spaces

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

section Open

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}

/-- The open subset of `P` where `y ∈ Y(P)` lies in `X`. -/
def rangeOf (hf : Space.IsOpenImmersion B S hS f) {P : BigFppfOver B S hS} (y : Y.obj (op P)) :
    Set ((SCH).obj P) :=
  Set.range ((SCH).map (hf.rep.snd (yonedaEquiv.symm y)))

lemma isOpen_rangeOf (hf : Space.IsOpenImmersion B S hS f) {P : BigFppfOver B S hS} (y : Y.obj (op P)) :
    IsOpen (rangeOf hf y) := by
  have : IsOpenImmersion ((SCH).map (hf.rep.snd (yonedaEquiv.symm y))) := hf.property_snd _
  exact ((SCH).map (hf.rep.snd (yonedaEquiv.symm y))).isOpenEmbedding.isOpen_range

/-- A morphism landing in the open locus pulls `y` back into `X`. -/
lemma mem_of_range (hf : Space.IsOpenImmersion B S hS f) {P Q : BigFppfOver B S hS} (q : Q ⟶ P)
    (y : Y.obj (op P)) (h : Set.range ((SCH).map q) ⊆ rangeOf hf y) :
    ∃ x, f.app (op Q) x = Y.map q.op y := by
  set g := yonedaEquiv.symm y with hg
  have hp := hf.rep.isPullback g
  have : IsOpenImmersion ((SCH).map (hf.rep.snd g)) := hf.property_snd g
  have hk₀ := IsOpenImmersion.lift_fac ((SCH).map (hf.rep.snd g)) ((SCH).map q) h
  let k : Q ⟶ hf.rep.pullback g :=
    overHom (IsOpenImmersion.lift ((SCH).map (hf.rep.snd g)) ((SCH).map q) h) (by
      have e₁ : (hf.rep.pullback g).hom.hom = (SCH).map (hf.rep.snd g) ≫ P.hom.hom :=
        (congrArg (fun k => k.hom) (Over.w (hf.rep.snd g))).symm
      have e₂ : (SCH).map q ≫ P.hom.hom = Q.hom.hom := congrArg (fun k => k.hom) (Over.w q)
      rw [e₁, ← Category.assoc, hk₀, e₂])
  have hk : k ≫ hf.rep.snd g = q := toScheme_map_injective (by
    rw [Functor.map_comp, map_overHom]
    exact hk₀)
  refine ⟨yonedaEquiv (yoneda.map k ≫ hf.rep.fst g), ?_⟩
  have e : yoneda.map k ≫ hf.rep.fst g ≫ f = yoneda.map q ≫ g := by
    rw [hp.w, ← Category.assoc, ← Functor.map_comp, hk]
  have e' := congrArg yonedaEquiv e
  rw [← Category.assoc, yonedaEquiv_comp, yonedaEquiv_comp] at e'
  refine e'.trans ?_
  simp [hg, yonedaEquiv]

/-- A morphism along which `y` comes from `X` lands in the open locus. -/
lemma range_sub_of_mem (hf : Space.IsOpenImmersion B S hS f) {P Q : BigFppfOver B S hS} (q : Q ⟶ P)
    (y : Y.obj (op P)) (x : X.obj (op Q)) (hx : f.app (op Q) x = Y.map q.op y) :
    Set.range ((SCH).map q) ⊆ rangeOf hf y := by
  set g := yonedaEquiv.symm y with hg
  have hp := hf.rep.isPullback g
  have heq : yonedaEquiv.symm x ≫ f = yoneda.map q ≫ g := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp]
    simp [hg, hx]
    rw [show yonedaEquiv (yoneda.map q) = q from Category.id_comp q]
  let e : Q ⟶ hf.rep.pullback g := yoneda.preimage (hp.lift _ _ heq)
  have he : e ≫ hf.rep.snd g = q := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_preimage]
    exact hp.lift_snd _ _ heq
  rintro _ ⟨b, rfl⟩
  refine ⟨(SCH).map e b, ?_⟩
  rw [← he, Functor.map_comp, Scheme.Hom.comp_apply]

/-- If the open locus of `y` is everything, `y` comes from `X`. -/
lemma mem_of_surj (hf : Space.IsOpenImmersion B S hS f) {P : BigFppfOver B S hS} (y : Y.obj (op P))
    (h : ∀ s, s ∈ rangeOf hf y) : ∃ x, f.app (op P) x = y := by
  obtain ⟨x, hx⟩ := mem_of_range hf (𝟙 P) y (fun s _ => h s)
  refine ⟨x, hx.trans ?_⟩
  simp

end Open

section Spec

/-- `Spec R` over `T`, as an object of the site. -/
abbrev spO {T : BigFppfOver B S hS} {R : CommRingCat.{u}} (h : B.Contains (Spec R))
    (b : Spec R ⟶ (SCH).obj T) : BigFppfOver B S hS :=
  siteObject B S hS h (b ≫ T.hom.hom)

/-- The structure morphism of `spO`. -/
def spT {T : BigFppfOver B S hS} {R : CommRingCat.{u}} (h : B.Contains (Spec R))
    (b : Spec R ⟶ (SCH).obj T) : spO h b ⟶ T :=
  overHom b rfl

/-- `K[P]`, `P` countable, stays in the site. -/
lemma contains_monoidAlgebra {K : Type u} [CommRing K] (hK : B.Contains (Spec (.of K))) (P : Type u)
    [AddCommMonoid P] [Countable P] : B.Contains (Spec (.of (AddMonoidAlgebra K P))) := by
  refine Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit _ hK ?_
  have h1 : Cardinal.mk (AddMonoidAlgebra K P) ≤ Cardinal.mk (P → K) :=
    Cardinal.mk_le_of_injective (f := fun x n => (AddMonoidAlgebra.coeff x) n) (fun x y h =>
      AddMonoidAlgebra.coeff_injective (Finsupp.ext fun n => congrFun h n))
  refine h1.trans ?_
  rw [← Cardinal.power_def]
  have h2 : Cardinal.mk K ≤ (Spec (CommRingCat.of K)).size := by
    rw [Scheme.size_Spec]
    exact le_max_right _ _
  refine (Cardinal.power_le_power_right h2).trans ?_
  exact Cardinal.power_le_power_left
    (fun h => by
      have := Scheme.aleph0_le_size (Spec (CommRingCat.of K))
      rw [h] at this
      exact absurd this (not_le.mpr Cardinal.aleph0_pos)) Cardinal.mk_le_aleph0

end Spec

section Main

variable {M : Type u} [AddCommGroup M] {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {aX : AAction (fppfO B S hS) M X} {aY : AAction (fppfO B S hS) M Y}
  {N : AddSubmonoid M} {F : AddSubgroup M}

/-- The value of a point of `Y^N` at the vertex of `𝔸(N)`: `n ↦ 1` on the face `F`, `n ↦ 0` off `F`. -/
def vertex (hF : IsFace F.toAddSubmonoid N) {T : BigFppfOver B S hS} (φ : AttractorPt aY N T) :
    Y.obj (op T) :=
  φ.app (𝟙 T) (APt.faceExt hF 1)

lemma vertex_baseChange (hF : IsFace F.toAddSubmonoid N) {T T' : BigFppfOver B S hS} (s : T' ⟶ T)
    (φ : AttractorPt aY N T) : vertex hF (φ.baseChange s) = Y.map s.op (vertex hF φ) := by
  have e := φ.naturality s (𝟙 T) (APt.faceExt hF 1)
  rw [← APt.faceExt_res] at e
  have hone : APt.res (𝒪 := fppfO B S hS) (P := F.toAddSubmonoid) s.op 1 = 1 := by
    ext q
    simp
  rw [hone, Category.comp_id] at e
  have e' : vertex hF (φ.baseChange s) = φ.app (𝟙 T' ≫ s) (APt.faceExt hF 1) := rfl
  rw [e', Category.id_comp]
  exact e

variable [Countable M]

/-- **The field case.** A point of `Y^N` with vertex in `X` has its values at field-valued points of
`𝔸(N)` in `X`: such a point is a translate of a generization of the vertex (`exists_generic_point_small`). -/
theorem mem_range_field (hg : EquivariantHom aX aY) (hf : Space.IsOpenImmersion B S hS hg.hom)
    (hF : IsFace F.toAddSubmonoid N) {T : BigFppfOver B S hS} (φ : AttractorPt aY N T)
    (x : X.obj (op T)) (hx : hg.hom.app _ x = vertex hF φ) {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K))) (tk : Spec (.of K) ⟶ (SCH).obj T)
    (a₀ : APt (fppfO B S hS) N (op (spO hK tk))) :
    ∃ x', hg.hom.app _ x' = φ.app (spT hK tk) a₀ := by
  classical
  let Pk : CommRingCat.{u} := CommRingCat.of K
  let Tk : BigFppfOver B S hS := spO hK tk
  let s : Tk ⟶ T := spT hK tk
  let eK : Γ((SCH).obj Tk, ⊤) ≃+* K := (Scheme.ΓSpecIso Pk).commRingCatIsoToRingEquiv
  let a₀' : Multiplicative N →* Γ((SCH).obj Tk, ⊤) := a₀
  let a₁ : Multiplicative N →* K := (eK : Γ((SCH).obj Tk, ⊤) →* K).comp a₀'
  have hne : ∀ n : N, (n : M) ∈ F → a₁ (Multiplicative.ofAdd n) ≠ 0 := by
    intro n hn h0
    let n' : N := ⟨-(n : M), hF.le (F.neg_mem hn)⟩
    have : a₁ (Multiplicative.ofAdd n) * a₁ (Multiplicative.ofAdd n') = 1 := by
      rw [← map_mul, ← map_one a₁]
      congr 1
      apply Multiplicative.toAdd.injective
      exact Subtype.ext (add_neg_cancel _)
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have hfm : ∀ a b : N, ((a + b : N) : M) ∈ F ↔ ((a : M) ∈ F ∧ (b : M) ∈ F) := fun a b =>
    ⟨fun h => hF.mem_of_add_mem a.2 b.2 h, fun h => F.add_mem h.1 h.2⟩
  let ch : Multiplicative N →* K :=
    { toFun := fun n => if ((Multiplicative.toAdd n : N) : M) ∈ F then 1 else 0
      map_one' := if_pos F.zero_mem
      map_mul' := fun a b => by
        have := hfm (Multiplicative.toAdd a) (Multiplicative.toAdd b)
        change ite (((Multiplicative.toAdd a + Multiplicative.toAdd b : N) : M) ∈ F) _ _ = _
        rw [if_congr this rfl rfl]
        change _ = ite _ _ _ * ite _ _ _
        by_cases ha : ((Multiplicative.toAdd a : N) : M) ∈ F <;>
          by_cases hb : ((Multiplicative.toAdd b : N) : M) ∈ F <;> simp [ha, hb] }
  let e : AddMonoidAlgebra K N →ₐ[K] K := AddMonoidAlgebra.lift K K N ch
  have he1 : ∀ n : N, e (AddMonoidAlgebra.single n 1) = if (n : M) ∈ F then 1 else 0 := by
    intro n
    rw [AddMonoidAlgebra.lift_single, one_smul]
    rfl
  obtain ⟨L, _, _, ι, ξ, χ, hLc, hξC, hξe, hχ⟩ := exists_generic_point_small N a₁ e (fun n h0 => by
    rw [he1, if_neg]
    exact fun hn => hne n hn h0)
  have hKM : B.Contains (Spec (.of (AddMonoidAlgebra K M))) := contains_monoidAlgebra hK M
  have hLs : B.Contains (Spec (.of L)) :=
    Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hKM hLc
  have hRs : B.Contains (Spec (.of (AddMonoidAlgebra K N))) := contains_monoidAlgebra hK N
  let R : CommRingCat.{u} := CommRingCat.of (AddMonoidAlgebra K N)
  let PL : CommRingCat.{u} := CommRingCat.of L
  let fC : Pk ⟶ R := CommRingCat.ofHom (algebraMap K (AddMonoidAlgebra K N))
  let fe : R ⟶ Pk := CommRingCat.ofHom e.toRingHom
  let fξ : R ⟶ PL := CommRingCat.ofHom ξ
  have hfe : fC ≫ fe = 𝟙 _ :=
    CommRingCat.hom_ext (RingHom.ext fun c => e.commutes c)
  let tP : Spec R ⟶ (SCH).obj T := Spec.map fC ≫ tk
  let TP : BigFppfOver B S hS := spO hRs tP
  let p : TP ⟶ Tk := overHom (Spec.map fC) (Category.assoc _ _ _).symm
  let i₀ : Tk ⟶ TP := overHom (Spec.map fe) (by
    change Spec.map fe ≫ (Spec.map fC ≫ tk) ≫ T.hom.hom = tk ≫ T.hom.hom
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, hfe, Spec.map_id, Category.id_comp])
  have hi₀p : i₀ ≫ p = 𝟙 _ := toScheme_map_injective (by
    rw [Functor.map_comp, map_overHom, map_overHom, ← Spec.map_comp, hfe, Spec.map_id,
      CategoryTheory.Functor.map_id]
    rfl)
  let TL : BigFppfOver B S hS := spO hLs (Spec.map fξ ≫ tP)
  let η : TL ⟶ TP := overHom (Spec.map fξ) (Category.assoc _ _ _).symm
  let eL : Γ((SCH).obj TL, ⊤) ≃+* L := (Scheme.ΓSpecIso PL).commRingCatIsoToRingEquiv
  -- the universal point of `𝔸(N)`
  let c : APt (fppfO B S hS) N (op TP) :=
    { toFun := fun n => (Scheme.ΓSpecIso R).inv.hom (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1)
      map_one' := map_one (Scheme.ΓSpecIso R).inv.hom
      map_mul' := fun a b => by
        exact (congrArg (Scheme.ΓSpecIso R).inv.hom (by
          rw [AddMonoidAlgebra.single_mul_single, mul_one]
          rfl)).trans (map_mul (Scheme.ΓSpecIso R).inv.hom _ _) }
  have hc₀ : APt.res i₀.op c = APt.faceExt hF 1 := by
    refine MonoidHom.ext fun n => ?_
    have h := congrArg (fun k => k.hom (AddMonoidAlgebra.single (Multiplicative.toAdd n) (1 : K)))
      (Scheme.ΓSpecIso_inv_naturality fe)
    have h' : (Scheme.ΓSpecIso Pk).inv.hom (e (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1)) =
        ((SCH).map i₀).appTop.hom (c n) := h
    refine h'.symm.trans ?_
    rw [he1]
    by_cases hn : ((Multiplicative.toAdd n : N) : M) ∈ F
    · rw [if_pos hn, APt.faceExt_pos hF 1 hn, map_one]
      rfl
    · rw [if_neg hn, APt.faceExt_neg hF 1 hn, map_zero]
      rfl
  let y := φ.app (p ≫ s) c
  have hy₀ : Y.map i₀.op y = hg.hom.app _ (X.map s.op x) := by
    have e₁ : φ.app (i₀ ≫ p ≫ s) (APt.res i₀.op c) = Y.map i₀.op y := φ.naturality i₀ (p ≫ s) c
    have e₂ : i₀ ≫ p ≫ s = s := by rw [← Category.assoc, hi₀p, Category.id_comp]
    rw [← e₁, e₂, hc₀, hom_naturality_apply, hx]
    have := vertex_baseChange hF s φ
    refine Eq.trans ?_ this
    change _ = φ.app (𝟙 Tk ≫ s) _
    rw [Category.id_comp]
  have hi := range_sub_of_mem hf i₀ y _ hy₀.symm
  let pL : Spec PL := ⟨⊥, Ideal.isPrime_bot⟩
  let pK : Spec Pk := ⟨⊥, Ideal.isPrime_bot⟩
  have hgen : (SCH).map η pL ∈ rangeOf hf y := by
    have hsp : ((SCH).map η pL) ⤳ ((SCH).map i₀ pK) := by
      refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
      intro t ht
      have h0 : ξ t = 0 := ht
      have h1 : e t = 0 := hξe t h0
      change fe.hom t ∈ (pK : PrimeSpectrum K).asIdeal
      have h2 : fe.hom t = 0 := h1
      rw [h2]
      exact Ideal.zero_mem _
    exact hsp.mem_open (isOpen_rangeOf hf y) (hi ⟨pK, rfl⟩)
  have hsub : Subsingleton (Spec PL) := Sec12Printed.spec_field_subsingleton L
  obtain ⟨v, hv⟩ := mem_of_range hf η y (by
    rintro _ ⟨b, rfl⟩
    have : b = pL := hsub.elim _ _
    rw [this]
    exact hgen)
  -- the translation
  let χu : Multiplicative M →* Γ((SCH).obj TL, ⊤)ˣ := (Units.map (eL.symm : L →* Γ((SCH).obj TL, ⊤))).comp χ
  let χ' : APt (fppfO B S hS) M (op TL) := (Units.coeHom _).comp χu
  let q : TL ⟶ Tk := η ≫ p
  have hqa : APt.res q.op a₀ = APt.toMagnet N χ' * APt.res η.op c := by
    refine MonoidHom.ext fun n => ?_
    let n₀ : N := Multiplicative.toAdd n
    have h1 : ((SCH).map η).appTop.hom (c n) = eL.symm (ξ (AddMonoidAlgebra.single n₀ 1)) :=
      (congrArg (fun k => k.hom (AddMonoidAlgebra.single n₀ (1 : K)))
        (Scheme.ΓSpecIso_inv_naturality fξ)).symm
    have h2 : ((SCH).map p).appTop.hom (a₀' n) = (Scheme.ΓSpecIso R).inv.hom (fC.hom (a₁ n)) := by
      have ha : a₀' n = (Scheme.ΓSpecIso Pk).inv.hom (a₁ n) := (eK.symm_apply_apply (a₀' n)).symm
      rw [ha]
      exact (congrArg (fun k => k.hom (a₁ n)) (Scheme.ΓSpecIso_inv_naturality fC)).symm
    have h3 : ((SCH).map η).appTop.hom ((Scheme.ΓSpecIso R).inv.hom (fC.hom (a₁ n))) =
        eL.symm (ξ (fC.hom (a₁ n))) :=
      (congrArg (fun k => k.hom (fC.hom (a₁ n))) (Scheme.ΓSpecIso_inv_naturality fξ)).symm
    have h4 : ξ (fC.hom (a₁ n)) = (χ (Multiplicative.ofAdd (n₀ : M)) : L) * ξ (AddMonoidAlgebra.single n₀ 1) :=
      (hξC _).trans (hχ n₀)
    change ((SCH).map (η ≫ p)).appTop.hom (a₀' n) =
      eL.symm (χ (Multiplicative.ofAdd (n₀ : M)) : L) * ((SCH).map η).appTop.hom (c n)
    rw [Functor.map_comp, Scheme.Hom.comp_appTop]
    change ((SCH).map η).appTop.hom (((SCH).map p).appTop.hom (a₀' n)) = _
    rw [h2, h3, h4, h1, map_mul]
  have hy' : Y.map q.op (φ.app s a₀) = hg.hom.app _ (aX.smul χ' v) := by
    have e₂ := φ.naturality q s a₀
    rw [← e₂, hqa, φ.equivariant, hg.map_smul, hv]
    congr 1
    have e₃ := φ.naturality η (p ≫ s) c
    rw [show q ≫ s = η ≫ p ≫ s from Category.assoc _ _ _]
    exact e₃
  have hr := range_sub_of_mem hf q (φ.app s a₀) _ hy'.symm
  refine mem_of_surj hf _ fun z => ?_
  have hzz : z = (SCH).map q pL := (Sec12Printed.spec_field_subsingleton K).elim _ _
  rw [hzz]
  exact hr ⟨pL, rfl⟩

/-- A point of `Y^N` with vertex in `X` has all its values in `X`. -/
theorem mem_range_app (hg : EquivariantHom aX aY) (hf : Space.IsOpenImmersion B S hS hg.hom)
    (hF : IsFace F.toAddSubmonoid N) {T : BigFppfOver B S hS} (φ : AttractorPt aY N T)
    (x : X.obj (op T)) (hx : hg.hom.app _ x = vertex hF φ) {T' : BigFppfOver B S hS} (t : T' ⟶ T)
    (a : APt (fppfO B S hS) N (op T')) : ∃ x', hg.hom.app _ x' = φ.app t a := by
  refine mem_of_surj hf _ fun s => ?_
  have hK := BigFppfSite.residueField_spec_contains B T'.left.2 s
  let m₀ := ((SCH).obj T').fromSpecResidueField s
  let tk := m₀ ≫ (SCH).map t
  let m : spO hK tk ⟶ T' := overHom m₀ (by
    have e₂ : (SCH).map t ≫ T.hom.hom = T'.hom.hom := congrArg (fun k => k.hom) (Over.w t)
    change m₀ ≫ T'.hom.hom = (m₀ ≫ (SCH).map t) ≫ T.hom.hom
    rw [Category.assoc, e₂])
  have hs : spT hK tk = m ≫ t := toScheme_map_injective rfl
  obtain ⟨x', hx'⟩ := mem_range_field hg hf hF φ x hx hK tk (APt.res m.op a)
  rw [hs, φ.naturality] at hx'
  refine range_sub_of_mem hf m _ x' hx' ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
  exact Scheme.fromSpecResidueField_apply s _

lemma app_injective (hg : EquivariantHom aX aY) (hf : Space.IsOpenImmersion B S hS hg.hom)
    {P : BigFppfOver B S hS} {x x' : X.obj (op P)} (h : hg.hom.app _ x = hg.hom.app _ x') : x = x' := by
  have hm := Space.mono_of_isOpenImmersion B S hS _ hf
  have := (NatTrans.mono_iff_mono_app hg.hom).1 hm (op P)
  exact (mono_iff_injective _).1 this h

/-- **`X^N = Y^N ×_Y X` along the vertex maps, on points.** -/
theorem existsUnique_attractorPt (hg : EquivariantHom aX aY) (hf : Space.IsOpenImmersion B S hS hg.hom)
    (hF : IsFace F.toAddSubmonoid N) {T : BigFppfOver B S hS} (φ : AttractorPt aY N T)
    (x : X.obj (op T)) (hx : hg.hom.app _ x = vertex hF φ) :
    ∃! ψ : AttractorPt aX N T, ψ.push hg = φ ∧ vertex hF ψ = x := by
  choose v hv using fun (T' : BigFppfOver B S hS) (t : T' ⟶ T)
    (a : APt (fppfO B S hS) N (op T')) => mem_range_app hg hf hF φ x hx t a
  let ψ : AttractorPt aX N T :=
    { app := fun {T'} t a => v T' t a
      naturality := fun s t a => app_injective hg hf (by
        rw [hv, hom_naturality_apply, hv, φ.naturality])
      equivariant := fun t h a => app_injective hg hf (by
        rw [hv, hg.map_smul, hv, φ.equivariant]) }
  refine ⟨ψ, ⟨AttractorPt.ext ?_, app_injective hg hf ?_⟩, ?_⟩
  · funext T' t a
    exact hv T' t a
  · exact (hv T (𝟙 T) _).trans hx.symm
  · rintro ψ' ⟨h₁, -⟩
    refine AttractorPt.ext ?_
    funext T' t a
    refine app_injective hg hf ?_
    exact (congrArg (fun p : AttractorPt aY N T => p.app t a) h₁).trans (hv T' t a).symm

omit [Countable M] in
/-- The vertex morphism `Z → X` from a presheaf representing `X^N`. -/
def repVertex {aX : AAction (fppfO B S hS) M X} (hF : IsFace F.toAddSubmonoid N)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (r : RepresentsAttractor aX N Z) : Z ⟶ X where
  app T := ↾ fun z => vertex hF (r.equiv (unop T) z)
  naturality T T' s := by
    ext z
    change vertex hF (r.equiv (unop T') (Z.map s.unop.op z)) =
      X.map s.unop.op (vertex hF (r.equiv (unop T) z))
    rw [r.naturality, vertex_baseChange]

/-- **Proposition 12.2 (i), cartesian form.** For an equivariant open immersion `f : X → Y`, the square
of `f^N` and `f` along the vertex maps is cartesian: `X^N = Y^N ×_Y X`. -/
theorem isPullback_repAttractorMap_open (hg : EquivariantHom aX aY)
    (hf : Space.IsOpenImmersion B S hS hg.hom) (hF : IsFace F.toAddSubmonoid N)
    {ZX ZY : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (rX : RepresentsAttractor aX N ZX) (rY : RepresentsAttractor aY N ZY) :
    IsPullback (repAttractorMap hg N rX rY) (repVertex hF rX) (repVertex hF rY) hg.hom := by
  have w : repAttractorMap hg N rX rY ≫ repVertex hF rY = repVertex hF rX ≫ hg.hom := by
    ext T z
    change vertex hF ((rY.equiv (unop T)) ((rY.equiv (unop T)).symm _)) = _
    rw [Equiv.apply_symm_apply]
    rfl
  refine IsPullback.of_forall_isPullback_app fun T => ?_
  rw [Limits.Types.isPullback_iff]
  refine ⟨congrArg (fun k => k.app T) w, ?_, ?_⟩
  · rintro z z' ⟨h₁, h₂⟩
    refine (rX.equiv (unop T)).injective ?_
    obtain ⟨ψ, -, hu⟩ := existsUnique_attractorPt hg hf hF
      ((rX.equiv (unop T) z).push hg) (vertex hF (rX.equiv (unop T) z)) rfl
    have hpush : (rX.equiv (unop T) z').push hg = (rX.equiv (unop T) z).push hg :=
      ((rY.equiv (unop T)).symm.injective h₁).symm
    rw [hu _ ⟨rfl, rfl⟩, hu _ ⟨hpush, h₂.symm⟩]
  · intro y x hxy
    have hxy' : hg.hom.app _ x = vertex hF (rY.equiv (unop T) y) := hxy.symm
    obtain ⟨ψ, ⟨h₁, h₂⟩, -⟩ := existsUnique_attractorPt hg hf hF (rY.equiv (unop T) y) x hxy'
    refine ⟨(rX.equiv (unop T)).symm ψ, ?_, ?_⟩
    · change (rY.equiv (unop T)).symm ((rX.equiv (unop T) ((rX.equiv (unop T)).symm ψ)).push hg) = y
      rw [Equiv.apply_symm_apply, h₁, Equiv.symm_apply_apply]
    · change vertex hF (rX.equiv (unop T) ((rX.equiv (unop T)).symm ψ)) = x
      rw [Equiv.apply_symm_apply, h₂]

/-- **Proposition 12.2 (i)** for algebraic spaces: if `f : X → Y` is an equivariant open immersion and
`X^N`, `Y^N` are represented, then `f^N : X^N → Y^N` is an open immersion. `M` is countable (site cutoff);
`N` is arbitrary. The representing presheaves need not be assumed algebraic spaces. -/
theorem isOpenImmersion_repAttractorMap (hg : EquivariantHom aX aY)
    (hf : Space.IsOpenImmersion B S hS hg.hom) (N : AddSubmonoid M)
    {ZX ZY : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (rX : RepresentsAttractor aX N ZX) (rY : RepresentsAttractor aY N ZY) :
    Space.IsOpenImmersion B S hS (repAttractorMap hg N rX rY) :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (isPullback_repAttractorMap_open hg hf (Sec12Printed.isFace_unitsOf N) rX rY).flip hf

/-- **The reduction step of Theorem 12.4**, for algebraic spaces: for `f : X → Y` an equivariant open
immersion, `X^N = Y^N ×_{Y^F} X^F`, for `F` a subgroup face of `N`. -/
theorem isPullback_repFace_open (hg : EquivariantHom aX aY)
    (hf : Space.IsOpenImmersion B S hS hg.hom) (hF : IsFace F.toAddSubmonoid N)
    {ZX ZY ZX' ZY' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (rX : RepresentsAttractor aX N ZX) (rY : RepresentsAttractor aY N ZY)
    (rX' : RepresentsAttractor aX F.toAddSubmonoid ZX')
    (rY' : RepresentsAttractor aY F.toAddSubmonoid ZY') :
    IsPullback (repAttractorMap hg N rX rY) (repFace rX rX' hF) (repFace rY rY' hF)
      (repAttractorMap hg F.toAddSubmonoid rX' rY') := by
  have hface : ∀ {T : BigFppfOver B S hS} (ψ : AttractorPt aX N T),
      (ψ.ofFace hF).push hg = (ψ.push hg).ofFace hF := fun _ => rfl
  have w : repAttractorMap hg N rX rY ≫ repFace rY rY' hF =
      repFace rX rX' hF ≫ repAttractorMap hg F.toAddSubmonoid rX' rY' := by
    ext T z
    change (rY'.equiv (unop T)).symm (((rY.equiv (unop T)) ((rY.equiv (unop T)).symm _)).ofFace hF) =
      (rY'.equiv (unop T)).symm (((rX'.equiv (unop T)) ((rX'.equiv (unop T)).symm _)).push hg)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl
  have hmono : ∀ {T : BigFppfOver B S hS} {ψ ψ' : AttractorPt aX F.toAddSubmonoid T},
      ψ.push hg = ψ'.push hg → ψ = ψ' := by
    intro T ψ ψ' h
    refine AttractorPt.ext ?_
    funext T' t a
    exact app_injective hg hf (congrArg (fun p : AttractorPt aY _ T => p.app t a) h)
  refine IsPullback.of_forall_isPullback_app fun T => ?_
  rw [Limits.Types.isPullback_iff]
  refine ⟨congrArg (fun k => k.app T) w, ?_, ?_⟩
  · rintro z z' ⟨h₁, -⟩
    refine (rX.equiv (unop T)).injective ?_
    refine AttractorPt.ext ?_
    funext T' t a
    have hpush : (rX.equiv (unop T) z).push hg = (rX.equiv (unop T) z').push hg :=
      (rY.equiv (unop T)).symm.injective h₁
    exact app_injective hg hf (congrArg (fun p : AttractorPt aY N _ => p.app t a) hpush)
  · intro y u hyu
    have hyu' : (rY.equiv (unop T) y).ofFace hF = (rX'.equiv (unop T) u).push hg := by
      have := (rY'.equiv (unop T)).symm.injective hyu
      exact this
    have hx : hg.hom.app _ (rX'.equiv (unop T) u).toPoint = vertex hF (rY.equiv (unop T) y) :=
      (congrArg (fun p : AttractorPt aY F.toAddSubmonoid (unop T) => p.toPoint) hyu').symm
    obtain ⟨ψ, ⟨h₁, h₂⟩, -⟩ := existsUnique_attractorPt hg hf hF (rY.equiv (unop T) y) _ hx
    refine ⟨(rX.equiv (unop T)).symm ψ, ?_, ?_⟩
    · change (rY.equiv (unop T)).symm ((rX.equiv (unop T) ((rX.equiv (unop T)).symm ψ)).push hg) = y
      rw [Equiv.apply_symm_apply, h₁, Equiv.symm_apply_apply]
    · change (rX'.equiv (unop T)).symm ((rX.equiv (unop T) ((rX.equiv (unop T)).symm ψ)).ofFace hF) = u
      rw [Equiv.apply_symm_apply, Equiv.symm_apply_eq]
      apply hmono
      rw [hface, h₁, hyu']

end Main

#print axioms isOpenImmersion_repAttractorMap
#print axioms isPullback_repAttractorMap_open
#print axioms isPullback_repFace_open

end AlgMag.Sec12Spaces
