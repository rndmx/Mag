/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec12PrintedLocal

/-!
# Theorem 12.4, schemes only

Mayeux, *Algebraic Magnetism*, Theorem 12.4. `X → S` is smooth with a Zariski locally linearizable
action, `N` is finitely generated (see `AlgMag.Sec12Printed.printed_affine` for the case `X` affine over
`S`, `M` finitely generated and `N` arbitrary). The attractors `X^N`, `X^{N^×}` are represented by
schemes `Zx`, `Zf` (representability is Theorem 8.3). Then `Zf` is covered by opens
`Spec B₀` over which `Zx → Zf` is `Spec B → Spec B₀`, with `B = Sym_{B₀}(P)` and `P` finite projective.
-/

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism

open scoped Classical

universe u

namespace AlgMag.Sec12Printed

open AlgMag.GB AlgMag.Lifts AlgMag.SmoothSchemes

attribute [local instance] gradedAlgebraOf

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M]

/-- **Definition 7.2** on the site `Over S`: `X` is covered by `S`-affine `D(M)_S`-stable opens. -/
structure LocLin {X : Over S} (aX : AAction (overO S) M (yoneda.obj X)) where
  /-- The index. -/
  I : Type u
  /-- The opens. -/
  W : I → Over S
  /-- The actions. -/
  act : ∀ i, AAction (overO S) M (yoneda.obj (W i))
  /-- The inclusions. -/
  j : ∀ i, W i ⟶ X
  isOpen : ∀ i, IsOpenImmersion (j i).left
  affine : ∀ i, IsAffineHom (W i).hom
  equivariant : ∀ i {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ W i),
    sm (act i) h x ≫ j i = sm aX h (x ≫ j i)
  covers : ∀ x : X.left, ∃ i, x ∈ Set.range (j i).left

section Square

variable {X W : Over S} {aX : AAction (overO S) M (yoneda.obj X)} [IsAffineHom W.hom]
  (aW : AAction (overO S) M (yoneda.obj W)) (j : W ⟶ X) [IsOpenImmersion j.left]
  (hj : ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ W), sm aW h x ≫ j = sm aX h (x ≫ j))

include hj in
lemma push_injective {P : AddSubmonoid M} {T : Over S} {ψ ψ' : AttractorPt aW P T}
    (h : AttractorPt.push (eqHom j hj) ψ = AttractorPt.push (eqHom j hj) ψ') : ψ = ψ' := by
  refine AttractorPt.ext ?_
  funext T₁ t a
  have e := congrArg (fun χ : AttractorPt aX P T => χ.app t a) h
  refine Over.OverMorphism.ext ((cancel_mono j.left).1 ?_)
  exact congrArg (fun k : T₁ ⟶ X => k.left) e

variable {P : AddSubmonoid M} {Zp : Over S} (rp : RepresentsAttractor aX P (yoneda.obj Zp))

/-- The bijection of `rp`, with its type spelled out. -/
abbrev rEq (T : Over S) : (T ⟶ Zp) ≃ AttractorPt aX P T := rp.equiv T

lemma rEq_comp {T T' : Over S} (s : T' ⟶ T) (w : T ⟶ Zp) :
    rEq rp T' (s ≫ w) = (rEq rp T w).baseChange s := rp.naturality s w

/-- `W^P → X^P` on the representing schemes. -/
def eMap : Zatt aW P ⟶ Zp :=
  (rEq rp (Zatt aW P)).symm
    (AttractorPt.push (eqHom j hj) (attEquiv aW P (Zatt aW P) (𝟙 (Zatt aW P))))

lemma eMap_spec {T : Over S} (w : T ⟶ Zatt aW P) :
    rEq rp T (w ≫ eMap aW j hj rp) = AttractorPt.push (eqHom j hj) (attEquiv aW P T w) := by
  rw [rEq_comp, eMap, Equiv.apply_symm_apply]
  have : attEquiv aW P T w = (attEquiv aW P (Zatt aW P) (𝟙 (Zatt aW P))).baseChange w := by
    rw [← attEquiv_comp, Category.comp_id]
  rw [this]
  refine AttractorPt.ext ?_
  funext T₁ t a
  rfl

end Square

section Main

variable {X W : Over S} {aX : AAction (overO S) M (yoneda.obj X)} [IsAffineHom W.hom]
  (aW : AAction (overO S) M (yoneda.obj W)) (j : W ⟶ X) [IsOpenImmersion j.left]
  (hj : ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ W), sm aW h x ≫ j = sm aX h (x ≫ j))
  {N : AddSubmonoid M} {F : AddSubgroup M} (hF : IsFace F.toAddSubmonoid N)
  {Zx Zf : Over S} (rx : RepresentsAttractor aX N (yoneda.obj Zx))
  (rf : RepresentsAttractor aX F.toAddSubmonoid (yoneda.obj Zf)) (z : Zx ⟶ Zf)
  (hz : ∀ (T : Over S) (w : T ⟶ Zx), rf.equiv T (w ≫ z) = AttractorPt.ofFace hF (rx.equiv T w))

include hz in
lemma eMap_square :
    eMap aW j hj rx ≫ z = faceZ aW N hF ≫ eMap aW j hj rf := by
  apply (rEq rf (Zatt aW N)).injective
  have hz' := hz (Zatt aW N) (eMap aW j hj rx)
  refine Eq.trans hz' ?_
  rw [eMap_spec aW j hj rf]
  have e2 := faceZ_spec aW N hF (𝟙 (Zatt aW N))
  rw [Category.id_comp] at e2
  rw [e2]
  change AttractorPt.ofFace hF (rEq rx (Zatt aW N) (eMap aW j hj rx)) = _
  have e := eMap_spec aW j hj rx (𝟙 (Zatt aW N))
  rw [Category.id_comp] at e
  rw [e]
  refine AttractorPt.ext ?_
  funext T₁ t a
  rfl

include hz in
/-- "We reduce to `X` affine over `S`": the universal property of `W^N = X^N ×_{X^F} W^F`. -/
theorem lift_N (w : N →+ ℕ) (hw : ∀ n : N, w n = 0 ↔ (n : M) ∈ F) {T : Over S} (t : T ⟶ Zx)
    (u : T ⟶ Zatt aW F.toAddSubmonoid) (hc : t ≫ z = u ≫ eMap aW j hj rf) :
    ∃ l : T ⟶ Zatt aW N, l ≫ eMap aW j hj rx = t ∧ l ≫ faceZ aW N hF = u := by
  have e₁ : AttractorPt.ofFace hF (rx.equiv T t) =
      AttractorPt.push (eqHom j hj) (attEquiv aW F.toAddSubmonoid T u) := by
    refine (hz T t).symm.trans ?_
    change rEq rf T (t ≫ z) = _
    rw [hc, eMap_spec]
  have hv : (AttractorPt.ofFace hF (rx.equiv T t)).toPoint = (u ≫ iAtt aW F.toAddSubmonoid) ≫ j := by
    rw [e₁]
    change (attEquiv aW F.toAddSubmonoid T u).toPoint ≫ j = _
    rw [toPoint_attEquiv]
  obtain ⟨ψ, hψ⟩ := exists_att_of_vertex j hj hF w hw (rx.equiv T t) _ hv
  refine ⟨(attEquiv aW N T).symm ψ, ?_, ?_⟩
  · apply (rEq rx T).injective
    rw [eMap_spec, Equiv.apply_symm_apply, hψ]
  · apply (attEquiv aW F.toAddSubmonoid T).injective
    rw [faceZ_spec, Equiv.apply_symm_apply]
    apply push_injective aW j hj
    rw [← e₁, ← hψ]
    refine AttractorPt.ext ?_
    funext T₁ t' a
    rfl

/-- A pullback square of `S`-schemes can be tested on `S`-schemes. -/
theorem isPullback_of_over {P A B C : Over S} (a : P ⟶ A) (b : P ⟶ B) (c : A ⟶ C) (d : B ⟶ C)
    (hcomm : a ≫ c = b ≫ d)
    (hlift : ∀ {T : Over S} (t : T ⟶ A) (u : T ⟶ B), t ≫ c = u ≫ d → ∃ l : T ⟶ P, l ≫ a = t ∧ l ≫ b = u)
    (huniq : ∀ {T : Over S} (l l' : T ⟶ P), l ≫ a = l' ≫ a → l ≫ b = l' ≫ b → l = l') :
    IsPullback a.left b.left c.left d.left := by
  have over {W : Scheme.{u}} (x : W ⟶ B.left) : (x ≫ B.hom) = (x ≫ B.hom) := rfl
  let ov {W : Scheme.{u}} (x : W ⟶ B.left) : Over S := Over.mk (x ≫ B.hom)
  have ex : ∀ (s : PullbackCone c.left d.left), ∃ m : s.pt ⟶ P.left, m ≫ a.left = s.fst ∧ m ≫ b.left = s.snd := by
    intro s
    let t : ov s.snd ⟶ A := Over.homMk s.fst (by
      change s.fst ≫ A.hom = s.snd ≫ B.hom
      rw [← Over.w c, ← Over.w d, ← Category.assoc, ← Category.assoc, s.condition])
    let u : ov s.snd ⟶ B := Over.homMk s.snd rfl
    obtain ⟨l, h₁, h₂⟩ := hlift t u (Over.OverMorphism.ext s.condition)
    exact ⟨l.left, congrArg (fun k => k.left) h₁, congrArg (fun k => k.left) h₂⟩
  refine ⟨⟨congrArg (fun k => k.left) hcomm⟩,
    ⟨PullbackCone.IsLimit.mk _ (fun s => (ex s).choose) (fun s => (ex s).choose_spec.1)
      (fun s => (ex s).choose_spec.2) (fun s m h₁ h₂ => ?_)⟩⟩
  obtain ⟨h₃, h₄⟩ := (ex s).choose_spec
  let T : Over S := ov s.snd
  have wm : ∀ {m : s.pt ⟶ P.left}, m ≫ b.left = s.snd → m ≫ P.hom = T.hom := by
    intro m h
    change m ≫ P.hom = s.snd ≫ B.hom
    rw [← h, Category.assoc, Over.w b]
  have := huniq (T := T) (Over.homMk m (wm h₂)) (Over.homMk _ (wm h₄))
    (Over.OverMorphism.ext (h₁.trans h₃.symm)) (Over.OverMorphism.ext (h₂.trans h₄.symm))
  exact congrArg (fun k => k.left) this

include hz in
theorem isPullback_eMap (w : N →+ ℕ) (hw : ∀ n : N, w n = 0 ↔ (n : M) ∈ F) :
    IsPullback (eMap aW j hj rx).left (faceZ aW N hF).left z.left (eMap aW j hj rf).left :=
  isPullback_of_over _ _ _ _ (eMap_square aW j hj hF rx rf z hz)
    (fun t u h => lift_N aW j hj hF rx rf z hz w hw t u h)
    (fun l l' h _ => by
      apply (attEquiv aW N _).injective
      apply push_injective aW j hj
      rw [← eMap_spec aW j hj rx, ← eMap_spec aW j hj rx, h])

/-- The chart square is a pullback. -/
theorem isPullback_chart_square (U : S.affineOpens) :
    IsPullback (iotaZ aW N U).left (PhiMap U.2 (rho0 aW N hF U.2)).left (faceZ aW N hF).left
      (iotaZ aW F.toAddSubmonoid U).left := by
  have mono₁ : ∀ {T : Over S} {l l' : T ⟶ Zloc aW F.toAddSubmonoid U.2},
      l ≫ iotaZ aW F.toAddSubmonoid U = l' ≫ iotaZ aW F.toAddSubmonoid U → l = l' := by
    intro T l l' h
    refine Over.OverMorphism.ext ((cancel_mono (iotaZ aW F.toAddSubmonoid U).left).1 ?_)
    exact congrArg (fun k => k.left) h
  refine isPullback_of_over _ _ _ _ (chart_square aW N hF U) (fun t u h => ?_) (fun l l' h _ => ?_)
  · have hT : LiesOver _ U.1 := LiesOver.of_hom u (liesOver_Zloc aW F.toAddSubmonoid U.2)
    obtain ⟨m, hm⟩ := exists_lift_iotaZ aW N U hT t
    refine ⟨m, hm, mono₁ ?_⟩
    rw [Category.assoc, ← chart_square, ← Category.assoc, hm, h]
  · refine Over.OverMorphism.ext ((cancel_mono (iotaZ aW N U).left).1 ?_)
    exact congrArg (fun k => k.left) h

end Main

section Open

variable {X W : Over S} {aX : AAction (overO S) M (yoneda.obj X)} [IsAffineHom W.hom]
  (aW : AAction (overO S) M (yoneda.obj W)) (j : W ⟶ X) [IsOpenImmersion j.left]
  (hj : ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ W), sm aW h x ≫ j = sm aX h (x ≫ j))
  {F : AddSubgroup M} {Zf : Over S}
  (rf : RepresentsAttractor aX F.toAddSubmonoid (yoneda.obj Zf))

lemma isFace_self (F : AddSubgroup M) : IsFace F.toAddSubmonoid F.toAddSubmonoid := by
  refine ⟨le_rfl, fun {x y} hx hy _ => ⟨hx, hy⟩⟩

/-- `X^F → X`. -/
def vF : Zf ⟶ X := (rEq rf Zf (𝟙 Zf)).toPoint

lemma comp_vF {T : Over S} (t : T ⟶ Zf) : t ≫ vF rf = (rEq rf T t).toPoint := by
  have h := rEq_comp rf t (𝟙 Zf)
  rw [Category.comp_id] at h
  rw [h]
  have := (rEq rf Zf (𝟙 Zf)).naturality t (𝟙 Zf) 1
  have hone : APt.res (𝒪 := overO S) (P := F.toAddSubmonoid) t.op 1 = 1 := by
    ext p
    simp
  rw [hone, Category.comp_id] at this
  have e : (AttractorPt.baseChange t (rEq rf Zf (𝟙 Zf))).toPoint = (rEq rf Zf (𝟙 Zf)).app t 1 := by
    change (rEq rf Zf (𝟙 Zf)).app (𝟙 T ≫ t) 1 = _
    rw [Category.id_comp]
  rw [e, this]
  rfl

lemma toPoint_ofFace_self {T : Over S} (φ : AttractorPt aX F.toAddSubmonoid T) :
    (AttractorPt.ofFace (isFace_self F) φ).toPoint = φ.toPoint := by
  change φ.app (𝟙 T) (APt.faceExt (isFace_self F) 1) = _
  congr 1
  exact MonoidHom.ext fun n => APt.faceExt_pos _ 1 (Multiplicative.toAdd n).2

theorem lift_F {T : Over S} (t : T ⟶ Zf) (u : T ⟶ W) (hc : t ≫ vF rf = u ≫ j) :
    ∃ l : T ⟶ Zatt aW F.toAddSubmonoid, l ≫ eMap aW j hj rf = t ∧ l ≫ iAtt aW F.toAddSubmonoid = u := by
  have hv : (AttractorPt.ofFace (isFace_self F) (rEq rf T t)).toPoint = u ≫ j := by
    rw [toPoint_ofFace_self, ← comp_vF, hc]
  obtain ⟨ψ, hψ⟩ := exists_att_of_vertex j hj (isFace_self F) 0
    (fun n => ⟨fun _ => (Multiplicative.toAdd (Multiplicative.ofAdd n)).2, fun _ => rfl⟩) (rEq rf T t) u hv
  refine ⟨(attEquiv aW F.toAddSubmonoid T).symm ψ, ?_, ?_⟩
  · apply (rEq rf T).injective
    rw [eMap_spec, Equiv.apply_symm_apply, hψ]
  · rw [← toPoint_attEquiv, Equiv.apply_symm_apply]
    refine Over.OverMorphism.ext ((cancel_mono j.left).1 ?_)
    have e : ψ.toPoint ≫ j = (rEq rf T t).toPoint := by
      rw [← hψ]
      rfl
    have e₂ : ψ.toPoint ≫ j = u ≫ j := by
      rw [e, ← comp_vF, hc]
    exact congrArg (fun k => k.left) e₂

theorem isPullback_eMap_F :
    IsPullback (eMap aW j hj rf).left (iAtt aW F.toAddSubmonoid).left (vF rf).left j.left :=
  isPullback_of_over _ _ _ _ (by
      have e := eMap_spec aW j hj rf (𝟙 (Zatt aW F.toAddSubmonoid))
      rw [Category.id_comp] at e
      rw [comp_vF, e]
      change (attEquiv aW F.toAddSubmonoid _ (𝟙 _)).toPoint ≫ j = _
      rw [toPoint_attEquiv, Category.id_comp])
    (fun t u h => lift_F aW j hj rf t u h)
    (fun l l' _ h => iAtt_cancel aW F.toAddSubmonoid h)

instance instOpenEF : IsOpenImmersion (eMap aW j hj rf).left :=
  MorphismProperty.of_isPullback (isPullback_eMap_F aW j hj rf).flip inferInstance

end Open

section Thm

variable {N : AddSubmonoid M}

/-- **Theorem 12.4** (schemes only). `X → S` is smooth with a Zariski locally linearizable action, `N`
is finitely generated, `Zx`, `Zf` represent `X^N`, `X^{N^×}`, `z : Zx → Zf` is the morphism `p_{N,N^×}`.
Every point of `Zf` has an open neighbourhood `e : Spec B₀ → Zf`, with preimage `e' : Spec B → Zx`,
such that `Zx → Zf` restricts to `Spec B → Spec B₀`, where `B = Sym_{B₀}(P)`, `P` finite projective
over `B₀`; here `B = O(W^N|_U)`, `B₀ = O(W^{N^×}|_U)`, for `W` a stable affine open and `U ⊆ S` affine. -/
theorem thm124 {X : Over S} {aX : AAction (overO S) M (yoneda.obj X)} [Smooth X.hom] (L : LocLin aX)
    [∀ i, IsAffineHom (L.W i).hom] (hfg : N.FG) {Zx Zf : Over S}
    (rx : RepresentsAttractor aX N (yoneda.obj Zx))
    (rf : RepresentsAttractor aX (unitsOf N).toAddSubmonoid (yoneda.obj Zf)) (z : Zx ⟶ Zf)
    (hz : ∀ (T : Over S) (w : T ⟶ Zx),
      rf.equiv T (w ≫ z) = AttractorPt.ofFace (isFace_unitsOf N) (rx.equiv T w))
    (y : Zf.left) :
    ∃ (i : L.I) (U : S.Opens) (hU : IsAffineOpen U)
      (e : (Zloc (L.act i) (unitsOf N).toAddSubmonoid hU).left ⟶ Zf.left)
      (e' : (Zloc (L.act i) N hU).left ⟶ Zx.left),
      IsOpenImmersion e ∧ IsOpenImmersion e' ∧ y ∈ Set.range e ∧
      IsPullback e' (PhiMap hU (rho0 (L.act i) N (isFace_unitsOf N) hU)).left z.left e ∧
      letI := (rho0 (L.act i) N (isFace_unitsOf N) hU).toRingHom.toAlgebra
      (Module.Finite (Qalg (L.act i) (unitsOf N).toAddSubmonoid hU)
        (Conormal (piB (gZ (L.act i) hU (F := unitsOf N)) (Yq (unitsOf N) N)
          (hI₁' (L.act i) N (isFace_unitsOf N) hU) (hI₀' (L.act i) hU)
          (sharp_Yq N (isFace_unitsOf N)))) ∧
      Module.Projective (Qalg (L.act i) (unitsOf N).toAddSubmonoid hU)
        (Conormal (piB (gZ (L.act i) hU (F := unitsOf N)) (Yq (unitsOf N) N)
          (hI₁' (L.act i) N (isFace_unitsOf N) hU) (hI₀' (L.act i) hU)
          (sharp_Yq N (isFace_unitsOf N)))) ∧
      Nonempty (SymmetricAlgebra (Qalg (L.act i) (unitsOf N).toAddSubmonoid hU)
        (Conormal (piB (gZ (L.act i) hU (F := unitsOf N)) (Yq (unitsOf N) N)
          (hI₁' (L.act i) N (isFace_unitsOf N) hU) (hI₀' (L.act i) hU)
          (sharp_Yq N (isFace_unitsOf N)))) ≃ₐ[Qalg (L.act i) (unitsOf N).toAddSubmonoid hU]
        Qalg (L.act i) N hU)) := by
  have hF := isFace_unitsOf N
  obtain ⟨w, hw⟩ := exists_weight_of_isFace hF hfg
  obtain ⟨i, xw, hxw⟩ := L.covers ((vF rf).left y)
  have hO : IsOpenImmersion (L.j i).left := L.isOpen i
  have hsm : Smooth (L.W i).hom := by
    rw [← Over.w (L.j i)]
    infer_instance
  have hj : ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ L.W i),
      sm (L.act i) h x ≫ L.j i = sm aX h (x ≫ L.j i) := @fun T h x => L.equivariant i h x
  -- the point `y` is in `W^F`
  let κ := Zf.left.residueField y
  let c : Spec κ := ⟨⊥, Ideal.isPrime_bot⟩
  have hc : Zf.left.fromSpecResidueField y c = y := Scheme.fromSpecResidueField_apply y _
  let T : Over S := Over.mk (Zf.left.fromSpecResidueField y ≫ Zf.hom)
  let t : T ⟶ Zf := Over.homMk (Zf.left.fromSpecResidueField y) rfl
  have hsub : Subsingleton (Spec κ) := inferInstanceAs (Subsingleton (PrimeSpectrum κ))
  have hr : Set.range (t ≫ vF rf).left ⊆ Set.range (L.j i).left := by
    rintro _ ⟨b, rfl⟩
    have hb : b = c := hsub.elim _ _
    rw [hb, Over.comp_left, Scheme.Hom.comp_apply]
    change (vF rf).left (Zf.left.fromSpecResidueField y c) ∈ _
    rw [hc]
    exact ⟨xw, hxw⟩
  let u : T ⟶ L.W i := Over.homMk (IsOpenImmersion.lift (L.j i).left _ hr) (by
    rw [← Over.w (L.j i), ← Category.assoc, IsOpenImmersion.lift_fac]
    exact Over.w (t ≫ vF rf))
  have hu : t ≫ vF rf = u ≫ L.j i := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _).symm
  obtain ⟨l, hl, -⟩ := lift_F (L.act i) (L.j i) hj rf t u hu
  -- an affine open of `S` around its image
  let p : (Zatt (L.act i) (unitsOf N).toAddSubmonoid).left := l.left c
  obtain ⟨V, hV, hpV, -⟩ := exists_isAffineOpen_mem_and_subset (X := S)
    (x := (Zatt (L.act i) (unitsOf N).toAddSubmonoid).hom p) (U := ⊤) trivial
  let U : S.affineOpens := ⟨V, hV⟩
  let O := (Zatt (L.act i) (unitsOf N).toAddSubmonoid).hom ⁻¹ᵁ V
  let T₂ : Over S := Over.mk (O.ι ≫ (Zatt (L.act i) (unitsOf N).toAddSubmonoid).hom)
  let a₂ : T₂ ⟶ Zatt (L.act i) (unitsOf N).toAddSubmonoid := Over.homMk O.ι rfl
  have hT₂ : LiesOver T₂ U.1 := liesOver_of_forall fun x => by
    change (Zatt (L.act i) (unitsOf N).toAddSubmonoid).hom (O.ι x) ∈ V
    exact x.2
  obtain ⟨m, hm⟩ := exists_lift_iotaZ (L.act i) (unitsOf N).toAddSubmonoid U hT₂ a₂
  have hpr : p ∈ Set.range (iotaZ (L.act i) (unitsOf N).toAddSubmonoid U).left := by
    refine ⟨m.left ⟨p, hpV⟩, ?_⟩
    have e2 : (m ≫ iotaZ (L.act i) (unitsOf N).toAddSubmonoid U).left ⟨p, hpV⟩ = a₂.left ⟨p, hpV⟩ := by
      rw [hm]
    exact (Scheme.Hom.comp_apply m.left _ _).symm.trans e2
  obtain ⟨q, hq⟩ := hpr
  refine ⟨i, V, hV, (iotaZ (L.act i) (unitsOf N).toAddSubmonoid U).left ≫ (eMap (L.act i) (L.j i) hj rf).left,
    (iotaZ (L.act i) N U).left ≫ (eMap (L.act i) (L.j i) hj rx).left, inferInstance, ?_, ⟨q, ?_⟩, ?_, ?_⟩
  · have := MorphismProperty.of_isPullback
      (P := @IsOpenImmersion) (isPullback_eMap (L.act i) (L.j i) hj hF rx rf z hz w hw).flip
      (instOpenEF (L.act i) (L.j i) hj rf)
    infer_instance
  · rw [Scheme.Hom.comp_apply, hq]
    have e2 : (l ≫ eMap (L.act i) (L.j i) hj rf).left c = t.left c := by rw [hl]
    exact ((Scheme.Hom.comp_apply l.left _ _).symm.trans e2).trans hc
  · exact (isPullback_chart_square (L.act i) hF U).paste_horiz
      (isPullback_eMap (L.act i) (L.j i) hj hF rx rf z hz w hw)
  · exact printed_affine (L.act i) N hF hV (Or.inl hfg)

end Thm

#print axioms AlgMag.Sec12Printed.thm124
#print axioms AlgMag.Sec12Printed.smooth_faceZ

end AlgMag.Sec12Printed
