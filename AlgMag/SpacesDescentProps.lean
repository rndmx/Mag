/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.GenM332Scheme
import AlgMag.Sec3Final
import AlgMag.PrintedProp151

/-!
# Propositions 3.31 (ii), 3.32 (ii), 15.1 from the descent lemma, for any fppf sheaf

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026). The descent lemma
is the statement `AlgMag.SD.DescentProp X`: for `δ : P → Γ`, `Γ` a finitely generated group, `j : P₀ → P` the
kernel of `δ`, points of `X` over `𝔸(P₀)_T` are the `D(Γ)`-invariant points over `𝔸(P)_T`.
Here Propositions 3.31 (ii), 3.32 (ii), 15.1 are reduced to it for every fppf sheaf `X` with an action.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgMag.SD

open AlgMag AlgMag.SQ

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

variable (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- `x` over `𝔸(P)_T` is `D(Γ)`-invariant, for the grading `δ`: `F(g w) = F(w)` on points. -/
def IsInvPt {P Γ : Type u} [AddCommMonoid P] [Countable P] [AddCommGroup Γ] (δ : P →+ Γ)
    {T : BigFppfOver B S hS} [IsAffine ((SCH).obj T)] (x : X.obj (op (specObj P T))) : Prop :=
  ∀ {T' : BigFppfOver B S hS} (t : T' ⟶ T) (g : APt (fppfO B S hS) Γ (op T'))
    (c : APt (fppfO B S hS) P (op T')),
    X.map (specLift t (g.comp (AddMonoidHom.toMultiplicative δ) * c)).op x = X.map (specLift t c).op x

/-- **Lemma D**: for `T` affine, `x ↦ x ∘ π` is a bijection from points over `𝔸(P₀)_T` to invariant points
over `𝔸(P)_T`. -/
structure DescentProp : Prop where
  uniq : ∀ {P P₀ Γ : Type u} [AddCommMonoid P] [Countable P] [AddCommMonoid P₀] [Countable P₀]
    [AddCommGroup Γ] [AddGroup.FG Γ] (δ : P →+ Γ) (j : P₀ →+ P), Function.Injective j →
    (∀ p, δ p = 0 ↔ p ∈ Set.range j) → ∀ (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)]
    (x y : X.obj (op (specObj P₀ T))),
    X.map (specAlong T j).op x = X.map (specAlong T j).op y → x = y
  desc : ∀ {P P₀ Γ : Type u} [AddCommMonoid P] [Countable P] [AddCommMonoid P₀] [Countable P₀]
    [AddCommGroup Γ] [AddGroup.FG Γ] (δ : P →+ Γ) (j : P₀ →+ P), Function.Injective j →
    (∀ p, δ p = 0 ↔ p ∈ Set.range j) → ∀ (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)]
    (x : X.obj (op (specObj P T))), IsInvPt X δ x → ∃ x₀, X.map (specAlong T j).op x₀ = x

variable {X}

section Core

variable {M : Type u} [AddCommGroup M] {aX : AAction (fppfO B S hS) M X}
  {K : AddSubmonoid M} {P Γ : Type u} [AddCommMonoid P] [Countable P] [AddCommGroup Γ] [AddGroup.FG Γ]

/-- The common core of §2 and §3: a point `x` over `𝔸(P)_T`, invariant, equivariant along `ν`, descends to a
unique point of `X^K`. -/
theorem existsUnique_chi (hD : DescentProp X) [Countable M] (δ : P →+ Γ) (j : K →+ P) (hj : Function.Injective j)
    (hk : ∀ p, δ p = 0 ↔ p ∈ Set.range j) (ν : P →+ M) (hν : ∀ k, ν (j k) = k)
    {T : BigFppfOver B S hS} [IsAffine ((SCH).obj T)] (x : X.obj (op (specObj P T)))
    (hinv : IsInvPt X δ x)
    (hequi : ∀ {T' : BigFppfOver B S hS} (t : T' ⟶ T) (e : APt (fppfO B S hS) M (op T'))
      (c : APt (fppfO B S hS) P (op T')),
      X.map (specLift t (e.comp (AddMonoidHom.toMultiplicative ν) * c)).op x =
        aX.smul e (X.map (specLift t c).op x)) :
    ∃! χ : AttractorPt aX K T, ∀ {T' : BigFppfOver B S hS} (t : T' ⟶ T) (c : APt (fppfO B S hS) P (op T')),
      χ.app t (APt.along j c) = X.map (specLift t c).op x := by
  obtain ⟨x₀, hx⟩ := hD.desc δ j hj hk T x hinv
  have lift : ∀ {T' : BigFppfOver B S hS} (t : T' ⟶ T) (c : APt (fppfO B S hS) P (op T')),
      X.map (specLift t (APt.along j c)).op x₀ = X.map (specLift t c).op x := by
    intro T' t c
    rw [specLift_along, op_comp, Functor.map_comp_apply, hx]
  have hmap : ∀ {T' T'' : BigFppfOver B S hS} (s : T'' ⟶ T') (t : T' ⟶ T) (a : APt (fppfO B S hS) K (op T')),
      X.map (specLift (s ≫ t) (APt.res s.op a)).op x₀ = X.map s.op (X.map (specLift t a).op x₀) := by
    intro T' T'' s t a
    rw [specLift_comp, op_comp, Functor.map_comp_apply]
  -- equivariance on the universal point
  let P₂ := ↥K × M
  let Pm := P × M
  let Q := specObj P₂ T
  let tQ : Q ⟶ T := specPr P₂ T
  let aU : APt (fppfO B S hS) ↥K (op Q) := APt.along (AddMonoidHom.inl _ _) (specPt P₂ T)
  let hU : APt (fppfO B S hS) M (op Q) := APt.along (AddMonoidHom.inr _ _) (specPt P₂ T)
  let jh : P₂ →+ Pm := j.prodMap (AddMonoidHom.id M)
  let δh : Pm →+ Γ := δ.comp (AddMonoidHom.fst _ _)
  let π : specObj Pm T ⟶ Q := specAlong T jh
  let tm : specObj Pm T ⟶ T := specPr Pm T
  let ch : APt (fppfO B S hS) P (op (specObj Pm T)) := APt.along (AddMonoidHom.inl _ _) (specPt Pm T)
  let eh : APt (fppfO B S hS) M (op (specObj Pm T)) := APt.along (AddMonoidHom.inr _ _) (specPt Pm T)
  have hπt : π ≫ tQ = tm := specAlong_pr T jh
  have hra : APt.res π.op aU = APt.along j ch := by
    have e := res_specAlong T jh
    refine MonoidHom.ext fun p => ?_
    exact congrArg (fun z => z (AddMonoidHom.toMultiplicative (AddMonoidHom.inl _ _) p)) e
  have hrh : APt.res π.op hU = eh := by
    have e := res_specAlong T jh
    refine MonoidHom.ext fun p => ?_
    refine (congrArg (fun z => z (AddMonoidHom.toMultiplicative (AddMonoidHom.inr _ _) p)) e).trans ?_
    have e0 : jh (0, Multiplicative.toAdd p) = (0, Multiplicative.toAdd p) :=
      Prod.ext (map_zero j) rfl
    exact congrArg (fun q => specPt Pm T (Multiplicative.ofAdd q)) e0
  let sh : APt (fppfO B S hS) P (op (specObj Pm T)) := eh.comp (AddMonoidHom.toMultiplicative ν) * ch
  have hmag : APt.along j sh = APt.toMagnet K eh * APt.along j ch := by
    refine MonoidHom.ext fun p => ?_
    change eh (Multiplicative.ofAdd (ν (j (Multiplicative.toAdd p)))) * _ =
      eh (Multiplicative.ofAdd ((Multiplicative.toAdd p : K) : M)) * _
    rw [hν]
    rfl
  have huniv : X.map (specLift tQ (APt.toMagnet K hU * aU)).op x₀ =
      aX.smul hU (X.map (specLift tQ aU).op x₀) := by
    refine hD.uniq δh jh (Function.Injective.prodMap hj Function.injective_id) (fun p => ?_) T _ _ ?_
    · constructor
      · intro hp
        obtain ⟨k, hk'⟩ := (hk p.1).1 hp
        exact ⟨(k, p.2), Prod.ext hk' rfl⟩
      · rintro ⟨k, rfl⟩
        exact (hk _).2 ⟨k.1, rfl⟩
    · have e1 : π ≫ specLift tQ (APt.toMagnet K hU * aU) = specLift tm (APt.along j sh) := by
        rw [← specLift_comp, hπt, hmag, APt.res_mul, hra, ← APt.toMagnet_res, hrh]
      have e2 : π ≫ specLift tQ aU = specLift tm (APt.along j ch) := by
        rw [← specLift_comp, hπt, hra]
      change X.map π.op _ = X.map π.op _
      rw [aX.map_smul π.op hU, hrh, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
        ← op_comp, ← op_comp, e1, e2, lift, lift, hequi]
  have hequi₀ : ∀ {T' : BigFppfOver B S hS} (t : T' ⟶ T) (h : APt (fppfO B S hS) M (op T'))
      (a : APt (fppfO B S hS) K (op T')),
      X.map (specLift t (APt.toMagnet K h * a)).op x₀ = aX.smul h (X.map (specLift t a).op x₀) := by
    intro T' t h a
    let pt : APt (fppfO B S hS) P₂ (op T') :=
      APt.along (AddMonoidHom.fst _ _) a * APt.along (AddMonoidHom.snd _ _) h
    let ξ : T' ⟶ Q := specLift t pt
    have hξt : ξ ≫ tQ = t := specLift_pr t pt
    have hξa : APt.res ξ.op aU = a := by
      refine MonoidHom.ext fun p => ?_
      have e := res_specLift t pt
      refine (congrArg (fun z => z (AddMonoidHom.toMultiplicative (AddMonoidHom.inl _ _) p)) e).trans ?_
      change a p * h (Multiplicative.ofAdd 0) = a p
      have : h (Multiplicative.ofAdd (0 : M)) = 1 := map_one h
      rw [this, mul_one]
    have hξh : APt.res ξ.op hU = h := by
      refine MonoidHom.ext fun p => ?_
      have e := res_specLift t pt
      refine (congrArg (fun z => z (AddMonoidHom.toMultiplicative (AddMonoidHom.inr _ _) p)) e).trans ?_
      change a (Multiplicative.ofAdd 0) * h p = h p
      have : a (Multiplicative.ofAdd (0 : ↥K)) = 1 := map_one a
      rw [this, one_mul]
    have e4 : ξ ≫ specLift tQ (APt.toMagnet K hU * aU) = specLift t (APt.toMagnet K h * a) := by
      rw [← specLift_comp, hξt, APt.res_mul, hξa, ← APt.toMagnet_res, hξh]
    have e5 : ξ ≫ specLift tQ aU = specLift t a := by
      rw [← specLift_comp, hξt, hξa]
    have e1 := congrArg (X.map ξ.op) huniv
    rw [aX.map_smul ξ.op hU, hξh, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
      ← op_comp, ← op_comp, e4, e5] at e1
    exact e1
  let χ₀ : AttractorPt aX K T :=
    { app := fun t a => X.map (specLift t a).op x₀
      naturality := fun s t a => hmap s t a
      equivariant := fun t h a => hequi₀ t h a }
  refine ⟨χ₀, fun t c => lift t c, fun χ hχ => ?_⟩
  refine AttractorPt.ext ?_
  funext T' t a
  have e1 := χ.app_eq_of_universal (specUniversal K T) t a
  have e2 : χ.app (specPr _ T) (specPt _ T) = x₀ := by
    refine hD.uniq δ j hj hk T _ _ ?_
    rw [hx]
    have hn := χ.naturality (specAlong T j) (specPr _ T) (specPt _ T)
    rw [specAlong_pr, res_specAlong] at hn
    rw [← hn, hχ]
    have e5 : specLift (specPr P T) (specPt P T) = 𝟙 _ :=
      (specLift_uniq _ _ _ (Category.id_comp _) (by simp)).symm
    rw [e5]
    simp
  exact e1.trans (congrArg (X.map (specLift t a).op) e2)

end Core

section Glue

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}

/-- Bijectivity on affine objects, for a natural map of fppf sheaves, gives bijectivity. -/
theorem bijective_of_affine (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) F)
    (hG : Presieve.IsSheaf (BigFppfOver.topology B S hS) G) (φ : F ⟶ G)
    (h : ∀ (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)], Function.Bijective (φ.app (op T)))
    (T : BigFppfOver B S hS) : Function.Bijective (φ.app (op T)) := by
  have hnat : ∀ {a b : (BigFppfOver B S hS)ᵒᵖ} (f : a ⟶ b) (x : F.obj a),
      φ.app b (F.map f x) = G.map f (φ.app a x) := fun f x => NatTrans.naturality_apply φ f x
  have hinj : ∀ T : BigFppfOver B S hS, Function.Injective (φ.app (op T)) := by
    intro T x y e
    obtain ⟨I, V, π, hV, hcov⟩ := exists_affine_cover T
    refine (hF _ hcov).isSeparatedFor.ext ?_
    rintro W g ⟨W', a, b, ⟨i⟩, rfl⟩
    have := hV i
    have e' : F.map (π i).op x = F.map (π i).op y := by
      apply (h (V i)).1
      rw [hnat, hnat, e]
    rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, e']
  refine ⟨hinj T, fun z => ?_⟩
  obtain ⟨I, V, π, hV, hcov⟩ := exists_affine_cover T
  have key : ∀ {W : BigFppfOver B S hS} (g : W ⟶ T), (Sieve.ofArrows V π) g →
      ∃ χ : F.obj (op W), φ.app (op W) χ = G.map g.op z := by
    rintro W g ⟨W', a, b, ⟨i⟩, rfl⟩
    have := hV i
    obtain ⟨χ, hχ⟩ := (h (V i)).2 (G.map (π i).op z)
    refine ⟨F.map a.op χ, ?_⟩
    rw [hnat, hχ, op_comp, Functor.map_comp_apply]
  choose x hx using @key
  have hcomp : Presieve.FamilyOfElements.Compatible (P := F)
      (R := (Sieve.ofArrows V π).arrows) (fun _ g hg => x g hg) := by
    intro Y₁ Y₂ W g₁ g₂ f₁ f₂ h₁ h₂ comm
    apply hinj W
    rw [hnat, hnat, hx, hx,
      ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, comm]
  have hamal := (hF _ hcov).isAmalgamation hcomp
  refine ⟨(hF _ hcov).amalgamate _ hcomp, (hG _ hcov).isSeparatedFor.ext ?_⟩
  intro W g hg
  rw [← hnat, hamal g hg, hx]

end Glue

section P332

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M] {aX : AAction (fppfO B S hS) M X}
  {N L : AddSubmonoid M}

/-- The first coordinate of `N × L`. -/
def nuN (N L : AddSubmonoid M) : ↥(N.prod L) →+ M :=
  (AddMonoidHom.fst M M).comp (N.prod L).subtype

/-- **Proposition 3.32 (ii)** on affine `T`. -/
theorem existsUnique_toBi_affine (hD : DescentProp X) [Countable M] {T : BigFppfOver B S hS}
    [IsAffine ((SCH).obj T)] (φ : AttractorPt (biAct aX) (N.prod L) T) :
    ∃! χ : AttractorPt aX (N ⊓ L) T, χ.toBi (hKinf N L) = φ := by
  have hu : ∀ {T' : BigFppfOver B S hS} (t : T' ⟶ T) (c : APt (fppfO B S hS) ↥(N.prod L) (op T')),
      φ.app t c = X.map (specLift t c).op (φ.app (specPr _ T) (specPt _ T)) :=
    fun t c => φ.app_eq_of_universal (specUniversal (N.prod L) T) t c
  obtain ⟨χ, hχ, hun⟩ := existsUnique_chi (aX := aX) (K := N ⊓ L) hD (dlt N L) (jD N L) jD_inj dlt_eq_zero
    (nuN N L) (fun _ => rfl) (φ.app (specPr _ T) (specPt _ T))
    (by
      intro T' t g c
      rw [← hu, ← hu]
      let h : APt (fppfO B S hS) (M × M) (op T') :=
        g.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst M M - AddMonoidHom.snd M M))
      have ha : g.comp (AddMonoidHom.toMultiplicative (dlt N L)) * c = APt.toMagnet (N.prod L) h * c := rfl
      have hdiag : h.comp (AddMonoidHom.toMultiplicative (diagHom M)) = 1 := by
        refine MonoidHom.ext fun m => ?_
        have h0 : ((AddMonoidHom.fst M M - AddMonoidHom.snd M M) (diagHom M (Multiplicative.toAdd m))) = 0 :=
          sub_self _
        change g (Multiplicative.ofAdd ((AddMonoidHom.fst M M - AddMonoidHom.snd M M)
          (diagHom M (Multiplicative.toAdd m)))) = 1
        rw [h0]
        exact map_one g
      rw [ha]
      refine (φ.equivariant t h c).trans ?_
      change aX.smul (h.comp (AddMonoidHom.toMultiplicative (diagHom M))) _ = _
      rw [hdiag]
      exact aX.one_smul _)
    (by
      intro T' t e c
      rw [← hu, ← hu]
      exact φ.equivariant t (e.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst M M))) c)
  refine ⟨χ, ?_, fun χ' hχ' => hun χ' ?_⟩
  · refine AttractorPt.ext ?_
    funext T' t c
    exact (hχ t c).trans (hu t c).symm
  · intro T' t c
    rw [← hu, ← hχ']
    rfl

/-- The map `f ↦ F`, as a morphism of functors. -/
noncomputable def toBiHom (N L : AddSubmonoid M) (aX : AAction (fppfO B S hS) M X) :
    attractor aX (N ⊓ L) ⟶ attractor (biAct aX) (N.prod L) where
  app T := ↾ fun χ => AttractorPt.toBi (hKinf N L) χ
  naturality _ _ _ := rfl

/-- `f ↦ F` is bijective. -/
theorem toBi_bijective (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) X) (hD : DescentProp X)
    [Countable M] (T : BigFppfOver B S hS) :
    Function.Bijective (fun χ : AttractorPt aX (N ⊓ L) T => χ.toBi (hKinf N L)) :=
  bijective_of_affine (isSheaf_attractor aX (N ⊓ L) _ hF)
    (isSheaf_attractor (biAct aX) (N.prod L) _ hF) (toBiHom N L aX)
    (fun T _ => ⟨fun χ χ' h => (existsUnique_toBi_affine hD ((toBiHom N L aX).app (op T) χ)).unique rfl h.symm,
      fun φ => (existsUnique_toBi_affine hD φ).exists⟩) T

/-- **Proposition 3.32 (ii)** for a sheaf satisfying Lemma D: `(X^N)^L = X^{N ∩ L}`, any `S`, any `T`. -/
theorem prop332_of_descent (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) X) (hD : DescentProp X)
    [Countable M] (T : BigFppfOver B S hS) :
    Function.Bijective (iterOfInf : AttractorPt aX (N ⊓ L) T → IterPt aX N L T) := by
  have hb := toBi_bijective (aX := aX) (N := N) (L := L) hF hD T
  constructor
  · intro χ χ' h
    exact hb.1 ((iterEquivBi T).symm.injective h)
  · intro Ψ
    obtain ⟨χ, hχ⟩ := hb.2 Ψ.toBi
    refine ⟨χ, ?_⟩
    apply (iterEquivBi T).injective
    rw [iterOfInf, Equiv.apply_symm_apply]
    exact hχ

/-- **Proposition 3.32 (ii)** on points, the input of Proposition 15.1. -/
theorem exists_inf_of_descent (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) X) (hD : DescentProp X)
    [Countable M] (T : BigFppfOver B S hS) (φ : AttractorPt (biAct aX) (N.prod L) T) :
    ∃ χ : AttractorPt aX (N ⊓ L) T, χ.toPoint = φ.toPoint := by
  obtain ⟨χ, rfl⟩ := (toBi_bijective (aX := aX) (N := N) (L := L) hF hD T).2 φ
  exact ⟨χ, (AttractorPt.toPoint_toBi _ χ).symm⟩

end P332

section P331

variable {M Z : Type u} [AddCommGroup M] [AddCommGroup Z] [AddGroup.FG Z] {f : M →+ Z}
  {Y : AddSubmonoid Z} {aX : AAction (fppfO B S hS) M X}

/-- `G(c) = c|_M • ψ(c|_Y)`, the printed `(g, x) ↦ g • ψ(x)`. -/
noncomputable def gVal' {T : BigFppfOver B S hS} (ψ : AttractorPt (actAlong f aX) Y T)
    {T' : BigFppfOver B S hS} (t : T' ⟶ T) (c : APt (fppfO B S hS) (M × Y) (op T')) : X.obj (op T') :=
  aX.smul (APt.along (AddMonoidHom.inl M Y) c) (ψ.app t (APt.along (AddMonoidHom.inr M Y) c))

omit [AddGroup.FG Z] in
lemma gVal'_res {T : BigFppfOver B S hS} (ψ : AttractorPt (actAlong f aX) Y T)
    {T' T'' : BigFppfOver B S hS} (s : T'' ⟶ T') (t : T' ⟶ T) (c : APt (fppfO B S hS) (M × Y) (op T')) :
    gVal' ψ (s ≫ t) (APt.res s.op c) = X.map s.op (gVal' ψ t c) := by
  refine Eq.trans ?_ (aX.map_smul s.op _ _).symm
  exact congrArg (aX.smul _) (ψ.naturality s t (APt.along (AddMonoidHom.inr M Y) c))

/-- **Proposition 3.31 (ii)** on affine `T`. -/
theorem existsUnique_ptAlong_affine (hD : DescentProp X) [Countable M] [Countable Z] {T : BigFppfOver B S hS}
    [IsAffine ((SCH).obj T)] (ψ : AttractorPt (actAlong f aX) Y T) :
    ∃! φ : AttractorPt aX (Y.comap f) T, ptAlong aX φ = ψ := by
  let x := gVal' ψ (specPr (M × Y) T) (specPt _ T)
  have hu : ∀ {T' : BigFppfOver B S hS} (t : T' ⟶ T) (c : APt (fppfO B S hS) (M × Y) (op T')),
      X.map (specLift t c).op x = gVal' ψ t c := by
    intro T' t c
    have h := gVal'_res ψ (specLift t c) (specPr _ T) (specPt _ T)
    rw [specLift_pr, res_specLift] at h
    exact h.symm
  obtain ⟨φ, hφ, hun⟩ := existsUnique_chi (aX := aX) (K := Y.comap f) hD (dl f Y) (jn f Y) (jn_inj f Y)
    (dl_eq_zero f Y) (AddMonoidHom.fst M Y) (fun _ => rfl) x
    (by
      intro T' t e c
      rw [hu, hu]
      let k : APt (fppfO B S hS) M (op T') := e.comp (AddMonoidHom.toMultiplicative f)
      set a₁ := e.comp (AddMonoidHom.toMultiplicative (dl f Y)) * c with ha₁
      have hl : APt.along (AddMonoidHom.inl M Y) a₁ = k * APt.along (AddMonoidHom.inl M Y) c := by
        refine MonoidHom.ext fun m => ?_
        change e (Multiplicative.ofAdd (dl f Y (Multiplicative.toAdd m, 0))) * _ = _
        have : dl f Y (Multiplicative.toAdd m, 0) = f (Multiplicative.toAdd m) := by simp [dl]
        rw [this]
        rfl
      have hr : APt.along (AddMonoidHom.inr M Y) c =
          APt.toMagnet Y e * APt.along (AddMonoidHom.inr M Y) a₁ := by
        refine MonoidHom.ext fun y => ?_
        change _ = e (Multiplicative.ofAdd ((Multiplicative.toAdd y : Y) : Z)) *
          (e (Multiplicative.ofAdd (dl f Y (0, Multiplicative.toAdd y))) * _)
        have h0 : dl f Y (0, Multiplicative.toAdd y) = -((Multiplicative.toAdd y : Y) : Z) := by
          simp [dl]
        rw [h0, ← mul_assoc, ← map_mul, ← ofAdd_add, add_neg_cancel, ofAdd_zero, map_one, one_mul]
        rfl
      change aX.smul _ _ = aX.smul _ (ψ.app t _)
      rw [hl, hr, ψ.equivariant, mul_comm k]
      exact aX.mul_smul _ k _)
    (by
      intro T' t e c
      rw [hu, hu]
      have e1 : APt.along (AddMonoidHom.inl M Y) (e.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst M Y)) * c) =
          e * APt.along (AddMonoidHom.inl M Y) c := MonoidHom.ext fun p => rfl
      have e2 : APt.along (AddMonoidHom.inr M Y) (e.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst M Y)) * c) =
          APt.along (AddMonoidHom.inr M Y) c := by
        refine MonoidHom.ext fun y => ?_
        change e (Multiplicative.ofAdd 0) * _ = _
        have : e (Multiplicative.ofAdd (0 : M)) = 1 := map_one e
        rw [this, one_mul]
        rfl
      change aX.smul _ (ψ.app t _) = _
      rw [e1, e2, aX.mul_smul]
      rfl)
  refine ⟨φ, ?_, fun φ' hφ' => hun φ' ?_⟩
  · refine AttractorPt.ext ?_
    funext T' t a
    let c : APt (fppfO B S hS) (M × Y) (op T') := a.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd M Y))
    have e1 : APt.along (jn f Y) c = a.comp (AddMonoidHom.toMultiplicative (linMagnetHom f Y)) := rfl
    have e2 : APt.along (AddMonoidHom.inl M Y) c = 1 := MonoidHom.ext fun m => map_one a
    have e3 : APt.along (AddMonoidHom.inr M Y) c = a := MonoidHom.ext fun y => rfl
    change φ.app t (a.comp (AddMonoidHom.toMultiplicative (linMagnetHom f Y))) = ψ.app t a
    rw [← e1, hφ, hu, gVal', e2, e3, aX.one_smul]
  · intro T' t c
    rw [hu]
    have ec : APt.along (jn f Y) c = APt.toMagnet (Y.comap f) (APt.along (AddMonoidHom.inl M Y) c) *
        (APt.along (AddMonoidHom.inr M Y) c).comp (AddMonoidHom.toMultiplicative (linMagnetHom f Y)) := by
      refine MonoidHom.ext fun n => ?_
      change c _ = c _ * c _
      rw [← map_mul]
      refine congrArg c (congrArg Multiplicative.ofAdd (Prod.ext ?_ ?_))
      · exact (add_zero _).symm
      · exact (zero_add _).symm
    rw [ec, φ'.equivariant]
    have hψ : ∀ a, φ'.app t (a.comp (AddMonoidHom.toMultiplicative (linMagnetHom f Y))) = ψ.app t a := by
      intro a
      rw [← hφ']
      rfl
    rw [hψ]
    rfl

/-- The map `φ ↦ φ ∘ A(f)`, as a morphism of functors. -/
noncomputable def ptAlongHom (Y : AddSubmonoid Z) (f : M →+ Z) (aX : AAction (fppfO B S hS) M X) :
    attractor aX (Y.comap f) ⟶ attractor (actAlong f aX) Y where
  app T := ↾ fun φ => ptAlong aX φ
  naturality _ _ _ := rfl

/-- **Proposition 3.31 (ii)** for a sheaf satisfying Lemma D: `X^{f⁻¹(Y)} = X^Y`, any `S`, any `T`. -/
theorem prop331_of_descent (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) X) (hD : DescentProp X)
    [Countable M] [Countable Z] (T : BigFppfOver B S hS) :
    Function.Bijective (ptAlong aX : AttractorPt aX (Y.comap f) T → AttractorPt (actAlong f aX) Y T) :=
  bijective_of_affine (isSheaf_attractor aX (Y.comap f) _ hF) (isSheaf_attractor (actAlong f aX) Y _ hF)
    (ptAlongHom Y f aX)
    (fun T _ => ⟨fun χ χ' h => (existsUnique_ptAlong_affine hD ((ptAlongHom Y f aX).app (op T) χ)).unique rfl h.symm,
      fun φ => (existsUnique_ptAlong_affine hD φ).exists⟩) T

end P331

section P151

variable {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {aX : AAction (fppfO B S hS) M X}

/-- **Proposition 15.1**: `X` a separated algebraic space satisfying Lemma D, `M` a f.g. group. The hypothesis
`h332` of `AlgMag.Prop151.prop151_of_prop332` is discharged. -/
theorem prop151_of_descent (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X) (hD : DescentProp X)
    (N : AddSubmonoid M) :
    IsPure (attractorImage aX) N ↔ ∀ L, L < N → attractorImage aX L < attractorImage aX N := by
  have : AddGroup.FG M := AddGroup.fg_iff_addMonoid_fg.mpr inferInstance
  have : Countable M := countable_of_fg M
  exact Prop151.prop151_of_prop332 hX hsep N fun L {T} φ =>
    exists_inf_of_descent ((isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf) hD T φ

end P151

end AlgMag.SD

#print axioms AlgMag.SD.prop332_of_descent
#print axioms AlgMag.SD.prop331_of_descent
#print axioms AlgMag.SD.prop151_of_descent
