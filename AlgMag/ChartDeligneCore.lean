/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartStrata
import AlgMag.ChartDeligne
import AlgMag.ChartDeligneIdeal

/-!
# Lemma 4.3 of the chart-lemma proof: Deligne's formula on points, elementwise

No sheaf `ψ : J^N → O_X` is built. On the affine chart `φ : V → X`, `Gam f` is the set of pairs
`(j, s)` with `s = j f` over `U₀`; for `y : W → X`, the relation `Lift` is the `Γ(E)`-span of the
image of `Gam f` on the chart `E = W ×_X V`. The torsion in `ker(J^N ⊗ C → C)` of the note is
`graph_cross`, and the raising of `N` is the torsion exponent of the noetherian `V[M] ×_X V`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

universe u

namespace AlgMag.ChartMain.DeligneInst

/-! ### Commutative algebra -/

/-- A uniform exponent for `I`-power torsion on a noetherian ring. -/
lemma exists_tors_bound {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    ∃ b : ℕ, ∀ z : R, (∀ c ∈ I, ∃ n : ℕ, c ^ n * z = 0) → ∀ d ∈ I ^ b, d * z = 0 := by
  classical
  let Tors : Ideal R :=
    { carrier := {z | ∀ c ∈ I, ∃ n : ℕ, c ^ n * z = 0}
      zero_mem' := fun c _ => ⟨0, by simp⟩
      add_mem' := by
        intro x y hx hy c hc
        obtain ⟨n, hn⟩ := hx c hc
        obtain ⟨m, hm⟩ := hy c hc
        refine ⟨n + m, ?_⟩
        rw [mul_add, pow_add]
        linear_combination (c ^ m) * hn + (c ^ n) * hm
      smul_mem' := by
        intro r x hx c hc
        obtain ⟨n, hn⟩ := hx c hc
        refine ⟨n, ?_⟩
        rw [smul_eq_mul]
        linear_combination r * hn }
  have hle : I ≤ (Submodule.annihilator (Tors : Submodule R R)).radical := by
    intro c hc
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian Tors : Tors.FG)
    have hx : ∀ z ∈ s, ∃ n : ℕ, c ^ n * z = 0 := fun z hz => by
      have : z ∈ Tors := by rw [← hs]; exact Submodule.subset_span hz
      exact this c hc
    choose! N hN using hx
    refine ⟨s.sup N, ?_⟩
    rw [Submodule.mem_annihilator]
    intro z hz
    rw [← hs] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      have hle := Finset.le_sup (f := N) hz
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      rw [smul_eq_mul, hk, pow_add, mul_right_comm, hN z hz, zero_mul]
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
    | smul r x _ hx => rw [smul_comm, hx, smul_zero]
  obtain ⟨b, hb⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle (IsNoetherian.noetherian I)
  refine ⟨b, fun z hz d hd => ?_⟩
  have := hb hd
  rw [Submodule.mem_annihilator] at this
  exact this z hz

/-- Faithfully flat descent of an element. -/
lemma exists_of_tmul_eq {A D : Type*} [CommRing A] [CommRing D] [Algebra A D]
    [Module.FaithfullyFlat A D] (b : D)
    (h : (b ⊗ₜ[A] (1 : D) : TensorProduct A D D) = 1 ⊗ₜ[A] b) : ∃ a : A, algebraMap A D a = b := by
  let Q := D ⧸ (LinearMap.range (Algebra.linearMap A D))
  let π : D →ₗ[A] Q := Submodule.mkQ _
  have hinj := Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := D) Q
  have h1 : (TensorProduct.mk A D Q 1) (π b) = 0 := by
    have e := congrArg (TensorProduct.map (LinearMap.id : D →ₗ[A] D) π) h
    simp only [TensorProduct.map_tmul, LinearMap.id_apply] at e
    have e1 : π 1 = 0 := by
      apply (Submodule.Quotient.mk_eq_zero _).2
      exact ⟨1, map_one (algebraMap A D)⟩
    rw [e1, TensorProduct.tmul_zero] at e
    exact e.symm
  have h2 : π b = 0 := hinj (by rw [h1, map_zero])
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).1 h2
  exact ⟨a, ha⟩

/-! ### The chart data -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- The ring map of a morphism of the site. -/
noncomputable abbrev sec {A A' : BigFppfOver B S hS} (c : A ⟶ A') :
    Γ((BigFppfOver.toScheme B S hS).obj A', ⊤) →+* Γ((BigFppfOver.toScheme B S hS).obj A, ⊤) :=
  ((BigFppfOver.toScheme B S hS).map c).appTop.hom

lemma sec_comp {A A' A'' : BigFppfOver B S hS} (a : A ⟶ A') (b : A' ⟶ A'') (x) :
    (sec (a ≫ b)) x = (sec a) ((sec b) x) := by
  change ((SCH).map (a ≫ b)).appTop.hom x = _
  rw [Functor.map_comp, Scheme.Hom.comp_appTop]; rfl

/-- A chart of a point `τ` of `X` on an affine `Z`: an affine `E = Z ×_X V`. -/
structure ChartOf {V : BigFppfOver B S hS} (φ : yoneda.obj V ⟶ X) {Z : BigFppfOver B S hS}
    (τ : X.obj (op Z)) where
  E : BigFppfOver B S hS
  affine : IsAffine ((BigFppfOver.toScheme B S hS).obj E)
  e₁ : E ⟶ Z
  e₂ : E ⟶ V
  etale : ((SCH).map e₁).appTop.hom.Etale
  surj : Surjective ((SCH).map e₁)
  w : φ.app (op E) e₂ = X.map e₁.op τ
  lift : ∀ {W : BigFppfOver B S hS} (z : W ⟶ Z) (v : W ⟶ V), φ.app (op W) v = X.map z.op τ →
    ∃ l : W ⟶ E, l ≫ e₁ = z ∧ l ≫ e₂ = v

/-- What Lemma 4.3 needs of `X`, `U₀ ⊂ X`, the chart `V` and the ideal `J`. -/
structure Ctx (actX : AAction (fppfO B S hS) M X) {U₀ : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)] (actU : AAction (fppfO B S hS) M (yoneda.obj U₀))
    (fU : yoneda.obj U₀ ⟶ X) {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (φ : yoneda.obj V ⟶ X) where
  /-- `J·Γ(W)`, on an affine `W`. -/
  idl : ∀ {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)], X.obj (op W) → Ideal Γ((SCH).obj W, ⊤)
  idl_map : ∀ {W W' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] [IsAffine ((BigFppfOver.toScheme B S hS).obj W')]
    (q : W' ⟶ W) (y : X.obj (op W)), idl (X.map q.op y) = (idl y).map (sec q)
  idl_smul : ∀ {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (h : Multiplicative M →* Γ((SCH).obj W, ⊤)) (y : X.obj (op W)),
    idl (smX actX h y) = idl y
  /-- A point of `X` on an affine with `J = 1` lies in `U₀`. -/
  lift_U : ∀ {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] (y : X.obj (op W)), idl y = ⊤ →
    ∃ y₀ : W ⟶ U₀, fU.app (op W) y₀ = y
  equiv : IsEquivariant actU actX fU
  mono : ∀ W, Function.Injective (fU.app W)
  noethV : IsNoetherianRing Γ((SCH).obj V, ⊤)
  chart : ∀ {Z : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)] (τ : X.obj (op Z)),
    Nonempty (ChartOf φ τ)

variable {actX : AAction (fppfO B S hS) M X} {U₀ : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)] {actU : AAction (fppfO B S hS) M (yoneda.obj U₀)}
  {fU : yoneda.obj U₀ ⟶ X} {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  {φ : yoneda.obj V ⟶ X}

/-! ### The relation on the chart -/

variable (fU φ) in
/-- `(j, s)` with `s = j f` over `U₀`. -/
def Gam (f : Γ((SCH).obj U₀, ⊤)) : Submodule Γ((SCH).obj V, ⊤) (Γ((SCH).obj V, ⊤) × Γ((SCH).obj V, ⊤)) where
  carrier := {p | ∀ ⦃W : BigFppfOver B S hS⦄ (c : W ⟶ V) (y₀ : W ⟶ U₀),
    φ.app (op W) c = fU.app (op W) y₀ → (sec c) p.2 = (sec c) p.1 * (sec y₀) f}
  zero_mem' := fun W c y₀ _ => by simp
  add_mem' := fun {p p'} hp hp' W c y₀ h => by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    rw [hp c y₀ h, hp' c y₀ h]; ring
  smul_mem' := fun r p hp W c y₀ h => by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_mul]
    rw [hp c y₀ h]; ring

variable (fU φ) in
/-- The span of `Gam f` along `c : A → V`. -/
def Graph {A : BigFppfOver B S hS} (c : A ⟶ V) (f : Γ((SCH).obj U₀, ⊤)) :
    Submodule Γ((SCH).obj A, ⊤) (Γ((SCH).obj A, ⊤) × Γ((SCH).obj A, ⊤)) :=
  Submodule.span _ ((fun p => ((sec c) p.1, (sec c) p.2)) '' {p | p ∈ Gam fU φ f})

lemma graph_map {A A' : BigFppfOver B S hS} (e : A' ⟶ A) (c : A ⟶ V) (f) {p}
    (hp : p ∈ Graph fU φ c f) : ((sec e) p.1, (sec e) p.2) ∈ Graph fU φ (e ≫ c) f := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨q, hq, rfl⟩ := hp
    refine Submodule.subset_span ⟨q, hq, ?_⟩
    simp only [sec_comp]
  | zero =>
    simp only [Prod.fst_zero, Prod.snd_zero, map_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    simpa using add_mem hx hy
  | smul r x _ hx =>
    have := Submodule.smul_mem _ ((sec e) r) hx
    simpa [Prod.smul_def] using this

/-- `Gam` is closed under the operations. -/
lemma gam_mul {f f'} {p p'} (hp : p ∈ Gam fU φ f) (hp' : p' ∈ Gam fU φ f') :
    (p.1 * p'.1, p.2 * p'.2) ∈ Gam fU φ (f * f') := fun W c y₀ h => by
  simp only [map_mul]
  rw [hp c y₀ h, hp' c y₀ h]; ring

lemma gam_add {f f'} {p p'} (hp : p ∈ Gam fU φ f) (hp' : p' ∈ Gam fU φ f') :
    (p.1 * p'.1, p.2 * p'.1 + p.1 * p'.2) ∈ Gam fU φ (f + f') := fun W c y₀ h => by
  simp only [map_mul, map_add]
  rw [hp c y₀ h, hp' c y₀ h]; ring

/-- A bilinear operation on `Graph`, from the generators. -/
lemma graph_bilin {A : BigFppfOver B S hS} (c : A ⟶ V) {f f' f''}
    (Φ : Γ((SCH).obj A, ⊤) × Γ((SCH).obj A, ⊤) → Γ((SCH).obj A, ⊤) × Γ((SCH).obj A, ⊤) →
      Γ((SCH).obj A, ⊤) × Γ((SCH).obj A, ⊤))
    (hadd : ∀ x y z, Φ (x + y) z = Φ x z + Φ y z) (hadd' : ∀ x y z, Φ x (y + z) = Φ x y + Φ x z)
    (hsm : ∀ (r : Γ((SCH).obj A, ⊤)) x z, Φ (r • x) z = r • Φ x z)
    (hsm' : ∀ (r : Γ((SCH).obj A, ⊤)) x z, Φ x (r • z) = r • Φ x z)
    (hgen : ∀ q ∈ Gam fU φ f, ∀ q' ∈ Gam fU φ f',
      Φ ((sec c) q.1, (sec c) q.2) ((sec c) q'.1, (sec c) q'.2) ∈ Graph fU φ c f'')
    {p p'} (hp : p ∈ Graph fU φ c f) (hp' : p' ∈ Graph fU φ c f') : Φ p p' ∈ Graph fU φ c f'' := by
  have h0 : ∀ x, Φ 0 x = 0 := fun x => by
    have := hsm 0 0 x; simpa using this
  have h0' : ∀ x, Φ x 0 = 0 := fun x => by
    have := hsm' 0 x 0; simpa using this
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨q, hq, rfl⟩ := hp
    induction hp' using Submodule.span_induction with
    | mem p' hp' =>
      obtain ⟨q', hq', rfl⟩ := hp'
      exact hgen q hq q' hq'
    | zero => rw [h0']; exact zero_mem _
    | add x y _ _ hx hy => rw [hadd']; exact add_mem hx hy
    | smul r x _ hx => rw [hsm']; exact Submodule.smul_mem _ r hx
  | zero => rw [h0]; exact zero_mem _
  | add x y _ _ hx hy => rw [hadd]; exact add_mem hx hy
  | smul r x _ hx => rw [hsm]; exact Submodule.smul_mem _ r hx

lemma graph_mul {A : BigFppfOver B S hS} (c : A ⟶ V) {f f'} {p p'}
    (hp : p ∈ Graph fU φ c f) (hp' : p' ∈ Graph fU φ c f') :
    (p.1 * p'.1, p.2 * p'.2) ∈ Graph fU φ c (f * f') := by
  refine graph_bilin c (fun x y => (x.1 * y.1, x.2 * y.2)) ?_ ?_ ?_ ?_ ?_ hp hp'
  · intro x y z; ext <;> simp [add_mul]
  · intro x y z; ext <;> simp [mul_add]
  · intro r x z; ext <;> simp [mul_assoc]
  · intro r x z; ext <;> simp [mul_left_comm]
  · intro q hq q' hq'
    exact Submodule.subset_span ⟨_, gam_mul hq hq', by simp⟩

lemma graph_add {A : BigFppfOver B S hS} (c : A ⟶ V) {f f'} {p p'}
    (hp : p ∈ Graph fU φ c f) (hp' : p' ∈ Graph fU φ c f') :
    (p.1 * p'.1, p.2 * p'.1 + p.1 * p'.2) ∈ Graph fU φ c (f + f') := by
  refine graph_bilin c (fun x y => (x.1 * y.1, x.2 * y.1 + x.1 * y.2)) ?_ ?_ ?_ ?_ ?_ hp hp'
  · intro x y z; ext <;> simp <;> ring
  · intro x y z; ext <;> simp <;> ring
  · intro r x z; ext <;> simp <;> ring
  · intro r x z; ext <;> simp <;> ring
  · intro q hq q' hq'
    exact Submodule.subset_span ⟨_, gam_add hq hq', by simp⟩

/-! ### The cross relation -/

section Cross

variable (C : Ctx actX actU fU φ)

variable (fU) in
/-- `z` vanishes over `U₀`, for the point `ρ` of `X` on `E`. -/
def Van {E : BigFppfOver B S hS} (ρ : X.obj (op E)) (z : Γ((SCH).obj E, ⊤)) : Prop :=
  ∀ ⦃W : BigFppfOver B S hS⦄ (c : W ⟶ E) (y₀ : W ⟶ U₀), X.map c.op ρ = fU.app (op W) y₀ → (sec c) z = 0

/-- On `D(g)`, `g` is a unit. -/
lemma isUnit_immι_basicOpen (E : BigFppfOver B S hS) (g : Γ((SCH).obj E, ⊤)) :
    IsUnit ((sec (Chart.immι E (((SCH).obj E).basicOpen g).ι)) g) := by
  let Y := (SCH).obj E
  have h := RingedSpace.isUnit_res_basicOpen Y.toRingedSpace (U := ⊤) g
  change IsUnit ((Y.basicOpen g).ι.appTop g)
  have hle : (Y.basicOpen g).ι ''ᵁ ⊤ ≤ Y.basicOpen g := by simp
  have e : (Y.basicOpen g).ι.appTop g =
      Y.presheaf.map hle.hom.op (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op g) := by
    rw [Scheme.Opens.ι_appTop, ← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  rw [e]
  exact h.map _

/-- A section vanishing on `D(g)` is killed by a power of `g`. -/
lemma exists_pow_of_immι_eq_zero (E : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj E)]
    (g z : Γ((SCH).obj E, ⊤)) (h : (sec (Chart.immι E (((SCH).obj E).basicOpen g).ι)) z = 0) :
    ∃ n : ℕ, g ^ n * z = 0 := Chart.basicOpen_ι_appTop_eq_zero g z h

include C in
/-- A section vanishing over `U₀` is `J`-power torsion. -/
lemma van_torsion {E : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj E)] {ρ : X.obj (op E)} {z}
    (hz : Van fU ρ z) (g) (hg : g ∈ C.idl ρ) : ∃ n : ℕ, g ^ n * z = 0 := by
  let W := Chart.immObj E (((SCH).obj E).basicOpen g).ι
  let i : W ⟶ E := Chart.immι E (((SCH).obj E).basicOpen g).ι
  haveI hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W) :=
    (isAffineOpen_top ((SCH).obj E) |>.basicOpen g : IsAffineOpen _)
  have hi : (sec i) g ∈ C.idl (X.map i.op ρ) := by
    rw [C.idl_map]; exact Ideal.mem_map_of_mem _ hg
  obtain ⟨y₀, hy₀⟩ := C.lift_U (X.map i.op ρ) (Ideal.eq_top_of_isUnit_mem _ hi (isUnit_immι_basicOpen E g))
  exact exists_pow_of_immι_eq_zero E g z (hz i y₀ hy₀.symm)

/-- A uniform torsion exponent on a noetherian affine. -/
lemma exists_van_bound {E : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj E)]
    [IsNoetherianRing Γ((SCH).obj E, ⊤)] (ρ : X.obj (op E)) :
    ∃ b : ℕ, ∀ z, Van fU ρ z → ∀ d ∈ C.idl ρ ^ b, d * z = 0 := by
  obtain ⟨b, hb⟩ := exists_tors_bound (C.idl ρ)
  exact ⟨b, fun z hz d hd => hb z (fun g hg => van_torsion C hz g hg) d hd⟩

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)] [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
lemma map_yoneda_app {A A' : BigFppfOver B S hS} (e : A' ⟶ A) (c : A ⟶ V) :
    φ.app (op A') (e ≫ c) = X.map e.op (φ.app (op A) c) :=
  NatTrans.naturality_apply φ e.op c

/-- The relation on a universal `E` with `c₂ = κ • c₁`. -/
lemma van_cross {E : BigFppfOver B S hS} (c₁ c₂ : E ⟶ V) (κ : Γ((SCH).obj E, ⊤)) {f}
    (hκ : ∀ ⦃W : BigFppfOver B S hS⦄ (c : W ⟶ E) (y₀ : W ⟶ U₀),
      φ.app (op W) (c ≫ c₁) = fU.app (op W) y₀ →
      ∃ y₁ : W ⟶ U₀, φ.app (op W) (c ≫ c₂) = fU.app (op W) y₁ ∧
        (sec y₁) f = (sec c) κ * (sec y₀) f) {p p'}
    (hp : p ∈ Gam fU φ f) (hp' : p' ∈ Gam fU φ f) :
    Van fU (φ.app (op E) c₁) ((sec c₁) p.1 * (sec c₂) p'.2 - κ * (sec c₂) p'.1 * (sec c₁) p.2) := by
  intro W c y₀ h
  rw [← map_yoneda_app] at h
  obtain ⟨y₁, h₁, h₂⟩ := hκ c y₀ h
  have e1 := hp (c ≫ c₁) y₀ h
  have e2 := hp' (c ≫ c₂) y₁ h₁
  rw [sec_comp, sec_comp] at e1 e2
  simp only [map_sub, map_mul]
  rw [e1, e2, h₂]
  ring

include C in
/-- Pull back the relation along `a : A → E`, for elements of the graphs. -/
lemma graph_cross_of {E A : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj E)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj A)] (c₁ c₂ : E ⟶ V) (κ : Γ((SCH).obj E, ⊤)) {f}
    (b : ℕ) (hb : ∀ z, Van fU (φ.app (op E) c₁) z → ∀ d ∈ C.idl (φ.app (op E) c₁) ^ b, d * z = 0)
    (hκ : ∀ ⦃W : BigFppfOver B S hS⦄ (c : W ⟶ E) (y₀ : W ⟶ U₀),
      φ.app (op W) (c ≫ c₁) = fU.app (op W) y₀ →
      ∃ y₁ : W ⟶ U₀, φ.app (op W) (c ≫ c₂) = fU.app (op W) y₁ ∧
        (sec y₁) f = (sec c) κ * (sec y₀) f)
    (a : A ⟶ E) {p p'} (hp : p ∈ Graph fU φ (a ≫ c₁) f) (hp' : p' ∈ Graph fU φ (a ≫ c₂) f)
    (d) (hd : d ∈ C.idl (φ.app (op A) (a ≫ c₁)) ^ b) :
    d * (p.1 * p'.2 - (sec a) κ * p'.1 * p.2) = 0 := by
  have hbase : ∀ q ∈ Gam fU φ f, ∀ q' ∈ Gam fU φ f,
      d * ((sec (a ≫ c₁)) q.1 * (sec (a ≫ c₂)) q'.2 - (sec a) κ * (sec (a ≫ c₂)) q'.1 *
        (sec (a ≫ c₁)) q.2) = 0 := by
    intro q hq q' hq'
    have hz := van_cross c₁ c₂ κ hκ hq hq'
    have hk := hb _ hz
    rw [map_yoneda_app, C.idl_map, ← Ideal.map_pow] at hd
    simp only [sec_comp, ← map_mul, ← map_sub]
    induction hd using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨d0, hd0, rfl⟩ := hx
      rw [← map_mul, hk d0 hd0, map_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul, hx, hy, add_zero]
    | smul r x _ hx => rw [smul_eq_mul, mul_assoc, hx, mul_zero]
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, hq, rfl⟩ := hx
    induction hp' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q', hq', rfl⟩ := hx
      exact hbase q hq q' hq'
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Prod.fst_add, Prod.snd_add]
      linear_combination hx + hy
    | smul r x _ hx =>
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      linear_combination r * hx
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Prod.fst_add, Prod.snd_add]
    linear_combination hx + hy
  | smul r x _ hx =>
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination r * hx

include C in
/-- A chart of a noetherian affine is noetherian. -/
lemma noeth_chart {Z : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)]
    [IsNoetherianRing Γ((SCH).obj Z, ⊤)] {τ : X.obj (op Z)} (c : ChartOf φ τ) :
    IsNoetherianRing Γ((SCH).obj c.E, ⊤) := by
  have h := c.etale
  letI := ((SCH).map c.e₁).appTop.hom.toAlgebra
  haveI : Algebra.Etale Γ((SCH).obj Z, ⊤) Γ((SCH).obj c.E, ⊤) := h
  exact Algebra.FiniteType.isNoetherianRing Γ((SCH).obj Z, ⊤) _

include C in
/-- `V[M]` is noetherian. -/
lemma noeth_gm : IsNoetherianRing Γ((SCH).obj (gmObj (M := M) V), ⊤) := by
  haveI := C.noethV
  have : Algebra.FiniteType (RT V) (R1 V M) := inferInstance
  haveI : IsNoetherianRing (R1 V M) := Algebra.FiniteType.isNoetherianRing (RT V) _
  exact isNoetherianRing_of_ringEquiv _
    (RingEquiv.ofBijective _ (spSec_bijective V (ι1 V (M := M)) contains1))

/-- **The cross relation**: the exponent `b` and the two relations, on `V ×_X V` and `V[M] ×_X V`. -/
theorem exists_cross : ∃ b : ℕ,
    (∀ {A : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj A)] (c₁ c₂ : A ⟶ V),
      φ.app (op A) c₂ = φ.app (op A) c₁ → ∀ {f p p'}, p ∈ Graph fU φ c₁ f → p' ∈ Graph fU φ c₂ f →
      ∀ d ∈ C.idl (φ.app (op A) c₁) ^ b, d * (p.1 * p'.2 - p'.1 * p.2) = 0) ∧
    (∀ {A : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj A)] (c₁ c₂ : A ⟶ V)
      (h : Multiplicative M →* Γ((SCH).obj A, ⊤)),
      φ.app (op A) c₂ = smX actX h (φ.app (op A) c₁) → ∀ {D f p p'}, f ∈ homog actU D →
      p ∈ Graph fU φ c₁ f → p' ∈ Graph fU φ c₂ f →
      ∀ d ∈ C.idl (φ.app (op A) c₁) ^ b,
        d * (p.1 * p'.2 - h (Multiplicative.ofAdd D) * p'.1 * p.2) = 0) := by
  classical
  haveI := C.noethV
  haveI := noeth_gm (M := M) C
  let pt : X.obj (op V) := yonedaEquiv φ
  -- `V ×_X V`
  obtain ⟨R⟩ := C.chart pt
  haveI := R.affine
  haveI := noeth_chart C R
  have hR : φ.app (op R.E) R.e₂ = φ.app (op R.E) R.e₁ := by
    rw [R.w, map_yonedaEquiv]
  obtain ⟨b₁, hb₁⟩ := exists_van_bound C (φ.app (op R.E) R.e₁)
  -- `V[M] ×_X V`
  obtain ⟨Q⟩ := C.chart (univX actX pt)
  haveI := Q.affine
  haveI := noeth_chart C Q
  obtain ⟨b₂, hb₂⟩ := exists_van_bound C (φ.app (op Q.E) (Q.e₁ ≫ gmπ (M := M) V))
  refine ⟨max b₁ b₂, ?_, ?_⟩
  · intro A _ c₁ c₂ hw f p p' hp hp' d hd
    obtain ⟨a, ha₁, ha₂⟩ := R.lift c₁ c₂ (by rw [hw, map_yonedaEquiv])
    subst ha₁ ha₂
    have hd' : d ∈ C.idl (φ.app (op A) (a ≫ R.e₁)) ^ b₁ :=
      Ideal.pow_le_pow_right (le_max_left _ _) hd
    have := graph_cross_of C R.e₁ R.e₂ 1 (f := f) b₁ hb₁ (fun W c y₀ h => ⟨y₀, ?_, by simp⟩) a hp hp' d hd'
    · simpa using this
    · rw [map_yoneda_app, hR, ← map_yoneda_app]; exact h
  · intro A _ c₁ c₂ h hw D f p p' hf hp hp' d hd
    let π := gmπ (M := M) V
    let χ : Multiplicative M →* Γ((SCH).obj Q.E, ⊤) := secPt (sec Q.e₁) (univPt1 (U := V))
    have hψ : (evalAt (sec c₁) h).comp (ι1 V (M := M)) = sec c₁ :=
      RingHom.ext fun b => evalAt_ι _ _ b
    obtain ⟨τ, hτ₁, hτ₂⟩ := exists_spLift (ι1 V (M := M)) contains1 c₁ _ hψ
    have hres : secPt (sec τ) (univPt1 (U := V)) = h := MonoidHom.ext fun m => by
      refine (hτ₂ _).trans ?_
      refine (evalAt_single _ _ (Multiplicative.toAdd m) 1).trans ?_
      rw [map_one, one_mul]
      rfl
    have huniv : X.map τ.op (univX actX pt) = φ.app (op A) c₂ := by
      rw [hw]
      unfold univX
      rw [smX_map, hres, ← Functor.map_comp_apply, ← op_comp]
      change smX actX h (X.map (τ ≫ spToT V (ι1 V (M := M)) contains1).op pt) = _
      rw [hτ₁, map_yonedaEquiv]
    obtain ⟨a, ha₁, ha₂⟩ := Q.lift τ c₂ huniv.symm
    have hac₁ : a ≫ Q.e₁ ≫ π = c₁ := by
      rw [← Category.assoc, ha₁]; exact hτ₁
    have hκ : (sec a) (χ (Multiplicative.ofAdd D)) = h (Multiplicative.ofAdd D) := by
      rw [← hres]
      change (sec a) ((sec Q.e₁) _) = (sec τ) _
      rw [← sec_comp, ha₁]
    have hd' : d ∈ C.idl (φ.app (op A) (a ≫ Q.e₁ ≫ π)) ^ b₂ := by
      rw [hac₁]; exact Ideal.pow_le_pow_right (le_max_right _ _) hd
    subst ha₂
    subst hac₁
    have := graph_cross_of C (Q.e₁ ≫ π) Q.e₂ (χ (Multiplicative.ofAdd D)) (f := f) b₂ hb₂
      (fun W c y₀ hy => ?_) a hp hp' d hd'
    · rwa [hκ] at this
    · let χ' := secPt (sec c) χ
      refine ⟨smulAt actU χ' y₀, ?_, ?_⟩
      · have e0 : φ.app (op Q.E) Q.e₂ = smX actX χ (φ.app (op Q.E) (Q.e₁ ≫ π)) := by
          rw [Q.w, map_yoneda_app]
          unfold univX
          rw [smX_map, ← map_yonedaEquiv]
        rw [map_yoneda_app, e0, smX_map, ← map_yoneda_app, hy]
        exact (C.equiv (T := op W) χ' y₀).symm
      · rw [appTop_smul_of_mem actU y₀ χ' hf, mul_comm]
        rfl

end Cross

/-! ### The pole bound -/

section Pole

variable (C : Ctx actX actU fU φ)

/-- A section over `D(g)` is `a / g^N`. -/
lemma exists_pow_mul_immι (E : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj E)]
    (g : Γ((SCH).obj E, ⊤))
    (F : Γ((SCH).obj (Chart.immObj E (((SCH).obj E).basicOpen g).ι), ⊤)) :
    ∃ (N : ℕ) (a : Γ((SCH).obj E, ⊤)),
      (sec (Chart.immι E (((SCH).obj E).basicOpen g).ι)) a =
        (sec (Chart.immι E (((SCH).obj E).basicOpen g).ι)) g ^ N * F := by
  let Y := (SCH).obj E
  let F' : Γ(Y, Y.basicOpen g) := (Y.basicOpen g).topIso.hom F
  obtain ⟨N, a, ha⟩ := exists_eq_pow_mul_of_isAffineOpen Y ⊤ (isAffineOpen_top Y) g F'
  refine ⟨N, a, ?_⟩
  have hT : Function.Injective (Y.basicOpen g).topIso.hom.hom :=
    (ConcreteCategory.bijective_of_isIso (Y.basicOpen g).topIso.hom).1
  have key : ∀ x : Γ(Y, ⊤), (Y.basicOpen g).topIso.hom ((Y.basicOpen g).ι.appTop x) =
      Y.presheaf.map (homOfLE (le_top : Y.basicOpen g ≤ ⊤)).op x := by
    intro x
    simp [Scheme.Opens.topIso]
    change (Y.presheaf.map _) ((Y.presheaf.map _) x) = _
    rw [← CommRingCat.comp_apply]
    exact ConcreteCategory.congr_hom (Y.presheaf.map_comp _ _).symm x
  apply hT
  let F₀ : Γ((Y.basicOpen g : Scheme.{u}), ⊤) := F
  change (Y.basicOpen g).topIso.hom ((Y.basicOpen g).ι.appTop a) =
    (Y.basicOpen g).topIso.hom ((Y.basicOpen g).ι.appTop g ^ N * F₀)
  rw [key, map_mul, map_pow, key]
  exact ha

include C in
/-- For `g ∈ J`, `(g^N, a) ∈ Gam f`. -/
lemma exists_gam_pow (f) (g) (hg : g ∈ C.idl (yonedaEquiv φ)) :
    ∃ (N : ℕ) (a : Γ((SCH).obj V, ⊤)), (g ^ N, a) ∈ Gam fU φ f := by
  let W := Chart.immObj V (((SCH).obj V).basicOpen g).ι
  let i : W ⟶ V := Chart.immι V (((SCH).obj V).basicOpen g).ι
  haveI hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W) :=
    (isAffineOpen_top ((SCH).obj V) |>.basicOpen g : IsAffineOpen _)
  have hi : (sec i) g ∈ C.idl (X.map i.op (yonedaEquiv φ)) := by
    rw [C.idl_map]; exact Ideal.mem_map_of_mem _ hg
  obtain ⟨y₀, hy₀⟩ := C.lift_U (X.map i.op (yonedaEquiv φ))
    (Ideal.eq_top_of_isUnit_mem _ hi (isUnit_immι_basicOpen V g))
  obtain ⟨N, a₀, ha₀⟩ := exists_pow_mul_immι V g ((sec y₀) f)
  obtain ⟨Eu⟩ := C.chart (fU.app (op U₀) (𝟙 U₀))
  haveI := Eu.affine
  have hfu : ∀ {W' : BigFppfOver B S hS} (z : W' ⟶ U₀),
      fU.app (op W') z = X.map z.op (fU.app (op U₀) (𝟙 U₀)) := fun {W'} z => by
    have := NatTrans.naturality_apply fU z.op (𝟙 U₀)
    simpa using this
  -- `δ` on `Eu = U₀ ×_X V`
  let e := Eu.e₂
  let δ : Γ((SCH).obj Eu.E, ⊤) := (sec e) a₀ - (sec e) g ^ N * (sec Eu.e₁) f
  let Y := (SCH).obj Eu.E
  let D := Chart.immObj Eu.E (Y.basicOpen ((sec e) g)).ι
  let ι : D ⟶ Eu.E := Chart.immι Eu.E (Y.basicOpen ((sec e) g)).ι
  haveI : IsOpenImmersion ((SCH).map i) := inferInstanceAs (IsOpenImmersion (((SCH).obj V).basicOpen g).ι)
  have hD : ∃ s : D ⟶ W, s ≫ i = ι ≫ e := by
    refine exists_factor_open i (ι ≫ e) ?_
    rintro _ ⟨y, rfl⟩
    have hm := mem_basicOpen_of_range ((SCH).map e) g (Y.basicOpen ((sec e) g)).ι
      (by rw [Scheme.Opens.range_ι]) y
    refine ⟨⟨_, hm⟩, ?_⟩
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
    rfl
  obtain ⟨s, hs⟩ := hD
  have hsy : ι ≫ Eu.e₁ = s ≫ y₀ := by
    apply C.mono (op D)
    have h1 : fU.app (op D) (ι ≫ Eu.e₁) = φ.app (op D) (ι ≫ e) := by
      rw [map_yoneda_app ι e, show φ.app (op Eu.E) e = _ from Eu.w, hfu, op_comp, Functor.map_comp_apply]
    rw [h1, ← hs, map_yoneda_app s i, map_yoneda_app (φ := fU) s y₀, hy₀, map_yonedaEquiv]
  have hδ : (sec ι) δ = 0 := by
    simp only [δ, map_sub, map_mul, map_pow]
    rw [← sec_comp, ← sec_comp, ← sec_comp, ← hs, hsy, sec_comp, sec_comp, sec_comp, ha₀]
    simp only [map_mul, map_pow]
    exact sub_self _
  obtain ⟨N', hN'⟩ := exists_pow_of_immι_eq_zero Eu.E ((sec e) g) δ hδ
  refine ⟨N + N', g ^ N' * a₀, ?_⟩
  intro W₁ c y₁ hc
  obtain ⟨l, hl₁, hl₂⟩ := Eu.lift y₁ c (by rw [hc, hfu])
  have := congrArg (sec l) hN'
  simp only [δ, map_mul, map_pow, map_sub, map_zero] at this
  simp only [← sec_comp] at this
  rw [hl₁, show l ≫ e = c from hl₂] at this
  simp only [map_mul, map_pow]
  rw [pow_add]
  linear_combination this

include C in
/-- **The pole bound.** -/
theorem exists_pole (f) : ∃ e : ℕ, ∀ j ∈ C.idl (yonedaEquiv φ) ^ e, ∃ s, (j, s) ∈ Gam fU φ f := by
  haveI := C.noethV
  let I : Ideal Γ((SCH).obj V, ⊤) := (Gam fU φ f).map (LinearMap.fst _ _ _)
  have hle : C.idl (yonedaEquiv φ) ≤ I.radical := by
    intro g hg
    obtain ⟨N, a, ha⟩ := exists_gam_pow C f g hg
    exact ⟨N, ⟨_, ha, rfl⟩⟩
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle (IsNoetherian.noetherian _)
  refine ⟨e, fun j hj => ?_⟩
  obtain ⟨p, hp, rfl⟩ := he hj
  exact ⟨p.2, hp⟩

end Pole

/-! ### The relation `Lift` on points -/

section LiftSec

variable (C : Ctx actX actU fU φ)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
/-- The ring map of a chart is faithfully flat. -/
lemma ChartOf.faithfullyFlat {Z : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)]
    {τ : X.obj (op Z)} (c : ChartOf φ τ) : ((SCH).map c.e₁).appTop.hom.FaithfullyFlat := by
  haveI := c.affine
  haveI := c.surj
  have hE : AlgebraicGeometry.Etale ((SCH).map c.e₁) :=
    (HasRingHomProperty.iff_of_isAffine (P := @AlgebraicGeometry.Etale)).2 c.etale
  exact faithfullyFlat_appTop ((SCH).map c.e₁)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
lemma ChartOf.injective {Z : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)]
    {τ : X.obj (op Z)} (c : ChartOf φ τ) : Function.Injective (sec c.e₁) := by
  letI := ((SCH).map c.e₁).appTop.hom.toAlgebra
  haveI : Module.FaithfullyFlat Γ((SCH).obj Z, ⊤) Γ((SCH).obj c.E, ⊤) :=
    RingHom.faithfullyFlat_algebraMap_iff.1 c.faithfullyFlat
  exact FaithfulSMul.algebraMap_injective _ _

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
/-- **Descent of elements** along a chart. -/
lemma ChartOf.descend {Z : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)]
    {τ : X.obj (op Z)} (c : ChartOf φ τ) (b : Γ((SCH).obj c.E, ⊤))
    (hb : ∀ {A : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj A)]
      (p₁ p₂ : A ⟶ c.E), p₁ ≫ c.e₁ = p₂ ≫ c.e₁ → (sec p₁) b = (sec p₂) b) :
    ∃ a, (sec c.e₁) a = b := by
  haveI := c.affine
  have : HasPullbacks (BigFppfOver B S hS) := hasPullbacks_bigFppfOver B S hS
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    preservesPullbacks_bigFppfOverToScheme B S hS
  let G := BigFppfOver.toScheme B S hS
  have hP : IsPullback (G.map (pullback.fst c.e₁ c.e₁)) (G.map (pullback.snd c.e₁ c.e₁))
      (G.map c.e₁) (G.map c.e₁) := (IsPullback.of_hasPullback _ _).map _
  have hA : IsAffine (G.obj (pullback c.e₁ c.e₁)) := by
    have h1 : IsAffineHom (G.map c.e₁) := isAffineHom_of_isAffine _
    have h2 : IsAffineHom (G.map (pullback.fst c.e₁ c.e₁)) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) hP.flip h1
    exact isAffine_of_isAffineHom (G.map (pullback.fst c.e₁ c.e₁))
  have hpush : IsPushout (G.map c.e₁).appTop (G.map c.e₁).appTop
      (G.map (pullback.fst c.e₁ c.e₁)).appTop (G.map (pullback.snd c.e₁ c.e₁)).appTop :=
    isPushout_appTop_of_isPullback hP
  letI := (G.map c.e₁).appTop.hom.toAlgebra
  haveI : Module.FaithfullyFlat Γ(G.obj Z, ⊤) Γ(G.obj c.E, ⊤) :=
    RingHom.faithfullyFlat_algebraMap_iff.1 c.faithfullyFlat
  obtain ⟨eQ, heQl, heQr⟩ := exists_ringEquiv_tensor (R := Γ(G.obj Z, ⊤))
    (C := Γ(G.obj c.E, ⊤)) (D := Γ(G.obj c.E, ⊤))
    (G.map (pullback.fst c.e₁ c.e₁)).appTop.hom (G.map (pullback.snd c.e₁ c.e₁)).appTop.hom hpush
  have h := hb (pullback.fst c.e₁ c.e₁) (pullback.snd c.e₁ c.e₁) pullback.condition
  have h2 : (b ⊗ₜ[Γ(G.obj Z, ⊤)] (1 : Γ(G.obj c.E, ⊤)) : TensorProduct _ _ _) = 1 ⊗ₜ b := by
    rw [← heQl, ← heQr]
    exact congrArg eQ h
  exact exists_of_tmul_eq b h2

variable (φ) in
/-- The chart of a point. -/
noncomputable def pick {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (y : X.obj (op W)) : ChartOf φ y := Classical.choice (C.chart y)

/-- `t = y^*ψ_f (r)`, on the chart. -/
def Lift {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] (y : X.obj (op W))
    (f : Γ((SCH).obj U₀, ⊤)) (r t : Γ((SCH).obj W, ⊤)) : Prop :=
  ((sec (pick φ C y).e₁) r, (sec (pick φ C y).e₁) t) ∈ Graph fU φ (pick φ C y).e₂ f

/-- The torsion exponent of the charts. -/
noncomputable def bd : ℕ := (exists_cross C).choose

lemma bd_spec₁ {A : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj A)] (c₁ c₂ : A ⟶ V)
    (h : φ.app (op A) c₂ = φ.app (op A) c₁) {f p p'} (hp : p ∈ Graph fU φ c₁ f)
    (hp' : p' ∈ Graph fU φ c₂ f) {d} (hd : d ∈ C.idl (φ.app (op A) c₁) ^ bd C) :
    d * (p.1 * p'.2 - p'.1 * p.2) = 0 :=
  (exists_cross C).choose_spec.1 c₁ c₂ h hp hp' d hd

lemma bd_spec₂ {A : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj A)] (c₁ c₂ : A ⟶ V)
    (h : Multiplicative M →* Γ((SCH).obj A, ⊤)) (hw : φ.app (op A) c₂ = smX actX h (φ.app (op A) c₁))
    {D f p p'} (hf : f ∈ homog actU D) (hp : p ∈ Graph fU φ c₁ f)
    (hp' : p' ∈ Graph fU φ c₂ f) {d} (hd : d ∈ C.idl (φ.app (op A) c₁) ^ bd C) :
    d * (p.1 * p'.2 - h (Multiplicative.ofAdd D) * p'.1 * p.2) = 0 :=
  (exists_cross C).choose_spec.2 c₁ c₂ h hw hf hp hp' d hd

/-- The pole order of `f`. -/
noncomputable def pole (f : Γ((SCH).obj U₀, ⊤)) : ℕ := (exists_pole C f).choose

lemma pole_spec (f) {j} (hj : j ∈ C.idl (yonedaEquiv φ) ^ pole C f) : ∃ s, (j, s) ∈ Gam fU φ f :=
  (exists_pole C f).choose_spec j hj

/-- The exponent which kills the ambiguity of `f`. -/
noncomputable def E₀ (f : Γ((SCH).obj U₀, ⊤)) : ℕ := pole C f + bd C

/-- The exponent `exp f` of the note: `lift_exists` needs twice `E₀`. -/
noncomputable def expo (f : Γ((SCH).obj U₀, ⊤)) : ℕ := E₀ C f + E₀ C f

lemma idl_app {A : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj A)] (c : A ⟶ V) :
    C.idl (φ.app (op A) c) = (C.idl (yonedaEquiv φ)).map (sec c) := by
  rw [← map_yonedaEquiv, C.idl_map]

/-- An element of `J^e Γ(A)` has a partner in the graph. -/
lemma exists_graph {A : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj A)]
    (c : A ⟶ V) (f) {r} (hr : r ∈ C.idl (φ.app (op A) c) ^ pole C f) :
    ∃ t, (r, t) ∈ Graph fU φ c f := by
  rw [idl_app, ← Ideal.map_pow] at hr
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    obtain ⟨s, hs⟩ := pole_spec C f hj
    exact ⟨(sec c) s, Submodule.subset_span ⟨_, hs, rfl⟩⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨t, ht⟩ := hx
    obtain ⟨t', ht'⟩ := hy
    exact ⟨t + t', add_mem ht ht'⟩
  | smul a x _ hx =>
    obtain ⟨t, ht⟩ := hx
    exact ⟨a * t, Submodule.smul_mem _ a ht⟩

/-- **The kill.** Two values at `r`, along `c₁` and `c₂ = κ • c₁`, differ by `J^{E₀}`-torsion. -/
lemma kill {A : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj A)] (c₁ c₂ : A ⟶ V)
    (κ : Γ((SCH).obj A, ⊤)) {f}
    (hc : ∀ {p p'}, p ∈ Graph fU φ c₁ f → p' ∈ Graph fU φ c₂ f →
      ∀ d ∈ C.idl (φ.app (op A) c₁) ^ bd C, d * (p.1 * p'.2 - κ * p'.1 * p.2) = 0)
    {r t₁ t₂} (h₁ : (r, t₁) ∈ Graph fU φ c₁ f) (h₂ : (r, t₂) ∈ Graph fU φ c₂ f)
    {z} (hz : z ∈ C.idl (φ.app (op A) c₁) ^ E₀ C f) : z * (t₂ - κ * t₁) = 0 := by
  unfold E₀ at hz
  rw [pow_add] at hz
  induction hz using Submodule.mul_induction_on' with
  | mem_mul_mem c' hc' d hd =>
    obtain ⟨u, hu⟩ := exists_graph C c₁ f hc'
    have e1 := hc hu h₂ d hd
    have e2 := bd_spec₁ C c₁ c₁ rfl h₁ hu hd
    simp only at e1 e2
    linear_combination e1 + κ * e2
  | add x _ y _ hx hy => rw [add_mul, hx, hy, add_zero]

/-- `lift_unique`. -/
theorem lift_unique {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    {y : X.obj (op W)} {f r t t'} (h : Lift C y f r t) (h' : Lift C y f r t') {c}
    (hc : c ∈ C.idl y ^ E₀ C f) : c * (t - t') = 0 := by
  let P := pick φ C y
  haveI := P.affine
  apply P.injective
  have hid : C.idl (φ.app (op P.E) P.e₂) = (C.idl y).map (sec P.e₁) := by
    rw [P.w, C.idl_map]
  have hz : (sec P.e₁) c ∈ C.idl (φ.app (op P.E) P.e₂) ^ E₀ C f := by
    rw [hid, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hc
  have := kill C P.e₂ P.e₂ 1 (fun hp hp' d hd => by
    have := bd_spec₁ C P.e₂ P.e₂ rfl hp hp' hd
    simpa using this) h' h hz
  simpa using this

/-- `lift_map`. -/
theorem lift_map {W W' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W')] (q : W' ⟶ W) {y : X.obj (op W)} {f r t}
    (h : Lift C y f r t) : Lift C (X.map q.op y) f ((sec q) r) ((sec q) t) := by
  let P := pick φ C y
  let P' := pick φ C (X.map q.op y)
  obtain ⟨l, hl₁, hl₂⟩ := P.lift (P'.e₁ ≫ q) P'.e₂ (by
    rw [P'.w, op_comp, Functor.map_comp_apply])
  have := graph_map l P.e₂ f h
  rw [hl₂] at this
  change ((sec P'.e₁) ((sec q) r), (sec P'.e₁) ((sec q) t)) ∈ Graph fU φ P'.e₂ f
  rw [← sec_comp, ← sec_comp, ← hl₁, sec_comp, sec_comp]
  exact this

/-- `lift_exists` -/
theorem lift_exists {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (y : X.obj (op W)) (f) {r} (hr : r ∈ C.idl y ^ expo C f) : ∃ t, Lift C y f r t := by
  let P := pick φ C y
  haveI := P.affine
  have hid : C.idl (φ.app (op P.E) P.e₂) = (C.idl y).map (sec P.e₁) := by
    rw [P.w, C.idl_map]
  unfold expo at hr
  rw [pow_add] at hr
  induction hr using Submodule.mul_induction_on' with
  | mem_mul_mem c hc r' hr' =>
    have hsub : ∀ {x}, x ∈ C.idl y ^ E₀ C f → (sec P.e₁) x ∈ C.idl (φ.app (op P.E) P.e₂) ^ E₀ C f := by
      intro x hx
      rw [hid, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hx
    have hle : ∀ {x}, x ∈ C.idl (φ.app (op P.E) P.e₂) ^ E₀ C f →
        x ∈ C.idl (φ.app (op P.E) P.e₂) ^ pole C f := fun hx =>
      Ideal.pow_le_pow_right (Nat.le_add_right _ _) hx
    obtain ⟨t', ht'⟩ := exists_graph C P.e₂ f (hle (hsub hr'))
    obtain ⟨t, ht⟩ := P.descend ((sec P.e₁) c * t') (by
      intro A _ p₁ p₂ hp
      have g₁ := graph_map p₁ P.e₂ f ht'
      have g₂ := graph_map p₂ P.e₂ f ht'
      simp only at g₁ g₂
      have e : (sec p₂) ((sec P.e₁) r') = (sec p₁) ((sec P.e₁) r') := by
        rw [← sec_comp, ← sec_comp, hp]
      rw [e] at g₂
      have hw : φ.app (op A) (p₂ ≫ P.e₂) = φ.app (op A) (p₁ ≫ P.e₂) := by
        rw [map_yoneda_app, map_yoneda_app, P.w, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
          ← op_comp, ← op_comp, hp]
      have hz : (sec p₁) ((sec P.e₁) c) ∈ C.idl (φ.app (op A) (p₁ ≫ P.e₂)) ^ E₀ C f := by
        rw [map_yoneda_app, C.idl_map, ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ (hsub hc)
      have := kill C (p₁ ≫ P.e₂) (p₂ ≫ P.e₂) 1 (fun hp hp' d hd => by
        have := bd_spec₁ C _ _ hw hp hp' hd
        simpa using this) g₁ g₂ hz
      have e' : (sec p₁) ((sec P.e₁) c) = (sec p₂) ((sec P.e₁) c) := by
        rw [← sec_comp, ← sec_comp, hp]
      simp only [map_mul]
      rw [← e']
      linear_combination -this)
    refine ⟨t, ?_⟩
    change ((sec P.e₁) (c * r'), (sec P.e₁) t) ∈ Graph fU φ P.e₂ f
    rw [ht, map_mul]
    exact Submodule.smul_mem _ ((sec P.e₁) c) ht'
  | add x _ x' _ hx hx' =>
    obtain ⟨t, ht⟩ := hx
    obtain ⟨t', ht'⟩ := hx'
    refine ⟨t + t', ?_⟩
    have := add_mem ht ht'
    simpa [Lift] using this

lemma idl_chart {Z : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)]
    {τ : X.obj (op Z)} (P : ChartOf φ τ) [IsAffine ((BigFppfOver.toScheme B S hS).obj P.E)] :
    C.idl (φ.app (op P.E) P.e₂) = (C.idl τ).map (sec P.e₁) := by
  rw [P.w, C.idl_map]

set_option maxHeartbeats 2000000 in
/-- `lift_smul`, on arbitrary charts. -/
lemma lift_smul_aux {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    {y : X.obj (op W)} {d f r t t'} (h : Multiplicative M →* Γ((SCH).obj W, ⊤))
    (hf : f ∈ homog actU d) (P : ChartOf φ y) (P' : ChartOf φ (smX actX h y))
    [IsAffine ((BigFppfOver.toScheme B S hS).obj P'.E)] (A : ChartOf φ (X.map P'.e₁.op y))
    [IsAffine ((BigFppfOver.toScheme B S hS).obj A.E)]
    (ht : ((sec P.e₁) r, (sec P.e₁) t) ∈ Graph fU φ P.e₂ f)
    (ht' : ((sec P'.e₁) r, (sec P'.e₁) t') ∈ Graph fU φ P'.e₂ f) {c}
    (hc : c ∈ C.idl y ^ E₀ C f) : c * (t' - h (Multiplicative.ofAdd d) * t) = 0 := by
  obtain ⟨l, hl₁, hl₂⟩ := P.lift (A.e₁ ≫ P'.e₁) A.e₂ (by
    rw [A.w, op_comp, Functor.map_comp_apply])
  have hρ : ∀ x, (sec (A.e₁ ≫ P'.e₁)) x = (sec A.e₁) ((sec P'.e₁) x) := fun x => sec_comp A.e₁ P'.e₁ x
  have hρ' : ∀ x, (sec (A.e₁ ≫ P'.e₁)) x = (sec l) ((sec P.e₁) x) := fun x => by
    rw [← hl₁, sec_comp]
  have g₁ : ((sec (A.e₁ ≫ P'.e₁)) r, (sec (A.e₁ ≫ P'.e₁)) t) ∈ Graph fU φ A.e₂ f := by
    have := graph_map l P.e₂ f ht
    rw [hl₂] at this
    rw [hρ' r, hρ' t]
    exact this
  have g₂ : ((sec (A.e₁ ≫ P'.e₁)) r, (sec (A.e₁ ≫ P'.e₁)) t') ∈ Graph fU φ (A.e₁ ≫ P'.e₂) f := by
    have := graph_map A.e₁ P'.e₂ f ht'
    rw [hρ r, hρ t']
    exact this
  let h' : Multiplicative M →* Γ((SCH).obj A.E, ⊤) := secPt (sec (A.e₁ ≫ P'.e₁)) h
  have hw : φ.app (op A.E) (A.e₁ ≫ P'.e₂) = smX actX h' (φ.app (op A.E) A.e₂) := by
    rw [map_yoneda_app, P'.w, smX_map, A.w, smX_map, ← Functor.map_comp_apply, ← op_comp]
    change smX actX _ _ = smX actX (secPt (sec (A.e₁ ≫ P'.e₁)) h) _
    congr 1
  have hz : (sec (A.e₁ ≫ P'.e₁)) c ∈ C.idl (φ.app (op A.E) A.e₂) ^ E₀ C f := by
    have e : ∀ n, C.idl (φ.app (op A.E) A.e₂) ^ n =
        ((C.idl y ^ n).map (sec P'.e₁)).map (sec A.e₁) := fun n => by
      rw [idl_chart C A, C.idl_map P'.e₁, Ideal.map_pow, Ideal.map_pow]
    rw [e, hρ c]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hc)
  have key := kill C A.e₂ (A.e₁ ≫ P'.e₂) (h' (Multiplicative.ofAdd d)) (fun hp hp' _ hd =>
    bd_spec₂ C _ _ h' hw hf hp hp' hd) g₁ g₂ hz
  have hinj : Function.Injective (sec (A.e₁ ≫ P'.e₁)) := by
    have : ⇑(sec (A.e₁ ≫ P'.e₁)) = (sec A.e₁) ∘ (sec P'.e₁) := funext hρ
    rw [this]
    exact A.injective.comp P'.injective
  apply hinj
  simp only [map_mul, map_sub, map_zero]
  exact key

/-- `lift_smul`. -/
theorem lift_smul {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    {y : X.obj (op W)} {d f r t t'} (h : Multiplicative M →* Γ((SCH).obj W, ⊤))
    (hf : f ∈ homog actU d) (ht : Lift C y f r t) (ht' : Lift C (smX actX h y) f r t') {c}
    (hc : c ∈ C.idl y ^ E₀ C f) : c * (t' - h (Multiplicative.ofAdd d) * t) = 0 := by
  haveI := (pick φ C (smX actX h y)).affine
  haveI := (pick φ C (X.map (pick φ C (smX actX h y)).e₁.op y)).affine
  exact lift_smul_aux C h hf _ _ (pick φ C _) ht ht' hc

lemma lift_mul_left {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    {y : X.obj (op W)} {f r t} (c) (h : Lift C y f r t) : Lift C y f (c * r) (c * t) := by
  have := Submodule.smul_mem _ ((sec (pick φ C y).e₁) c) h
  simpa [Lift] using this

lemma lift_add' {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    {y : X.obj (op W)} {f f' r r' t t'} (h : Lift C y f r t) (h' : Lift C y f' r' t') :
    Lift C y (f + f') (r * r') (t * r' + r * t') := by
  have := graph_add (fU := fU) (pick φ C y).e₂ h h'
  simpa [Lift] using this

lemma lift_mul {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    {y : X.obj (op W)} {f f' r r' t t'} (h : Lift C y f r t) (h' : Lift C y f' r' t') :
    Lift C y (f * f') (r * r') (t * t') := by
  have := graph_mul (fU := fU) (pick φ C y).e₂ h h'
  simpa [Lift] using this

/-- **The formula on `U`.** On a point of `U₀`, the value at `r` is `r f`. -/
lemma lift_formula {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (y₀ : W ⟶ U₀) {f r t} (h : Lift C (fU.app (op W) y₀) f r t) : t = r * (sec y₀) f := by
  let P := pick φ C (fU.app (op W) y₀)
  apply P.injective
  have hw : φ.app (op P.E) P.e₂ = fU.app (op P.E) (P.e₁ ≫ y₀) := by
    rw [P.w, map_yoneda_app (φ := fU)]
  have key : ∀ p ∈ Graph fU φ P.e₂ f, p.2 = p.1 * (sec (P.e₁ ≫ y₀)) f := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, hq, rfl⟩ := hx
      exact hq P.e₂ _ hw
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Prod.fst_add, Prod.snd_add]
      rw [hx, hy]; ring
    | smul r x _ hx =>
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      rw [hx]; ring
  have := key _ h
  simp only at this
  rw [this, map_mul, sec_comp]

/-- `(1, b)` for `f` coming from a global function, e.g. on the base. -/
lemma lift_one_of {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (y : X.obj (op W)) (f) (b : Γ((SCH).obj V, ⊤)) (hb : (1, b) ∈ Gam fU φ f) (t)
    (ht : (sec (pick φ C y).e₁) t = (sec (pick φ C y).e₂) b) : Lift C y f 1 t := by
  refine Submodule.subset_span ⟨(1, b), hb, ?_⟩
  simp [ht]

end LiftSec

end AlgMag.ChartMain.DeligneInst
