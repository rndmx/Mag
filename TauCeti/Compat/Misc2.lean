/- Backport (compat, not Tau Ceti code), second batch (2026-11-10): names used by Tau Ceti 7ca783d4
that are absent or renamed in Mathlib 16edf57. Apache-2.0. See TauCeti/CHANGES.md. -/
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Group.Monoid

alias MonoidHom.coe_ofClass := MonoidHom.coe_coe
alias LinearMap.coe_ofClass := LinearMap.coe_coe

/-! 1b1ccf4 renamed MulEquiv.coe_monoidHom_* to MulEquiv.toMonoidHom_* (coercion form). -/
alias MulEquiv.toMonoidHom_trans := MulEquiv.coe_monoidHom_trans
alias MulEquiv.toMonoidHom_comp_toMonoidHom_symm := MulEquiv.coe_monoidHom_comp_coe_monoidHom_symm
alias MulEquiv.toMonoidHom_symm_comp_toMonoidHom := MulEquiv.coe_monoidHom_symm_comp_coe_monoidHom

/-! 1b1ccf4 introduced `HasUniqueRoots M` (`n`-th power injective for `n ≠ 0`); this is exactly the
16edf57 definition of `IsMulTorsionFree` (1b1ccf4 weakened `IsMulTorsionFree` to commuting pairs;
the two agree for commutative monoids). -/
abbrev HasUniqueRoots (M : Type*) [Monoid M] : Prop := IsMulTorsionFree M

theorem IsMulTorsionFree.hasUniqueRoots {M : Type*} [CommMonoid M] [IsMulTorsionFree M] :
    HasUniqueRoots M := ‹_›
