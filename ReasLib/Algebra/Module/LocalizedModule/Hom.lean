/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Linear Maps from Localized Modules

@stack 07K0
-/

@[expose] public section

universe u v w x

namespace IsLocalizedModule

variable {R : Type u} [CommSemiring R] (S : Submonoid R)
variable {M : Type v} {M' : Type w} {N : Type x}
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid M'] [Module R M']
variable [AddCommMonoid N] [Module R N]
variable (f : M →ₗ[R] M') [IsLocalizedModule S f]

/-- Precomposition with a localization map identifies maps from the localized module with maps
from the original module, provided the denominators act invertibly on the target. -/
@[stacks 07K0 "Hom-form universal property of module localization"]
noncomputable def homLinearEquiv
    (hS : ∀ s : S, IsUnit (algebraMap R (Module.End R N) s)) :
    (M' →ₗ[R] N) ≃ₗ[R] (M →ₗ[R] N) where
  toFun g := g.comp f
  invFun g := IsLocalizedModule.lift S f g hS
  left_inv g := IsLocalizedModule.lift_unique S f (g.comp f) hS g rfl
  right_inv g := IsLocalizedModule.lift_comp S f g hS
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp, stacks 07K0 "localized Hom equivalence is precomposition"]
theorem homLinearEquiv_apply
    (hS : ∀ s : S, IsUnit (algebraMap R (Module.End R N) s))
    (g : M' →ₗ[R] N) :
    homLinearEquiv S f hS g = g.comp f :=
  rfl

@[simp, stacks 07K0 "inverse localized Hom equivalence is the universal lift"]
theorem homLinearEquiv_symm_apply
    (hS : ∀ s : S, IsUnit (algebraMap R (Module.End R N) s))
    (g : M →ₗ[R] N) :
    (homLinearEquiv S f hS).symm g = IsLocalizedModule.lift S f g hS :=
  rfl

end IsLocalizedModule

namespace LocalizedModule

variable {R : Type u} [CommSemiring R] (S : Submonoid R)
variable {M : Type v} {N : Type x}
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

/-- The Hom-form universal property for the canonical localized module. -/
@[stacks 07K0 "canonical Hom-form universal property of module localization"]
noncomputable def homLinearEquiv
    (hS : ∀ s : S, IsUnit (algebraMap R (Module.End R N) s)) :
    (LocalizedModule S M →ₗ[R] N) ≃ₗ[R] (M →ₗ[R] N) :=
  IsLocalizedModule.homLinearEquiv S (mkLinearMap S M) hS

@[simp, stacks 07K0 "canonical localized Hom equivalence is precomposition"]
theorem homLinearEquiv_apply
    (hS : ∀ s : S, IsUnit (algebraMap R (Module.End R N) s))
    (g : LocalizedModule S M →ₗ[R] N) :
    homLinearEquiv S hS g = g.comp (mkLinearMap S M) :=
  rfl

@[simp, stacks 07K0 "inverse canonical localized Hom equivalence is lift"]
theorem homLinearEquiv_symm_apply
    (hS : ∀ s : S, IsUnit (algebraMap R (Module.End R N) s))
    (g : M →ₗ[R] N) :
    (homLinearEquiv S hS).symm g = LocalizedModule.lift S g hS := by
  apply (homLinearEquiv S hS).injective
  rw [LinearEquiv.apply_symm_apply, homLinearEquiv_apply, LocalizedModule.lift_comp]

end LocalizedModule
