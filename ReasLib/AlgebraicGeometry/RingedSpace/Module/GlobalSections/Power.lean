/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Linear
public import ReasLib.CategoryTheory.Linear.PrincipalPower
import Mathlib.Tactic.CrossRefAttribute

/-!
# Global-section views of principal powers

The categorical principal-power construction is owned by
`CategoryTheory.Linear.PrincipalPower`.  This leaf only records the genuine bridge between that
scalar action and the sectionwise endomorphism `globalSectionMul`; it intentionally does not create
parallel kernel, quotient, or instance owners in the ringed-space namespace.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.GlobalSections.Power

variable {X : RingedSpace.{u}}

/-- Multiplication by a global section is the source-facing divisibility predicate. -/
@[stacks 0EHA "global-section divisibility"]
abbrev IsDivisible (f : globalSectionsRing X) (M : X.Modules) : Prop :=
  Epi (globalSectionMul f M)

/-- Multiplication by a global section is the source-facing torsion-free predicate. -/
@[stacks 0EHA "global-section torsion freeness"]
abbrev IsTorsionFree (f : globalSectionsRing X) (M : X.Modules) : Prop :=
  Mono (globalSectionMul f M)

/-- The categorical scalar power agrees with the corresponding sectionwise multiplication map. -/
@[stacks 0EHA "global-section scalar-power bridge"]
theorem smulPow_eq_globalSectionMul
    (f : globalSectionsRing X) (M : X.Modules) (n : ℕ) :
    CategoryTheory.Linear.PrincipalPower.smulPow f M n =
      globalSectionMul (f ^ n) M := sorry

/-- Source-facing divisibility is equivalent to the categorical scalar-divisibility predicate. -/
@[stacks 0EHA "global-section divisibility bridge"]
theorem isDivisible_iff_linear (f : globalSectionsRing X) (M : X.Modules) :
    IsDivisible f M ↔ CategoryTheory.Linear.PrincipalPower.IsDivisible f M := sorry

/-- Source-facing torsion-freeness is equivalent to the categorical scalar predicate. -/
@[stacks 0EHA "global-section torsion-free bridge"]
theorem isTorsionFree_iff_linear (f : globalSectionsRing X) (M : X.Modules) :
    IsTorsionFree f M ↔ CategoryTheory.Linear.PrincipalPower.IsTorsionFree f M := sorry

/-- Convert an explicit source-facing torsion-free certificate into the canonical typeclass form. -/
theorem isTorsionFree_of
    (f : globalSectionsRing X) (M : X.Modules) (h : IsTorsionFree f M) :
    CategoryTheory.Linear.PrincipalPower.IsTorsionFree f M := sorry

/-- Convert an explicit source-facing divisibility certificate into the canonical typeclass form. -/
theorem isDivisible_of
    (f : globalSectionsRing X) (M : X.Modules) (h : IsDivisible f M) :
    CategoryTheory.Linear.PrincipalPower.IsDivisible f M := sorry

/-- Multiplication by `f` followed by a categorical scalar power is the next power, in the
source-facing global-section notation. -/
@[stacks 0EHA "global-section power composition"]
theorem globalSectionMul_comp_smulPow
    (f : globalSectionsRing X) (M : X.Modules) (n : ℕ) :
    globalSectionMul f M ≫ CategoryTheory.Linear.PrincipalPower.smulPow f M n =
      CategoryTheory.Linear.PrincipalPower.smulPow f M (n + 1) := sorry

/-- Multiplication by the unit global section is the identity on every module sheaf. -/
@[simp, stacks 0EHA "unit global-section multiplication"]
theorem globalSectionMul_one (M : X.Modules) :
    globalSectionMul (1 : globalSectionsRing X) M = 𝟙 M := sorry

/-- The zeroth categorical scalar power is the identity on a module sheaf. -/
@[simp, stacks 0EHA "zeroth global-section scalar power"]
theorem smulPow_zero (f : globalSectionsRing X) (M : X.Modules) :
    CategoryTheory.Linear.PrincipalPower.smulPow f M 0 = 𝟙 M := sorry

/-- Morphisms of module sheaves commute with categorical powers of a global-section action. -/
@[stacks 0EHA "naturality of global-section scalar powers"]
theorem smulPow_natural
    (f : globalSectionsRing X) {M N : X.Modules} (φ : M ⟶ N) (n : ℕ) :
    CategoryTheory.Linear.PrincipalPower.smulPow f M n ≫ φ =
      φ ≫ CategoryTheory.Linear.PrincipalPower.smulPow f N n := sorry

end AlgebraicGeometry.RingedSpace.GlobalSections.Power
