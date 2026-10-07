module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exactness of the affine tilde functor
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.tilde

/-- The affine tilde functor from modules to modules on `Spec R` is exact. -/
@[stacks 01HV]
theorem exact (R : CommRingCat.{u}) :
    exactFunctor (ModuleCat R) (Spec R).Modules
      (AlgebraicGeometry.tilde.functor R) := sorry

/-- Affine tilde sheafification preserves finite limits.  This reusable
instance is the left-exact half of `tilde.exact`. -/
@[stacks 01HV "finite limits of tilde"]
noncomputable instance preservesFiniteLimits (R : CommRingCat.{u}) :
    Limits.PreservesFiniteLimits (AlgebraicGeometry.tilde.functor R) := sorry

/-- Affine tilde sheafification preserves finite colimits.  This reusable
instance is the right-exact half of `tilde.exact`. -/
@[stacks 01HV "finite colimits of tilde"]
noncomputable instance preservesFiniteColimits (R : CommRingCat.{u}) :
    Limits.PreservesFiniteColimits (AlgebraicGeometry.tilde.functor R) := sorry

end AlgebraicGeometry.tilde
