/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Stalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.DualExt

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (ModuleDerived X)]

/-- The degree-`i` dual Ext sheaf of `F` against `K`, defined by degree `-i`
cohomology of their derived internal Hom. -/
noncomputable def sheaf (H : MonoidalClosed (ModuleDerived X))
    (F : X.Modules) (K : ModuleDerived X) (i : ℤ) : X.Modules :=
  ModuleDerived.cohomologySheaf
    ((MonoidalClosed.ihomOf H
      ((DerivedCategory.singleFunctor X.Modules 0).obj F)).obj K) (-i)

/-- The dual Ext sheaf is the degree-reversed cohomology sheaf of derived internal Hom. -/
theorem sheaf_def (H : MonoidalClosed (ModuleDerived X))
    (F : X.Modules) (K : ModuleDerived X) (i : ℤ) :
    sheaf H F K i =
      ModuleDerived.cohomologySheaf
        ((MonoidalClosed.ihomOf H
          ((DerivedCategory.singleFunctor X.Modules 0).obj F)).obj K) (-i) := sorry

/-- The stalk of a dual Ext sheaf is the corresponding cohomology stalk of the
derived internal Hom. -/
theorem stalk (H : MonoidalClosed (ModuleDerived X))
    (F : X.Modules) (K : ModuleDerived X) (i : ℤ) (x : X) :
    RingedSpace.stalkModuleCat (sheaf H F K i) x =
      ModuleDerived.cohomologyStalk
        ((MonoidalClosed.ihomOf H
          ((DerivedCategory.singleFunctor X.Modules 0).obj F)).obj K) (-i) x := sorry

/-- The cumulative support of the dual Ext sheaves in degrees at most `i`. -/
noncomputable def supportUpTo (H : MonoidalClosed (ModuleDerived X))
    (F : X.Modules) (K : ModuleDerived X) (i : ℤ) : Set X :=
  {x | ∃ j : ℤ, j ≤ i ∧ x ∈ RingedSpace.moduleSupport (sheaf H F K j)}

/-- Membership in cumulative dual Ext support is membership in the support of some
dual Ext sheaf of degree at most `i`. -/
theorem mem_supportUpTo (H : MonoidalClosed (ModuleDerived X))
    (F : X.Modules) (K : ModuleDerived X) (i : ℤ) (x : X) :
    x ∈ supportUpTo H F K i ↔
      ∃ j : ℤ, j ≤ i ∧ x ∈ RingedSpace.moduleSupport (sheaf H F K j) := sorry

end AlgebraicGeometry.RingedSpace.DualExt
