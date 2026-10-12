/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.UnderlyingSheaf

/-!
# Underlying additive sheaves of modules on closed subsets

This module records the forgetful functor from modules over a restricted
structure sheaf to additive sheaves on the corresponding closed subset.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u w w'

namespace AlgebraicGeometry.RingedSpace

/-- The forgetful functor from modules over the restricted structure sheaf on
`Z ⊆ X` to sheaves of abelian groups on `Z`. -/
abbrev closedSubsetModuleUnderlyingSheaf (X : RingedSpace.{u}) (Z : Set X) :
    ClosedSubset.Modules X Z ⥤ (TopCat.of Z).Sheaf AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (ClosedSubset.ringCatSheaf X Z)

/-- The underlying-additive-sheaf functor of modules on `Z ⊆ X` is additive. -/
instance closedSubsetModuleUnderlyingSheaf_additive (X : RingedSpace.{u}) (Z : Set X) :
    (closedSubsetModuleUnderlyingSheaf X Z).Additive := sorry

/-- The underlying-additive-sheaf functor of modules on `Z ⊆ X` is faithful. -/
instance closedSubsetModuleUnderlyingSheaf_faithful (X : RingedSpace.{u}) (Z : Set X) :
    (closedSubsetModuleUnderlyingSheaf X Z).Faithful := sorry

/-- The underlying-additive-sheaf functor of modules on `Z ⊆ X` preserves finite limits. -/
instance closedSubsetModuleUnderlyingSheaf_preservesFiniteLimits
    (X : RingedSpace.{u}) (Z : Set X) :
    PreservesFiniteLimits (closedSubsetModuleUnderlyingSheaf X Z) := sorry

/-- The underlying-additive-sheaf functor of modules on `Z ⊆ X` preserves all small limits. -/
@[stacks 03DB "underlying closed-subset module sheaf preserves limits"]
instance closedSubsetModuleUnderlyingSheaf_preservesLimits
    (X : RingedSpace.{u}) (Z : Set X) :
    PreservesLimits (closedSubsetModuleUnderlyingSheaf X Z) := sorry

/-- The underlying-additive-sheaf functor on a closed subset preserves limits of every shape. -/
@[stacks 03DB "underlying closed-subset module sheaf preserves limits of any shape"]
instance closedSubsetModuleUnderlyingSheaf_preservesLimitsOfShape
    (X : RingedSpace.{u}) (Z : Set X) {J : Type w} [Category.{w'} J] :
    PreservesLimitsOfShape J (closedSubsetModuleUnderlyingSheaf X Z) := sorry

/-- The underlying-additive-sheaf functor of modules on `Z ⊆ X` preserves finite colimits. -/
instance closedSubsetModuleUnderlyingSheaf_preservesFiniteColimits
    (X : RingedSpace.{u}) (Z : Set X) :
    PreservesFiniteColimits (closedSubsetModuleUnderlyingSheaf X Z) := sorry

end AlgebraicGeometry.RingedSpace
