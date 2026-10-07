module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.TStructure
open scoped CartesianClosed CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry
namespace RingedSpace
namespace ModuleDerived
namespace IsPerfect

variable {X : Scheme.{u}} [hX : IsNoetherian X]
variable {E L : ModuleDerived X.toRingedSpace}
variable [DerivedCategory.DerivedTensor.Right.Has (C := Modules X.toRingedSpace)]

include hX

/-- A perfect derived module on a Noetherian scheme has coherent cohomology and is
cohomologically bounded. -/
theorem boundedCoherentCohomology (hE : IsPerfect E) :
    DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) E ∧
      (t.bounded : ObjectProperty (ModuleDerived X.toRingedSpace)) E := sorry

/-- Derived tensor product with a perfect left factor on a Noetherian scheme preserves
coherent cohomology. -/
theorem tensorCoherentCohomology (hE : IsPerfect E)
    (hL : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L) :
    DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) (E ⊗ᴸ L) := sorry

/-- Derived internal Hom from a perfect object on a Noetherian scheme preserves coherent
cohomology of its target. -/
theorem internalHomCoherentCohomology
    [MonoidalCategory (ModuleDerived X.toRingedSpace)]
    [MonoidalClosed (ModuleDerived X.toRingedSpace)]
    (hE : IsPerfect E)
    (hL : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L) :
    DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) (E ⟹ L) := sorry

/-- Derived tensor product with a perfect left factor on a Noetherian scheme preserves
bounded coherent cohomology. -/
theorem tensorBoundedCoherentCohomology (hE : IsPerfect E)
    (hL : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L)
    (hL_bounded : (t.bounded : ObjectProperty (ModuleDerived X.toRingedSpace)) L) :
    DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) (E ⊗ᴸ L) ∧
      (t.bounded : ObjectProperty (ModuleDerived X.toRingedSpace)) (E ⊗ᴸ L) := sorry

/-- Derived internal Hom from a perfect object on a Noetherian scheme preserves bounded
coherent cohomology of its target. -/
theorem internalHomBoundedCoherentCohomology
    [MonoidalCategory (ModuleDerived X.toRingedSpace)]
    [MonoidalClosed (ModuleDerived X.toRingedSpace)]
    (hE : IsPerfect E)
    (hL : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L)
    (hL_bounded : (t.bounded : ObjectProperty (ModuleDerived X.toRingedSpace)) L) :
    DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) (E ⟹ L) ∧
      (t.bounded : ObjectProperty (ModuleDerived X.toRingedSpace)) (E ⟹ L) := sorry

/-- Derived tensor product with a perfect left factor on a Noetherian scheme preserves
bounded-below coherent cohomology. -/
theorem tensorBoundedBelowCoherentCohomology (hE : IsPerfect E)
    (hL : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L)
    (hL_boundedBelow : (t.plus : ObjectProperty (ModuleDerived X.toRingedSpace)) L) :
    DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) (E ⊗ᴸ L) ∧
      (t.plus : ObjectProperty (ModuleDerived X.toRingedSpace)) (E ⊗ᴸ L) := sorry

/-- Derived internal Hom from a perfect object on a Noetherian scheme preserves bounded-below
coherent cohomology of its target. -/
theorem internalHomBoundedBelowCoherentCohomology
    [MonoidalCategory (ModuleDerived X.toRingedSpace)]
    [MonoidalClosed (ModuleDerived X.toRingedSpace)]
    (hE : IsPerfect E)
    (hL : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L)
    (hL_boundedBelow : (t.plus : ObjectProperty (ModuleDerived X.toRingedSpace)) L) :
    DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) (E ⟹ L) ∧
      (t.plus : ObjectProperty (ModuleDerived X.toRingedSpace)) (E ⟹ L) := sorry

/-- Derived tensor product with a perfect left factor on a Noetherian scheme preserves
bounded-above coherent cohomology. -/
theorem tensorBoundedAboveCoherentCohomology (hE : IsPerfect E)
    (hL : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L)
    (hL_boundedAbove : (t.minus : ObjectProperty (ModuleDerived X.toRingedSpace)) L) :
    DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) (E ⊗ᴸ L) ∧
      (t.minus : ObjectProperty (ModuleDerived X.toRingedSpace)) (E ⊗ᴸ L) := sorry

/-- Derived internal Hom from a perfect object on a Noetherian scheme preserves bounded-above
coherent cohomology of its target. -/
theorem internalHomBoundedAboveCoherentCohomology
    [MonoidalCategory (ModuleDerived X.toRingedSpace)]
    [MonoidalClosed (ModuleDerived X.toRingedSpace)]
    (hE : IsPerfect E)
    (hL : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L)
    (hL_boundedAbove : (t.minus : ObjectProperty (ModuleDerived X.toRingedSpace)) L) :
    DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) (E ⟹ L) ∧
      (t.minus : ObjectProperty (ModuleDerived X.toRingedSpace)) (E ⟹ L) := sorry

end IsPerfect
end ModuleDerived
end RingedSpace
end AlgebraicGeometry
