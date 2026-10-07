module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NewUpperShriek

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped DerivedCategory.CohomologyIn

universe u

/- Compatibility check for the new upper-shriek functor. -/
#check (AlgebraicGeometry.Scheme.Hom.NewUpperShriek.functor :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Scheme.Hom.FiniteType f]
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    [MonoidalCategory (RingedSpace.ModuleDerived Y.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived Y.toRingedSpace)]
    (HY : MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace))
    (ωX : RingedSpace.ModuleDerived X.toRingedSpace)
    (ωY : RingedSpace.ModuleDerived Y.toRingedSpace)
    (hωX : RingedSpace.ModuleDerived.IsDualizingComplex ωX HX)
    (hωY : RingedSpace.ModuleDerived.IsDualizingComplex ωY HY),
    D⁺[SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf] ⥤
      D⁺[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf])
