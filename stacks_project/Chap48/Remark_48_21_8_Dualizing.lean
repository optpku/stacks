module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NewUpperShriek.Dualizing

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

#check (DerivedCoh.structureSheafPlus_mem :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X],
    DerivedCategory.Plus.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)
      (DerivedQCoh.structureSheafPlus X).obj)

#check (DerivedCoh.structureSheafPlus :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X], DerivedCoh.Plus X)

#check (DerivedCoh.structureSheafPlus_isIsomorphic :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X],
    IsIsomorphic (DerivedCoh.structureSheafPlus X).obj.obj
      (DerivedQCoh.structureSheaf X).obj)

#check (NewUpperShriekAssignment.dualizingObject :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y),
    RingedSpace.ModuleDerived X.obj.left.toRingedSpace)

#check (NewUpperShriekAssignment.dualizingObject_eq :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y),
    D.dualizingObject f =
      ((D.map f).obj (DerivedCoh.structureSheafPlus Y.obj.left)).obj.obj)

#check (NewUpperShriekAssignment.dualizingModule :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y), X.obj.left.Modules)

#check (NewUpperShriekAssignment.dualizingModule_eq :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y),
    D.dualizingModule f =
      RingedSpace.ModuleDerived.cohomologySheaf (D.dualizingObject f) 0)

end AlgebraicGeometry.Scheme
