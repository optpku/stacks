module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Koszul.PrincipalOpen

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.ModuleDerived.Koszul
open KoszulComplex.PowerTower

universe u

/- Compatibility check for the powered-Koszul colimit comparison on a finite union of
principal opens. -/
#check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.Koszul.homColimitToOpenH0 :
    ∀ {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
      (E : AlgebraicGeometry.RingedSpace.ModuleDerived
        (Spec (CommRingCat.of A)).toRingedSpace),
      colimit (homDiagram (derivedIdealSystem f ⋙ affineDerivedTilde A) E) ⟶
        restrictionHomH0 f E)
