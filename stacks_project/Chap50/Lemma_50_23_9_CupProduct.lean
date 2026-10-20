module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.HodgeCup
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin.HodgeCup

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open DerivedCategory.DerivedTensor.Right.Monoidal Functor.RightDerived.Homotopy
open scoped DerivedTensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham
namespace Gysin

variable {X S : Scheme.{u}}

#check (hodgeModelIso :
    ∀ (f : X ⟶ S) (p q : ℕ),
      (forget₂ (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
          AddCommGrpCat).obj
        ((DerivedCategory.homologyFunctor
          (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace)) (q : ℤ)).obj
          ((RingedSpace.Module.Derived.GlobalSections.functor X.toRingedSpace).obj
            ((ModuleCech.moduleToDerived X).obj
              ((Scheme.QCoh.inclusion X).obj (relativeFormQCoh f p))))) ≅
      (forget₂ (ModuleCat (coefficientRing f)) AddCommGrpCat).obj
        (hodgeCohomologyObject f p (q : ℤ)))

#check (hodgeFundamentalClassOne :
    ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [Scheme.Hom.FinitePresentation i]
      (f : X ⟶ S) [Smooth f] [IsKoszulRegularImmersion i] (c : ℕ)
      [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)],
    hodgeCohomologyObject f c (c : ℤ))

end Gysin
end AlgebraicGeometry.Scheme.DeRham

end
