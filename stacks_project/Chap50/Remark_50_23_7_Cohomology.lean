module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin.Cohomology

open AlgebraicGeometry CategoryTheory
open RingedSpace.ModuleDerived
open SheafOfModules.RingedSite.ExteriorPower
open scoped AlgebraicGeometry

universe u

/- The source-facing compatibility bridge exposes the smooth/Koszul-regular lower bound. -/
#check (@AlgebraicGeometry.Scheme.DeRham.Gysin.supportedDerivedRelativeFormIsGEOfSmoothOfKoszulRegular :
    {Z X S : Scheme.{u}} → (i : Z ⟶ X) → [IsClosedImmersion i] →
      [Scheme.Hom.FinitePresentation i] → (f : X ⟶ S) → [Smooth f] →
      [IsKoszulRegularImmersion i] → (p c : ℕ) →
      [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] →
        (AlgebraicGeometry.Scheme.DeRham.Gysin.supportedDerived i f (p + c)).IsGE (c : ℤ))

/- The source-facing compatibility bridge exposes the cohomological Gysin map. -/
#check (@AlgebraicGeometry.Scheme.DeRham.Gysin.hodgeCohomologyMap :
    {Z X S : Scheme.{u}} → (i : Z ⟶ X) → [IsClosedImmersion i] →
      [Scheme.Hom.FinitePresentation i] → (f : X ⟶ S) → (p q c : ℕ) →
      [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] →
      [(AlgebraicGeometry.Scheme.DeRham.Gysin.supportedDerived
        i f (p + c)).IsGE (c : ℤ)] →
        (DerivedCategory.homologyFunctor
            (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace)) (q + c : ℤ)).obj
          ((RingedSpace.moduleSectionsRestrictionDerived i.toShHom ⊤).obj
            ((RingedSpace.Module.Derived.GlobalSections.functor Z.toRingedSpace).obj
              ((DerivedCategory.singleFunctor Z.toRingedSpace.Modules (c : ℤ)).obj
                ((Scheme.Modules.toRingedSpace Z).obj
                  (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))))) ⟶
        (DerivedCategory.homologyFunctor
            (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace)) (q + c : ℤ)).obj
          ((RingedSpace.Module.Derived.GlobalSections.functor X.toRingedSpace).obj
            ((ModuleCech.moduleToDerived X).obj
              ((Scheme.QCoh.inclusion X).obj
                (AlgebraicGeometry.Scheme.DeRham.Gysin.relativeFormQCoh f (p + c))))))
