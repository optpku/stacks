module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin.Cohomology.Differential

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom

universe u

/- Lemma 50.23.8: for a smooth morphism `f : X ⟶ S` and a finitely presented
Koszul-regular closed immersion `i : Z ⟶ X` whose conormal sheaf has rank `c`, the
cohomological Gysin maps `γ^(p,q)` commute with the relative de Rham differentials. -/
@[stacks 0G8B]
#check (AlgebraicGeometry.Scheme.DeRham.Gysin.hodgeCohomologyMap_d :
    ∀ {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [FinitePresentation i]
      (f : X ⟶ S) [Smooth f] [IsKoszulRegularImmersion i] (c p q : ℕ)
      [SheafOfModules.IsFiniteLocallyFreeOfRank c (conormalSheaf i)],
      CommSq
        ((forget₂ (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
          AddCommGrpCat).map
          (AlgebraicGeometry.Scheme.DeRham.Gysin.hodgeCohomologyMapOfSmoothOfKoszulRegular
            i f p q c))
        (AlgebraicGeometry.Scheme.DeRham.Gysin.hodgeSourceDifferential i f p q c)
        (AlgebraicGeometry.Scheme.DeRham.Gysin.hodgeTargetDifferential f p q c)
        ((forget₂ (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
          AddCommGrpCat).map
          (AlgebraicGeometry.Scheme.DeRham.Gysin.hodgeCohomologyMapOfSmoothOfKoszulRegular
            i f (p + 1) q c)))
