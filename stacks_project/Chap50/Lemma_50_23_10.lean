/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin.Cohomology.BaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.DeRham.Gysin

noncomputable section

universe u

/- Lemma 50.23.10 -/
@[stacks 0G8D] #check (AlgebraicGeometry.Scheme.DeRham.Gysin.hodgeCohomologyMap_baseChange :
    {Z' X' S' Z X S : Scheme.{u}} →
    (h : Z' ⟶ Z) → (i' : Z' ⟶ X') → (i : Z ⟶ X) → (g : X' ⟶ X) →
    (f' : X' ⟶ S') → (f : X ⟶ S) → (k : S' ⟶ S) →
    [IsClosedImmersion i'] → [IsClosedImmersion i] →
    [FinitePresentation i'] → [FinitePresentation i] →
    [Smooth f'] → [Smooth f] →
    [IsKoszulRegularImmersion i'] → [IsKoszulRegularImmersion i] →
    (c p q : ℕ) →
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (conormalSheaf i')] →
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (conormalSheaf i)] →
    (sqZX : IsPullback h i' i g) → (sqXS : CommSq g f' f k) →
    [IsIso (Conormal.map sqZX.toCommSq)] →
    CommSq
      ((forget₂ (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
        AddCommGrpCat.{u}).map
          (hodgeCohomologyMapOfSmoothOfKoszulRegular i f p q c))
      (BaseChange.sourceCohomology h i' i g f' f k c p q sqZX sqXS)
      (BaseChange.targetCohomology h i' i g f' f k c p q sqZX sqXS)
      ((forget₂ (ModuleCat (RingedSpace.globalSectionsRing X'.toRingedSpace))
        AddCommGrpCat.{u}).map
          (hodgeCohomologyMapOfSmoothOfKoszulRegular i' f' p q c)))

end
