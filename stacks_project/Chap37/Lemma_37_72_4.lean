module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.StructureSheafSurjectivity

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 37.72.4: for a proper morphism with fibers of dimension at most one and
vanishing first cohomology of their structure sheaves, local surjectivity of the
structure-sheaf pushforward map is preserved by every base change. -/
@[stacks 0E7I] #check
  (AlgebraicGeometry.Scheme.HigherDirectImage.baseChange_structureSheafMap_isLocallySurjective :
    ∀ {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
      (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (1 : WithBot ℕ∞))
      (hH1 : ∀ y : Y,
        IsZero (Scheme.Modules.cohomology
          (SheafOfModules.unit (f.fiber y).ringCatSheaf) 1))
      [Sheaf.IsLocallySurjective
        (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom)]
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
      (hcart : IsPullback g' f' f g),
      Sheaf.IsLocallySurjective
        (RingedSpace.Hom.commRingSheafPushforwardMap f'.toShHom))
