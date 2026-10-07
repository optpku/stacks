module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.OpenImmersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 51.12.2 -/
@[stacks 0BLT]
#check (AlgebraicGeometry.Scheme.HigherDirectImage.isCoherent_of_finiteLocallyFree :
  ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens) (n : ℕ),
    (∀ p : ℕ, p < n →
      (AlgebraicGeometry.RingedSpace.Hom.higherDirectImageModule U.ι.toShHom
        (SheafOfModules.unit U.toScheme.ringCatSheaf : U.toScheme.Modules) p).IsCoherent) →
    ∀ (F : U.toScheme.Modules) [SheafOfModules.IsFiniteLocallyFree F] (p : ℕ), p < n →
      (AlgebraicGeometry.RingedSpace.Hom.higherDirectImageModule U.ι.toShHom F p).IsCoherent)
