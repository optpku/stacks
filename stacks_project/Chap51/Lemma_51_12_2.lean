/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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
