/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.WLocalAffine.FiniteStage

/-!
# Affine schemes attached to vanishing patterns

The product ring `A_E` of the component localizations is realized as an affine
scheme `X_E = Spec(A_E)`, identified with the coproduct of the component
spectra via mathlib's finite `sigmaSpec` comparison.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.WLocalAffine

#check (AlgebraicGeometry.Scheme.WLocalAffine.scheme :
  {A : Type u} → [CommRing A] → Finset A → Scheme.{u})

#check (AlgebraicGeometry.Scheme.WLocalAffine.sigmaIso :
  ∀ {A : Type u} [CommRing A] (E : Finset A),
    (∐ fun p : VanishingPattern E ↦ componentScheme p) ≅ scheme E)
