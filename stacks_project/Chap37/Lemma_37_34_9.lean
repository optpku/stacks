/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.FiberDimension
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FiniteTypeApproximationDiagram

/- Lemma 37.34.9: an affine finitely presented morphism whose fibres all have
dimension `d` admits a finite-type approximation diagram whose approximating
morphism also has every fibre of dimension `d`. -/
@[stacks 05FJ] #check
  (AlgebraicGeometry.FiniteTypeApproximationDiagram.exists_isPullback_of_fiberDimension_eq :
    ∀ {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
      (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
      (d : ℕ), (∀ s : S, f.fiberDimension s = (d : WithBot ℕ∞)) →
        ∃ (S₀ : Scheme.{u}) (_ : IsAffine S₀) (π : S ⟶ S₀)
          (_ : Scheme.Hom.FiniteType (specULiftZIsTerminal.from S₀))
          (D : FiniteTypeApproximationDiagram f π) (_ : IsAffine D.W)
          (_ : Scheme.Hom.FiniteType D.toSi),
          IsPullback D.toW f D.toSi π ∧
            ∀ s₀ : S₀, D.toSi.fiberDimension s₀ = (d : WithBot ℕ∞))

end AlgebraicGeometry.FiniteTypeApproximationDiagram
