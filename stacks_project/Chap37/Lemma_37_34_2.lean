/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Module
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FiniteTypeApproximationDiagram

/- Lemma 37.34.2: an affine finitely presented morphism `f : X ⟶ S` and a finitely
presented module `ℱ` on `X` admit a finite-type approximation diagram together with a
coherent module `ℱ₀` whose pullback along `D.toW` is isomorphic to `ℱ`. -/
@[stacks 05FC]
#check (AlgebraicGeometry.FiniteTypeApproximationDiagram.exists_isPullback_with_coherent :
  ∀ {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
    (ℱ : X.Modules) [ℱ.IsFinitePresentation],
    ∃ (S₀ : Scheme.{u}) (_ : IsAffine S₀) (π : S ⟶ S₀)
      (_ : Scheme.Hom.FiniteType (specULiftZIsTerminal.from S₀))
      (D : FiniteTypeApproximationDiagram f π) (_ : IsAffine D.W)
      (_ : Scheme.Hom.FiniteType D.toSi) (ℱ₀ : D.W.Modules) (_ : ℱ₀.IsCoherent),
      IsPullback D.toW f D.toSi π ∧
        Nonempty ((Scheme.Modules.pullback D.toW).obj ℱ₀ ≅ ℱ))

end AlgebraicGeometry.FiniteTypeApproximationDiagram
