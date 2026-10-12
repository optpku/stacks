/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Affine
import ReasLib.AlgebraicGeometry.Scheme.Limit.Constructible
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.GeometricallyReduced.Constructible

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FiniteTypeApproximationDiagram

/-- An affine finitely presented morphism with geometrically reduced fibres is obtained by
base change from a geometrically reduced finite-type morphism between affine schemes over
`Spec ℤ`. -/
theorem exists_isPullback_of_geometricallyReduced
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) [Scheme.Hom.FinitePresentation f] [GeometricallyReduced f] :
    ∃ (S₀ : Scheme.{u}) (_ : IsAffine S₀) (π : S ⟶ S₀)
      (_ : Scheme.Hom.FiniteType (specULiftZIsTerminal.from S₀))
      (D : FiniteTypeApproximationDiagram f π) (_ : IsAffine D.W)
      (_ : Scheme.Hom.FiniteType D.toSi) (_ : GeometricallyReduced D.toSi),
      IsPullback D.toW f D.toSi π := sorry

end AlgebraicGeometry.FiniteTypeApproximationDiagram
