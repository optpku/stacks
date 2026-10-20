/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Affine
import ReasLib.AlgebraicGeometry.Scheme.Limit.Constructible
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.GeometricallyConnected
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.ConnectedComponents

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FiniteTypeApproximationDiagram

/-- An affine finitely presented morphism with geometrically connected fibres is obtained by
base change from a geometrically connected finite-type morphism between affine schemes over
`Spec ℤ`. -/
theorem exists_isPullback_of_geometricallyConnected
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) [Scheme.Hom.FinitePresentation f] [GeometricallyConnected f] :
    ∃ (S₀ : Scheme.{u}) (_ : IsAffine S₀) (π : S ⟶ S₀)
      (_ : Scheme.Hom.FiniteType (specULiftZIsTerminal.from S₀))
      (D : FiniteTypeApproximationDiagram f π) (_ : IsAffine D.W)
      (_ : Scheme.Hom.FiniteType D.toSi) (_ : GeometricallyConnected D.toSi),
      IsPullback D.toW f D.toSi π := sorry

end AlgebraicGeometry.FiniteTypeApproximationDiagram
