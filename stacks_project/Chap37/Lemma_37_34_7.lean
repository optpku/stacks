/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.GeometricallyIrreducible
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FiniteTypeApproximationDiagram

/- Lemma 37.34.7: an affine finitely presented morphism `f : X ⟶ S` with geometrically
irreducible fibres is obtained from a geometrically irreducible finite-type morphism
`D.toSi : D.W ⟶ S₀` between affine schemes by a cartesian square, where `S₀` is of
finite type over `Spec ℤ`. -/
@[stacks 05FH] #check
  (AlgebraicGeometry.FiniteTypeApproximationDiagram.exists_isPullback_of_geometricallyIrreducible :
    ∀ {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
      (f : X ⟶ S) [Scheme.Hom.FinitePresentation f] [GeometricallyIrreducible f],
      ∃ (S₀ : Scheme.{u}) (_ : IsAffine S₀) (π : S ⟶ S₀)
        (_ : Scheme.Hom.FiniteType (specULiftZIsTerminal.from S₀))
        (D : FiniteTypeApproximationDiagram f π) (_ : IsAffine D.W)
        (_ : Scheme.Hom.FiniteType D.toSi) (_ : GeometricallyIrreducible D.toSi),
        IsPullback D.toW f D.toSi π)

end AlgebraicGeometry.FiniteTypeApproximationDiagram
