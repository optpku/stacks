/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiberDegree.Points
import StacksCheckRecall

/-!
# Point-fibre cardinality of universally bounded morphisms

A uniform bound on field-valued fibre degrees of a morphism from a scheme to an
algebraic space bounds the number of points in each fibre of `|U| → |X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.3.6: Let `S` be a scheme. Let `X` be an algebraic space over `S`, and let
`U` be a scheme over `S`. Let `φ : U ⟶ X` be a morphism over `S`. If the fibres of
`φ` are universally bounded, then there exists an integer `n` such that each fibre of
`|U| → |X|` has at most `n` elements. -/
@[stacks 03JQ] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_mapOfOver_fibre_encard_le_of_universallyBoundedFibres :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X),
      universallyBoundedFibres φ →
        ∃ n : ℕ, ∀ x : Points X, (Points.mapOfOver φ ⁻¹' {x}).encard ≤ n)

/- The integer bounding field-valued fibre degrees also bounds the number of points in
each fibre of the induced map `|U| → |X|`. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.degreesOfFibresBoundedBy.mapOfOver_fibre_encard_le :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} (f : ofOver U ⟶ X)
      {n : ℕ}, degreesOfFibresBoundedBy f n → ∀ x : Points X,
        (Points.mapOfOver f ⁻¹' {x}).encard ≤ n)

end AlgebraicGeometry.AlgebraicSpace
