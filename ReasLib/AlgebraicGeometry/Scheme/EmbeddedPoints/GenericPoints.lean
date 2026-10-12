/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AssociatedPoints.GenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.EmbeddedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.FiniteGeneration
public import ReasLib.AlgebraicGeometry.Scheme.WeaklyAssociatedPoints

/-!
# Embedded and generic points of schemes

This file characterizes embedded points of a locally Noetherian scheme using
its associated and generic points.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A point of a locally Noetherian scheme is embedded exactly when it is associated but is not
a generic point of an irreducible component. -/
theorem embeddedPoint_iff_mem_associatedPoints_and_not_mem_genericPoints
    (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) :
    X.embeddedPoint x ↔
      x ∈ X.associatedPoints ∧
        x ∉ genericPoints X := sorry

/-- If a locally Noetherian scheme has no embedded points, each weakly associated point is the
generic point of an irreducible component. -/
theorem weakAss_subset_genericPoints_of_embeddedPoints_eq_empty
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hembedded : X.embeddedPoints = (∅ : Set X)) :
    X.weakAss ⊆ genericPoints X := sorry

end AlgebraicGeometry.Scheme
