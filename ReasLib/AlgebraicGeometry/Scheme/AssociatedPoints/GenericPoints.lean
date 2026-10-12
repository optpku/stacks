/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AssociatedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Support

/-!
# Generic and associated points of schemes

This file relates generic points of irreducible components to associated points of the
structure sheaf.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X]

/-- Every generic point of an irreducible component of a locally Noetherian scheme is an
associated point of its structure sheaf. -/
theorem genericPoints_subset_associatedPoints :
    genericPoints X ⊆ X.associatedPoints := sorry

end AlgebraicGeometry.Scheme
