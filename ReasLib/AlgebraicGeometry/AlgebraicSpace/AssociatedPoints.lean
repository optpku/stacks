/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.WeaklyAssociatedPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedPoints.LocallyNoetherian

/-!
# Associated points of locally Noetherian algebraic spaces

The associated points of a locally Noetherian algebraic space are its weakly associated points.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- On a locally Noetherian algebraic space, the associated points of `X` are its
weakly associated points. -/
def associatedPoints [IsLocallyNoetherian X] : Set (Points X) :=
  X.weakAss

/-- On a locally Noetherian algebraic space, the associated points of `X` equal
`WeakAss(X)`. -/
theorem associatedPoints_eq_weakAss [IsLocallyNoetherian X] :
    associatedPoints X = X.weakAss :=
  rfl

/-- Membership in the associated locus of a locally Noetherian algebraic space is
membership in its weakly associated locus. -/
theorem mem_associatedPoints_iff [IsLocallyNoetherian X] (x : Points X) :
    x ∈ associatedPoints X ↔ x ∈ X.weakAss :=
  Iff.rfl

end AlgebraicGeometry.AlgebraicSpace
