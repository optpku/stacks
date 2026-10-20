/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.AssociatedCycle

/-!
# Associated cycles of closed subspaces
-/

public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubspace

/-- The multiplicity-weighted degree-`k` cycle of a closed subspace, as a locally
finite integer function on `|X|`. -/
noncomputable def cycle {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (Y : ClosedSubspace X) (d : Points X → ℤ) (k : ℤ) :
    Function.locallyFinsupp (Points X) ℤ :=
  associatedCycle Y d k

end AlgebraicGeometry.AlgebraicSpace.ClosedSubspace
