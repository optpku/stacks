/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace AffineOpenCover

/-- An algebraic space has an affine open cover of cardinality t if it is the
union of t affine open subspaces. -/
def HasCard {S : Scheme.{u}} (X : AlgebraicSpace S) (t : ℕ) : Prop :=
  ∃ U : Fin t → OpenSubspace X, (∀ i, IsAffine (U i).X) ∧ ⋃ i, (U i).pointsSet = Set.univ

/-- HasCard X t is a cover of X by t affine open subspaces. -/
theorem hasCard_iff {S : Scheme.{u}} (X : AlgebraicSpace S) (t : ℕ) :
    HasCard X t ↔
      ∃ U : Fin t → OpenSubspace X,
        (∀ i, IsAffine (U i).X) ∧ ⋃ i, (U i).pointsSet = Set.univ := sorry

end AffineOpenCover

end AlgebraicGeometry.AlgebraicSpace
