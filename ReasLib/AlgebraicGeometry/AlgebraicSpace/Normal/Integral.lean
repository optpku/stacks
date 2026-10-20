/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Normal integral affine étale charts

A point of a normal integral algebraic space is in the image of an étale morphism
from a normal integral affine scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every point of a normal integral algebraic space over a scheme lies in the
image of an étale morphism from a normal integral affine scheme over the same base. -/
@[stacks 0AYH]
theorem exists_isAffine_isNormal_isIntegral_etale {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsNormal X] [IsIntegral X] (x : Points X) :
    ∃ (U : Over S) (f : ofOver U ⟶ X) (u : U.left),
      AlgebraicGeometry.IsAffine U.left ∧ Scheme.isNormal U.left ∧
        AlgebraicGeometry.IsIntegral U.left ∧ Etale f ∧
          Points.mapOfOver f u = x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
