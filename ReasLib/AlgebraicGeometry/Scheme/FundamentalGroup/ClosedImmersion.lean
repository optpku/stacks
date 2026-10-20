/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.FundamentalGroup
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {p : ℕ} [Fact p.Prime]

/-- A closed immersion of connected affine schemes over a prime field induces an injective
map on étale fundamental groups at every geometric point of the source. -/
theorem fundamentalGroupMap_injective_of_isClosedImmersion
    {Z X : SchemeOverField (ZMod p)}
    [IsAffine Z.left] [IsAffine X.left]
    [ConnectedSpace Z.left] [ConnectedSpace X.left]
    (i : Z ⟶ X) [IsClosedImmersion i.left]
    (zbar : AlgebraicGeometry.Scheme.GeometricPoint Z.left) :
    Function.Injective
      (AlgebraicGeometry.Scheme.GeometricPoint.fundamentalGroupMap i.left zbar) := sorry

end AlgebraicGeometry.SchemeOverField
