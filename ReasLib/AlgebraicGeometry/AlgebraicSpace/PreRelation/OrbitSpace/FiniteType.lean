/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.OrbitSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.OrbitMap
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- An invariant morphism for a pre-relation whose two spaces are locally of finite type
over the base is an orbit space if and only if the natural quotient map on geometric
points is bijective for every geometric point of the base. -/
@[stacks 04A0]
theorem isOrbitSpace_iff_bijective_weaklyEquivalentQuotMap
    {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B} (P : PreRelation U)
    {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    [LocallyOfFiniteType U.hom] [LocallyOfFiniteType P.left.hom] :
    P.IsOrbitSpace φ ↔
      ∀ kbar : GeometricPoint B, Function.Bijective (P.weaklyEquivalentQuotMap hφ kbar) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
