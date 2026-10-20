/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Specialization.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyCatenary
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.RelativeFunction

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- A locally finite-type morphism from a decent algebraic space to a universally
catenary algebraic space pulls a dimension function back to a dimension function
after adding the residue-field transcendence degree. -/
instance instIsDimensionFunction_relativeDimensionFunction {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] (f : X ⟶ B) [IsDecent X]
    [LocallyOfFiniteType f] (δ : Points B → ℤ) [IsDimensionFunction δ] :
    IsDimensionFunction ((relativeDimensionFunction f) δ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
