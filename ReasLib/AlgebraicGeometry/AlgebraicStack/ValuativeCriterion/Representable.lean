/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack
namespace ValuativeCriterion.Existence

/-- A morphism of algebraic stacks representable by algebraic spaces satisfies
the existence part of the valuative criterion if and only if every scheme-slice
representing morphism of algebraic spaces satisfies that criterion. -/
theorem iff_has {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    Existence f ↔
      Groupoids.Hom.has (@AlgebraicSpace.ValuativeCriterion.Existence S) f :=
  sorry

end ValuativeCriterion.Existence
end AlgebraicGeometry.AlgebraicStack
