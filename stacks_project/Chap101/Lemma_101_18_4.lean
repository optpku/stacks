/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteTypePoints
import StacksCheckRecall

/-!
# Images of finite type points under locally finite type morphisms

A locally-of-finite-type morphism of algebraic stacks sends finite-type points
to finite-type points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType

/- Lemma 101.18.4: Let `f : X ⟶ Y` be a morphism of algebraic stacks. If `f`
is locally of finite type, then
`Points.map f '' finiteTypePoints X ⊆ finiteTypePoints Y`. -/
@[stacks 06G0] #check
  (AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType.image_finiteTypePoints_subset :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [LocallyOfFiniteType f],
      Points.map f '' finiteTypePoints X ⊆ finiteTypePoints Y)

/- A locally-of-finite-type morphism of algebraic stacks sends finite-type
points to finite-type points. -/
#check (AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType.map_mem_finiteTypePoints :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [LocallyOfFiniteType f]
    {x : Points X} (hx : x ∈ finiteTypePoints X),
    Points.map f x ∈ finiteTypePoints Y)

end AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
