module

public import stacks_project.Chap101.Lemma_101_18_4_FiniteTypePoint

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

/-- Lemma 101.18.4: Let `f : X ⟶ Y` be a morphism of algebraic stacks. If `f`
is locally of finite type, then
`Points.map f '' finiteTypePoints X ⊆ finiteTypePoints Y`. -/
@[stacks 06G0]
theorem image_finiteTypePoints_subset {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [LocallyOfFiniteType f] :
    Points.map f '' finiteTypePoints X ⊆ finiteTypePoints Y :=
  sorry

/-- A locally-of-finite-type morphism of algebraic stacks sends finite-type
points to finite-type points. -/
theorem map_mem_finiteTypePoints {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [LocallyOfFiniteType f]
    {x : Points X} (hx : x ∈ finiteTypePoints X) :
    Points.map f x ∈ finiteTypePoints Y :=
  sorry

end AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
