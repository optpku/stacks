module

public import stacks_project.Chap67.Lemma_67_25_4_FiniteTypePoint

/-!
# Images of finite type points under locally finite type morphisms

A locally-of-finite-type morphism of algebraic spaces sends finite-type points
to finite-type points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType

/-- Lemma 67.25.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is locally of finite type, then
`Points.map f '' finiteTypePoints X ⊆ finiteTypePoints Y`. -/
@[stacks 06EI]
theorem image_finiteTypePoints_subset {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] :
    Points.map f '' finiteTypePoints X ⊆ finiteTypePoints Y :=
  sorry

/-- A locally-of-finite-type morphism of algebraic spaces sends finite-type
points to finite-type points. -/
theorem map_mem_finiteTypePoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] {x : Points X}
    (hx : x ∈ finiteTypePoints X) :
    Points.map f x ∈ finiteTypePoints Y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType
