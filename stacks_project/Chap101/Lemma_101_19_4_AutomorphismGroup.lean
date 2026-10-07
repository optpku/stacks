module

public import stacks_project.Chap101.Lemma_101_19_2_AutomorphismGroup

/-!
# Isomorphisms of automorphism-group algebraic spaces along a morphism

A morphism `f : X ⟶ Y` of algebraic stacks induces the Isom comparison
`Isom_X(p, p) ⟶ Isom_Y(p ≫ f, p ≫ f)` on the automorphism group algebraic
space of a field-valued point `p`. This map is an isomorphism of algebraic
spaces when it has the `isomorphisms` morphism property in the sense of
scheme-slice tests.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace automorphismGroup

/-- The comparison `G_p ⟶ G_{p ≫ f}` of automorphism group algebraic spaces
induced by a morphism of algebraic stacks is an isomorphism. -/
def IsIsoMap {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) (p : FieldValuedPoint X) : Prop :=
  Groupoids.Hom.has (MorphismProperty.isomorphisms (AlgebraicSpace S))
    (isomComparison f p.toHom p.toHom)

/-- `IsIsoMap f p` means that the Isom comparison of automorphism groups along
`f` at `p` has the isomorphisms morphism property of algebraic spaces. -/
theorem IsIsoMap_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (p : FieldValuedPoint X) :
    IsIsoMap f p ↔
      Groupoids.Hom.has (MorphismProperty.isomorphisms (AlgebraicSpace S))
        (isomComparison f p.toHom p.toHom) :=
  sorry

namespace IsIsoMap

/-- If the automorphism-group comparison along `f` at `p` is an isomorphism,
then the underlying Isom comparison has the isomorphisms morphism property. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] {f : X ⟶ Y} {p : FieldValuedPoint X} :
    IsIsoMap f p →
      Groupoids.Hom.has (MorphismProperty.isomorphisms (AlgebraicSpace S))
        (isomComparison f p.toHom p.toHom) :=
  sorry

/-- The automorphism-group comparison along `f` at `p` is an isomorphism if the
underlying Isom comparison has the isomorphisms morphism property. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] {f : X ⟶ Y} {p : FieldValuedPoint X} :
    Groupoids.Hom.has (MorphismProperty.isomorphisms (AlgebraicSpace S))
        (isomComparison f p.toHom p.toHom) →
      IsIsoMap f p :=
  sorry

end IsIsoMap

end automorphismGroup

end AlgebraicGeometry.AlgebraicStack
