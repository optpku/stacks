module

public import stacks_project.Chap100.Definition_100_4_2_Points

/-!
# Surjective morphisms of algebraic stacks

A morphism of algebraic stacks is surjective when the induced map of
associated point spaces is surjective. This extends the representable-by-algebraic-spaces
notion, without requiring representability of the morphism itself.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks is surjective if the induced map of associated
point spaces is surjective. -/
@[mk_iff]
class Surjective {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) : Prop where
  /-- The induced map on points is surjective. -/
  map_surjective : Function.Surjective (Points.map f)

namespace Surjective

/-- The identity morphism of an algebraic stack is surjective. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] : Surjective (𝟙 X) :=
  sorry

/-- A surjective morphism of algebraic stacks induces a surjective map of associated
point spaces. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Surjective f] : Function.Surjective (Points.map f) :=
  sorry

/-- A morphism of algebraic stacks is surjective as soon as the induced map of
associated point spaces is surjective. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    {f : X ⟶ Y} (hf : Function.Surjective (Points.map f)) : Surjective f :=
  sorry

/-- A 1-morphism of algebraic stacks which is surjective in the sense of relative
representability by algebraic spaces is surjective as a morphism of algebraic stacks. -/
instance of_groupoidsHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Groupoids.Hom.Surjective f] :
    Surjective f :=
  sorry

/-- An isomorphism of algebraic stacks is surjective. -/
instance of_isIso {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [IsIso f] : Surjective f :=
  sorry

end Surjective

end AlgebraicGeometry.AlgebraicStack
