module

public import stacks_project.Chap101.Lemma_101_26_1

/-!
# Flatness at a point for morphisms of algebraic stacks

A morphism of algebraic stacks is flat at a source point when the equivalent
test-square conditions of Lemma 101.26.1 hold.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism `f : X ⟶ Y` of algebraic stacks is flat at a point `x` of
`Points X` when some 2-commutative algebraic-space test square over `f`
through a germ mapping to `x`, with flat target atlas and flat comparison,
has top arrow flat at that germ. -/
def FlatAt {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (x : Points X) : Prop :=
  existsFlatAtPointSquare f x

/-- `FlatAt f x` is the existence of a flat-at-a-point test square through `x`
whose top arrow is flat at the chosen point. -/
theorem flatAt_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (x : Points X) :
    FlatAt f x ↔ existsFlatAtPointSquare f x :=
  sorry

namespace FlatAt

/-- A flat-at-a-point test square through `x` whose top arrow is flat at `u`
witnesses `FlatAt f x`. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} {x : Points X}
    {U V : AlgebraicSpace S} (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
    (h : U ⟶ V) (u : AlgebraicSpace.Points U)
    (hsq : IsFlatAtPointSquare f a b h) (hx : Points.mapSpace a u = x)
    (hh : AlgebraicSpace.FlatAt h u) : FlatAt f x :=
  sorry

/-- A morphism that is flat at `x` admits a flat-at-a-point test square
through `x` whose top arrow is flat at the chosen point. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} {x : Points X}
    (hf : FlatAt f x) :
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V) (u : AlgebraicSpace.Points U),
      IsFlatAtPointSquare f a b h ∧ Points.mapSpace a u = x ∧
        AlgebraicSpace.FlatAt h u :=
  sorry

end FlatAt

/-- Flatness at a point is equivalent to the universal test-square condition
that every 2-commutative algebraic-space square over `f` through `x` with
flat target atlas and flat comparison has top arrow flat at the chosen
point. -/
theorem flatAt_iff_forall {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (x : Points X) :
    FlatAt f x ↔ forallFlatAtPointSquare f x :=
  sorry

end AlgebraicGeometry.AlgebraicStack
