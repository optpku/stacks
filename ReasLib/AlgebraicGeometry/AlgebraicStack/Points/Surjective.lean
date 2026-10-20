module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property

/-!
# Points-map characterization of surjective representable morphisms

A morphism of algebraic stacks representable by algebraic spaces is surjective
if and only if the induced map of points is surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace Surjective

/-- A morphism of algebraic stacks representable by algebraic spaces is
surjective if and only if its induced map of points is surjective. -/
theorem iff_map {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    Surjective f ↔ Function.Surjective (AlgebraicStack.Points.map f) :=
  sorry

/-- A morphism of algebraic stacks representable by algebraic spaces is
surjective whenever its induced map of points is surjective. -/
theorem of_map {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    (h : Function.Surjective (AlgebraicStack.Points.map f)) :
    Surjective f :=
  (iff_map hf).mpr h

/-- A surjective morphism of algebraic stacks representable by algebraic
spaces induces a surjective map of points. -/
theorem map_surjective {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Surjective f] :
    Function.Surjective (AlgebraicStack.Points.map f) :=
  (iff_map (relativelyRepresentable f)).mp inferInstance

/-- A morphism of algebraic stacks representable by algebraic spaces has
surjective scheme-slice representing morphisms if and only if its induced map
of points is surjective. -/
theorem has_iff_map {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.Surjective S) f ↔
      Function.Surjective (AlgebraicStack.Points.map f) := by
  constructor
  · intro h
    exact (iff_map hf).mp ⟨hf, h⟩
  · intro h
    exact (of_map hf h).of_represents

end Surjective

end AlgebraicGeometry.Groupoids.Hom
