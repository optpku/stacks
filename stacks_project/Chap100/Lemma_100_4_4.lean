module

public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty

/-!
# Points-map characterization of surjective representable morphisms

A morphism of algebraic stacks representable by algebraic spaces is surjective
in the sense of Section 100.3 if and only if the induced map of points is
surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace Surjective

/-- Lemma 100.4.4: Let `f : X ⟶ Y` be a morphism of algebraic stacks which is
representable by algebraic spaces. Then `Points.map f : Points X → Points Y` is
surjective if and only if `f` is surjective in the sense of Section 100.3. -/
@[stacks 04XI]
theorem iff_map {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    Surjective f ↔ Function.Surjective (AlgebraicStack.Points.map f) :=
  sorry

/-- If a morphism of algebraic stacks representable by algebraic spaces induces a
surjective map of points, then it is surjective in the sense of Section 100.3. -/
theorem of_map {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    (h : Function.Surjective (AlgebraicStack.Points.map f)) :
    Surjective f :=
  sorry

/-- A 1-morphism of algebraic stacks which is surjective in the sense of
Section 100.3 induces a surjective map of points. -/
theorem map_surjective {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Surjective f] :
    Function.Surjective (AlgebraicStack.Points.map f) :=
  sorry

/-- A morphism of algebraic stacks representable by algebraic spaces has the
algebraic-space surjectivity property on scheme-slice representing morphisms if
and only if the induced map of points is surjective. -/
theorem has_iff_map {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.Surjective S) f ↔
      Function.Surjective (AlgebraicStack.Points.map f) :=
  sorry

end Surjective

end AlgebraicGeometry.Groupoids.Hom
