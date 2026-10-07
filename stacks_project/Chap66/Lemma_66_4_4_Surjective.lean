module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Surjectivity of morphisms from schemes to algebraic spaces

A morphism from a scheme to an algebraic space is surjective in the sense of
Spaces, Definition 65.5.1 if and only if the induced map of points is surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : ofOver T ⟶ X` from a scheme to an algebraic space is surjective in the
sense of `(MorphismProperty.over (@AlgebraicGeometry.Surjective)).presheaf` if and only if
the induced map of points `Points.map f` is surjective. -/
theorem ofOver_presheaf_surjective_iff {S : Scheme.{u}} {T : Over S} {X : AlgebraicSpace S}
    (f : ofOver T ⟶ X) :
    (MorphismProperty.over (@AlgebraicGeometry.Surjective)).presheaf f ↔
      Function.Surjective (Points.map f) :=
  sorry

/-- A morphism from a scheme to an algebraic space that is surjective in the sense of
`(MorphismProperty.over (@AlgebraicGeometry.Surjective)).presheaf` induces a surjective map
of points. -/
theorem ofOver_presheaf_surjective {S : Scheme.{u}} {T : Over S} {X : AlgebraicSpace S}
    {f : ofOver T ⟶ X} (hf : (MorphismProperty.over (@AlgebraicGeometry.Surjective)).presheaf f) :
    Function.Surjective (Points.map f) :=
  sorry

/-- If the induced map of points of a morphism from a scheme to an algebraic space is
surjective, then the morphism is surjective in the sense of
`(MorphismProperty.over (@AlgebraicGeometry.Surjective)).presheaf`. -/
theorem ofOver_presheaf_surjective_of_map {S : Scheme.{u}} {T : Over S} {X : AlgebraicSpace S}
    {f : ofOver T ⟶ X} (hf : Function.Surjective (Points.map f)) :
    (MorphismProperty.over (@AlgebraicGeometry.Surjective)).presheaf f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
