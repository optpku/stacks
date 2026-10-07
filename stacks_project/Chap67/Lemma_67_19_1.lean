module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap67.Lemma_67_19_1_FieldPoints

/-!
# Universally injective representable morphisms of algebraic spaces

A representable morphism of algebraic spaces is universally injective in the
sense of Section 67.3 if and only if it is injective on field-valued points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.19.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a representable
morphism of algebraic spaces over `S`. Then `f` is universally injective in the
sense of Section 67.3 if and only if for all fields `K` the map `X(K) → Y(K)` is
injective. -/
@[stacks 03MU]
theorem universallyInjective_presheaf_iff_injectiveOnFieldPoints
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.UniversallyInjective : MorphismProperty Scheme.{u})).presheaf f ↔
      injectiveOnFieldPoints f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
