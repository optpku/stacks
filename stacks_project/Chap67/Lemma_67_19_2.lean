module

public import Mathlib.Data.List.TFAE
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_19_1_FieldPoints
public import stacks_project.Chap67.Lemma_67_19_5_UniversallyInjective

/-!
# Characterizations of universally injective morphisms of algebraic spaces

A morphism of algebraic spaces is universally injective iff it is injective on
field-valued points iff its relative diagonal is surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace UniversallyInjective

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Lemma 67.19.2: for a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `injectiveOnFieldPoints f`,
`UniversallyInjective f`, and `Surjective (pullback.diagonal f)`. -/
@[stacks 040X]
theorem tfae (f : X ⟶ Y) :
    List.TFAE [injectiveOnFieldPoints f, UniversallyInjective f,
      Surjective (pullback.diagonal f)] :=
  sorry

/-- A morphism of algebraic spaces is universally injective if and only if it is
injective on field-valued points. -/
theorem iff_injectiveOnFieldPoints (f : X ⟶ Y) :
    UniversallyInjective f ↔ injectiveOnFieldPoints f :=
  sorry

/-- A morphism of algebraic spaces is universally injective if and only if its
relative diagonal is surjective. -/
theorem iff_diagonal (f : X ⟶ Y) :
    UniversallyInjective f ↔ Surjective (pullback.diagonal f) :=
  sorry

/-- The relative diagonal of a universally injective morphism of algebraic spaces
is surjective. -/
instance surjective_diagonal {f : X ⟶ Y} [UniversallyInjective f] :
    Surjective (pullback.diagonal f) :=
  sorry

end UniversallyInjective

end AlgebraicGeometry.AlgebraicSpace
