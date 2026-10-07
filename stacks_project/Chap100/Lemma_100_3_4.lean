module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap73.Lemma_73_7_3_Precoverage
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty
public import stacks_project.Chap100.Lemma_100_11_1_Flat

/-!
# Testing representable morphisms of algebraic stacks on a stacky fppf covering

A property of morphisms of algebraic spaces that is fppf local on the target
and stable under base change may be tested on the 2-fibre-product projection
of one representable, surjective, flat, locally of finite presentation base
change of a morphism of algebraic stacks representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Lemma 100.3.4: Let `P` be a property of morphisms of algebraic spaces that
is fppf local on the target and stable under base change. Let `f : X ⟶ Y` be a
morphism of algebraic stacks representable by algebraic spaces. Let
`g : Z ⟶ Y` be a morphism of algebraic stacks which is representable by
algebraic spaces, surjective, flat, and locally of finite presentation. Set
`W = Z ×_Y X`. Then `f` has `P` if and only if the projection
`TwoFibreProduct.fst g f : W ⟶ Z` has `P`. -/
@[stacks 06TY]
theorem has_iff_of_weak_covering {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f)
    (g : Z ⟶ Y) [Surjective g] [Flat g] [LocallyOfFinitePresentation g] :
    has P f ↔ has P (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f) :=
  sorry

namespace has

/-- If the 2-fibre-product projection of `f` along a representable, surjective,
flat, locally of finite presentation morphism of algebraic stacks has `P`, then
`f` has `P`. -/
theorem of_weak_covering {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f)
    (g : Z ⟶ Y) [Surjective g] [Flat g] [LocallyOfFinitePresentation g] :
    has P (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f) → has P f :=
  sorry

/-- If `f` has `P`, then the 2-fibre-product projection of `f` along a
representable, surjective, flat, locally of finite presentation morphism of
algebraic stacks has `P`. -/
theorem weak_covering_spec {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f)
    (g : Z ⟶ Y) [Surjective g] [Flat g] [LocallyOfFinitePresentation g] :
    has P f → has P (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f) :=
  sorry

end has

end AlgebraicGeometry.Groupoids.Hom
