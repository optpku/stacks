module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Lemma_100_11_1_Flat

/-!
# Representability of morphisms of algebraic stacks on one fppf covering

A morphism of algebraic stacks is representable by algebraic spaces if and only
if the 2-fibre product against one algebraic-space covering that is surjective,
flat, and locally of finite presentation is an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 100.3.1: Let `f : X ⟶ Y` be a morphism of algebraic stacks. Let `W`
be an algebraic space and let `g : W.toGroupoids ⟶ Y` be surjective, locally of
finite presentation, and flat. Then `f` is representable by algebraic spaces if
and only if the 2-fibre product `TwoFibreProduct.apex g f` is an algebraic
space. -/
@[stacks 04ZP]
theorem relativelyRepresentableByAlgebraicSpaces_iff_of_covering
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g] :
    relativelyRepresentableByAlgebraicSpaces f ↔
      IsRepresentableByAlgebraicSpace
        (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f) :=
  sorry

/-- If the 2-fibre product of `g : W.toGroupoids ⟶ Y` against `f` is an algebraic
space, then `f` is representable by algebraic spaces. -/
theorem relativelyRepresentableByAlgebraicSpaces_of_covering
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g] :
    IsRepresentableByAlgebraicSpace
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f) →
      relativelyRepresentableByAlgebraicSpaces f :=
  sorry

/-- If `f` is representable by algebraic spaces, then the 2-fibre product of
`g : W.toGroupoids ⟶ Y` against `f` is an algebraic space. -/
theorem relativelyRepresentableByAlgebraicSpaces_covering_spec
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g] :
    relativelyRepresentableByAlgebraicSpaces f →
      IsRepresentableByAlgebraicSpace
        (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
