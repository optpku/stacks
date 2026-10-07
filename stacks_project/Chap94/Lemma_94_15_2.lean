module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber

/-!
# Faithfulness of morphisms of algebraic stacks

A 1-morphism of algebraic stacks over a scheme `S` is representable by
algebraic spaces if and only if it is faithful, equivalently if and only if
every fibre functor is faithful.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 94.15.2 (1): let `S` be a scheme contained in `Sch_fppf`. Let
`f : X ⟶ Y` be a 1-morphism of algebraic stacks over `S`. Then for every
object `U` of `(Sch/S)_fppf` the fibre functor
`fiberFunctor f U : X.p.Fiber U ⥤ Y.p.Fiber U` is faithful if and only if
the functor `f` is faithful, i.e. `(toBasedFunctor f).Faithful`. -/
@[stacks 04Y5]
theorem fiberwiseFaithful_iff_faithful {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    (∀ U : Over S, (fiberFunctor f U).Faithful) ↔ (toBasedFunctor f).Faithful :=
  sorry

/-- Lemma 94.15.2 (2): let `S` be a scheme contained in `Sch_fppf`. Let
`f : X ⟶ Y` be a 1-morphism of algebraic stacks over `S`. Then `f` is
representable by algebraic spaces if and only if for every object `U` of
`(Sch/S)_fppf` the fibre functor
`fiberFunctor f U : X.p.Fiber U ⥤ Y.p.Fiber U` is faithful. -/
@[stacks 04Y5]
theorem relativelyRepresentableByAlgebraicSpaces_iff_fiberwiseFaithful
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    relativelyRepresentableByAlgebraicSpaces f ↔
      ∀ U : Over S, (fiberFunctor f U).Faithful :=
  sorry

/-- Lemma 94.15.2 (3): let `S` be a scheme contained in `Sch_fppf`. Let
`f : X ⟶ Y` be a 1-morphism of algebraic stacks over `S`. Then `f` is
representable by algebraic spaces if and only if the functor `f` is faithful,
i.e. `(toBasedFunctor f).Faithful`. -/
@[stacks 04Y5]
theorem relativelyRepresentableByAlgebraicSpaces_iff_faithful
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    relativelyRepresentableByAlgebraicSpaces f ↔ (toBasedFunctor f).Faithful :=
  sorry

/-- A faithful 1-morphism of algebraic stacks over `S` is representable by
algebraic spaces. -/
theorem relativelyRepresentableByAlgebraicSpaces_of_faithful
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (hf : (toBasedFunctor f).Faithful) :
    relativelyRepresentableByAlgebraicSpaces f :=
  sorry

/-- A 1-morphism of algebraic stacks over `S` that is faithful on every fibre
is representable by algebraic spaces. -/
theorem relativelyRepresentableByAlgebraicSpaces_of_fiberwiseFaithful
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (hU : ∀ U : Over S, (fiberFunctor f U).Faithful) :
    relativelyRepresentableByAlgebraicSpaces f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
