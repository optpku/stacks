module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Monomorphism
import StacksCheckRecall

/-!
# Representable monomorphisms are fibrewise fully faithful

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces and a monomorphism in the sense of
Definition 94.10.1 is fully faithful on fibre categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/- Lemma 94.10.10: let `S` be a scheme contained in `Sch_fppf`. Let
`j : X ⟶ Y` be a 1-morphism of categories fibred in groupoids over
`(Sch/S)_fppf`. Assume `j` is representable by algebraic spaces and a
monomorphism in the sense of Definition 94.10.1, so
`has (MorphismProperty.monomorphisms (AlgebraicSpace S)) j`
(Descent on Spaces, Lemma 74.11.30 is why monomorphism is an admissible `P`).
Then `j` is fully faithful on fibre categories: for every `U : Over S` the
fibre functor `fiberFunctor j U` is `Full` and `Faithful`. -/
@[stacks 05UK] #check (AlgebraicGeometry.Groupoids.Hom.has.fiberwiseFullyFaithful :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} {j : X ⟶ Y},
    relativelyRepresentableByAlgebraicSpaces j →
    AlgebraicGeometry.Groupoids.Hom.has
      (MorphismProperty.monomorphisms (AlgebraicSpace S)) j →
    ∀ U : Over S, (fiberFunctor j U).Full ∧ (fiberFunctor j U).Faithful)

end AlgebraicGeometry.Groupoids.Hom
