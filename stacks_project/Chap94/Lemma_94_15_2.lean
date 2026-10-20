module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Representable.Faithful
import StacksCheckRecall

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

/- Lemma 94.15.2: for a morphism of algebraic stacks over a scheme, representability
by algebraic spaces, faithfulness, and faithfulness on every fibre are equivalent. -/
@[stacks 04Y5] #check
  (AlgebraicGeometry.AlgebraicStack.relativelyRepresentableByAlgebraicSpaces_iff_faithful :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
      (f : X ⟶ Y),
      relativelyRepresentableByAlgebraicSpaces f ↔ (toBasedFunctor f).Faithful)

#check
  (AlgebraicGeometry.AlgebraicStack.relativelyRepresentableByAlgebraicSpaces_iff_fiberwiseFaithful :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
      (f : X ⟶ Y),
      relativelyRepresentableByAlgebraicSpaces f ↔
        ∀ U : Over S, (fiberFunctor f U).Faithful)

section

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
variable (f : X ⟶ Y)

#check
  (CategoryTheory.FiberedCategoryOver.Groupoids.faithful_iff_fiberwise f :
    (toBasedFunctor f).Faithful ↔ ∀ U : Over S, (fiberFunctor f U).Faithful)

end

#check
  (AlgebraicGeometry.AlgebraicStack.relativelyRepresentableByAlgebraicSpaces_of_faithful :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
      (f : X ⟶ Y) (hf : (toBasedFunctor f).Faithful),
      relativelyRepresentableByAlgebraicSpaces f)

#check
  (AlgebraicGeometry.AlgebraicStack.relativelyRepresentableByAlgebraicSpaces_of_fiberwiseFaithful :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
      (f : X ⟶ Y) (hU : ∀ U : Over S, (fiberFunctor f U).Faithful),
      relativelyRepresentableByAlgebraicSpaces f)
