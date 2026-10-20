module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Bicategory
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Definition 94.12.3 (1): the 2-category of algebraic stacks over a scheme `S`
contained in `Sch_fppf` is the full sub-2-category of categories fibred in
groupoids over `(Sch/S)_fppf` whose objects are algebraic stacks over `S`. -/
@[stacks 03YP] #check (AlgebraicGeometry.AlgebraicStacks : Scheme.{u} → Type (u + 2))

/- Definition 94.12.3 (2): a 1-morphism `X ⟶ Y` in `AlgebraicStacks S` is any
functor of categories over `(Sch/S)_fppf`, as in Categories, Definition 4.32.1. -/
@[stacks 03YP] #check (AlgebraicGeometry.AlgebraicStacks.ι :
  ∀ (S : Scheme.{u}), StrictPseudofunctor (AlgebraicStacks S) (GroupoidsOver S))

/- Definition 94.12.3 (3): a 2-morphism in `AlgebraicStacks S` is a transformation
between functors over `(Sch/S)_fppf`, as in Categories, Definition 4.32.1. -/
@[stacks 03YP] #check (AlgebraicGeometry.AlgebraicStacks.toBased :
  ∀ (S : Scheme.{u}),
    StrictPseudofunctor (AlgebraicStacks S) (BasedCategory.{u, u + 1} (Over S)))

/- The 2-category of algebraic stacks over `S` is a (2,1)-category: every
2-morphism is an isomorphism. -/
#check (AlgebraicGeometry.AlgebraicStacks.locallyGroupoid :
  ∀ {S : Scheme.{u}}, Bicategory.IsLocallyGroupoid (AlgebraicStacks S))
