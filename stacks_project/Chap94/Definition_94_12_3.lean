module

public import stacks_project.Chap94.Definition_94_12_3_AlgebraicStacks
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

variable (S : Scheme.{u})

/- Definition 94.12.3 (1): the 2-category of algebraic stacks over a scheme `S`
contained in `Sch_fppf` is the full sub-2-category of categories fibred in
groupoids over `(Sch/S)_fppf` whose objects are algebraic stacks over `S`. -/
@[stacks 03YP] #check (AlgebraicStacks S)

/- Definition 94.12.3 (2): a 1-morphism `X ⟶ Y` in `AlgebraicStacks S` is any
functor of categories over `(Sch/S)_fppf`, as in Categories, Definition 4.32.1. -/
@[stacks 03YP] #check (fun (X Y : AlgebraicStacks S) ↦ (X ⟶ Y))

variable {X Y : AlgebraicStacks S} (F G : X ⟶ Y)

/- Definition 94.12.3 (3): a 2-morphism in `AlgebraicStacks S` is a transformation
between functors over `(Sch/S)_fppf`, as in Categories, Definition 4.32.1. -/
@[stacks 03YP] #check (F ⟶ G)

/- The 2-category of algebraic stacks over `S` is a (2,1)-category: every
2-morphism is an isomorphism. -/
@[stacks 03YP] #check (inferInstance : Bicategory.IsLocallyGroupoid (AlgebraicStacks S))
