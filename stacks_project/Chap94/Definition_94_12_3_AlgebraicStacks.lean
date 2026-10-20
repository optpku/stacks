/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Bicategory
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
import StacksCheckRecall

/-!
# The 2-category of algebraic stacks

The 2-category of algebraic stacks over a scheme `S` is the full sub-2-category
of categories fibred in groupoids over `(Sch/S)_fppf` whose objects are
algebraic stacks over `S`. All ambient 1-morphisms and 2-morphisms are
retained.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/- Definition 94.12.3: algebraic stacks over a scheme form the full sub-2-category
of categories fibred in groupoids on the objects satisfying `AlgebraicStack`. -/
@[stacks 03YP] #check (AlgebraicGeometry.AlgebraicStacks : Scheme.{u} → Type (u + 2))

namespace AlgebraicStacks

#check (AlgebraicGeometry.AlgebraicStacks.of :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], AlgebraicStacks S)

#check (AlgebraicGeometry.AlgebraicStacks.toGroupoids :
  ∀ {S : Scheme.{u}}, AlgebraicStacks S → GroupoidsOver S)

#check (AlgebraicGeometry.AlgebraicStacks.ι :
  ∀ (S : Scheme.{u}), StrictPseudofunctor (AlgebraicStacks S) (GroupoidsOver S))

#check (AlgebraicGeometry.AlgebraicStacks.eq :
  ∀ (S : Scheme.{u}),
    AlgebraicStacks S = (AlgebraicStack.objectProperty S).FullSubbicategory)

#check (AlgebraicGeometry.AlgebraicStacks.mem :
  ∀ {S : Scheme.{u}} (X : AlgebraicStacks S), AlgebraicStack (toGroupoids X))

#check (AlgebraicGeometry.AlgebraicStacks.of_toGroupoids :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    toGroupoids (of X) = X)

#check (AlgebraicGeometry.AlgebraicStacks.ι_obj :
  ∀ {S : Scheme.{u}} (X : AlgebraicStacks S), (ι S).obj X = toGroupoids X)

#check (AlgebraicGeometry.AlgebraicStacks.locallyGroupoid :
  ∀ {S : Scheme.{u}}, Bicategory.IsLocallyGroupoid (AlgebraicStacks S))

#check (AlgebraicGeometry.AlgebraicStacks.toBased :
  ∀ (S : Scheme.{u}),
    StrictPseudofunctor (AlgebraicStacks S) (BasedCategory.{u, u + 1} (Over S)))

#check (AlgebraicGeometry.AlgebraicStacks.toBased_eq :
  ∀ (S : Scheme.{u}),
    toBased S =
      (ι S).comp (FiberedCategoryOver.Groupoids.toBased.{u + 1, u, u + 1, u} (Over S)))

end AlgebraicStacks

end AlgebraicGeometry
