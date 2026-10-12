/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Definition
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack

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

set_option linter.checkUnivs false in
/-- The 2-category of algebraic stacks over a scheme `S`, as the full
sub-2-category of `GroupoidsOver S` on the object property `AlgebraicStack`. -/
abbrev AlgebraicStacks (S : Scheme.{u}) :=
  (AlgebraicStack.objectProperty S).FullSubbicategory

namespace AlgebraicStacks

/-- Package a category fibred in groupoids over `(Sch/S)_fppf` that is an
algebraic stack as an object of `AlgebraicStacks S`. -/
def of {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    AlgebraicStacks S :=
  ObjectProperty.FullSubbicategory.mk (AlgebraicStack.objectProperty S) X ‹AlgebraicStack X›

/-- The underlying category fibred in groupoids over `(Sch/S)_fppf`. -/
abbrev toGroupoids {S : Scheme.{u}} (X : AlgebraicStacks S) : GroupoidsOver S :=
  X.1

/-- The canonical inclusion of algebraic stacks into categories fibred in
groupoids over `(Sch/S)_fppf`. -/
abbrev ι (S : Scheme.{u}) :
    StrictPseudofunctor (AlgebraicStacks S) (GroupoidsOver S) :=
  ObjectProperty.FullSubbicategory.ι (AlgebraicStack.objectProperty S)

/-- `AlgebraicStacks S` is the full sub-2-category of `GroupoidsOver S` on
algebraic stacks. -/
theorem eq (S : Scheme.{u}) :
    AlgebraicStacks S = (AlgebraicStack.objectProperty S).FullSubbicategory :=
  sorry

/-- The underlying groupoid fibration of an object of `AlgebraicStacks S` is an
algebraic stack. -/
instance mem {S : Scheme.{u}} (X : AlgebraicStacks S) :
    AlgebraicStack (toGroupoids X) :=
  X.property

/-- Packaging a category fibred in groupoids as an algebraic stack forgets to
the original object. -/
theorem of_toGroupoids {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    toGroupoids (of X) = X := sorry

/-- The inclusion into groupoid fibrations sends an algebraic stack to its
underlying object of `GroupoidsOver S`. -/
theorem ι_obj {S : Scheme.{u}} (X : AlgebraicStacks S) :
    (ι S).obj X = toGroupoids X := sorry

/-- The 2-category of algebraic stacks over `S` is a (2,1)-category: every
2-morphism is invertible. -/
instance locallyGroupoid {S : Scheme.{u}} :
    Bicategory.IsLocallyGroupoid (AlgebraicStacks S) := sorry

/-- The canonical inclusion of algebraic stacks into the 2-category
`Cat / (Sch/S)_fppf` of categories over `(Sch/S)_fppf`. -/
def toBased (S : Scheme.{u}) :
    StrictPseudofunctor (AlgebraicStacks S) (BasedCategory.{u, u + 1} (Over S)) :=
  (ι S).comp (FiberedCategoryOver.Groupoids.toBased.{u + 1, u, u + 1, u} (Over S))

/-- The `Cat / (Sch/S)_fppf` inclusion is the composite of `ι` with the
forgetful map from categories fibred in groupoids. -/
theorem toBased_eq (S : Scheme.{u}) :
    toBased S =
      (ι S).comp (FiberedCategoryOver.Groupoids.toBased.{u + 1, u, u + 1, u} (Over S)) :=
  sorry

end AlgebraicStacks

end AlgebraicGeometry
