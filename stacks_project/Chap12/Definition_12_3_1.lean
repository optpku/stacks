/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

variable (A : Type u) [Category.{v} A]

/- Definition 12.3.1 (1): a preadditive category is a category whose hom-sets are abelian groups
and whose composition law is bilinear in both variables; this is the canonical mathlib class
`CategoryTheory.Preadditive`. -/
@[stacks 00ZY] #check Preadditive

section

variable [Preadditive A]

/- Companion recall: in a preadditive category, zero morphisms are derived API via the canonical
instance `Preadditive.preadditiveHasZeroMorphisms`, so the owner-level statement remains
`Preadditive A`. -/
#check (inferInstance : Limits.HasZeroMorphisms A)

end

/- Definition 12.3.1 (2): for preadditive categories, an additive functor is a functor whose map
on every hom-group is an additive homomorphism; this is the canonical mathlib class
`CategoryTheory.Functor.Additive`. -/
@[stacks 00ZY] #check Functor.Additive

end CategoryTheory
