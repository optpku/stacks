/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphisms in the category of categories

An isomorphism in `Cat` is precisely the data needed to make its underlying functor an
equivalence.  This leaf exposes the forward implication as a reusable typeclass bridge.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.Cat.Hom

variable {C D : Cat.{v, u}}

/-- An isomorphism in `Cat` induces an equivalence of the underlying categories. -/
@[stacks 0GZH "categorical endpoint for pro-DGA QC equivalences"]
instance isEquivalence_toFunctor (F : C ⟶ D) [IsIso F] :
    F.toFunctor.IsEquivalence := sorry

end CategoryTheory.Cat.Hom
