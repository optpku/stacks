/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Filtration.FiniteInjective.Embedding
import StacksCheckRecall

@[expose] public section

/-!
# Exercise 111.30.5
-/

universe v u

/- Exercise 111.30.5: every finite filtered object over an abelian category with enough
injectives admits a strict monomorphism into a finite filtered-injective object. -/
@[stacks 028C] #check
  (CategoryTheory.FilteredObject.Finite.FilteredInjective.Embedding.nonempty :
    ∀ {C : Type u} [_root_.CategoryTheory.Category.{v} C]
      [CategoryTheory.Abelian C] [CategoryTheory.EnoughInjectives C]
      (A : CategoryTheory.FilteredObject.Finite.category C),
      Nonempty (CategoryTheory.FilteredObject.Finite.FilteredInjective.Embedding A))
