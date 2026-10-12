/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.BinaryBiproduct.Indecomposable
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits

universe v u

/-
Definition 47.5.5. An object `X` of an additive category is indecomposable if it
is nonzero and every biproduct decomposition `X ≅ Y ⊞ Z` has a zero summand.
-/
@[stacks 08Y6] #check (@CategoryTheory.indecomposable_iff :
  ∀ {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C] (X : C),
    CategoryTheory.Indecomposable X ↔
      ¬ IsZero X ∧ ∀ Y Z, (X ≅ Y ⊞ Z) → IsZero Y ∨ IsZero Z)
