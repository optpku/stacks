/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

open Limits

universe v u

section

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (x y : C) [HasBinaryProduct x y]

/- Definition 12.3.5: in a preadditive category, the textbook direct sum `x ⊕ y` is the binary
product `x × y`, i.e. the product object `x ⨯ y`. -/
@[stacks 0102] #check (x ⨯ y)

/- Companion recall: the source-facing direct sum comes with the usual projection maps
`prod.fst : x ⨯ y ⟶ x` and `prod.snd : x ⨯ y ⟶ y`. -/
#check prod.fst
#check prod.snd

/- Companion recall: in a preadditive category, the direct-sum inclusions into the source-facing
product object are the canonical morphisms `prod.inl : x ⟶ x ⨯ y` and
`prod.inr : y ⟶ x ⨯ y`. -/
#check prod.inl
#check prod.inr

/- Companion recall: Lemma 12.3.4 supplies the canonical binary biproduct view of the same
product-based direct sum. -/
#check HasBinaryBiproduct.of_hasBinaryProduct

/- Companion recall: the chosen binary biproduct object `x ⊞ y` is canonically isomorphic to the
source-facing product object `x ⨯ y`. -/
#check biprod.isoProd

end

end CategoryTheory
