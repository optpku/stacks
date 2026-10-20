/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Cleavage.Pseudofunctor.Construction
public import ReasLib.CategoryTheory.Bicategory.LocallyDiscrete

import StacksCheckRecall

@[expose] public section

/-!
# Lemma 4.33.7

This file records the three source-text items of Lemma 4.33.7 by tagging their canonical owners
directly; it does not introduce a second textbook-facing API.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace Functor.Cleavage

variable {p : S ⥤ C} (χ : p.Cleavage)
variable {U V W : C} (f : V ⟶ U) (g : W ⟶ V)

/- Lemma 4.33.7 (1): for composable morphisms `f : V ⟶ U` and `g : W ⟶ V`, the canonical
comparison `(g ≫ f)⁎[χ] ≅ f⁎[χ] ⋙ g⁎[χ]` is `Functor.Cleavage.Reindex.compIso`. -/
@[stacks 02XO "(1)"]
#check (CategoryTheory.Functor.Cleavage.Reindex.compIso χ f g :
  χ.reindex (g ≫ f) ≅ χ.reindex f ⋙ χ.reindex g)

/- Lemma 4.33.7 (2): the canonical unit isomorphism
`α_U : 𝟭 (Fiber p U) ≅ (𝟙 U)⁎[χ]` is `Functor.Cleavage.Reindex.idIso`. -/
@[stacks 02XO "(2)"]
#check (CategoryTheory.Functor.Cleavage.Reindex.idIso χ U :
  𝟭 (Functor.Fiber p U) ≅ χ.reindex (𝟙 U))

/- Lemma 4.33.7 (3): the fiber categories, pullback functors, composition comparisons, and unit
comparisons assemble into a pseudofunctor valued in the `(2,1)`-category `Pith Cat`. The ordinary
`Cat`-valued pseudofunctor is mapped to its canonical pith by
`Bicategory.Pith.pseudofunctorToPith`. -/
@[stacks 02XO "(3)"]
#check (Bicategory.Pith.pseudofunctorToPith
    (CategoryTheory.Functor.Cleavage.toPseudofunctor χ) :
  LocallyDiscrete Cᵒᵖ ⥤ᵖ Bicategory.Pith Cat)

end Functor.Cleavage

end CategoryTheory
