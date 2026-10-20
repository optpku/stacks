/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import ReasLib.CategoryTheory.Sites.Cover.Image
import Mathlib.Tactic.CrossRefAttribute

/-!
# Effectivity for cover descent

The basic interface separates the fully faithful half of descent, supplied by
a prestack, from the essential-surjectivity half.  A second theorem combines it
with the image of a cover along a continuous functor.
-/

@[expose] public section

universe t u uC uD u' v vC vD v'

namespace CategoryTheory

open Bicategory

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})

/-- A prestack's descent functor is an equivalence once its essential surjectivity is known. -/
theorem IsPrestack.toDescentData_isEquivalence
    [F.IsPrestack J] {ι : Type t} {U : C} {X : ι → C}
    (f : ∀ i, X i ⟶ U) (h_cover : Sieve.ofArrows _ f ∈ J U)
    (h_essSurj : (F.toDescentData f).EssSurj) :
    (F.toDescentData f).IsEquivalence := sorry

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (F : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{v', u'})

/-- A stack has effective descent for the image of every cover along a continuous functor. -/
theorem IsStack.ImageCover.toDescentData_isEquivalence
    {U : C} (T : J.Cover U) (u : C ⥤ D) [u.IsContinuous J K] [F.IsStack K] :
    (F.toDescentData (fun I : T.Arrow ↦ u.map I.f)).IsEquivalence := sorry

end Pseudofunctor

end CategoryTheory
