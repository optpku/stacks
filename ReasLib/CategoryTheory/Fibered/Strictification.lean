/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Bicategory
public import ReasLib.CategoryTheory.Fibered.Split
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck

/-!
# Strictification of fibred categories

This module exposes strictification independently of any textbook chapter.  The API has three
levels:

* a strict `Cat`-valued presheaf together with a heterogeneous equivalence over the base;
* a bundled split fibred-category model, still allowing the necessary universe enlargement;
* a bicategorical equivalence when the source already lives in the enlarged owner universe.

The projection-level theorems are the universe-polymorphic owners.  The
`FiberedCategoryOver` specializations remove routine rebundling from downstream applications.
-/

@[expose] public section

universe vC vS uC uS uAux

namespace CategoryTheory

open scoped CategoryTheory.Bicategory

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]

namespace Functor.IsFibered.Strictification

/-- Every fibred functor admits a strict contravariant `Cat`-valued model whose
co-Grothendieck projection is equivalent to the original functor over the base.

The total-category universes of the source are independent of those of the base.  The target
universes are the least evident maxima containing the source objects and morphisms together with
the objects and arrows stored by the strictification. -/
@[stacks 004A "strict Cat-valued presheaf model"]
theorem existsCatPresheafModel
    (p : S ⥤ C) [p.IsFibered] :
    ∃ (F : Cᵒᵖ ⥤ Cat.{max vC vS, max (max uC vC) uS})
      (e : BasedCategory.ofFunctor p ⥤ᵇ
        BasedCategory.ofFunctor
          (Pseudofunctor.CoGrothendieck.forget F.toPseudofunctor')),
      e.IsEquivalence := sorry

/-- Every fibred functor admits an equivalent split fibred-category model over the same base.
The heterogeneous based equivalence is the canonical comparison level when strictification
enlarges the total-category universes. -/
@[stacks 004A "based split strictification"]
theorem existsBasedSplitModel
    (p : S ⥤ C) [p.IsFibered] :
    ∃ (Y : FiberedCategoryOver.{
        uC, vC, max (max uC vC) uS, max vC vS} C)
      (e : BasedCategory.ofFunctor p ⥤ᵇ Y.toBasedCategory),
      e.IsEquivalence ∧ Functor.IsFibered.Split Y.p := sorry

section SaturatedOwner

variable {Sₛ : Type (max uC (max vC uAux))}
  [Category.{max vC vS} Sₛ]

/-- If the source already occupies a universe closed under the base objects and arrows,
strictification can be expressed as a bicategorical equivalence to a split
`FiberedCategoryOver` object in the same owner bicategory. -/
@[stacks 004A "same-owner split strictification"]
theorem existsSplitModel
    (p : Sₛ ⥤ C) [p.IsFibered] :
    ∃ (Y : FiberedCategoryOver.{
        uC, vC, max uC (max vC uAux), max vC vS} C)
      (_ : FiberedCategoryOver.ofFunctor p ≌ Y),
      Functor.IsFibered.Split Y.p := sorry

end SaturatedOwner

end Functor.IsFibered.Strictification

namespace FiberedCategoryOver.Strictification

/-- Bundled specialization of `Functor.IsFibered.Strictification.existsCatPresheafModel`.
It avoids reconstructing
`BasedCategory.ofFunctor X.p` at each application site. -/
@[stacks 004A "bundled strict Cat-valued presheaf model"]
theorem existsCatPresheafModel
    (X : FiberedCategoryOver.{uC, vC, uS, vS} C) :
    ∃ (F : Cᵒᵖ ⥤ Cat.{max vC vS, max (max uC vC) uS})
      (e : X.toBasedCategory ⥤ᵇ
        BasedCategory.ofFunctor
          (Pseudofunctor.CoGrothendieck.forget F.toPseudofunctor')),
      e.IsEquivalence := sorry

/-- Bundled specialization of `Functor.IsFibered.Strictification.existsBasedSplitModel`.
It returns a split replacement and its heterogeneous comparison directly from `X`. -/
@[stacks 004A "bundled based split strictification"]
theorem existsBasedSplitModel
    (X : FiberedCategoryOver.{uC, vC, uS, vS} C) :
    ∃ (Y : FiberedCategoryOver.{
        uC, vC, max (max uC vC) uS, max vC vS} C)
      (e : X.toBasedCategory ⥤ᵇ Y.toBasedCategory),
      e.IsEquivalence ∧ Functor.IsFibered.Split Y.p := sorry

/-- Bundled same-owner specialization of `Functor.IsFibered.Strictification.existsSplitModel`.
Use this form when later constructions consume a bicategorical equivalence rather than a
heterogeneous based equivalence. -/
@[stacks 004A "bundled same-owner split strictification"]
theorem existsSplitModel
    (X : FiberedCategoryOver.{uC, vC,
      max uC (max vC uAux), max vC vS} C) :
    ∃ (Y : FiberedCategoryOver.{
        uC, vC, max uC (max vC uAux), max vC vS} C)
      (_ : X ≌ Y), Functor.IsFibered.Split Y.p := sorry

end FiberedCategoryOver.Strictification

end CategoryTheory
