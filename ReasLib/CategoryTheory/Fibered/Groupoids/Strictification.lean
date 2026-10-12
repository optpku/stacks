/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Biequivalence
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Presheaf
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Realization
public import ReasLib.CategoryTheory.Fibered.Groupoids.Split
public import ReasLib.CategoryTheory.Fibered.Strictification

/-!
# Strictification of categories fibred in groupoids

The strict-presheaf theorem, same-owner equivalence theorem, and invariant
essential-surjectivity theorem are exposed here as complementary views of strictification.
The first retains a concrete `Cᵒᵖ ⥤ Grpd` model across heterogeneous total-category universes.
The second is the primary interface inside a fixed owner bicategory. The third records the
biequivalence-level realization property.
-/

@[expose] public section

universe vC vS uC uS uAux

namespace CategoryTheory

open Pseudofunctor.CoGrothendieck
open scoped Bicategory Pseudofunctor.StrongTrans

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]

namespace Functor.IsFibered.InGroupoids.Strictification

/-- Every category fibred in groupoids admits a strict contravariant groupoid-valued presheaf
model whose co-Grothendieck projection is equivalent to the original projection over the base.

The source total-category universes are independent.  The target universes are enlarged only by
the base objects and arrows that occur in the strict presentation. -/
@[stacks 02ZA "strict groupoid-valued presheaf model"]
theorem existsPresheafModel
    (p : S ⥤ C) [Functor.IsFibered.InGroupoids p] :
    ∃ (F : Cᵒᵖ ⥤ Grpd.{max vC vS, max (max uC vC) uS})
      (e : BasedCategory.ofFunctor p ⥤ᵇ
        BasedCategory.ofFunctor (groupoidPresheafProjection F)),
      e.IsEquivalence := sorry

section SaturatedOwner

variable {Sₛ : Type (max uC (max uAux vC))}
  [Category.{max vC vS} Sₛ]

/-- If the source total category already occupies an owner universe closed under the base
objects and arrows, groupoid strictification is an actual bicategorical equivalence to a split
category fibred in groupoids in the same owner.

The split target is the invariant formalization of being presented by a strict
`Grpd`-valued presheaf; use `IsFibered.Split.InGroupoids.iff_existsPresheafModel` when the
literal co-Grothendieck presentation is needed. -/
@[stacks 02XY "same-owner split groupoid strictification"]
theorem existsSplitModel
    (p : Sₛ ⥤ C) [Functor.IsFibered.InGroupoids p] :
    ∃ (Y : FiberedCategoryOver.Groupoids.{
        uC, vC, max uC (max uAux vC), max vC vS} C)
      (_ : FiberedCategoryOver.Groupoids.ofFunctor p ≌ Y),
      Functor.IsFibered.Split.InGroupoids Y.p := sorry

end SaturatedOwner

end Functor.IsFibered.InGroupoids.Strictification

namespace FiberedCategoryOver.Groupoids.Strictification

/-- Bundled specialization of
`Functor.IsFibered.InGroupoids.Strictification.existsPresheafModel`. It lets downstream code
start from an owner object without rebuilding its projection or based category. -/
@[stacks 02ZA "bundled strict groupoid-valued presheaf model"]
theorem existsPresheafModel
    (X : FiberedCategoryOver.Groupoids.{uC, vC, uS, vS} C) :
    ∃ (F : Cᵒᵖ ⥤ Grpd.{max vC vS, max (max uC vC) uS})
      (e : X.toBasedCategory ⥤ᵇ
        BasedCategory.ofFunctor (groupoidPresheafProjection F)),
      e.IsEquivalence := sorry

/-- Bundled same-owner specialization of
`Functor.IsFibered.InGroupoids.Strictification.existsSplitModel`. This is the primary
strictification API for
downstream bicategorical constructions: it returns the target, the actual equivalence, and its
split-in-groupoids property without exposing a universe-boundary based functor. -/
@[stacks 02XY "bundled same-owner split groupoid strictification"]
theorem existsSplitModel
    (X : FiberedCategoryOver.Groupoids.{uC, vC,
      max uC (max uAux vC), max vC vS} C) :
    ∃ (Y : FiberedCategoryOver.Groupoids.{
        uC, vC, max uC (max uAux vC), max vC vS} C)
      (_ : X ≌ Y), Functor.IsFibered.Split.InGroupoids Y.p := sorry

end FiberedCategoryOver.Groupoids.Strictification

namespace Pseudofunctor.CoGrothendieck

/-- Co-Grothendieck realization of groupoid-valued pseudofunctors is essentially surjective onto
categories fibred in groupoids, at the owner universe closed under the base objects and arrows.
This is the invariant bicategorical form of
`Functor.IsFibered.InGroupoids.Strictification.existsPresheafModel`. -/
@[stacks 02ZA "co-Grothendieck realization essential surjectivity"]
instance realizationEssSurj :
    ((realization (𝒞 := C) :
      StrictPseudofunctor
        (Pseudofunctor.GroupoidValued.{
          max uC (max uAux vC), vC, max vC vS, uC} C)
        (FiberedCategoryOver.Groupoids.{
          uC, vC, max uC (max uAux vC), max vC vS} C)).toPseudofunctor).EssSurj := sorry

end Pseudofunctor.CoGrothendieck

end CategoryTheory
