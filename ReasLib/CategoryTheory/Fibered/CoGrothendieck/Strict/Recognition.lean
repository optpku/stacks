/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Strict.Comparison

/-!
# Recognition of strict co-Grothendieck models

This leaf gives the source-facing characterization of intrinsic split fibredness by existence of
a strict co-Grothendieck model.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u₁} [Category.{v₁} C]

namespace Functor.IsFibered.Split

variable {S : Type u₂} [Category.{v₂} S]

/-- Intrinsic splitness is equivalent to being strictly isomorphic over `C` to the
co-Grothendieck construction of a contravariant category-valued functor.

The right side is retained as the source-facing recognition API. The left side is the reusable
owner because it records the actual splitting rather than privileging one presentation of the
total category. -/
@[stacks 02XW "strict co-Grothendieck characterization"]
theorem iff_existsCoGrothendieckModel (p : S ⥤ C) :
    IsFibered.Split p ↔
      ∃ F : Cᵒᵖ ⥤ Cat.{v₂, u₂},
        Nonempty (BasedCategory.StrictIso (BasedCategory.ofFunctor p)
          (BasedCategory.ofFunctor
            (Pseudofunctor.CoGrothendieck.forget F.toPseudofunctor'))) := sorry
/- Proof strategy: in the forward direction choose the explicit split cleavage stored by the
left side, take `SplitCleavage.toCatPresheaf`, and use
`SplitCleavage.CoGrothendieck.StrictIso.apply`. Conversely, equip the strict presheaf model with
`Pseudofunctor.CoGrothendieck.splitCleavage` and apply
`BasedCategory.StrictIso.isFiberedSplit_iff`. -/

end Functor.IsFibered.Split

end CategoryTheory
