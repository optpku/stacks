/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Slice
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange

/-!
# Fiber-pair criteria for relative representability

This module separates the source-facing fiber-pair condition from the invariant slice-base-change
condition.  The named intermediate predicate lets applications state and transport the recurring
representability hypothesis without repeating its full dependent quantifier.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Functor

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Groupoids C}

namespace FiberedCategoryOver.Groupoids

namespace Hom

/-- Every canonical slice base change of `F` has representable presheaf of fiberwise isomorphism
classes.  This is the compact invariant owner for the recurring slice hypothesis in relative
representability arguments. -/
def sliceFiberClasses.representable (F : X ⟶ Y) : Prop :=
  sliceFiberClasses.satisfies
    (fun _ P ↦ P.IsRepresentable) F

/-- The source-facing fiber-pair condition for `F`: every object of a target fiber admits a
slice-Yoneda representative for which the associated base-change iso-class presheaf is
representable. -/
@[stacks 02Y9 "representable fiber-class presheaves on fiber pairs"]
def fiberPairClasses.representable (F : X ⟶ Y) : Prop :=
  fiberPairClasses.satisfies
    (fun _ P ↦ P.IsRepresentable) F

/-- The named fiber-pair condition unfolds to representability of each concrete fiber-pair
presheaf. -/
theorem fiberPairClasses.representable_iff
    (F : X ⟶ Y) :
    fiberPairClasses.representable F ↔
      ∀ ⦃U : C⦄ (y : Y.p.Fiber U),
        (fiberPairClasses F y).IsRepresentable := sorry

/-- The named slice-base-change condition unfolds to representability of the iso-class presheaf
for every slice morphism. -/
theorem sliceFiberClasses.representable_iff
    (F : X ⟶ Y) :
    sliceFiberClasses.representable F ↔
      ∀ ⦃U : C⦄ (G : FiberedCategoryOver.Groupoids.slice U ⟶ Y),
        (sliceFiberClasses F G).IsRepresentable := sorry

/-- The fiber-pair condition is equivalent to the invariant condition on every canonical slice
base change. -/
theorem fiberPairClasses.representable_iff_slice
    (F : X ⟶ Y) :
    fiberPairClasses.representable F ↔
      sliceFiberClasses.representable F := sorry

end Hom

namespace relativelyRepresentable

/-- Fiberwise faithfulness together with the source-facing fiber-pair condition implies relative
representability. -/
@[stacks 02Y9]
theorem ofFiberwiseFaithful
    {F : X ⟶ Y}
    (hFaithful : ∀ U : C, (fiberFunctor F U).Faithful)
    (hPairs : Hom.fiberPairClasses.representable F) :
    relativelyRepresentable F := sorry

/-- Faithfulness of the total based functor together with the invariant slice-base-change
iso-class condition implies relative representability. -/
theorem ofFaithful
    {F : X ⟶ Y}
    (hFaithful : (toBasedFunctor F).Faithful)
    (hRepresentable : Hom.sliceFiberClasses.representable F) :
    relativelyRepresentable F := sorry

end relativelyRepresentable

end FiberedCategoryOver.Groupoids

end CategoryTheory
