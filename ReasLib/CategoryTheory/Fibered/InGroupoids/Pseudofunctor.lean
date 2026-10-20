/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.GroupoidValued
public import ReasLib.CategoryTheory.Fibered.Cleavage.Pseudofunctor.Construction
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Fibers

/-!
# Indexed-category presentations of categories fibred in groupoids

A cleavage on a category fibred in groupoids yields the canonical fibre pseudofunctor, and each
of its values is a groupoid. The pointwise instance and `toGroupoidValued` package this same
`Cat`-valued pseudofunctor in the invariant owner expected by downstream constructions.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open scoped CategoryTheory.Bicategory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace Functor.Cleavage

variable {p : S ⥤ C}

namespace toPseudofunctor

/-- Every value of the canonical fibre pseudofunctor associated to a cleavage on a category
fibred in groupoids carries its canonical groupoid instance. -/
instance objIsGroupoid
    [Functor.IsFibered.InGroupoids p] (χ : p.Cleavage)
    (U : LocallyDiscrete Cᵒᵖ) : IsGroupoid ((χ.toPseudofunctor).obj U) := sorry

/-- The canonical fibre pseudofunctor associated to a cleavage on a category fibred in groupoids
is groupoid-valued. -/
@[stacks 003V "(3)"]
theorem isGroupoidValued
    [Functor.IsFibered.InGroupoids p] (χ : p.Cleavage) :
    ∀ U : LocallyDiscrete Cᵒᵖ, IsGroupoid ((χ.toPseudofunctor).obj U) := sorry
/- Proof strategy: the value at `U` is the standard fibre `p.Fiber (unop U)`; apply
`Functor.IsFibered.InGroupoids.fiberIsGroupoid`. -/

end toPseudofunctor

/-- Package the canonical fibre pseudofunctor as an object of the invariant bicategory of
groupoid-valued pseudofunctors. No new pseudofunctor data or cleavage choice is introduced. -/
@[stacks 003V "(3)"]
noncomputable def toGroupoidValued
    [Functor.IsFibered.InGroupoids p] (χ : p.Cleavage) :
    Pseudofunctor.GroupoidValued C :=
  Pseudofunctor.GroupoidValued.mk χ.toPseudofunctor

/-- Forgetting the groupoid-valued owner recovers the canonical fibre pseudofunctor. -/
@[simp]
theorem toGroupoidValued.toPseudofunctor
    [Functor.IsFibered.InGroupoids p] (χ : p.Cleavage) :
    (χ.toGroupoidValued).toPseudofunctor = χ.toPseudofunctor := sorry

end Functor.Cleavage

end CategoryTheory
