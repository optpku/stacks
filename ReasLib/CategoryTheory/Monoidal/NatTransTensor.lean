/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor squares for monoidal natural transformations

This leaf exposes the square form of the tensor axiom for a monoidal natural
transformation.  It is deliberately independent of any derived-category model:
Čech totalizations, derived tensor functors, and comparison constructions can
all use the same bridge.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe uC vC uD vD

namespace CategoryTheory.NatTrans.IsMonoidal

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
variable {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
variable {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal]

/-- The tensor component of a monoidal natural transformation, written as a
commuting square.  This is the reusable form of the equality
`μ F X Y ≫ τ.app (X ⊗ Y) = (τ.app X ⊗ₘ τ.app Y) ≫ μ G X Y`.
-/
@[stacks 0FKV "tensor square of a monoidal natural transformation"]
theorem tensorCommSq (τ : F ⟶ G) [IsMonoidal τ] (X Y : C) :
    CommSq
      (Functor.LaxMonoidal.μ F X Y)
      (τ.app X ⊗ₘ τ.app Y)
      (τ.app (X ⊗ Y))
      (Functor.LaxMonoidal.μ G X Y) := sorry

end CategoryTheory.NatTrans.IsMonoidal
