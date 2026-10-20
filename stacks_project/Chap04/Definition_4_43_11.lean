/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import StacksCheckRecall

@[expose] public section


universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [SymmetricCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [SymmetricCategory D]
variable (F : C ⥤ D)

/- The source needs both an invertible monoidal tensorator and its compatibility with symmetry.
`Functor.Monoidal` supplies the first but not the second, while `Functor.LaxBraided` supplies the
compatibility square without invertibility. The canonical owner `Functor.Braided` extends both.
Although that owner is stated for braided categories, specializing its source and target to the
ambient `SymmetricCategory` instances recovers exactly the source notion: `Monoidal.μIso` is the
displayed isomorphism and `LaxBraided.braided` is the displayed commuting square. Recalling the
combined owner avoids a parallel symmetric-only wrapper and exposes the standard typeclass API. -/

/- Definition 4.43.11: a functor of symmetric monoidal categories is a strong monoidal functor
whose tensorator commutes with the symmetric braidings. -/
@[stacks 0FFY "strong monoidal functors preserving the symmetric braiding"]
#check (Braided F : Type (max u₁ v₂))

end Functor
end CategoryTheory
