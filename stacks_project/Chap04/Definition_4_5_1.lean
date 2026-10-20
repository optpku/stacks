/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import StacksCheckRecall

@[expose] public section


universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {X Y P : C} {ι₁ : X ⟶ P} {ι₂ : Y ⟶ P}

/- Canonical-selection rationale: the source keeps the candidate object `P` and coprojections
`ι₁`, `ι₂` explicit. `BinaryCofan.mk` packages exactly that data, and `IsColimit` supplies the
mediating morphism, both commutative triangles, and uniqueness. The alternatives
`HasBinaryCoproduct` and `coprodIsCoprod` instead assume existence and select `X ⨿ Y`, so they
belong to the downstream chosen-object API. Specializing the generic `IsColimit` owner to this
binary cofan recovers the source without generalizing its assumptions and exposes the standard
`desc`, factorization, and hom-ext API for later items. -/

/- Definition 4.5.1: morphisms `ι₁ : X ⟶ P` and `ι₂ : Y ⟶ P` exhibit `P` as a coproduct of `X`
and `Y` precisely when the binary cofan `BinaryCofan.mk ι₁ ι₂` is colimiting. -/
@[stacks 04AO "binary coproduct object with coprojections and universal mapping property"]
#check (IsColimit (BinaryCofan.mk ι₁ ι₂) : Type (max u v))

/- Companion recall: the unique-factorization clause in the textbook definition is the canonical
theorem `IsColimit.existsUnique`. -/
#check IsColimit.existsUnique

/- Companion recall: for a binary cofan of the form `BinaryCofan.mk ι₁ ι₂`, the converse
direction is the binary-coproduct-specific constructor `BinaryCofan.IsColimit.mk`. -/
#check BinaryCofan.IsColimit.mk

end CategoryTheory.Limits
