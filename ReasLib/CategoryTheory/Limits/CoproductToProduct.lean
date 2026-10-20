/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# The Canonical Map from a Coproduct to a Product

@stack 02FT

For a family in a category with zero morphisms, coproduct projections and product lifts define a
canonical diagonal comparison from its coproduct to its product.
-/

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {I : Type w} (X : I → C) [HasCoproduct X] [HasProduct X]

-- Local instance justification (noncanonical choice): `Sigma.π` requires decidable equality on
-- the index type; the comparison is noncomputable and does not expose this choice.
local instance indexDecidableEq : DecidableEq I := Classical.decEq I

/-- The canonical diagonal morphism from the coproduct of a family to its product. -/
@[stacks 02FT "canonical coproduct-to-product comparison"]
def coproductToProduct : (∐ X) ⟶ ∏ᶜ X :=
  Pi.lift fun i ↦ Sigma.π X i

/-- The `i`-th product component of `coproductToProduct X` is the canonical projection from the
coproduct to `X i`. -/
@[stacks 02FT "components of the coproduct-to-product comparison", reassoc (attr := simp)]
theorem coproductToProduct_π (i : I) :
    coproductToProduct X ≫ Pi.π X i = Sigma.π X i := sorry

/-- The diagonal summand-factor component of `coproductToProduct X` is the identity. -/
@[stacks 02FT "diagonal component of the coproduct-to-product comparison", reassoc (attr := simp)]
theorem ι_coproductToProduct_π (i : I) :
    Sigma.ι X i ≫ coproductToProduct X ≫ Pi.π X i = 𝟙 (X i) := sorry

/-- An off-diagonal summand-factor component of `coproductToProduct X` is zero. -/
@[stacks 02FT "off-diagonal component of the coproduct-to-product comparison", reassoc (attr := simp)]
theorem ι_coproductToProduct_π_of_ne {i j : I} (h : i ≠ j) :
    Sigma.ι X i ≫ coproductToProduct X ≫ Pi.π X j = 0 := sorry

end CategoryTheory.Limits
