/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.SaturatedMultiplicativeSystem

/-!
# Products of denominator classes

This module records that the fraction-calculus and saturation interfaces for morphism
properties are preserved by products of categories.  The component instances are exposed
separately so users that need only one side of the calculus do not have to assume a saturated
multiplicative system.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.MorphismProperty

variable {C₁ : Type u₁} {C₂ : Type u₂}
variable [Category.{v₁} C₁] [Category.{v₂} C₂]
variable (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)

namespace HasLeftCalculusOfFractions

/-- The product of two denominator classes admitting left fractions again admits left
fractions, computed componentwise. -/
@[stacks 0FPH "product left calculus of fractions"]
instance prod [W₁.HasLeftCalculusOfFractions] [W₂.HasLeftCalculusOfFractions] :
    (W₁.prod W₂).HasLeftCalculusOfFractions := sorry

end HasLeftCalculusOfFractions

namespace HasRightCalculusOfFractions

/-- The product of two denominator classes admitting right fractions again admits right
fractions, computed componentwise. -/
@[stacks 0FPH "product right calculus of fractions"]
instance prod [W₁.HasRightCalculusOfFractions] [W₂.HasRightCalculusOfFractions] :
    (W₁.prod W₂).HasRightCalculusOfFractions := sorry

end HasRightCalculusOfFractions

namespace HasSaturationAxiom

/-- The intrinsic saturation axiom MS4 is preserved by products of morphism properties. -/
@[stacks 0FPH "product saturation axiom"]
instance prod [W₁.HasSaturationAxiom] [W₂.HasSaturationAxiom] :
    (W₁.prod W₂).HasSaturationAxiom := sorry

end HasSaturationAxiom

namespace IsSaturatedMultiplicativeSystem

/-- The product of two saturated multiplicative systems is a saturated multiplicative system. -/
@[stacks 0FPH "product saturated multiplicative system"]
instance prod [W₁.IsSaturatedMultiplicativeSystem]
    [W₂.IsSaturatedMultiplicativeSystem] :
    (W₁.prod W₂).IsSaturatedMultiplicativeSystem := sorry

end IsSaturatedMultiplicativeSystem

end CategoryTheory.MorphismProperty
