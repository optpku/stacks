/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction
public import ReasLib.CategoryTheory.MorphismProperty.Saturation

/-!
# Saturated multiplicative systems

A saturated multiplicative system is a morphism property with both calculi of fractions and the
intrinsic saturation axiom.  The three ingredients remain independently reusable: MS4 is owned
by `HasSaturationAxiom`, while the localization closure operator is owned by `saturation`.
-/

@[expose] public section

universe v u

namespace CategoryTheory
namespace MorphismProperty

variable {C : Type u} [Category.{v} C]

/-- Isomorphisms admit a left calculus of fractions. -/
instance isomorphisms_hasLeftCalculusOfFractions :
    (isomorphisms C).HasLeftCalculusOfFractions := sorry

/-- Isomorphisms admit a right calculus of fractions. -/
instance isomorphisms_hasRightCalculusOfFractions :
    (isomorphisms C).HasRightCalculusOfFractions := sorry

/-- A saturated multiplicative system has left and right calculi of fractions and satisfies the
intrinsic saturation axiom MS4. -/
@[stacks 05Q8 "saturated multiplicative systems"]
class IsSaturatedMultiplicativeSystem (W : MorphismProperty C) : Prop where
  /-- The system admits left fractions. -/
  toHasLeftCalculusOfFractions : W.HasLeftCalculusOfFractions
  /-- The system admits right fractions. -/
  toHasRightCalculusOfFractions : W.HasRightCalculusOfFractions
  /-- The system satisfies the intrinsic saturation axiom MS4. -/
  toHasSaturationAxiom : W.HasSaturationAxiom

attribute [instance] IsSaturatedMultiplicativeSystem.toHasLeftCalculusOfFractions
attribute [instance] IsSaturatedMultiplicativeSystem.toHasRightCalculusOfFractions
attribute [instance] IsSaturatedMultiplicativeSystem.toHasSaturationAxiom

namespace IsSaturatedMultiplicativeSystem

variable (W : MorphismProperty C)

/-- Construct a saturated multiplicative system from explicit left and right fraction calculi
and a proof of MS4. -/
theorem of (h_left : W.HasLeftCalculusOfFractions)
    (h_right : W.HasRightCalculusOfFractions)
    (h_ms4 : ∀ {X₀ X₁ X₂ X₃ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃),
      W (f ≫ g) → W (g ≫ h) → W g) :
    W.IsSaturatedMultiplicativeSystem := sorry

/-- Explicitly assemble a saturated multiplicative system from its three independent components.

This is intentionally not an instance: the owner already exports each component as an instance,
so registering the reverse construction would create a typeclass cycle. -/
theorem ofComponents [W.HasLeftCalculusOfFractions]
    [W.HasRightCalculusOfFractions] [W.HasSaturationAxiom] :
    W.IsSaturatedMultiplicativeSystem := sorry

/-- The opposite of a saturated multiplicative system is saturated. -/
instance op [W.IsSaturatedMultiplicativeSystem] :
    W.op.IsSaturatedMultiplicativeSystem :=
  ofComponents W.op

/-- Passing a saturated multiplicative system on an opposite category back to the original
category preserves saturation. -/
instance unop (W : MorphismProperty Cᵒᵖ) [W.IsSaturatedMultiplicativeSystem] :
    W.unop.IsSaturatedMultiplicativeSystem :=
  ofComponents W.unop

/-- A saturated multiplicative system is equivalently a morphism property with both fraction
calculi and the intrinsic saturation axiom. -/
theorem iff : W.IsSaturatedMultiplicativeSystem ↔
    W.HasLeftCalculusOfFractions ∧ W.HasRightCalculusOfFractions ∧ W.HasSaturationAxiom := sorry

/-- The MS4 consequence of a saturated multiplicative system, stated with the traditional
three-composable-morphisms interface. -/
theorem saturation [W.IsSaturatedMultiplicativeSystem] {X₀ X₁ X₂ X₃ : C}
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃)
    (h_fg : W (f ≫ g)) (h_gh : W (g ≫ h)) : W g := sorry

/-- Every isomorphism belongs to a saturated multiplicative system. -/
theorem isomorphisms_le [W.IsSaturatedMultiplicativeSystem] : isomorphisms C ≤ W := sorry

/-- A saturated multiplicative system is stable under pre- and postcomposition by
isomorphisms. -/
instance respectsIso [W.IsSaturatedMultiplicativeSystem] : W.RespectsIso := sorry

/-- A saturated multiplicative system is a fixed point of the canonical localization
saturation closure operator. -/
theorem isClosed [W.IsSaturatedMultiplicativeSystem] :
    (MorphismProperty.saturation (C := C)).IsClosed W := sorry

/-- The canonical localization saturation of a saturated multiplicative system is itself. -/
theorem saturation_eq [W.IsSaturatedMultiplicativeSystem] :
    (MorphismProperty.saturation (C := C)) W = W := sorry

end IsSaturatedMultiplicativeSystem


end MorphismProperty
end CategoryTheory
