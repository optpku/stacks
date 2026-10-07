module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Cap

/-!
# Bilinearity of the fibre-cycle action

This file records that the action of a family of fibre cycles on a cycle of
the base is additive in each variable.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace CyclesOnFibers

variable {S X Y : Scheme.{u}} [UniversallyCatenary S]
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType (f ≫ p)]
    (δ : S → ℤ) [IsDimensionFunction δ] (r : ℕ) (e : ℤ)

/- Lemma 62.11.1 (1): the action is additive in the family of fibre cycles. -/
@[stacks 0H66] #check
  (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.cap_add_left p f δ (r := (r : ℤ)) :
    ∀ (α₁ α₂ : CyclesOnFibers f (r : ℤ))
      (β : CycleGroup Y (p.relativeDimensionFunction δ) e),
      cap p f δ (α₁ + α₂) β = cap p f δ α₁ β + cap p f δ α₂ β)

/- Lemma 62.11.1 (2): the action is additive in the cycle on the base. -/
@[stacks 0H66] #check
  (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.cap_add_right p f δ (r := (r : ℤ)) :
    ∀ (α : CyclesOnFibers f (r : ℤ))
      (β₁ β₂ : CycleGroup Y (p.relativeDimensionFunction δ) e),
      cap p f δ α (β₁ + β₂) = cap p f δ α β₁ + cap p f δ α β₂)

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
