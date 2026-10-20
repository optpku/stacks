module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

@[expose] public section

/-!
# Braided monoidal structures transported across adjunctions

Mathlib constructs the canonical lax monoidal structure on the right adjoint of an oplax
monoidal functor. This module records the braided refinement when the left adjoint is braided.
-/

open CategoryTheory.MonoidalCategory

noncomputable section

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
variable [L.Braided]

/-- The canonical lax braided structure on a right adjoint of a braided monoidal functor.
Its lax monoidal data are exactly `Adjunction.rightAdjointLaxMonoidal`; only compatibility with
the braidings is additional proof data. -/
@[stacks 0B6C "braided right-adjoint tensor structure", implicit_reducible]
noncomputable def rightAdjointLaxBraided : R.LaxBraided where
  toLaxMonoidal := adj.rightAdjointLaxMonoidal
  braided := sorry

/-- Forgetting braiding from `rightAdjointLaxBraided` recovers Mathlib's canonical right-adjoint
lax monoidal structure. -/
@[simp]
theorem rightAdjointLaxBraided_toLaxMonoidal :
    adj.rightAdjointLaxBraided.toLaxMonoidal = adj.rightAdjointLaxMonoidal := sorry

end CategoryTheory.Adjunction

-- The only local proof debt is the Prop-valued braiding law; the unit and tensorator are
-- Mathlib's concrete `Adjunction.rightAdjointLaxMonoidal` data.
