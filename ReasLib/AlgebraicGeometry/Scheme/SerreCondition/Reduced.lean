module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition.Reduced

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- A locally Noetherian scheme is reduced exactly when all of its stalks satisfy Serre's
conditions `(S₁)` and `(R₀)`. -/
theorem isReduced_iff_stalkwise_serre :
    IsReduced X ↔
      (∀ x : X, SerreConditionS (X.presheaf.stalk x) 1) ∧
        ∀ x : X, SerreConditionR (X.presheaf.stalk x) 0 := sorry

end AlgebraicGeometry.Scheme
