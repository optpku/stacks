module

public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.SerreCondition

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- A locally Noetherian scheme is regular if and only if it satisfies Serre's condition
`(Rₖ)` for every natural number `k`. -/
theorem regular_iff_forall_satisfiesSerreConditionR (X : Scheme.{u}) [IsLocallyNoetherian X] :
    Regular X ↔ ∀ k : ℕ, satisfiesSerreConditionR X k := sorry

end AlgebraicGeometry.Scheme
