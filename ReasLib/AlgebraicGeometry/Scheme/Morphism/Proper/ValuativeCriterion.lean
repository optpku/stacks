module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes is proper if and only if it satisfies the valuative criterion and is
quasi-compact, quasi-separated, and locally of finite type. -/
theorem isProper_iff_valuativeCriterion {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsProper f ↔ ValuativeCriterion f ∧ QuasiCompact f ∧ QuasiSeparated f ∧
      LocallyOfFiniteType f := sorry

end AlgebraicGeometry
