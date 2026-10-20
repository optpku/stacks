module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reasonable

/-!
# Reasonableness under étale morphisms

The source of an étale morphism to a reasonable algebraic space is reasonable.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsReasonable

/-- The source of an étale morphism to a reasonable algebraic space is reasonable. -/
theorem of_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Etale f] [IsReasonable Y] : IsReasonable X := sorry

end AlgebraicGeometry.AlgebraicSpace.IsReasonable
