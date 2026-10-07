module

public import Mathlib.AlgebraicGeometry.Properties

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsIntegral

/-- A scheme is integral exactly when it is nonempty and every nonempty affine open
has a domain of sections. -/
theorem iff_forall_affineOpen (X : Scheme.{u}) :
    IsIntegral X ↔
      Nonempty X ∧
        ∀ U : X.Opens, IsAffineOpen U → Nonempty U → IsDomain Γ(X, U) := sorry

end AlgebraicGeometry.IsIntegral
