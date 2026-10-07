module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Affine opens of schemes
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- An open of a scheme is affine when its associated open subscheme is affine. -/
abbrev IsAffineOpen {X : Scheme.{u}} (U : X.Opens) : Prop :=
  _root_.AlgebraicGeometry.IsAffineOpen U

end AlgebraicGeometry.Scheme
