module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Affine

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The ring of global sections of an integral normal scheme is a normal ring. -/
theorem isNormalRing_globalSections
    (X : Scheme.{u}) [AlgebraicGeometry.IsIntegral X] (hX : X.isNormal) :
    _root_.IsNormalRing (Γ(X, ⊤)) := sorry

end AlgebraicGeometry.Scheme
