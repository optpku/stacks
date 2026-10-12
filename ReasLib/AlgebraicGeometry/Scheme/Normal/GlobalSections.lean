/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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
