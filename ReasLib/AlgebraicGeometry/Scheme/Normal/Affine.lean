/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normal

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- An integral scheme is normal if and only if the section ring on every nonempty affine open
is a normal ring. -/
@[stacks 033L]
theorem isNormal_iff_forall_affineOpen_isNormalRing
    (X : Scheme.{u}) [AlgebraicGeometry.IsIntegral X] :
    X.isNormal ↔
      ∀ U : X.affineOpens, (U : Set X).Nonempty → _root_.IsNormalRing (Γ(X, U)) := sorry

end AlgebraicGeometry.Scheme
