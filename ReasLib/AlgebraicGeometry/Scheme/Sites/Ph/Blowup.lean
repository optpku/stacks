/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic

/-!
# Blowup squares and sheaves for the ph topology

Sheaves of types for the big ph topology send blowup squares to pullback squares.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme.Ph.Sheaf

/-- A sheaf on the big ph site sends a cartesian blowup square with finitely presented
closed center to a pullback square of section types. -/
theorem map_isPullback_of_isBlowup {S : Scheme.{u}}
    (F : CategoryTheory.Sheaf (Scheme.bigPhSite S) (Type v)) (sq : Square (Over S))
    [IsClosedImmersion sq.f₃₄.left] [LocallyOfFinitePresentation sq.f₃₄.left]
    (h_pullback : (sq.map (Over.forget S)).IsPullback)
    [IsBlowup sq.f₂₄.left (sq.f₃₄.left).ker] :
    (sq.op.map F.obj).IsPullback := sorry

end AlgebraicGeometry.Scheme.Ph.Sheaf
