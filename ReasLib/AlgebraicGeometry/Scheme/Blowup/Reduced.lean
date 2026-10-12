/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Affine
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Reduced

@[expose] public section

universe u

namespace AlgebraicGeometry.Blowup

/-- The blowup of a reduced scheme along an ideal sheaf is reduced. -/
@[stacks 0808]
theorem isReduced {X : Scheme.{u}} {I : X.IdealSheafData} (π : Blowup X I)
    [IsReduced X] : IsReduced π.scheme := sorry

end AlgebraicGeometry.Blowup
