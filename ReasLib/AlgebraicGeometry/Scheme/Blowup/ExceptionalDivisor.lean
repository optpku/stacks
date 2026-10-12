/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Rees
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Localization

/-!
# Exceptional divisors of blowups

This file relates the inverse-image center ideal of a blowup to the first twist in its Rees
relative projective-spectrum presentation.
-/

@[expose] public section

namespace AlgebraicGeometry

universe u

open CategoryTheory

noncomputable section

variable {X : Scheme.{u}} {I : X.IdealSheafData}

namespace Blowup

/-- The canonical morphism from the exceptional ideal sheaf of a blowup to its first Rees twist
is an isomorphism. -/
theorem exceptionalIdealToTwistOne_isIso (π : Blowup X I) :
    IsIso π.reesPresentation.exceptionalIdealToTwistOne := sorry

end Blowup

end

end AlgebraicGeometry
