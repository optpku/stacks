/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.MeromorphicFunction.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Pullback
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Regular

/-!
# Pullbacks along blowups

Effective Cartier divisors and regular meromorphic denominators admit pullback
along a chosen blowup.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Blowup

variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- The pullback of an effective Cartier divisor along a blowup morphism is defined. -/
theorem pullbackDefined (π : Blowup X I) (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] :
    Scheme.IdealSheafData.pullbackDefined D π.hom := sorry

/-- A blowup morphism pulls regular meromorphic denominators back to regular denominators. -/
theorem pullbacksRegularMeromorphicFunctionsDefined (π : Blowup X I) :
    LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined π.hom.toLRSHom := sorry

end AlgebraicGeometry.Blowup
