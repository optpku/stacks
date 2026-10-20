/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- An integral one-dimensional closed subscheme of an integral smooth surface over a field
is an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_of_smoothSurface
    {k : Type u} [Field k] (S : SchemeOverField k) [Smooth S.hom]
    [IsIntegral S.left] (hSdim : topologicalKrullDim S.left = 2)
    (C : S.left.IdealSheafData) [IsIntegral C.subscheme]
    (hCdim : topologicalKrullDim C.subscheme = 1) :
    IsEffectiveCartierDivisor C.subschemeι := sorry

/-- An integral curve on an integral smooth surface of dimension two canonically defines an
effective Cartier divisor. -/
instance instIsEffectiveCartierDivisorOfSmoothSurface
    {k : Type u} [Field k] (S : SchemeOverField k) [Smooth S.hom]
    [IsIntegral S.left] [Fact (topologicalKrullDim S.left = 2)]
    (C : S.left.IdealSheafData) [IsIntegral C.subscheme]
    [Fact (topologicalKrullDim C.subscheme = 1)] :
    IsEffectiveCartierDivisor C.subschemeι :=
  isEffectiveCartierDivisor_of_smoothSurface S Fact.out C Fact.out

end AlgebraicGeometry.Scheme.IdealSheafData
