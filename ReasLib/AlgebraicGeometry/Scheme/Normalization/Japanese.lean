/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents.Integral
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Coproduct.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Finite.Cover
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Basic
public import ReasLib.RingTheory.IntegralClosure.Pi

/-!
# Normalization of Japanese schemes

The normalization morphism of an integral Japanese scheme is finite.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The normalization morphism of an integral Japanese scheme is finite. -/
theorem isFinite_normalizationTo_of_isJapanese (X : Scheme.{u}) [IsIntegral X]
    (hX : IsJapanese X) : IsFinite X.normalizationTo := sorry

end AlgebraicGeometry.Scheme
