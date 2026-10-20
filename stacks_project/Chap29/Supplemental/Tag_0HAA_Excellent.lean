/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Excellent

/-!
# Excellent and quasi-excellent schemes

A scheme is (quasi-)excellent when the corresponding ring property holds on an affine open
neighbourhood of every point. These predicates are the scheme-level specializations of
`HasRingPropertyLocally` to `IsExcellentRing` and `IsQuasiExcellentRing`.
-/

universe u

#check (AlgebraicGeometry.Scheme.QuasiExcellent : AlgebraicGeometry.Scheme.{u} → Prop)
#check (AlgebraicGeometry.Scheme.Excellent : AlgebraicGeometry.Scheme.{u} → Prop)
