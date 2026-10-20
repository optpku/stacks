/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.QuasiAffine

/-!
# Ind-Quasi-Affine Schemes

This file defines ind-quasi-affineness for schemes and records its basic
relationship with quasi-affineness.
-/

@[expose] public section

open TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme is ind-quasi-affine if each of its quasi-compact open subschemes is
quasi-affine. -/
class IsIndQuasiAffine (X : Scheme.{u}) : Prop where
  quasiAffine_of_isCompact :
    ∀ (U : X.Opens), IsCompact (U : Set X) → U.toScheme.IsQuasiAffine

namespace IsQuasiAffine

/-- Every quasi-affine scheme is ind-quasi-affine. -/
instance isIndQuasiAffine (X : Scheme.{u}) [X.IsQuasiAffine] : X.IsIndQuasiAffine := sorry

end IsQuasiAffine

/-- Ind-quasi-affineness is equivalent to quasi-affineness of every
quasi-compact open subscheme. -/
theorem isIndQuasiAffine_iff (X : Scheme.{u}) :
    X.IsIndQuasiAffine ↔
      ∀ (U : X.Opens), IsCompact (U : Set X) → U.toScheme.IsQuasiAffine := sorry

end AlgebraicGeometry.Scheme
