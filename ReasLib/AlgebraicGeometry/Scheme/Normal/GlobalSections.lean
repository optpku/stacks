/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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
