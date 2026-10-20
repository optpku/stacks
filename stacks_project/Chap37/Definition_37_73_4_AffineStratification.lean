/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineStratification

@[expose] public section

universe u

#check (AlgebraicGeometry.Scheme.FiniteAffineStratification.number :
  (X : AlgebraicGeometry.Scheme.{u}) → [Nonempty X] → [CompactSpace X] →
    [QuasiSeparatedSpace X] → ℕ)
