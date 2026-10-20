/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.FiniteTypeInverseSystem

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.FiniteTypeInverseSystem :
  (A : Type u) → [CommRing A] → [TopologicalSpace A] →
    Type (u + 1))
