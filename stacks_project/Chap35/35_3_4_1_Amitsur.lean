/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Amitsur.Complex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

@[expose] public section

universe u

#check (@Algebra.Amitsur.extended :
  (R A M : Type u) → [CommRing R] → [CommRing A] → [Algebra R A] →
    [AddCommGroup M] → [Module R M] → CochainComplex (ModuleCat R) ℕ)
