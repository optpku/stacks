/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Determinant

universe u v

#check (CategoryTheory.TwoPeriodicEndomorphism.determinant :
  ∀ {R : Type u} [CommRing R] [IsLocalRing R]
    (K : CategoryTheory.TwoPeriodicEndomorphism (ModuleCat.{v} R))
    (hM : IsFiniteLength R K.X) (hK : K.toCochainComplex.Acyclic),
    (IsLocalRing.ResidueField R)ˣ)
