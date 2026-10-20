/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Multiplicity

universe u v

#check (CategoryTheory.CochainComplex.multiplicity :
  ∀ {R : Type u} [Ring R] (K : CochainComplex (ModuleCat.{v} R) (ZMod 2)),
    IsFiniteLength R (K.homology 0) → IsFiniteLength R (K.homology 1) → ℤ)

#check (CategoryTheory.CochainComplex.multiplicity_def :
  ∀ {R : Type u} [Ring R] (K : CochainComplex (ModuleCat.{v} R) (ZMod 2))
    (h₀ : IsFiniteLength R (K.homology 0)) (h₁ : IsFiniteLength R (K.homology 1)),
    CategoryTheory.CochainComplex.multiplicity K h₀ h₁ =
      ((Module.length R (K.homology 0)).toNat : ℤ) -
        ((Module.length R (K.homology 1)).toNat : ℤ))

#check (CategoryTheory.TwoPeriodicEndomorphism.multiplicity :
  ∀ {R : Type u} [Ring R]
    (K : CategoryTheory.TwoPeriodicEndomorphism (ModuleCat.{v} R)),
    IsFiniteLength R (K.toCochainComplex.homology 0) →
      IsFiniteLength R (K.toCochainComplex.homology 1) → ℤ)

#check (CategoryTheory.TwoPeriodicEndomorphism.multiplicity_eq :
  ∀ {R : Type u} [Ring R]
    (K : CategoryTheory.TwoPeriodicEndomorphism (ModuleCat.{v} R))
    (h₀ : IsFiniteLength R (K.toCochainComplex.homology 0))
    (h₁ : IsFiniteLength R (K.toCochainComplex.homology 1)),
    CategoryTheory.TwoPeriodicEndomorphism.multiplicity K h₀ h₁ =
      CategoryTheory.CochainComplex.multiplicity K.toCochainComplex h₀ h₁)
