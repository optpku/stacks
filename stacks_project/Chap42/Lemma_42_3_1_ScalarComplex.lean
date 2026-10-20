/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Scalar.Multiplicity

universe u v

open CategoryTheory

#check (CategoryTheory.TwoPeriodicEndomorphism.ofZeroScalar :
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x : R),
    CategoryTheory.TwoPeriodicEndomorphism (ModuleCat R))

#check (CategoryTheory.TwoPeriodicEndomorphism.ofZeroScalar_X :
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x : R),
    (CategoryTheory.TwoPeriodicEndomorphism.ofZeroScalar M x).X = ModuleCat.of R M)

#check (CategoryTheory.TwoPeriodicEndomorphism.ofZeroScalar_d₀ :
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x : R),
    (CategoryTheory.TwoPeriodicEndomorphism.ofZeroScalar M x).d₀ = 0)

#check (CategoryTheory.TwoPeriodicEndomorphism.ofZeroScalar_d₁ :
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x : R),
    (CategoryTheory.TwoPeriodicEndomorphism.ofZeroScalar M x).d₁ =
      ModuleCat.ofHom (LinearMap.lsmul R M x))

#check (CategoryTheory.TwoPeriodicEndomorphism.ofZeroScalar_homology_isFiniteLength :
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : R) (_ : Module.supportDim R M ≤ 1)
    (_ : Module.supportDim R (QuotSMulTop x M) ≤ 0) (i : ZMod 2),
    IsFiniteLength R
      ((CategoryTheory.TwoPeriodicEndomorphism.ofZeroScalar M x).toCochainComplex.homology i))
