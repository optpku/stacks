/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.AlgebraicGeometry.RelativeCycle
public import stacks_project.Chap62.Lemma_62_4_1_Specialization
public import stacks_project.Chap62.Lemma_62_6_6_Family

/-!
# Relative cycles

This file records the specialization-compatibility predicate that distinguishes
relative `r`-cycles among families of fibrewise cycles.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Specialization `sp_{X/R} : Z_r(X_η) → Z_r(X_0)` along a discrete valuation ring. -/
noncomputable abbrev specialize
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] (r : ℕ) :
    f.fiberCycleGroup (genericPoint (Spec (CommRingCat.of R))) r →+
      f.fiberCycleGroup (IsLocalRing.closedPoint R) r :=
  Scheme.Hom.cycleSpecialization f r

#check (AlgebraicGeometry.Scheme.Hom.cycleSpecialization_apply :
  ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] (r : ℕ)
    (α : f.fiberCycleGroup (genericPoint (Spec (CommRingCat.of R))) r)
    (x : f.fiber (IsLocalRing.closedPoint R)),
    CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r
        (specialize f r α) x =
      Scheme.Hom.cycleSpecializationCoeff f r α x)

#check (AlgebraicGeometry.RelativeCycle.IsRelative :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S} [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] {r : ℕ}, f.FiberCycleFamily r → Prop)

#check (AlgebraicGeometry.RelativeCycle.isRelative_iff :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S} [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] {r : ℕ} (α : f.FiberCycleFamily r),
    IsRelative α ↔
      ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
        (g : Spec (CommRingCat.of R) ⟶ S),
        Scheme.Hom.cycleSpecialization (pullback.snd f g) r
            (FamilyOfCyclesOnFibres.baseChange f g r α
              (genericPoint (Spec (CommRingCat.of R)))) =
          FamilyOfCyclesOnFibres.baseChange f g r α
            (IsLocalRing.closedPoint R))

end AlgebraicGeometry.RelativeCycle
