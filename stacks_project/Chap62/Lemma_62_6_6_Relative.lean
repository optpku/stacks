module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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

/-- Coefficients of specialization are the weighted associated cycles of scheme-theoretic images
of generic-fibre components, restricted to the closed fibre. -/
theorem specialize_apply
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] (r : ℕ)
    (α : f.fiberCycleGroup (genericPoint (Spec (CommRingCat.of R))) r)
    (x : f.fiber (IsLocalRing.closedPoint R)) :
    CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r
        (specialize f r α) x =
      Scheme.Hom.cycleSpecializationCoeff f r α x := sorry

/-- A family of fibrewise `r`-cycles is a relative `r`-cycle when it is compatible with
specialization after every base change to the spectrum of a discrete valuation ring. -/
def IsRelative {X S : Scheme.{u}} {f : X ⟶ S} [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] {r : ℕ} (α : Family f r) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (g : Spec (CommRingCat.of R) ⟶ S),
    specialize (pullback.snd f g) r
        (FamilyOfCyclesOnFibres.baseChange f g r α
          (genericPoint (Spec (CommRingCat.of R)))) =
      FamilyOfCyclesOnFibres.baseChange f g r α (IsLocalRing.closedPoint R)

/-- Relative `r`-cycles are exactly the fibrewise families compatible with DVR specialization. -/
theorem isRelative_iff {X S : Scheme.{u}} {f : X ⟶ S} [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] {r : ℕ} (α : Family f r) :
    IsRelative α ↔
      ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
        (g : Spec (CommRingCat.of R) ⟶ S),
        specialize (pullback.snd f g) r
            (FamilyOfCyclesOnFibres.baseChange f g r α
              (genericPoint (Spec (CommRingCat.of R)))) =
          FamilyOfCyclesOnFibres.baseChange f g r α
            (IsLocalRing.closedPoint R) := sorry

end AlgebraicGeometry.RelativeCycle
