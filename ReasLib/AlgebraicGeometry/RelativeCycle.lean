/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Specialization

/-!
# Relative cycles

Relative cycles are families of fibre cycles compatible with specialization
after every base change to the spectrum of a discrete valuation ring.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- A family of fibrewise `r`-cycles is relative when its base change along every
morphism from the spectrum of a discrete valuation ring is compatible with specialization. -/
def IsRelative {X S : Scheme.{u}} {f : X ⟶ S} [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] {r : ℕ} (α : f.FiberCycleFamily r) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (g : Spec (CommRingCat.of R) ⟶ S),
    Scheme.Hom.cycleSpecialization (pullback.snd f g) r
        (FamilyOfCyclesOnFibres.baseChange f g r α
          (genericPoint (Spec (CommRingCat.of R)))) =
      FamilyOfCyclesOnFibres.baseChange f g r α (IsLocalRing.closedPoint R)

/-- Relative `r`-cycles are exactly the fibrewise families compatible with specialization
after every base change to the spectrum of a discrete valuation ring. -/
theorem isRelative_iff {X S : Scheme.{u}} {f : X ⟶ S} [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] {r : ℕ} (α : f.FiberCycleFamily r) :
    IsRelative α ↔
      ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
        (g : Spec (CommRingCat.of R) ⟶ S),
        Scheme.Hom.cycleSpecialization (pullback.snd f g) r
            (FamilyOfCyclesOnFibres.baseChange f g r α
              (genericPoint (Spec (CommRingCat.of R)))) =
          FamilyOfCyclesOnFibres.baseChange f g r α (IsLocalRing.closedPoint R) := sorry

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f]
variable (r : ℕ)

/-- The zero family of fibrewise `r`-cycles is a relative `r`-cycle. -/
theorem isRelative_zero : IsRelative (0 : f.FiberCycleFamily r) := sorry

/-- The sum of relative `r`-cycles is a relative `r`-cycle. -/
theorem isRelative_add {α β : f.FiberCycleFamily r} (hα : IsRelative α)
    (hβ : IsRelative β) : IsRelative (α + β) := sorry

/-- The negative of a relative `r`-cycle is a relative `r`-cycle. -/
theorem isRelative_neg {α : f.FiberCycleFamily r} (hα : IsRelative α) :
    IsRelative (-α) := sorry

/-- The additive subgroup of fibrewise `r`-cycle families compatible with
specialization after every base change to the spectrum of a discrete valuation ring. -/
def group : AddSubgroup (f.FiberCycleFamily r) where
  carrier := {α | IsRelative α}
  zero_mem' := isRelative_zero f r
  add_mem' := isRelative_add f r
  neg_mem' := isRelative_neg f r

/-- Membership in the subgroup of relative `r`-cycles is the predicate `IsRelative`. -/
theorem mem_group_iff (α : f.FiberCycleFamily r) :
    α ∈ group f r ↔ IsRelative α := sorry

/-- A family lies in the subgroup of relative `r`-cycles if and only if specialization
after every discrete valuation ring base change sends its generic-fibre value to
its closed-fibre value. -/
theorem mem_group_iff_specialization (α : f.FiberCycleFamily r) :
    α ∈ group f r ↔
      ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
        (g : Spec (CommRingCat.of R) ⟶ S),
        Scheme.Hom.cycleSpecialization (pullback.snd f g) r
            (FamilyOfCyclesOnFibres.baseChange f g r α
              (genericPoint (Spec (CommRingCat.of R)))) =
          FamilyOfCyclesOnFibres.baseChange f g r α (IsLocalRing.closedPoint R) := sorry

end AlgebraicGeometry.RelativeCycle
