/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle
public import stacks_project.Chap62.Lemma_62_6_6_Relative

/-!
# The group of relative cycles

This file names the additive group `z(X/S, r)` of relative `r`-cycles on a
locally finite type morphism `f : X ⟶ S` from a locally Noetherian scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

#check (AlgebraicGeometry.RelativeCycle.isRelative_zero :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] (r : ℕ), IsRelative (0 : f.FiberCycleFamily r))

#check (AlgebraicGeometry.RelativeCycle.isRelative_add :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] (r : ℕ) {α β : f.FiberCycleFamily r},
    IsRelative α → IsRelative β → IsRelative (α + β))

#check (AlgebraicGeometry.RelativeCycle.isRelative_neg :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] (r : ℕ) {α : f.FiberCycleFamily r},
    IsRelative α → IsRelative (-α))

#check (AlgebraicGeometry.RelativeCycle.group :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] (r : ℕ), AddSubgroup (f.FiberCycleFamily r))

#check (AlgebraicGeometry.RelativeCycle.mem_group_iff :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] (r : ℕ) (α : f.FiberCycleFamily r),
    α ∈ group f r ↔ IsRelative α)

#check (AlgebraicGeometry.RelativeCycle.mem_group_iff_specialization :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] (r : ℕ) (α : f.FiberCycleFamily r),
    α ∈ group f r ↔
      ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
        (g : Spec (CommRingCat.of R) ⟶ S),
        Scheme.Hom.cycleSpecialization (pullback.snd f g) r
            (FamilyOfCyclesOnFibres.baseChange f g r α
              (genericPoint (Spec (CommRingCat.of R)))) =
          FamilyOfCyclesOnFibres.baseChange f g r α (IsLocalRing.closedPoint R))

end AlgebraicGeometry.RelativeCycle
