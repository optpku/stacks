module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CompletelyDecomposed
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import stacks_project.Chap62.«62_16_0_1_CycleClass»
public import stacks_project.Chap62.Definition_62_6_1_Specialization
public import stacks_project.Chap62.Lemma_62_5_1_Operations

/-!
# Non-Noetherian approximations of fibre-cycle families

This file names the two existence conditions of Lemma 62.16.1: descent from a
relative cycle on a finite type morphism of Noetherian schemes, and landing in
the image of `hilbertCycleClass` after a completely decomposed proper
finite-presentation base change.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Hom

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- The relative-cycle predicate with explicit locally Noetherian and locally
finite type hypotheses, for use when those facts are existential witnesses
rather than ambient instances. -/
def isRelativeWith {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ) (α : Family f r)
    (hS : IsLocallyNoetherian S) (hf : LocallyOfFiniteType f) : Prop :=
  @IsRelative X S f hS hf r α

/-- When the locally Noetherian and locally finite type instances are available,
`isRelativeWith` agrees with `IsRelative`. -/
theorem isRelativeWith_iff {X S : Scheme.{u}} {f : X ⟶ S}
    [hS : IsLocallyNoetherian S] [hf : LocallyOfFiniteType f]
    (r : ℕ) (α : Family f r) :
    isRelativeWith f r α hS hf ↔ IsRelative α :=
  sorry

/-- Base change of a fibre-cycle family along a cartesian square, with an
explicit locally finite type hypothesis on the original morphism. -/
noncomputable def baseChangeWith {S X S' X' : Scheme.{u}} {f : X ⟶ S}
    {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'} (hf : LocallyOfFiniteType f)
    (hpb : IsPullback g' f' f g) {r : ℤ} (α : f.FiberCycleFamily r) :
    f'.FiberCycleFamily r :=
  @FiberCycleFamily.baseChange S X S' X' f g g' f' hf hpb r α

/-- `baseChangeWith` agrees with `FiberCycleFamily.baseChange` when the locally
finite type instance is available. -/
theorem baseChangeWith_eq {S X S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} [hf : LocallyOfFiniteType f]
    (hpb : IsPullback g' f' f g) {r : ℤ} (α : f.FiberCycleFamily r) :
    baseChangeWith hf hpb α = FiberCycleFamily.baseChange hpb α :=
  sorry

/-- A family of `r`-cycles on fibres of `X / S` arises by cartesian base change
from a relative `r`-cycle on a finite type morphism of Noetherian schemes. -/
def existsNoetherianBaseChange {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (r : ℕ) (α : f.FiberCycleFamily (r : ℤ)) : Prop :=
  ∃ (S0 X0 : Scheme.{u}) (f0 : X0 ⟶ S0) (hS : IsNoetherian S0)
    (hFT : f0.FiniteType) (g : S ⟶ S0) (g' : X ⟶ X0)
    (hpb : IsPullback g' f f0 g) (α0 : Family f0 r),
    IsNoetherian X0 ∧
      isRelativeWith f0 r α0 hS.toIsLocallyNoetherian hFT.toLocallyOfFiniteType ∧
        baseChangeWith hFT.toLocallyOfFiniteType hpb α0 = α

/-- Unfolding of `existsNoetherianBaseChange`: a cartesian square from a finite
type morphism of Noetherian schemes, a relative `r`-cycle on that morphism, and
agreement after `FiberCycleFamily.baseChange`. -/
theorem existsNoetherianBaseChange_iff {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (r : ℕ) (α : f.FiberCycleFamily (r : ℤ)) :
    existsNoetherianBaseChange f r α ↔
      ∃ (S0 X0 : Scheme.{u}) (f0 : X0 ⟶ S0) (hS : IsNoetherian S0)
        (hFT : f0.FiniteType) (g : S ⟶ S0) (g' : X ⟶ X0)
        (hpb : IsPullback g' f f0 g) (α0 : Family f0 r),
        IsNoetherian X0 ∧
          isRelativeWith f0 r α0 hS.toIsLocallyNoetherian
              hFT.toLocallyOfFiniteType ∧
            baseChangeWith hFT.toLocallyOfFiniteType hpb α0 = α :=
  sorry

/-- A family of `r`-cycles on fibres of `X / S` becomes a Hilbert cycle class
after base change along some completely decomposed proper morphism of finite
presentation. -/
def existsCompletelyDecomposedHilbert {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (r : ℕ) (α : f.FiberCycleFamily (r : ℤ)) : Prop :=
  ∃ (S' : Scheme.{u}) (g : S' ⟶ S),
    IsProper g ∧ CompletelyDecomposed g ∧ Scheme.Hom.FinitePresentation g ∧
      FiberCycleFamily.baseChange (IsPullback.of_hasPullback f g) α ∈
        Set.range (hilbertCycleClass (pullback.snd f g) r)

/-- Unfolding of `existsCompletelyDecomposedHilbert`: a completely decomposed
proper finite-presentation morphism whose base change of `α` lies in the range
of `hilbertCycleClass`. -/
theorem existsCompletelyDecomposedHilbert_iff {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (r : ℕ) (α : f.FiberCycleFamily (r : ℤ)) :
    existsCompletelyDecomposedHilbert f r α ↔
      ∃ (S' : Scheme.{u}) (g : S' ⟶ S),
        IsProper g ∧ CompletelyDecomposed g ∧
          Scheme.Hom.FinitePresentation g ∧
            FiberCycleFamily.baseChange (IsPullback.of_hasPullback f g) α ∈
              Set.range (hilbertCycleClass (pullback.snd f g) r) :=
  sorry

end AlgebraicGeometry.RelativeCycle
