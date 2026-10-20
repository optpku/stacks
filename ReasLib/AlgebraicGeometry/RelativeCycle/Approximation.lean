module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.RelativeCycle
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.Hilbert
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Envelope
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Noetherian approximation of relative cycles

Noetherian finite-type descent of a fibre-cycle family is equivalent to Hilbert
generation after a completely decomposed proper finite-presentation base change.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Hom

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- A family of `r`-cycles on fibres of `X / S` arises by cartesian base change
from a relative `r`-cycle on a finite type morphism of Noetherian schemes. -/
def existsNoetherianBaseChange {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (r : ℕ) (α : f.FiberCycleFamily (r : ℤ)) : Prop :=
  ∃ (S0 X0 : Scheme.{u}) (f0 : X0 ⟶ S0) (hS : IsNoetherian S0)
    (hFT : f0.FiniteType) (g : S ⟶ S0) (g' : X ⟶ X0)
    (hpb : IsPullback g' f f0 g)
    (α0 : @Scheme.Hom.FiberCycleFamily X0 S0 f0 hFT.toLocallyOfFiniteType (r : ℤ)),
    IsNoetherian X0 ∧
      @IsRelative X0 S0 f0 hS.toIsLocallyNoetherian hFT.toLocallyOfFiniteType r α0 ∧
        @FiberCycleFamily.baseChange S0 X0 S X f0 g g' f
          hFT.toLocallyOfFiniteType hpb (r : ℤ) α0 = α

/-- Noetherian finite-type descent is witnessed by a cartesian square, a
relative cycle, and equality of its base change with the given family. -/
theorem existsNoetherianBaseChange_iff {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (r : ℕ) (α : f.FiberCycleFamily (r : ℤ)) :
    existsNoetherianBaseChange f r α ↔
      ∃ (S0 X0 : Scheme.{u}) (f0 : X0 ⟶ S0) (hS : IsNoetherian S0)
        (hFT : f0.FiniteType) (g : S ⟶ S0) (g' : X ⟶ X0)
        (hpb : IsPullback g' f f0 g)
        (α0 : @Scheme.Hom.FiberCycleFamily X0 S0 f0 hFT.toLocallyOfFiniteType (r : ℤ)),
        IsNoetherian X0 ∧
          @IsRelative X0 S0 f0 hS.toIsLocallyNoetherian hFT.toLocallyOfFiniteType r α0 ∧
            @FiberCycleFamily.baseChange S0 X0 S X f0 g g' f
              hFT.toLocallyOfFiniteType hpb (r : ℤ) α0 = α :=
  Iff.rfl

/-- A family of `r`-cycles on fibres of `X / S` becomes a Hilbert cycle class
after base change along some completely decomposed proper morphism of finite
presentation. -/
def existsCompletelyDecomposedHilbert {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (r : ℕ) (α : f.FiberCycleFamily (r : ℤ)) : Prop :=
  ∃ (S' : Scheme.{u}) (g : S' ⟶ S),
    IsProper g ∧ CompletelyDecomposed g ∧ Scheme.Hom.FinitePresentation g ∧
      FiberCycleFamily.baseChange (IsPullback.of_hasPullback f g) α ∈
        Set.range (hilbertCycleClass (pullback.snd f g) r)

/-- Hilbert generation after completely decomposed proper finite-presentation
base change is witnessed by a morphism with these properties and range membership
of the pulled-back family in the Hilbert cycle-class map. -/
theorem existsCompletelyDecomposedHilbert_iff {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (r : ℕ) (α : f.FiberCycleFamily (r : ℤ)) :
    existsCompletelyDecomposedHilbert f r α ↔
      ∃ (S' : Scheme.{u}) (g : S' ⟶ S),
        IsProper g ∧ CompletelyDecomposed g ∧ Scheme.Hom.FinitePresentation g ∧
          FiberCycleFamily.baseChange (IsPullback.of_hasPullback f g) α ∈
            Set.range (hilbertCycleClass (pullback.snd f g) r) :=
  Iff.rfl

/-- Over a quasi-compact quasi-separated base, a family of nonnegative-dimensional
fibre cycles for a finite-presentation morphism descends from a relative cycle on
a finite type morphism of Noetherian schemes if and only if it becomes a Hilbert
cycle class after completely decomposed proper finite-presentation base change. -/
@[stacks 0H6W]
theorem existsNoetherianBaseChange_iff_existsCompletelyDecomposedHilbert
    {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [Scheme.Hom.FinitePresentation f]
    (r : ℕ) (α : f.FiberCycleFamily (r : ℤ)) :
    existsNoetherianBaseChange f r α ↔
      existsCompletelyDecomposedHilbert f r α :=
  sorry

/-- Hilbert generation after completely decomposed proper finite-presentation
base change is equivalent to Hilbert generation after a finite-presentation
envelope. -/
theorem existsCompletelyDecomposedHilbert_iff_existsEnvelope
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (r : ℕ) (α : f.FiberCycleFamily (r : ℤ)) :
    existsCompletelyDecomposedHilbert f r α ↔
      ∃ (S' : Scheme.{u}) (g : S' ⟶ S),
        IsEnvelope g ∧ Scheme.Hom.FinitePresentation g ∧
          FiberCycleFamily.baseChange (IsPullback.of_hasPullback f g) α ∈
            Set.range (hilbertCycleClass (pullback.snd f g) r) :=
  sorry

/-- The base change of a relative cycle on a finite type morphism of Noetherian
schemes satisfies Noetherian finite-type descent on the chosen pullback. -/
theorem existsNoetherianBaseChange_of_chosenPullback
    {X0 S0 S : Scheme.{u}} (f0 : X0 ⟶ S0) (g : S ⟶ S0)
    [IsNoetherian S0] [IsNoetherian X0] [f0.FiniteType]
    (r : ℕ) {α0 : f0.FiberCycleFamily (r : ℤ)} (hα0 : IsRelative α0)
    {α : (pullback.snd f0 g).FiberCycleFamily (r : ℤ)}
    (hα : FiberCycleFamily.baseChange (IsPullback.of_hasPullback f0 g) α0 = α) :
    existsNoetherianBaseChange (pullback.snd f0 g) r α :=
  sorry

end AlgebraicGeometry.RelativeCycle
