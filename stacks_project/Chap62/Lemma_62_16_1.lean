/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Envelope
public import stacks_project.Chap62.Lemma_62_16_1_Approximation

/-!
# Relative cycles in the non-Noetherian case

This file records the equivalence between Noetherian finite-type approximation
of a fibre-cycle family and membership in the image of `hilbertCycleClass`
after a completely decomposed proper finite-presentation base change.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Hom

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Lemma 62.16.1: for a quasi-compact quasi-separated scheme `S`, a morphism
`f : X ⟶ S` of finite presentation, `r ≥ 0`, and a family `α` of `r`-cycles on
fibres of `X / S`, the following are equivalent: (1) `α` is the base change of
some relative `r`-cycle `α0 ∈ z(X0 / S0, r)` along a cartesian square from a
finite type morphism of Noetherian schemes `X0 ⟶ S0`; (2) some completely
decomposed proper morphism `g : S' ⟶ S` of finite presentation has `g^* α` in
the image of the Hilbert cycle-class map `hilbertCycleClass` (62.16.0.1). -/
@[stacks 0H6W]
theorem existsNoetherianBaseChange_iff_existsCompletelyDecomposedHilbert
    {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [Scheme.Hom.FinitePresentation f]
    (r : ℕ) (α : f.FiberCycleFamily (r : ℤ)) :
    existsNoetherianBaseChange f r α ↔
      existsCompletelyDecomposedHilbert f r α :=
  sorry

/-- A Noetherian finite-type approximation of a fibre-cycle family yields a
completely decomposed proper finite-presentation base change whose pullback
lies in the image of `hilbertCycleClass`. -/
theorem existsCompletelyDecomposedHilbert_of_existsNoetherianBaseChange
    {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [Scheme.Hom.FinitePresentation f]
    (r : ℕ) (α : f.FiberCycleFamily (r : ℤ))
    (hα : existsNoetherianBaseChange f r α) :
    existsCompletelyDecomposedHilbert f r α :=
  sorry

/-- If some completely decomposed proper finite-presentation base change of a
fibre-cycle family lies in the image of `hilbertCycleClass`, then the family
arises from a relative cycle on a finite type morphism of Noetherian schemes. -/
theorem existsNoetherianBaseChange_of_existsCompletelyDecomposedHilbert
    {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [Scheme.Hom.FinitePresentation f]
    (r : ℕ) (α : f.FiberCycleFamily (r : ℤ))
    (hα : existsCompletelyDecomposedHilbert f r α) :
    existsNoetherianBaseChange f r α :=
  sorry

/-- Condition (2) is equivalent to the same statement with a proper completely
decomposed morphism packaged as an envelope. -/
theorem existsCompletelyDecomposedHilbert_iff_existsEnvelope
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (r : ℕ) (α : f.FiberCycleFamily (r : ℤ)) :
    existsCompletelyDecomposedHilbert f r α ↔
      ∃ (S' : Scheme.{u}) (g : S' ⟶ S),
        IsEnvelope g ∧ Scheme.Hom.FinitePresentation g ∧
          FiberCycleFamily.baseChange (IsPullback.of_hasPullback f g) α ∈
            Set.range (hilbertCycleClass (pullback.snd f g) r) :=
  sorry

/-- A sufficient form of condition (1): if `X` is the chosen pullback of a
finite type morphism of Noetherian schemes and `α` is the corresponding
`FiberCycleFamily.baseChange` of a relative `r`-cycle, then
`existsNoetherianBaseChange` holds. -/
theorem existsNoetherianBaseChange_of_chosenPullback
    {X0 S0 S : Scheme.{u}} (f0 : X0 ⟶ S0) (g : S ⟶ S0)
    [hS0 : IsNoetherian S0] [hX0 : IsNoetherian X0] [hFT : f0.FiniteType]
    (r : ℕ) {α0 : Family f0 r}
    (hα0 : isRelativeWith f0 r α0 hS0.toIsLocallyNoetherian
      hFT.toLocallyOfFiniteType)
    {α : (pullback.snd f0 g).FiberCycleFamily (r : ℤ)}
    (hα : FiberCycleFamily.baseChange (IsPullback.of_hasPullback f0 g) α0 = α) :
    existsNoetherianBaseChange (pullback.snd f0 g) r α :=
  sorry

end AlgebraicGeometry.RelativeCycle
