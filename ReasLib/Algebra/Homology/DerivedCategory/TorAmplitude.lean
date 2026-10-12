/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tor-amplitude of derived module complexes

The generic owner is `CategoryTheory.DerivedCategory.DerivedTensor`.  This file is the thin
`ModuleCat` specialization: it preserves the explicit base-ring spelling used in algebra while
sharing the actual predicates and their general API with ringed spaces and other monoidal abelian
categories.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory

variable (R : Type u) [CommRing R]

/-- The module-category specialization of Tor-amplitude in `[a, b]`. -/
@[stacks 0652 "(1), module-category specialization"]
abbrev HasTorAmplitudeIn (K : DerivedCategory (ModuleCat R)) (a b : ℤ) : Prop :=
  DerivedTensor.HasTorAmplitudeIn K a b

/-- The module-category specialization of finite Tor dimension. -/
@[stacks 0652 "(2), module-category specialization"]
abbrev HasFiniteTorDimension (K : DerivedCategory (ModuleCat R)) : Prop :=
  DerivedTensor.HasFiniteTorDimension K

/-- Finite Tor dimension is the existence of a finite Tor-amplitude interval. -/
@[stacks 0652 "finite Tor dimension as a Tor-amplitude interval"]
theorem hasFiniteTorDimension_iff (K : DerivedCategory (ModuleCat R)) :
    HasFiniteTorDimension R K ↔ ∃ a b : ℤ, HasTorAmplitudeIn R K a b := sorry
/- Proof strategy: specialize
`DerivedTensor.hasFiniteTorDimension_iff` to `C := ModuleCat R`. -/

/-- Tor-amplitude in a fixed finite interval implies finite Tor dimension. -/
@[stacks 0652 "interval Tor amplitude implies finite Tor dimension"]
theorem HasTorAmplitudeIn.hasFiniteTorDimension
    {K : DerivedCategory (ModuleCat R)} {a b : ℤ} (hK : HasTorAmplitudeIn R K a b) :
    HasFiniteTorDimension R K := sorry
/- Proof strategy: apply the generic
`DerivedTensor.HasTorAmplitudeIn.hasFiniteTorDimension` constructor. -/

/-- The module-category specialization of a lower Tor-amplitude bound. -/
@[stacks 0652 "lower Tor-amplitude, module-category specialization"]
abbrev HasTorAmplitudeGE (K : DerivedCategory (ModuleCat R)) (a : ℤ) : Prop :=
  DerivedTensor.HasTorAmplitudeGE K a

/-- A finite Tor-amplitude interval supplies its lower bound. -/
@[stacks 0652 "interval Tor amplitude supplies a lower bound"]
theorem HasTorAmplitudeIn.hasTorAmplitudeGE
    {K : DerivedCategory (ModuleCat R)} {a b : ℤ} (hK : HasTorAmplitudeIn R K a b) :
    HasTorAmplitudeGE R K a := sorry
/- Proof strategy: apply the generic lower-bound projection
`DerivedTensor.HasTorAmplitudeIn.hasTorAmplitudeGE`. -/

/-- The module-category specialization of an upper Tor-amplitude bound. -/
@[stacks 0652 "upper Tor-amplitude, module-category specialization"]
abbrev HasTorAmplitudeLE (K : DerivedCategory (ModuleCat R)) (b : ℤ) : Prop :=
  DerivedTensor.HasTorAmplitudeLE K b

/-- A finite Tor-amplitude interval supplies its upper bound. -/
@[stacks 0652 "interval Tor amplitude supplies an upper bound"]
theorem HasTorAmplitudeIn.hasTorAmplitudeLE
    {K : DerivedCategory (ModuleCat R)} {a b : ℤ} (hK : HasTorAmplitudeIn R K a b) :
    HasTorAmplitudeLE R K b := sorry
/- Proof strategy: apply the generic upper-bound projection
`DerivedTensor.HasTorAmplitudeIn.hasTorAmplitudeLE`. -/

/-- Lower Tor-amplitude is equivalent to vanishing of the tested tensor homology
below its lower bound. -/
@[stacks 0652 "lower Tor-amplitude vanishing criterion"]
theorem hasTorAmplitudeGE_iff (K : DerivedCategory (ModuleCat R)) (a : ℤ) :
    HasTorAmplitudeGE R K a ↔
      ∀ (M : ModuleCat R) (i : ℤ), i < a →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
          (DerivedTensor.Right.obj K
            ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj M))) := sorry
/- Proof strategy: specialize the generic lower-support criterion to `ModuleCat R`, then use
`DerivedCategory.isGE_iff` to express the result through homology vanishing. -/

/-- Upper Tor-amplitude is equivalent to vanishing of the tested tensor homology
above its upper bound. -/
@[stacks 0652 "upper Tor-amplitude vanishing criterion"]
theorem hasTorAmplitudeLE_iff (K : DerivedCategory (ModuleCat R)) (b : ℤ) :
    HasTorAmplitudeLE R K b ↔
      ∀ (M : ModuleCat R) (i : ℤ), b < i →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
          (DerivedTensor.Right.obj K
            ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj M))) := sorry
/- Proof strategy: specialize the generic upper-support criterion to `ModuleCat R`, then use
`DerivedCategory.isLE_iff` to express the result through homology vanishing. -/

end CategoryTheory.DerivedCategory

namespace CategoryTheory.ModuleCat

variable (R : Type u) [CommRing R]

/-- The generic Tor-dimension predicate specialized to an `R`-module. -/
@[stacks 0652 "(3), module-category specialization"]
abbrev HasTorDimensionLE (M : ModuleCat R) (d : ℕ) : Prop :=
  DerivedCategory.DerivedTensor.HasTorDimensionLE M d

/-- Finite Tor dimension for a degree-zero `R`-module. -/
@[stacks 0652 "(4), module-category specialization"]
abbrev HasFiniteTorDimension (M : ModuleCat R) : Prop :=
  DerivedCategory.DerivedTensor.HasFiniteTorDimension
    ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj M)

end CategoryTheory.ModuleCat

namespace CategoryTheory.DerivedCategory

variable (R : Type u) [CommRing R]

/-- A bounded cochain complex whose terms have finite Tor dimension has finite Tor dimension
after passage to the derived category. -/
@[stacks 066H "bounded termwise finite Tor dimension"]
theorem HasFiniteTorDimension.of_bounded_of_termwise
    (K : CochainComplex (ModuleCat R) ℤ)
    (hbounded : CochainComplex.bounded (ModuleCat R) K)
    (hterm : ∀ i : ℤ, ModuleCat.HasFiniteTorDimension (R := R) (K.X i)) :
    HasFiniteTorDimension R (DerivedCategory.Q.obj K) := sorry
/- Proof strategy: choose common Tor-amplitude bounds for the finitely many nonzero terms, then
propagate them through the bounded complex by the triangulated Tor-amplitude API. -/

end CategoryTheory.DerivedCategory
