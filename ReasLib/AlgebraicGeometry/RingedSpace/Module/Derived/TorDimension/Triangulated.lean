/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Stalk
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude.Triangulated
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude.Retracts
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Triangles and summands of Tor-amplitude objects

This is the ringed-space view of the generic `DerivedTensor.TorAmplitude` closure API.  The
source-facing statements use the intrinsic `D(𝒪_X)` object property and do not expose stalk
transport or the complex-level tensor instances used by the generic owner.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Pretriangulated

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.TorAmplitude

variable {X : RingedSpace.{u}} {a b : ℤ}

/-- Lemma 20.48.6 (1): the third vertex inherits the common Tor-amplitude interval. -/
@[stacks 08CJ "(1)"]
theorem obj₃_of_distinguished
    (T : Triangle (RingedSpace.ModuleDerived X))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived X))
    (h₁ : RingedSpace.HasTorAmplitudeIn T.obj₁ (a + 1) (b + 1))
    (h₂ : RingedSpace.HasTorAmplitudeIn T.obj₂ a b) :
    RingedSpace.HasTorAmplitudeIn T.obj₃ a b := sorry

/-- Lemma 20.48.6 (2): the middle vertex inherits the common Tor-amplitude interval. -/
@[stacks 08CJ "(2)"]
theorem obj₂_of_distinguished
    (T : Triangle (RingedSpace.ModuleDerived X))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived X))
    (h₁ : RingedSpace.HasTorAmplitudeIn T.obj₁ a b)
    (h₃ : RingedSpace.HasTorAmplitudeIn T.obj₃ a b) :
    RingedSpace.HasTorAmplitudeIn T.obj₂ a b := sorry

/-- Lemma 20.48.6 (3): the first vertex inherits the shifted interval. -/
@[stacks 08CJ "(3)"]
theorem obj₁_of_distinguished
    (T : Triangle (RingedSpace.ModuleDerived X))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived X))
    (h₂ : RingedSpace.HasTorAmplitudeIn T.obj₂ (a + 1) (b + 1))
    (h₃ : RingedSpace.HasTorAmplitudeIn T.obj₃ a b) :
    RingedSpace.HasTorAmplitudeIn T.obj₁ (a + 1) (b + 1) := sorry

/-- Lemma 20.48.8: Tor-amplitude in a fixed interval descends to both biproduct summands. -/
@[stacks 08CK]
theorem summands_of_biprod
    (K L : RingedSpace.ModuleDerived X)
    (hKL : RingedSpace.HasTorAmplitudeIn (K ⊞ L) a b) :
    RingedSpace.HasTorAmplitudeIn K a b ∧
      RingedSpace.HasTorAmplitudeIn L a b := sorry

/-- The left summand of a biproduct inherits its Tor-amplitude interval. -/
theorem left_of_biprod
    (K L : RingedSpace.ModuleDerived X)
    (hKL : RingedSpace.HasTorAmplitudeIn (K ⊞ L) a b) :
    RingedSpace.HasTorAmplitudeIn K a b := sorry

/-- The right summand of a biproduct inherits its Tor-amplitude interval. -/
theorem right_of_biprod
    (K L : RingedSpace.ModuleDerived X)
    (hKL : RingedSpace.HasTorAmplitudeIn (K ⊞ L) a b) :
    RingedSpace.HasTorAmplitudeIn L a b := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.TorAmplitude
