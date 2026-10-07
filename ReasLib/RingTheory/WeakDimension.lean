module

public import ReasLib.Algebra.Category.ModuleCat.FlatResolution
public import ReasLib.RingTheory.GlobalDimension.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Weak dimension of rings

Weak dimension is the uniform Tor-dimension bound on all modules.  This owner parallels
`HasGlobalDimensionLE`, while delegating the module-level invariant to the generic derived-tensor
API specialized to `ModuleCat`.

@stack 092D
-/

@[expose] public section

open CategoryTheory

universe u

variable (R : Type u) [CommRing R]

/-- A ring has weak dimension at most `d` when every module has Tor dimension at most `d`. -/
@[stacks 092D]
class HasWeakDimensionLE (d : ℕ) : Prop where
  /-- Every module has the prescribed Tor-dimension bound. -/
  hasTorDimensionLE (M : ModuleCat.{u} R) :
    DerivedCategory.DerivedTensor.HasTorDimensionLE M d

/-- A weak-dimension bound supplies a finite flat resolution for every module. -/
theorem HasWeakDimensionLE.hasFiniteFlatResolutionLengthLE (d : ℕ)
    [HasWeakDimensionLE R d] (M : ModuleCat.{u} R) :
    ModuleCat.HasFiniteFlatResolutionLengthLE M d := sorry

/-- A global-dimension bound implies the same weak-dimension bound. -/
@[stacks 092D "weak-dimension bound induced by a global-dimension bound"]
instance instOfGlobalDimensionLE (d : ℕ) [HasGlobalDimensionLE R d] :
    HasWeakDimensionLE R d := sorry
