/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Local
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Characterizations of perfect derived modules on ringed spaces

The public statements use the native ringed-space predicates.  Tensor totalizations, derived
tensor existence, and restriction presentations are inferred by the owner leaves and do not
appear as mathematical hypotheses.
-/

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}

/-- Lemma 20.49.4: if `E` has Tor-amplitude in a nonempty interval `[a, b]` and is
`(a - 1)`-pseudo-coherent, then `E` is perfect. -/
@[stacks 08CP]
theorem isPerfect_of_hasTorAmplitudeIn_of_isMPseudoCoherent
    (E : ModuleDerived X) (a b : ℤ) (hab : a ≤ b)
    (hamp : RingedSpace.HasTorAmplitudeIn E a b)
    (hpc : IsMPseudoCoherent E (a - 1)) :
    IsPerfect E := sorry

/-- Lemma 20.49.5: a derived `𝒪_X`-module is perfect exactly when it is pseudo-coherent
and locally has finite Tor dimension. -/
@[stacks 08CQ]
theorem isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension
    (E : ModuleDerived X) :
    IsPerfect E ↔ IsPseudoCoherent E ∧ LocallyHasFiniteTorDimension E := sorry

/-- A perfect derived module is pseudo-coherent and locally has finite Tor dimension. -/
theorem IsPerfect.isPseudoCoherent_and_locallyHasFiniteTorDimension
    {E : ModuleDerived X} (hE : IsPerfect E) :
    IsPseudoCoherent E ∧ LocallyHasFiniteTorDimension E := sorry

/-- A perfect derived module is pseudo-coherent. -/
theorem IsPerfect.isPseudoCoherent
    {E : ModuleDerived X} (hE : IsPerfect E) :
    IsPseudoCoherent E := sorry

/-- A perfect derived module locally has finite Tor dimension. -/
theorem IsPerfect.locallyHasFiniteTorDimension
    {E : ModuleDerived X} (hE : IsPerfect E) :
    LocallyHasFiniteTorDimension E := sorry

/-- A pseudo-coherent derived module of locally finite Tor dimension is perfect. -/
theorem IsPseudoCoherent.isPerfect_of_locallyHasFiniteTorDimension
    {E : ModuleDerived X} (hpc : IsPseudoCoherent E)
    (htor : LocallyHasFiniteTorDimension E) :
    IsPerfect E := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived
