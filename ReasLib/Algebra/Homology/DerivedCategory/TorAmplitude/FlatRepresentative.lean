/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.FlatRepresentative.LowerBounded
import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.FlatCokernel
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lower-bounded flat representatives and Tor-amplitude

This file identifies the lower Tor-amplitude predicate for derived modules with the reusable
lower-bounded K-flat representative predicate.

@stack 0654
@stack 0BYL
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory

variable {R : Type u} [CommRing R]

/-- Lemma 15.67.3: an object of `D(R)` has Tor-amplitude in `[a, b]` exactly when it admits a
termwise-flat cochain representative supported in `[a, b]`. -/
@[stacks 0654]
theorem hasTorAmplitudeIn_iff_hasFlatRepresentativeIn
    (K : DerivedCategory (ModuleCat R)) (a b : ℤ) :
    HasTorAmplitudeIn R K a b ↔ HasFlatRepresentativeIn K a b := sorry
/- Proof strategy: for the forward direction, choose a bounded-above flat resolution supported
above `b` and truncate at `a`, using `FlatCokernel.ofTorAmplitudeIn_cokernel` at the cutoff.  For
the reverse direction, bounded termwise-flat complexes are K-flat, so their ordinary tensor
complexes compute the derived tensor and have no terms outside `[a, b]`. -/

/-- Tor-amplitude in `[a, b]` yields a termwise-flat representative supported in that interval. -/
@[stacks 0654 "forward implication"]
theorem HasTorAmplitudeIn.hasFlatRepresentativeIn
    {K : DerivedCategory (ModuleCat R)} {a b : ℤ} (hK : HasTorAmplitudeIn R K a b) :
    HasFlatRepresentativeIn K a b := sorry
/- Proof strategy: apply the forward implication of
`hasTorAmplitudeIn_iff_hasFlatRepresentativeIn`. -/

/-- A termwise-flat representative supported in `[a, b]` yields Tor-amplitude in that interval. -/
@[stacks 0654 "reverse implication"]
theorem HasFlatRepresentativeIn.hasTorAmplitudeIn
    {K : DerivedCategory (ModuleCat R)} {a b : ℤ} (hK : HasFlatRepresentativeIn K a b) :
    HasTorAmplitudeIn R K a b := sorry
/- Proof strategy: apply the reverse implication of
`hasTorAmplitudeIn_iff_hasFlatRepresentativeIn`. -/

/-- Lemma 15.67.4: an object of `D(R)` has Tor-amplitude in `[a, ∞]` exactly when it admits a
K-flat, termwise-flat cochain representative supported in degrees `≥ a`. -/
@[stacks 0BYL]
theorem hasTorAmplitudeGE_iff_hasFlatRepresentativeGE
    (K : DerivedCategory (ModuleCat R)) (a : ℤ) :
    HasTorAmplitudeGE R K a ↔ HasFlatRepresentativeGE K a := sorry
/- Proof strategy: choose a termwise-flat K-flat representative, use lower Tor-amplitude to make
the cutoff cokernel flat, and pass to the smart lower truncation for the forward direction.  For
the reverse direction, compute derived tensor with the chosen K-flat representative and use its
strict support in degrees `≥ a`. -/

/-- A lower Tor-amplitude bound yields a K-flat, termwise-flat representative with the same
lower support bound. -/
@[stacks 0BYL "forward implication"]
theorem HasTorAmplitudeGE.hasFlatRepresentativeGE
    {K : DerivedCategory (ModuleCat R)} {a : ℤ} (hK : HasTorAmplitudeGE R K a) :
    HasFlatRepresentativeGE K a := sorry
/- Proof strategy: apply the forward implication of
`hasTorAmplitudeGE_iff_hasFlatRepresentativeGE`. -/

/-- A K-flat, termwise-flat representative supported in degrees `≥ a` yields the corresponding
lower Tor-amplitude bound. -/
@[stacks 0BYL "reverse implication"]
theorem HasFlatRepresentativeGE.hasTorAmplitudeGE
    {K : DerivedCategory (ModuleCat R)} {a : ℤ} (hK : HasFlatRepresentativeGE K a) :
    HasTorAmplitudeGE R K a := sorry
/- Proof strategy: apply the reverse implication of
`hasTorAmplitudeGE_iff_hasFlatRepresentativeGE`. -/

end CategoryTheory.DerivedCategory
