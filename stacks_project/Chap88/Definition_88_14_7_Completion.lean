/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.LocalizationAway
public import ReasLib.RingTheory.Topology.Adic.Complete

/-!
# Completed principal localization

The completed principal localization is provided by the reusable adic-completion
construction in `ReasLib.RingTheory.AdicCompletion.LocalizationAway`.
-/

@[expose] public section

universe u

variable {A : Type u} [CommRing A]

#check (completedPrincipalLocalization : ∀ {A : Type u} [CommRing A], Ideal A → A → Type u)
