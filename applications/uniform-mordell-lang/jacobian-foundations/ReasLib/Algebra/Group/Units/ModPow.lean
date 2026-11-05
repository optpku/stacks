/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll

Adapted from MichaelStollBayreuth/EllipticCurves at
4c43c4089d2960904c0a4c1bb4668e827d80a62d.
Source fragments: Basic.lean:147-151, SelmerGroup.lean:98-166.
Changes: relocated general group infrastructure to its mathematical owner;
declaration names, hypotheses, and proof bodies are preserved.
The upstream files have no per-file copyright header; repository license and author retained.
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Power classes of units

`Units.modPow α n` abbreviates Mathlib's quotient of `αˣ` by the range of the
`n`-th power homomorphism. Only `CommMonoid α` is required, with no finiteness
or nonzero-exponent assumption. This notation is useful for units of general
commutative monoids, Kummer power classes, and arithmetic descent.

Finiteness results for an arbitrary finitely generated commutative group live
in `ReasLib.GroupTheory.Finiteness.Abelian`.
-/

@[expose] public section

/-- The group of `n`-th power classes of units of `α`, using Mathlib's quotient
by the range of the power homomorphism. This abbreviation introduces no new carrier. -/
abbrev Units.modPow (α : Type*) [CommMonoid α] (n : ℕ) : Type _ :=
  αˣ ⧸ (powMonoidHom n : αˣ →* αˣ).range

end
