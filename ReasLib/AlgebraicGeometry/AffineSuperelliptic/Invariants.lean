/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.AffineSuperelliptic.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.GeometricGenus
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Gonality

/-!
# Invariants of the affine superelliptic curve

This module records the genus and gonality statements for nonsingular
projective models of `y ^ ℓ = x * (x - 1) ^ 3`.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineSuperelliptic

/-- Over an algebraically closed field `k`, every nonsingular projective model of
`y ^ ℓ = x * (x - 1) ^ 3` has genus `(ℓ - 1) / 2` when `ℓ > 100` is prime
and nonzero in `k`. -/
theorem genus_eq {k : Type u} [Field k] [IsAlgClosed k] {ℓ : ℕ} [Fact ℓ.Prime]
    [NeZero (ℓ : k)] (hℓ : 100 < ℓ)
    (Y : NonsingularProjectiveModel.WithIso (over k ℓ)) :
    Y.genus = (ℓ - 1) / 2 := sorry

/-- Over an algebraically closed field `k`, every nonsingular projective model of
`y ^ ℓ = x * (x - 1) ^ 3` has gonality at most `4` when `ℓ > 100` is prime
and nonzero in `k`. -/
theorem gonality_le_four {k : Type u} [Field k] [IsAlgClosed k] {ℓ : ℕ}
    [Fact ℓ.Prime] [NeZero (ℓ : k)] (hℓ : 100 < ℓ)
    (Y : NonsingularProjectiveModel.WithIso (over k ℓ)) :
    Y.gonality ≤ 4 := sorry

end AlgebraicGeometry.AffineSuperelliptic
