/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AffineSuperelliptic.Invariants
import StacksCheckRecall

/-!
# Exercise 111.59.3

Over an algebraically closed field `k`, for a prime `ℓ > 100` distinct from
the characteristic of `k`, the nonsingular projective models of the affine
curve `y ^ ℓ = x * (x - 1) ^ 3` in `𝔸^2_k` have genus `(ℓ - 1) / 2` and
gonality at most `4`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineSuperelliptic

/- Exercise 111.59.3 (1): over an algebraically closed field `k`, if `ℓ > 100` is
prime and distinct from the characteristic of `k`, then every nonsingular
projective model `Y` of the affine curve `y ^ ℓ = x * (x - 1) ^ 3` in
`𝔸^2_k` has genus `(ℓ - 1) / 2`. -/
@[stacks 0DT2]
#check (AlgebraicGeometry.AffineSuperelliptic.genus_eq :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {ℓ : ℕ} [Fact ℓ.Prime]
    [NeZero (ℓ : k)] (hℓ : 100 < ℓ)
    (Y : NonsingularProjectiveModel.WithIso (over k ℓ)),
      Y.genus = (ℓ - 1) / 2)

/- Exercise 111.59.3 (2): in the same setting, the gonality of `Y` is at most `4`. -/
@[stacks 0DT2]
#check (AlgebraicGeometry.AffineSuperelliptic.gonality_le_four :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {ℓ : ℕ} [Fact ℓ.Prime]
    [NeZero (ℓ : k)] (hℓ : 100 < ℓ)
    (Y : NonsingularProjectiveModel.WithIso (over k ℓ)),
      Y.gonality ≤ 4)

end AlgebraicGeometry.AffineSuperelliptic
