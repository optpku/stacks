/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace.Infinite.Cohomology
import StacksCheckRecall

/-!
# Exercise 111.60.6

Zariski cohomology of the structure sheaf of the complement of the origin in
infinite affine space over a field.

The source's last sentence asks for a guess about higher degrees. The second
check records the positive-degree vanishing answer to that question.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedAffineSpace.Infinite

/- Exercise 111.60.6 (1): if `k` is a field, the first cohomology of the
complement of the origin in countably infinite affine space with coefficients
in its structure sheaf vanishes. -/
@[stacks 0EEQ] #check
  (AlgebraicGeometry.PuncturedAffineSpace.Infinite.cohomology_one_isZero :
    ∀ (k : Type u) [Field k],
      IsZero (AlgebraicGeometry.PuncturedAffineSpace.Infinite.structureSheafCohomology k 1))

/- Exercise 111.60.6 (2): the positive-degree vanishing theorem records the
answer to the source's question about the groups `Hⁱ(U, 𝒪_U)` for `i ≥ 1`. -/
@[stacks 0EEQ] #check
  (AlgebraicGeometry.PuncturedAffineSpace.Infinite.cohomology_isZero :
    ∀ (k : Type u) [Field k] (i : ℕ), 0 < i →
      IsZero (AlgebraicGeometry.PuncturedAffineSpace.Infinite.structureSheafCohomology k i))

end AlgebraicGeometry.PuncturedAffineSpace.Infinite
