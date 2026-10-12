/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Regularity.Monotonicity
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 33.35.10: Let `k` be a field, let `n ≥ 0`, and let `ℱ` be a coherent sheaf on
`ℙⁿ_k`. If `ℱ` is `m`-regular, then `ℱ` is `(m + 1)`-regular. -/
@[stacks 08A6] #check
  (AlgebraicGeometry.ProjectiveSpace.IsMRegular.add_one :
    ∀ {k : Type u} [Field k] {n : ℕ}
      {ℱ : (AlgebraicGeometry.ProjectiveSpace.scheme k n).Modules} [ℱ.IsCoherent] {m : ℤ},
      AlgebraicGeometry.ProjectiveSpace.IsMRegular k n ℱ m →
        AlgebraicGeometry.ProjectiveSpace.IsMRegular k n ℱ (m + 1))
