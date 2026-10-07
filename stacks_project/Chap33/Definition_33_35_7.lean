module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Regularity

@[expose] public section

universe u

/- Definition 33.35.7: for a field `k`, `n : ℕ`, and a coherent module sheaf `ℱ` on
standard projective `n`-space over `k`, the sheaf `ℱ` is `m`-regular when the cohomology of
`ℱ(m - i)` vanishes for every `i` with `0 < i` and `i ≤ n`. -/
@[stacks 08A3] #check
  (AlgebraicGeometry.ProjectiveSpace.IsMRegular :
    ∀ (k : Type u) [Field k] (n : ℕ)
      (ℱ : (AlgebraicGeometry.ProjectiveSpace.scheme k n).Modules) [ℱ.IsCoherent]
      (m : ℤ), Prop)
