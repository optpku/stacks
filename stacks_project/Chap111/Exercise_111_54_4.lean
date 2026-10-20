/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AffineTriangle.Picard
import StacksCheckRecall

/-!
# Picard group of the affine triangle

The source triangle obtained by cyclically identifying `0` on one copy of
`𝔸¹_k` with `1` on the next is the affine scheme
`Spec (k[x, y] / (x * y * (x + y + 1)))`.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry

namespace AlgebraicGeometry.AffineTriangle

/- Exercise 111.54.4: for a field `k`, the affine triangle has Picard group
additively equivalent to `Additive kˣ`. -/
@[stacks 06A3] #check
  (AlgebraicGeometry.AffineTriangle.picardGroup_addEquiv :
    ∀ (k : Type u) [Field k],
      Nonempty ((AlgebraicGeometry.AffineTriangle.scheme k).PicardGroup ≃+ Additive kˣ))

end AlgebraicGeometry.AffineTriangle
