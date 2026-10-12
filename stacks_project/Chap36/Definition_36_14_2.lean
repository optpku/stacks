/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ApproximationByPerfectComplexes

universe u

/- Definition 36.14.2: approximation by perfect complexes holds on a scheme `X` when every
closed subset `T` with retrocompact complement admits an integer `r` such that every
`(m - r)`-pseudo-coherent `E ∈ D_QCoh(𝒪_X)` whose cohomology in degrees at least `m - r` is
supported on `T` has a perfect approximation supported on `T` through degree `m`. -/
@[stacks 08EN] #check (AlgebraicGeometry.Scheme.HasApproximationByPerfectComplexes :
  AlgebraicGeometry.Scheme.{u} → Prop)
