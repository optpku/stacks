/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Separated
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 28.26.7: if every point of a scheme `X` lies in an affine nonvanishing open `X_s`
for some global section `s` of a positive tensor power of an invertible `𝒪_X`-module
`L`, then `X` is separated. -/
@[stacks 01PY] #check
  (AlgebraicGeometry.Scheme.Modules.isSeparated_of_affine_nonvanishing :
    ∀ {X : Scheme.{u}} {L : X.Modules}
      [hL : AlgebraicGeometry.Scheme.Modules.Invertible L],
      (∀ x : X, ∃ n : ℕ, 0 < n ∧ ∃ s : Γ(RingedSpace.TensorPower.sheaf L n, ⊤),
        AlgebraicGeometry.Scheme.Modules.AffineOpenNeighborhood x (hL.nonvanishingOpen s)) →
      X.IsSeparated)
