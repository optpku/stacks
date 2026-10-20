/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hypersurface.CoordinateProjection
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom

universe u

namespace AlgebraicGeometry.ProjectiveSpace.Hypersurface

/- Exercise 111.39.5: a hypersurface in projective 3-space defined by
`F = X₀G + X₁H`, with homogeneous `G`, `H` of positive degree and no common
projective zero of `X₀`, `X₁`, `G`, `H`, admits a nonconstant morphism over
`Spec k` to projective 1-space. On field-valued points it sends
`(x₀ : x₁ : x₂ : x₃)` to `(x₀ : x₁)` whenever the first two coordinates are
not both zero. -/
@[stacks 02AB] #check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.exists_isNonconstant :
    ∀ {k : Type u} [Field k] {d : ℕ}
      (F G H : MvPolynomial (Fin 4) k)
      (hF : F ∈ ProjectiveSpace.grading k 3 (d + 1))
      (hG : G ∈ ProjectiveSpace.grading k 3 d)
      (hH : H ∈ ProjectiveSpace.grading k 3 d) (hd : 0 < d)
      (hEq : F = MvPolynomial.X 0 * G + MvPolynomial.X 1 * H)
      (hZero : NoCommonZero G H),
      ∃ f : Over.mk (hom 3 (d + 1) F hF) ⟶ ProjectiveSpace.schemeOver k 1,
        f.left.IsNonconstant ∧ IsCoordinateProjectionOnFieldPoints F hF f.left)

end AlgebraicGeometry.ProjectiveSpace.Hypersurface
