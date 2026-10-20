/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Dimension.Affine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Remark 111.33.18: if a scheme is affine, then its dimension is the Krull
dimension of the underlying ring Γ(X, ⊤). Ring-theoretic Krull-dimension
computations therefore apply. -/
@[stacks 02F0]
#check (AlgebraicGeometry.Scheme.topologicalKrullDim_eq_ringKrullDim_of_isAffine :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsAffine X],
      topologicalKrullDim X = ringKrullDim Γ(X, ⊤))
