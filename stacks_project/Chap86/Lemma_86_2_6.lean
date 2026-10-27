/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Dualizing.DimensionFunction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

universe u

/- Lemma 86.2.6: let `S` be a scheme. Let `X` be a locally Noetherian quasi-separated
algebraic space over `S`. Let `ω` be a dualizing complex on `X`, in the sense of
`IsDualizingComplex` from Lemma 86.2.1. Then the unique function `δ : Points X → ℤ`
such that the shift of the derived étale stalk of `ω` at a geometric point over `x`
by `-δ x` is a normalized dualizing complex over the étale local ring is a dimension
function on `Points X`. -/
@[stacks 0E53] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.normalizationDegree_isDimensionFunction :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsLocallyNoetherian X] [IsQuasiSeparated X]
      {ω : DerivedQCoh X} (hω : IsDualizingComplex ω),
      IsDimensionFunction (normalizationDegree hω))
