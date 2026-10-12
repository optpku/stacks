/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ChowGroup.Codimension

open AlgebraicGeometry CategoryTheory

universe u

/-
Remark 42.42.2: For a scheme decomposed into clopen strata of generic relative dimension
`n`, the codimension-zero fundamental Chow class has component `[Xₙ]ₙ` on each stratum.
-/
@[stacks 0FE4] #check
  (AlgebraicGeometry.ChowGroup.Codimension.fundamentalClass :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S}
      [UniversallyCatenary S] [LocallyOfFiniteType f]
      {δ : S → ℤ} [IsDimensionFunction δ],
      (D : AlgebraicGeometry.Scheme.Hom.GenericDimensionStratification f δ) →
        AlgebraicGeometry.ChowGroup.Codimension D 0)
