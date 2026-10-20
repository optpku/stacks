/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.CodimensionZeroStalk

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Every codimension-zero point under the meromorphic-decomposition hypotheses admits a
pointed open scheme chart. -/
#check (AlgebraicGeometry.AlgebraicSpace.exists_isOpenImmersion_chart_of_mem_codimZero :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (η : codimZeroPoints X),
    ∃ c : OpenImmersionChart X, Points.mapOfOver c.ι c.u = η)
