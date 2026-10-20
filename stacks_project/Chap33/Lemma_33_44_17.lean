/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Cohomology.Vanishing

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

universe u

/- Lemma 33.44.17: let `k` be an algebraically closed field, let `X` be a proper curve over
`k`, and set `g = dim_k H^1(X, 𝒪_X)`. Every invertible `𝒪_X`-module `ℒ` of degree at least
`2 * g - 1` has vanishing first cohomology. -/
@[stacks 0B90] #check
  (AlgebraicGeometry.Scheme.Modules.firstCohomology_isZero_of_curveDegree_ge :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (X : Over (Spec (CommRingCat.of k))) [Curve X] [IsProper X.hom]
      {ℒ : X.left.Modules} [Scheme.Modules.Invertible ℒ],
      2 * (Scheme.Hom.cohomologyFinrank X.hom
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 : ℤ) - 1 ≤
          Scheme.Modules.curveDegreeOfInvertible X.hom
            (topologicalKrullDim_eq_one X).le ℒ →
        IsZero (Scheme.Modules.cohomology ℒ 1))
