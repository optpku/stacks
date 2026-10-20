/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Connectedness
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.DerivedQCoh.ProperDualizingComplex

noncomputable section

universe u

/- Exercise 111.59.4: over an algebraically closed field `k`, a reduced projective
`k`-scheme `X` whose irreducible components all have topological Krull dimension `1`
is disconnected whenever
`1 < Scheme.Hom.cohomologyFinrank X.hom (curveDualizingModule X.hom) 1`. -/
@[stacks 0DT3] #check
  (AlgebraicGeometry.SchemeOverField.not_connectedSpace_of_one_lt_cohomologyFinrank_curveDualizingModule :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
      [IsReduced X.left] [Projective X.hom],
      (∀ Z : irreducibleComponents X.left, topologicalKrullDim Z = 1) →
      1 < Scheme.Hom.cohomologyFinrank X.hom (curveDualizingModule X.hom) 1 →
      ¬ ConnectedSpace X.left)

/- Over an algebraically closed field, a reduced connected projective scheme whose
irreducible components all have topological Krull dimension `1` has first cohomology
of the curve dualizing module of dimension at most `1`. -/
#check
  (AlgebraicGeometry.SchemeOverField.cohomologyFinrank_curveDualizingModule_le_one_of_connectedSpace :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
      [IsReduced X.left] [Projective X.hom] [ConnectedSpace X.left],
      (∀ Z : irreducibleComponents X.left, topologicalKrullDim Z = 1) →
      Scheme.Hom.cohomologyFinrank X.hom (curveDualizingModule X.hom) 1 ≤ 1)
