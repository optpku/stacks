/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.Classification

@[expose] public section

open AlgebraicGeometry CategoryTheory Set

universe u

/- Exercise 111.39.2: over a field `k`, an irreducible reduced closed subscheme
`Z ⊂ P^2_k` is a closed point, a positive-degree irreducible hypersurface, or
the whole projective plane. -/
@[stacks 02A8] #check
  (AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.eq_closedPoint_or_hasHomogeneousEquation_or_isIso :
    ∀ (k : Type u) [Field k]
      (Z : (AlgebraicGeometry.ProjectiveSpace.scheme k 2).IdealSheafData)
      [IsReduced Z.subscheme] [IrreducibleSpace Z.subscheme],
      (∃ x : AlgebraicGeometry.ProjectiveSpace.scheme k 2,
          x ∈ closedPoints (AlgebraicGeometry.ProjectiveSpace.scheme k 2) ∧
            (Z.support : Set (AlgebraicGeometry.ProjectiveSpace.scheme k 2)) = {x}) ∨
        (∃ F : MvPolynomial (Fin 3) k,
          0 < F.totalDegree ∧
            Irreducible F ∧
            AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.HasHomogeneousEquation 2 Z F) ∨
        IsIso Z.subschemeι)
