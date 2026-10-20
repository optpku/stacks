/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hypersurface
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.39.3 -/
@[stacks 02A9] #check
  (AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.hypersurface_inter_nonempty :
    ∀ {k : Type u} [Field k]
      (Z₁ Z₂ : (AlgebraicGeometry.ProjectiveSpace.scheme k 2).IdealSheafData),
      IrreducibleSpace Z₁.subscheme → IrreducibleSpace Z₂.subscheme →
      (F₁ F₂ : MvPolynomial (Fin 3) k) →
      AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.HasHomogeneousEquation 2 Z₁ F₁ →
      AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.HasHomogeneousEquation 2 Z₂ F₂ →
      0 < F₁.totalDegree → 0 < F₂.totalDegree →
      Irreducible F₁ → Irreducible F₂ →
      ((Z₁.support ⊓ Z₂.support :
          TopologicalSpace.Closeds (AlgebraicGeometry.ProjectiveSpace.scheme k 2)) :
        Set (AlgebraicGeometry.ProjectiveSpace.scheme k 2)).Nonempty)
