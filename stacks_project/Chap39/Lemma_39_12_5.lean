/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.GradedEquivariant.Sections

universe u

/- Lemma 39.12.5: the global sections of an equivariant quasi-coherent module on the
graded affine scheme carry a canonical compatible grading, and the affine tilde counit is an
equivariant isomorphism. -/
@[stacks 0EKL] #check
  (AlgebraicGeometry.GradedSpec.EquivariantSections.counitIsIso :
    {A : Type u} → [CommRing A] → (𝒜 : ℤ → Submodule ℤ A) → [GradedAlgebra 𝒜] →
      (D : AlgebraicGeometry.Scheme.QCoh.Equivariant
        AlgebraicGeometry.MultiplicativeGroup.group
        (AlgebraicGeometry.GradedSpec.action 𝒜)) →
          CategoryTheory.IsIso
            (AlgebraicGeometry.GradedSpec.EquivariantSections.counit 𝒜 D))
