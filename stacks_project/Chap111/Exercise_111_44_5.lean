/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Surface.Cohomology

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Exercise 111.44.5: over an algebraically closed field `k`, a projective
surface `X` admits a coherent `𝒪_X`-module `F` such that `H²(X, F)` is
nonzero. -/
@[stacks 0DB8]
#check (AlgebraicGeometry.SchemeOverField.exists_isCoherent_secondCohomology_not_isZero :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k) [Projective X.hom],
      topologicalKrullDim X.left = 2 →
        ∃ (F : X.left.Modules) (_ : F.IsCoherent),
          ¬ IsZero (Scheme.Hom.cohomology X.hom F 2))

end AlgebraicGeometry.SchemeOverField
