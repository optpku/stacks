/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlongSubspace.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlongSubspace.PowerQuotient

/-!
# When the canonical comparison of completions is an isomorphism

The comparison from completion along a closed subspace to completion along its
support is an isomorphism under finite presentation, but not in general.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 87.38.6: The canonical comparison is an isomorphism for a
finite-presentation closed inclusion, but can fail without finite presentation. -/
@[stacks 0H8N] #check (AlgebraicGeometry.AlgebraicSpace.isIso_toCompletionAlong :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] [FinitePresentation i],
    IsIso (AlgebraicGeometry.AlgebraicSpace.completionAlongSubspace.toCompletionAlong i))

#check (AlgebraicGeometry.AlgebraicSpace.not_isIso_toCompletionAlong_counterexample :
  ∀ {R : Type u} [CommRing R] [Nontrivial R],
    ¬ IsIso (AlgebraicGeometry.AlgebraicSpace.completionAlongSubspace.toCompletionAlong
      (AlgebraicGeometry.AlgebraicSpace.completionAlongSubspace.counterexample.closedImmersion R)))

#check (AlgebraicGeometry.AlgebraicSpace.not_isIso_toCompletionAlong_counterexample (R := ℤ) :
  ¬ IsIso (AlgebraicGeometry.AlgebraicSpace.completionAlongSubspace.toCompletionAlong
    (AlgebraicGeometry.AlgebraicSpace.completionAlongSubspace.counterexample.closedImmersion ℤ)))
