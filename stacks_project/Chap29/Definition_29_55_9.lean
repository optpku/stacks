/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.WeakNormalization.Normal
import StacksCheckRecall

universe u

variable (X : AlgebraicGeometry.Scheme.{u})
variable [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]

/- Definition 29.55.9

Let `X` be a scheme such that every quasi-compact open has finitely many irreducible components.
We say `X` is weakly normal if the weak normalization `X^{wn} ⟶ X` is an isomorphism.
-/
@[stacks 0H3S] #check
  (AlgebraicGeometry.Scheme.weaklyNormal_iff (X := X) :
    AlgebraicGeometry.Scheme.WeaklyNormal X ↔
      ∀ W : AlgebraicGeometry.Scheme.WeakNormalization X, CategoryTheory.IsIso W.toScheme)
