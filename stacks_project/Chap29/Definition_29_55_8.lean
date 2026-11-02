/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.WeakNormalization.Normalization
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Definition 29.55.8

Let `X` be a scheme such that every quasi-compact open has finitely many irreducible components.
The weak normalization of `X` is the weak normalization of `X` in its normalization.
-/
@[stacks 0H3R] #check
  (fun (X : Scheme.{u}) [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
      (W : Scheme.WeakNormalization X) =>
    ⟨W.fromNormalization_comp_toScheme, W.isUniversalHomeomorphism_toScheme,
      W.nonempty_isInitial⟩ :
    ∀ (X : Scheme.{u}) [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X],
      ∀ W : Scheme.WeakNormalization X,
        W.fromNormalization ≫ W.toScheme = X.normalizationTo ∧
          UniversalHomeomorphism W.toScheme ∧ Nonempty (IsInitial W.1))
