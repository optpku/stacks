/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Connected.FiniteSeparable
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/-!
# Finite-Separable Test for Geometric Connectedness

Lemma 33.7.11 is the scheme-level owner of the finite-separable criterion;
the affine Chapter 10 statement is its `Spec` specialization.
-/

/- Lemma 33.7.11 (Tag 0389): a scheme over `k` is geometrically connected if and only if
every finite separable field-extension base change is connected. -/
@[stacks 0389]
#check
  (AlgebraicGeometry.GeometricallyConnected.iff_finiteSeparable :
    ∀ {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)),
      AlgebraicGeometry.GeometricallyConnected f ↔
        ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K]
          [Algebra.IsSeparable k K],
          ConnectedSpace
            (CategoryTheory.Limits.pullback f
              (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) :
              AlgebraicGeometry.Scheme))
