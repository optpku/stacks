/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber.ConnectedComponents.Semicontinuity
import StacksCheckRecall

/-!
# Lower semicontinuity of geometric fibre-component counts of proper flat morphisms

The target-indexed geometric fibre-component count of a proper, flat morphism of
finite presentation of algebraic spaces is lower semicontinuous on the space of
points of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.36.7: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is proper, flat, and of finite presentation,
then the function `n_{X/Y} : |Y| → ℤ` counting the number of geometric connected
components of fibres of `f` (Lemma 76.30.1) is lower semicontinuous.

The canonical `ℕ∞`-valued `geometricFiberComponentCount f` represents this
nonnegative integer count: proper geometric fibres are Noetherian and hence
have finitely many connected components. -/
@[stacks 0E1D] #check
  (AlgebraicGeometry.AlgebraicSpace.lowerSemicontinuous_geometricFiberComponentCount :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [Proper f] → [Flat f] → [FinitePresentation f] →
        LowerSemicontinuous (geometricFiberComponentCount f))
