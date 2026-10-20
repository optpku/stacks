/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.DiscreteFieldFibers
import StacksCheckRecall

/-!
# Locally quasi-finite morphisms of algebraic spaces and discrete field fibers

A locally finite-type morphism of algebraic spaces is locally quasi-finite
exactly when every scheme-theoretic field fiber has discrete space of points.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.27.5: A locally finite-type morphism of algebraic spaces is locally
quasi-finite exactly when every field fiber has discrete point space. -/
@[stacks 06RW] #check
  (AlgebraicGeometry.AlgebraicSpace.locallyQuasiFinite_iff_discreteFieldFibers :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [LocallyOfFiniteType f] → (LocallyQuasiFinite f ↔ discreteFieldFibers f))
