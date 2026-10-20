/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedPoints.Relative.Constructible
import StacksCheckRecall

/-!
# Lemma 71.4.10

The locus of points of a scheme `Y` at which the associated points of a
finitely presented module on a finite-presentation algebraic space over `Y`
lie in a quasi-compact open subspace is locally constructible.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 71.4.10: Let `Y` be a scheme. Let `X` be an algebraic space of finite
presentation over `Y`. Let `F` be a quasi-coherent `𝒪_X`-module of finite
presentation. Let `U ⊂ X` be an open subspace such that `U → Y` is quasi-compact.
Then `E = {y ∈ Y | Ass_{X_y}(F_y) ⊆ |U_y|}` is locally constructible in `Y`. -/
@[stacks 0CVV] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.associatedPoints_fiber_subset_isLocallyConstructible :
    ∀ {Y : Scheme.{u}} {X : AlgebraicSpace Y} (f : X ⟶ ofOver (Over.mk (𝟙 Y)))
      [FinitePresentation f] (F : X.Modules) [F.IsFinitePresentation]
      (U : OpenSubspace X) [QuasiCompact (U.ι ≫ f)],
      Topology.IsLocallyConstructible
        (AlgebraicGeometry.AlgebraicSpace.Modules.associatedPointsFiberSubset f F U))

