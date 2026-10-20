/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.IrreducibleComponents

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.27.7: for a finitely presented morphism of schemes, each finite
level set of the geometric irreducible-fibre component count is locally constructible. -/
@[stacks 055B] #check
  (AlgebraicGeometry.Scheme.Hom.FinitePresentation.geometricIrreducibleFiberComponentCount_levelSet_isLocallyConstructible :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.Scheme.Hom.FinitePresentation f] (n : ℕ),
      Topology.IsLocallyConstructible
        {y : Y | f.geometricIrreducibleFiberComponentCount y = n})
