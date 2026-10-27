/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.InertiaProduct

/-! # The inertia of the Picard stack -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

universe u

/- Lemma 108.8.4: for a flat, proper, finitely presented morphism with universally
isomorphic canonical structure-sheaf map, Picard inertia is the multiplicative-group
product with the Picard stack. -/
@[stacks 0DNH] #check (AlgebraicGeometry.AlgebraicSpace.inertia_mulGroupProduct :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [Flat f] [Proper f] [FinitePresentation f] [Hom.IsIsoBaseChangeStructurePushforward f],
    StackOver.Groupoids.Hom.IsEquivalence (Picard.inertiaMulGroupHom f :
      StackOver.Groupoids.inertia (picardStack f) ⟶ Picard.mulGroupProduct f))
