/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 29.41.4 (1): The composition of proper morphisms is proper. -/
@[stacks 01W3] #check (@AlgebraicGeometry.IsProper.instCompScheme :
  ∀ {X Y : AlgebraicGeometry.Scheme} {Z : AlgebraicGeometry.Scheme}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.IsProper f] [AlgebraicGeometry.IsProper g],
    AlgebraicGeometry.IsProper (f ≫ g))

/- Lemma 29.41.4 (2): The composition of universally closed morphisms is universally closed. -/
@[stacks 01W3] #check (@AlgebraicGeometry.universallyClosedTypeComp :
  ∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.UniversallyClosed f] [AlgebraicGeometry.UniversallyClosed g],
    AlgebraicGeometry.UniversallyClosed (f ≫ g))
