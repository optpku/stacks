/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.PseudoCoherent.Composition
import StacksCheckRecall

/-!
# Composition of pseudo-coherent morphisms of algebraic spaces

A composition of pseudo-coherent morphisms of algebraic spaces is
pseudo-coherent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.46.3: A composition of pseudo-coherent morphisms is pseudo-coherent. -/
@[stacks 06BT] #check
  (AlgebraicGeometry.AlgebraicSpace.PseudoCoherent.comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
      (f : X ⟶ Y) (g : Y ⟶ Z) [PseudoCoherent f] [PseudoCoherent g],
      PseudoCoherent (f ≫ g))

#check (AlgebraicGeometry.AlgebraicSpace.PseudoCoherent.instIsStableUnderComposition :
  ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
    (@PseudoCoherent S : MorphismProperty (AlgebraicSpace S)))
