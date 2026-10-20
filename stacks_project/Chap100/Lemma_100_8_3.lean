/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Monomorphism.Composition
import StacksCheckRecall

/-!
# Composition of monomorphisms of algebraic stacks

The composition of monomorphisms of algebraic stacks is a monomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

/- Lemma 100.8.3: compositions of monomorphisms of algebraic stacks are
monomorphisms. -/
@[stacks 04ZY] #check
  (AlgebraicGeometry.Groupoids.Hom.Mono.instIsStableUnderComposition :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.Groupoids.Hom.Mono S : MorphismProperty (GroupoidsOver S)))

#check (AlgebraicGeometry.Groupoids.Hom.Mono.comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.Groupoids.Hom.Mono f] [AlgebraicGeometry.Groupoids.Hom.Mono g],
      AlgebraicGeometry.Groupoids.Hom.Mono (f ≫ g))
