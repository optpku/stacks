/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.ClosedImmersion
public import stacks_project.Chap87.Lemma_87_27_3_ClosedImmersion
public import stacks_project.Chap88.Definition_88_21_1_Formal
import StacksCheckRecall

/-!
# Composition of closed immersions of formal algebraic spaces

The composition of two closed immersions of formal algebraic spaces is again a
closed immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/- Lemma 87.27.2: The composition of two closed immersions of formal algebraic
spaces is a closed immersion. -/
@[stacks 0GHW] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion.comp :
    ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
      [ClosedImmersion f] [ClosedImmersion g],
      ClosedImmersion (f ≫ g))

end AlgebraicGeometry.FormalAlgebraicSpace
