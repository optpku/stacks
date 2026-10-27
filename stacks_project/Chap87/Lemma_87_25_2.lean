/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Surjective
public import stacks_project.Chap87.Lemma_87_25_2_Surjective
import StacksCheckRecall

/-!
# Composition of surjective morphisms of formal algebraic spaces

The composition of two surjective morphisms of formal algebraic spaces is
again surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/- Lemma 87.25.2: The composition of two surjective morphisms of formal
algebraic spaces is a surjective morphism. -/
@[stacks 0GHQ] #check (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.surjective_comp :
  ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    (RX : ReductionData X) (RY : ReductionData Y) (RZ : ReductionData Z)
    (f : X ⟶ Y) (g : Y ⟶ Z),
    ReductionData.Surjective RX RY f → ReductionData.Surjective RY RZ g →
      ReductionData.Surjective RX RZ (f ≫ g))

end AlgebraicGeometry.FormalAlgebraicSpace
