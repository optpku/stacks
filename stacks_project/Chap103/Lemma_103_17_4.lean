/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Pullback.Coherent
import StacksCheckRecall

/-!
# Pullback of coherent modules on locally Noetherian algebraic stacks

A morphism of locally Noetherian algebraic stacks pulls coherent modules back
to coherent modules.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]
variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
variable [∀ x : X.total, HasWeakSheafify
    ((inheritedFppfTopology X).over x) AddCommGrpCat.{u}]
variable [∀ x : X.total,
    ((inheritedFppfTopology X).over x).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ y : Y.total, HasWeakSheafify
    ((inheritedFppfTopology Y).over y) AddCommGrpCat.{u}]
variable [∀ y : Y.total,
    ((inheritedFppfTopology Y).over y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/- Lemma 103.17.4: let `f : X ⟶ Y` be a morphism of locally Noetherian algebraic
stacks. Then `f^*` sends coherent modules on `Y` to coherent modules on `X`. -/
@[stacks 0GR8] #check (AlgebraicGeometry.AlgebraicStack.pullback_isCoherent :
  ∀ (f : X ⟶ Y) (G : SheafOfModules.{u} (structureSheaf Y))
    [AlgebraicStack.IsCoherent G],
    AlgebraicStack.IsCoherent ((modulePullback f).obj G))

end AlgebraicGeometry.AlgebraicStack
