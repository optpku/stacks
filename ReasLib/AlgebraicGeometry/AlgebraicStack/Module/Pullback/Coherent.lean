module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Pullback

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

/-- Pullback along a morphism of locally Noetherian algebraic stacks sends coherent
modules on the target to coherent modules on the source. -/
@[stacks 0GR8]
instance pullback_isCoherent (f : X ⟶ Y)
    (G : SheafOfModules.{u} (structureSheaf Y))
    [AlgebraicStack.IsCoherent G] :
    AlgebraicStack.IsCoherent ((modulePullback f).obj G) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
