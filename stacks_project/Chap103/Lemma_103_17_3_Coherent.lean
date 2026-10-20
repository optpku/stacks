module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.FiniteLocallyFree
public import stacks_project.Chap103.Lemma_103_17_3_Instances
public import stacks_project.Chap103.Lemma_103_17_4_Coherent

/-!
# Elementary coherent modules on locally Noetherian algebraic stacks

On a locally Noetherian algebraic stack, the structure module `𝒪_X`, every
invertible `𝒪_X`-module, and every finite locally free `𝒪_X`-module is coherent.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S}
variable [AlgebraicStack X] [IsLocallyNoetherian X]

#check (AlgebraicGeometry.AlgebraicStack.structureSheaf_isCoherent :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X] [IsLocallyNoetherian X],
    AlgebraicStack.IsCoherent (SheafOfModules.unit (structureSheaf X)))

#check (AlgebraicGeometry.AlgebraicStack.instIsCoherentUnit :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X] [IsLocallyNoetherian X],
    AlgebraicStack.IsCoherent (SheafOfModules.unit (structureSheaf X)))

#check (AlgebraicGeometry.AlgebraicStack.isCoherent_of_isInvertible :
  ∀ (L : SheafOfModules.{u} (structureSheaf X))
    [SheafOfModules.IsFiniteLocallyFreeOfRank 1 L], AlgebraicStack.IsCoherent L)

#check (AlgebraicGeometry.AlgebraicStack.instIsCoherentOfIsInvertible :
  ∀ (L : SheafOfModules.{u} (structureSheaf X))
    [SheafOfModules.IsFiniteLocallyFreeOfRank 1 L], AlgebraicStack.IsCoherent L)

#check (AlgebraicGeometry.AlgebraicStack.isCoherent_of_isFiniteLocallyFree :
  ∀ (F : SheafOfModules.{u} (structureSheaf X))
    [SheafOfModules.IsFiniteLocallyFree F], AlgebraicStack.IsCoherent F)

#check (AlgebraicGeometry.AlgebraicStack.instIsCoherentOfIsFiniteLocallyFree :
  ∀ (F : SheafOfModules.{u} (structureSheaf X))
    [SheafOfModules.IsFiniteLocallyFree F], AlgebraicStack.IsCoherent F)

end AlgebraicGeometry.AlgebraicStack
