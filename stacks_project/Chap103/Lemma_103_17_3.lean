module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.FiniteLocallyFree
public import stacks_project.Chap103.Lemma_103_17_3_Instances
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver
open AlgebraicGeometry.AlgebraicStack

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] [IsLocallyNoetherian X]
variable (F : SheafOfModules.{u} (structureSheaf X))

/- Lemma 103.17.3 (1): on a locally Noetherian algebraic stack `X`, the structure
module `𝒪_X` is coherent. -/
@[stacks 0GR7]
#check (AlgebraicGeometry.AlgebraicStack.structureSheaf_isCoherent X :
  AlgebraicStack.IsCoherent (SheafOfModules.unit (structureSheaf X)))

/- The structure module of a locally Noetherian algebraic stack is canonically
coherent. -/
#check (AlgebraicGeometry.AlgebraicStack.instIsCoherentUnit X :
  AlgebraicStack.IsCoherent (SheafOfModules.unit (structureSheaf X)))

variable (L : SheafOfModules.{u} (structureSheaf X))
  [SheafOfModules.IsFiniteLocallyFreeOfRank 1 L] in
/- Lemma 103.17.3 (2): on a locally Noetherian algebraic stack, any invertible
`𝒪_X`-module is coherent. -/
@[stacks 0GR7]
#check (AlgebraicGeometry.AlgebraicStack.isCoherent_of_isInvertible L : AlgebraicStack.IsCoherent L)

variable (L : SheafOfModules.{u} (structureSheaf X))
  [SheafOfModules.IsFiniteLocallyFreeOfRank 1 L] in
/- Invertible modules on a locally Noetherian algebraic stack are canonically
coherent. -/
#check (AlgebraicGeometry.AlgebraicStack.instIsCoherentOfIsInvertible L : AlgebraicStack.IsCoherent L)

variable [SheafOfModules.IsFiniteLocallyFree F] in
/- Lemma 103.17.3 (3): more generally, any finite locally free `𝒪_X`-module on a
locally Noetherian algebraic stack is coherent. -/
@[stacks 0GR7]
#check (AlgebraicGeometry.AlgebraicStack.isCoherent_of_isFiniteLocallyFree F : AlgebraicStack.IsCoherent F)

variable [SheafOfModules.IsFiniteLocallyFree F] in
/- Finite locally free modules on a locally Noetherian algebraic stack are
canonically coherent. -/
#check (AlgebraicGeometry.AlgebraicStack.instIsCoherentOfIsFiniteLocallyFree F : AlgebraicStack.IsCoherent F)

end AlgebraicGeometry.AlgebraicStack
