module

public import stacks_project.Chap103.Lemma_103_17_3_Coherent
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
#check (structureSheaf_isCoherent X :
  AlgebraicStack.IsCoherent (SheafOfModules.unit (structureSheaf X)))

/- The structure module of a locally Noetherian algebraic stack is canonically
coherent. -/
@[stacks 0GR7]
#check (instIsCoherentUnit X :
  AlgebraicStack.IsCoherent (SheafOfModules.unit (structureSheaf X)))

/- Lemma 103.17.3 (2): on a locally Noetherian algebraic stack, any invertible
`𝒪_X`-module is coherent. -/
variable (L : SheafOfModules.{u} (structureSheaf X))
  [SheafOfModules.IsFiniteLocallyFreeOfRank 1 L] in
@[stacks 0GR7]
#check (isCoherent_of_isInvertible L : AlgebraicStack.IsCoherent L)

/- Invertible modules on a locally Noetherian algebraic stack are canonically
coherent. -/
variable (L : SheafOfModules.{u} (structureSheaf X))
  [SheafOfModules.IsFiniteLocallyFreeOfRank 1 L] in
@[stacks 0GR7]
#check (instIsCoherentOfIsInvertible L : AlgebraicStack.IsCoherent L)

/- Lemma 103.17.3 (3): more generally, any finite locally free `𝒪_X`-module on a
locally Noetherian algebraic stack is coherent. -/
variable [SheafOfModules.IsFiniteLocallyFree F] in
@[stacks 0GR7]
#check (isCoherent_of_isFiniteLocallyFree F : AlgebraicStack.IsCoherent F)

/- Finite locally free modules on a locally Noetherian algebraic stack are
canonically coherent. -/
variable [SheafOfModules.IsFiniteLocallyFree F] in
@[stacks 0GR7]
#check (instIsCoherentOfIsFiniteLocallyFree F : AlgebraicStack.IsCoherent F)

end AlgebraicGeometry.AlgebraicStack
