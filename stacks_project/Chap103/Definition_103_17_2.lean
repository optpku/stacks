module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.Category
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver

universe u

variable {S : Scheme.{u}} (X : GroupoidsOver S)
variable [AlgebraicStack X] [AlgebraicStack.IsLocallyNoetherian X]

/- Definition 103.17.2 (1): let `X` be a locally Noetherian algebraic stack. An
`𝒪_X`-module `F` is called coherent if `F` satisfies one (and hence all) of the
equivalent conditions of Lemma 103.17.1. -/
@[stacks 0GR6] #check (AlgebraicGeometry.AlgebraicStack.IsCoherent :
  SheafOfModules.{u} (structureSheaf X) → Prop)

/- Definition 103.17.2 (2): the category of coherent `𝒪_X`-modules is denoted
`Coh(𝒪_X)`. -/
@[stacks 0GR6] #check (AlgebraicGeometry.AlgebraicStack.Coh X : Type (u + 1))

/- Coherence of an `𝒪_X`-module on a locally Noetherian algebraic stack is
equivalent to finite presentation. -/
#check (AlgebraicGeometry.AlgebraicStack.isCoherent_iff :
  ∀ (F : SheafOfModules.{u} (structureSheaf X)),
    AlgebraicStack.IsCoherent F ↔ F.IsFinitePresentation)

/- The forgetful inclusion `Coh(𝒪_X) ⥤ Mod(𝒪_X)`. -/
#check (AlgebraicGeometry.AlgebraicStack.Coh.inclusion X :
  AlgebraicStack.Coh X ⥤ SheafOfModules.{u} (structureSheaf X))
