module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Sheafification.Fppf

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

/-- The structure module of a locally Noetherian algebraic stack is coherent. -/
theorem structureSheaf_isCoherent (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] :
    AlgebraicStack.IsCoherent (SheafOfModules.unit (structureSheaf X)) :=
  sorry

/-- The structure module of a locally Noetherian algebraic stack is canonically
coherent. -/
instance instIsCoherentUnit (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] :
    AlgebraicStack.IsCoherent (SheafOfModules.unit (structureSheaf X)) :=
  structureSheaf_isCoherent X

/-- An invertible `𝒪_X`-module, encoded as finite locally free of rank one, is
coherent on a locally Noetherian algebraic stack. -/
theorem isCoherent_of_isInvertible (L : SheafOfModules.{u} (structureSheaf X))
    [SheafOfModules.IsFiniteLocallyFreeOfRank 1 L] :
    AlgebraicStack.IsCoherent L :=
  sorry

/-- Invertible modules on a locally Noetherian algebraic stack are canonically
coherent. -/
instance instIsCoherentOfIsInvertible (L : SheafOfModules.{u} (structureSheaf X))
    [SheafOfModules.IsFiniteLocallyFreeOfRank 1 L] :
    AlgebraicStack.IsCoherent L :=
  isCoherent_of_isInvertible L

/-- A finite locally free `𝒪_X`-module on a locally Noetherian algebraic stack is
coherent. -/
theorem isCoherent_of_isFiniteLocallyFree (F : SheafOfModules.{u} (structureSheaf X))
    [SheafOfModules.IsFiniteLocallyFree F] :
    AlgebraicStack.IsCoherent F :=
  sorry

/-- Finite locally free modules on a locally Noetherian algebraic stack are
canonically coherent. -/
instance instIsCoherentOfIsFiniteLocallyFree
    (F : SheafOfModules.{u} (structureSheaf X))
    [SheafOfModules.IsFiniteLocallyFree F] :
    AlgebraicStack.IsCoherent F :=
  isCoherent_of_isFiniteLocallyFree F

end AlgebraicGeometry.AlgebraicStack
