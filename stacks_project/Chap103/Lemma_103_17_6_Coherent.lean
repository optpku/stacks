/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import stacks_project.Chap103.Definition_103_17_2_Coh
public import stacks_project.Chap103.Lemma_103_17_3_Instances

/-!
# Extension closure of coherent modules on locally Noetherian algebraic stacks

On a locally Noetherian algebraic stack, coherent `𝒪_X`-modules are closed under
extensions in `Mod(𝒪_X)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.Limits CategoryTheory.ObjectProperty GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S}
variable [AlgebraicStack X] [IsLocallyNoetherian X]

/-- In a short exact sequence of `𝒪_X`-modules on a locally Noetherian algebraic
stack, coherence of the outer terms implies coherence of the middle term. -/
theorem IsCoherent.middle_of_shortExact
    {sc : ShortComplex (SheafOfModules.{u} (structureSheaf X))}
    (hsc : sc.ShortExact)
    [AlgebraicStack.IsCoherent sc.X₁] [AlgebraicStack.IsCoherent sc.X₃] :
    AlgebraicStack.IsCoherent sc.X₂ :=
  sorry

/-- Coherent `𝒪_X`-modules on a locally Noetherian algebraic stack are closed
under extensions. -/
instance closedUnderExtensions :
    (coherentModuleProperty X).IsClosedUnderExtensions :=
  sorry

end AlgebraicGeometry.AlgebraicStack
