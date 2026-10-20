/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Sheafification.Fppf

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
