/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality

/-!
# Coherent cohomology of derived internal Hom on algebraic spaces

On a locally Noetherian algebraic space, derived internal Hom from an object with
bounded-above coherent cohomology to an object with bounded-below coherent cohomology
has bounded-below coherent cohomology.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open CategoryTheory
open CategoryTheory.MonoidalClosed
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable [IsLocallyNoetherian X] [MonoidalCategory (ModuleDerived X)]
variable (H : MonoidalClosed (ModuleDerived X)) (K L : ModuleDerived X)

/-- On a locally Noetherian algebraic space, derived internal Hom from an object with
bounded-above coherent cohomology to an object with bounded-below coherent cohomology has
bounded-below coherent cohomology. -/
theorem boundedBelowCoherentCohomology
    (hK_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) K)
    (hK_boundedAbove :
      (t.minus : ObjectProperty (ModuleDerived X)) K)
    (hL_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) L)
    (hL_boundedBelow :
      (t.plus : ObjectProperty (ModuleDerived X)) L) :
    DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent (structureSheaf X))
        ((ihomOf H K).obj L) ∧
      (t.plus : ObjectProperty (ModuleDerived X))
        ((ihomOf H K).obj L) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom
