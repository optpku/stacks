/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent

/-!
# Coherent modules on locally Noetherian algebraic stacks

On a locally Noetherian algebraic stack, an `𝒪_X`-module is coherent when it is
finitely presented as a sheaf of modules on the fppf ringed topos.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S}
variable [AlgebraicStack X] [IsLocallyNoetherian X]
variable [∀ x : X.total, HasWeakSheafify
    ((inheritedFppfTopology X).over x) AddCommGrpCat.{u}]
variable [∀ x : X.total,
    ((inheritedFppfTopology X).over x).WEqualsLocallyBijective AddCommGrpCat.{u}]

#check (AlgebraicGeometry.AlgebraicStack.IsCoherent :
  SheafOfModules.{u} (structureSheaf X) → Prop)

#check (AlgebraicGeometry.AlgebraicStack.instIsCoherent_of_isFinitePresentation :
  ∀ (F : SheafOfModules.{u} (structureSheaf X)) [F.IsFinitePresentation],
    AlgebraicStack.IsCoherent F)

#check (AlgebraicGeometry.AlgebraicStack.isCoherent_iff :
  ∀ (F : SheafOfModules.{u} (structureSheaf X)),
    AlgebraicStack.IsCoherent F ↔ F.IsFinitePresentation)

end AlgebraicGeometry.AlgebraicStack
