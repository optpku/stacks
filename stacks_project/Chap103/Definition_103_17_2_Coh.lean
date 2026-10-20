/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.Category
public import stacks_project.Chap103.Lemma_103_17_3_Instances
public import stacks_project.Chap103.Lemma_103_17_4_Coherent
import StacksCheckRecall

/-!
# Coherent modules on locally Noetherian algebraic stacks

On a locally Noetherian algebraic stack, an `𝒪_X`-module is coherent when it
satisfies the equivalent conditions of Lemma 103.17.1, recorded by the existing
class `AlgebraicStack.IsCoherent`. The category of such modules is the full
subcategory `Coh`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} (X : GroupoidsOver S)
variable [AlgebraicStack X] [IsLocallyNoetherian X]

#check (AlgebraicGeometry.AlgebraicStack.coherentModuleProperty X :
  ObjectProperty (SheafOfModules.{u} (structureSheaf X)))

#check (AlgebraicGeometry.AlgebraicStack.coherentModuleProperty_eq X :
  coherentModuleProperty X = AlgebraicStack.IsCoherent)

#check (AlgebraicGeometry.AlgebraicStack.mem_coherentModuleProperty_iff :
  ∀ (F : SheafOfModules.{u} (structureSheaf X)),
    coherentModuleProperty X F ↔ AlgebraicStack.IsCoherent F)

/- Definition 103.17.2: the category of coherent `𝒪_X`-modules is denoted
`Coh(𝒪_X)`. -/
@[stacks 0GR6] #check (AlgebraicGeometry.AlgebraicStack.Coh X : Type (u + 1))

#check (AlgebraicGeometry.AlgebraicStack.Coh.inclusion X :
  Coh X ⥤ SheafOfModules.{u} (structureSheaf X))

end AlgebraicGeometry.AlgebraicStack
