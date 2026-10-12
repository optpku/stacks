/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap103.Lemma_103_17_3_Instances
public import stacks_project.Chap103.Lemma_103_17_4_Coherent

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

/-- The object property of coherent `𝒪_X`-modules on a locally Noetherian
algebraic stack. -/
abbrev coherentModuleProperty {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] :
    ObjectProperty (SheafOfModules.{u} (structureSheaf X)) :=
  AlgebraicStack.IsCoherent

/-- `coherentModuleProperty X` is the stack-local coherence class. -/
theorem coherentModuleProperty_eq {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] :
    coherentModuleProperty X = AlgebraicStack.IsCoherent :=
  sorry

/-- A module sheaf on a locally Noetherian algebraic stack lies in
`coherentModuleProperty X` if and only if it is coherent. -/
theorem mem_coherentModuleProperty_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X]
    (F : SheafOfModules.{u} (structureSheaf X)) :
    coherentModuleProperty X F ↔ AlgebraicStack.IsCoherent F :=
  sorry

/-- The category `Coh(𝒪_X)` of coherent modules on a locally Noetherian
algebraic stack. -/
abbrev Coh {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] :=
  (coherentModuleProperty X).FullSubcategory

namespace Coh

/-- The inclusion of coherent modules into all `𝒪_X`-modules. -/
abbrev inclusion {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] :
    Coh X ⥤ SheafOfModules.{u} (structureSheaf X) :=
  (coherentModuleProperty X).ι

end Coh

end AlgebraicGeometry.AlgebraicStack
