/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import stacks_project.Chap101.Definition_101_8_1_Noetherian
public import stacks_project.Chap96.Definition_96_6_1_StructureSheaf

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

/-- An `𝒪_X`-module on a locally Noetherian algebraic stack is coherent when it is
finitely presented as a sheaf of modules on the fppf ringed topos. -/
protected class IsCoherent (F : SheafOfModules.{u} (structureSheaf X)) : Prop extends
    F.IsFinitePresentation

/-- Finite presentation of an `𝒪_X`-module on a locally Noetherian algebraic stack
is the defining condition for coherence. -/
instance instIsCoherent_of_isFinitePresentation
    (F : SheafOfModules.{u} (structureSheaf X)) [F.IsFinitePresentation] :
    AlgebraicStack.IsCoherent F where

/-- On a locally Noetherian algebraic stack, coherence of an `𝒪_X`-module is equivalent
to finite presentation. -/
theorem isCoherent_iff (F : SheafOfModules.{u} (structureSheaf X)) :
    AlgebraicStack.IsCoherent F ↔ F.IsFinitePresentation :=
  sorry

end AlgebraicGeometry.AlgebraicStack
