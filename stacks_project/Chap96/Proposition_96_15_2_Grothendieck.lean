/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import stacks_project.Chap96.Definition_96_11_1_QCoh
public import stacks_project.Chap96.Lemma_96_15_1_Abelian

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

/-- The category of quasi-coherent modules on an algebraic stack is Grothendieck abelian. -/
instance instIsGrothendieckAbelian {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    IsGrothendieckAbelian (QCoh X) :=
  sorry

/-- The inclusion of quasi-coherent modules into all module sheaves has a right adjoint. -/
instance inclusionIsLeftAdjoint {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    (inclusion X).IsLeftAdjoint :=
  sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
