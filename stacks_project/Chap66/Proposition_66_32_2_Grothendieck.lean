/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap66.Lemma_66_29_7_Quasicoherent

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

/-- The category of quasi-coherent modules on an algebraic space is Grothendieck abelian. -/
instance instIsGrothendieckAbelian {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsGrothendieckAbelian (QCoh X) :=
  sorry

/-- The inclusion of quasi-coherent modules into all module sheaves has a right adjoint. -/
instance inclusionIsLeftAdjoint {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (inclusion X).IsLeftAdjoint :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QCoh
