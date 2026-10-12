/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import stacks_project.Chap66.Proposition_66_32_2_Grothendieck

/-!
# Coherators for quasi-coherent modules on algebraic spaces

The inclusion of quasi-coherent modules into all module sheaves on an algebraic space admits a
chosen right adjoint, the coherator. This module records the adjunction and its additive
structure.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

/-- The coherator from all module sheaves on an algebraic space to quasi-coherent module sheaves. -/
noncomputable def coherator {S : Scheme.{u}} (X : AlgebraicSpace S) : X.Modules ⥤ QCoh X :=
  (inclusion X).rightAdjoint

/-- Quasi-coherent inclusion is left adjoint to the coherator. -/
noncomputable def coheratorAdjunction {S : Scheme.{u}} (X : AlgebraicSpace S) :
    inclusion X ⊣ coherator X :=
  Adjunction.ofIsLeftAdjoint (inclusion X)

/-- The coherator is additive. -/
instance coherator.additive {S : Scheme.{u}} (X : AlgebraicSpace S) : (coherator X).Additive :=
  (coheratorAdjunction X).right_adjoint_additive

end AlgebraicGeometry.AlgebraicSpace.QCoh
