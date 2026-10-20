/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import stacks_project.Chap96.Proposition_96_15_2_Grothendieck

/-!
# Coherators for quasi-coherent modules on algebraic stacks

The inclusion of quasi-coherent modules into all module sheaves on an algebraic stack admits a
chosen right adjoint, the coherator. This module records the adjunction and its additive
structure.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

/-- The coherator from all module sheaves on an algebraic stack to quasi-coherent module sheaves. -/
noncomputable def coherator {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    RingedSite.ModuleCat.{u} (fppfRingedSite X) ⥤ QCoh X :=
  (inclusion X).rightAdjoint

/-- Quasi-coherent inclusion is left adjoint to the coherator. -/
noncomputable def coheratorAdjunction {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    inclusion X ⊣ coherator X :=
  Adjunction.ofIsLeftAdjoint (inclusion X)

/-- The coherator is additive. -/
instance coherator.additive {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    (coherator X).Additive :=
  (coheratorAdjunction X).right_adjoint_additive

end AlgebraicGeometry.GroupoidsOver.QCoh
