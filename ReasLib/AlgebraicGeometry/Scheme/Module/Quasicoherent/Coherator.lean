/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Grothendieck

/-!
# Coherators for Quasicoherent Modules

The inclusion of quasicoherent modules into all module sheaves admits a chosen right adjoint,
the coherator. This module records the adjunction and its additive structure.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/-- The coherator from all module sheaves on a scheme to quasicoherent module sheaves. -/
noncomputable def coherator (X : Scheme.{u}) : X.Modules ⥤ QCoh X :=
  (inclusion X).rightAdjoint

/-- Quasicoherent inclusion is left adjoint to the coherator. -/
noncomputable def coheratorAdjunction (X : Scheme.{u}) :
    inclusion X ⊣ coherator X :=
  Adjunction.ofIsLeftAdjoint (inclusion X)

/-- The coherator is additive. -/
instance coherator.additive (X : Scheme.{u}) : (coherator X).Additive :=
  (coheratorAdjunction X).right_adjoint_additive

end AlgebraicGeometry.Scheme.QCoh
