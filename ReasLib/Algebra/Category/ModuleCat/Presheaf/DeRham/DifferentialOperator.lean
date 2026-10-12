/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.DeRham
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.DifferentialOperator
public import ReasLib.RingTheory.Kaehler.DeRham.DifferentialOperator
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential-operator order of presheaf de Rham differentials

The objectwise algebraic first-order bound assembles into the corresponding
bound for the de Rham differential of commutative-ring presheaves.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace PresheafOfModules.DeRham

variable {C : Type u} [Category.{v} C]
variable {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{max u v}}

/-- Every differential in the relative de Rham complex of commutative-ring
presheaves is a differential operator of order at most one. -/
@[stacks 0G3Y "presheaf de Rham differentials are first order"]
theorem d_isOrderOne (φ : O₁ ⟶ O₂) (p : ℕ) :
    PresheafOfModules.IsDifferentialOperatorOfOrder φ (d φ p) 1 := sorry

end PresheafOfModules.DeRham
