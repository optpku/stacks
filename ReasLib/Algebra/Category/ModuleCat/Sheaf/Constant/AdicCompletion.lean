/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import ReasLib.Algebra.Category.ModuleCat.IdealPower.Functor
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.IdealPower

/-!
# Completed constant sheaves of modules

The sheaf `lim n, (M / I ^ n M)̲` attached to a module `M`, together with the
restriction-of-scalars form used for finite modules over the adic completion.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Ideal.PowerQuotient
open Opposite

noncomputable section

universe u v w

namespace CategoryTheory.ConstantSheaf.AdicCompletion

variable {C : Type u} [Category.{v} C] {R : Type w} [CommRing R]

/-- The inverse system `n ↦ M / I ^ n M` in `ModuleCat R`. -/
def moduleSystem (I : Ideal R) (M : ModuleCat.{w} R) :
    ℕᵒᵖ ⥤ ModuleCat.{w} R :=
  Functor.ofOpSequence (stageStep I M)

/-- The module-level inverse system evaluates at `n` to the exact-power quotient. -/
theorem moduleSystem_obj (I : Ideal R) (M : ModuleCat.{w} R) (n : ℕ) :
    (moduleSystem I M).obj (op n) = stage I M n := sorry

variable (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{w} R)]

/-- The inverse system of constant sheaves `n ↦ (M / I ^ n M)̲`. -/
def constantSystem (I : Ideal R) (M : ModuleCat.{w} R) :
    ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{w} R) :=
  moduleSystem I M ⋙ constantSheaf J (ModuleCat.{w} R)

/-- The constant-sheaf inverse system evaluates to the constant sheaf on a quotient stage. -/
theorem constantSystem_obj (I : Ideal R) (M : ModuleCat.{w} R) (n : ℕ) :
    (constantSystem J I M).obj (op n) =
      (constantSheaf J (ModuleCat.{w} R)).obj (stage I M n) := sorry

/-- The completed constant sheaf `lim n, (M / I ^ n M)` of an `R`-module. -/
def ofModule (I : Ideal R) (M : ModuleCat.{w} R) :
    Sheaf J (ModuleCat.{w} R) :=
  limit (constantSystem J I M)

/-- Projection of the completed constant sheaf onto the constant sheaf of a quotient stage. -/
def ofModule_π (I : Ideal R) (M : ModuleCat.{w} R) (n : ℕ) :
    ofModule J I M ⟶ (constantSheaf J (ModuleCat.{w} R)).obj (stage I M n) :=
  limit.π (constantSystem J I M) (op n)

/-- Stagewise identification of `R / I ^ n R` with the ring quotient `R / I ^ n`. -/
def stageIsoIdealQuotient (I : Ideal R) (n : ℕ) :
    stage I (ModuleCat.of R R) n ≅ idealPowerQuotientSequence I n :=
  LinearEquiv.toModuleIso
    (Submodule.quotEquivOfEq (I ^ n • (⊤ : Submodule R R)) (I ^ n) (by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]))

/-- The inverse systems `n ↦ R / I ^ n R` and `n ↦ R / I ^ n` are isomorphic. -/
def moduleSystemIso (I : Ideal R) :
    moduleSystem I (ModuleCat.of R R) ≅ idealPowerQuotientSystem I :=
  NatIso.ofComponents (fun n ↦ stageIsoIdealQuotient I n.unop) sorry

/-- The constant-sheaf towers for the two quotient systems on `R` are isomorphic. -/
def constantSystemIso (I : Ideal R) :
    constantSystem J I (ModuleCat.of R R) ≅
      constantIdealPowerQuotientSheafSystem J I :=
  Functor.isoWhiskerRight (moduleSystemIso I) (constantSheaf J (ModuleCat.{w} R))

/-- The completed constant sheaf of `R` as an `R`-module agrees with the inverse limit
of the constant ideal-power quotient sheaves. -/
def ofModule_self (I : Ideal R) :
    ofModule J I (ModuleCat.of R R) ≅
      limit (constantIdealPowerQuotientSheafSystem J I) :=
  HasLimit.isoOfNatIso (constantSystemIso J I)

/-- The comparison `ofModule_self` intertwines the canonical projections to
constant quotient stages. -/
theorem ofModule_self_π (I : Ideal R) (n : ℕ) :
    (ofModule_self J I).hom ≫
        limit.π (constantIdealPowerQuotientSheafSystem J I) (op n) =
      ofModule_π J I (ModuleCat.of R R) n ≫
        (constantSheaf J (ModuleCat.{w} R)).map (stageIsoIdealQuotient I n).hom := sorry

/-- The completed constant sheaf of an `AdicCompletion I R`-module, regarded as
an `R`-module sheaf by restriction of scalars along `algebraMap R (AdicCompletion I R)`. -/
abbrev ofAdicModule (I : Ideal R) (M : ModuleCat.{w} (AdicCompletion I R)) :
    Sheaf J (ModuleCat.{w} R) :=
  ofModule J I ((ModuleCat.restrictScalars (algebraMap R (AdicCompletion I R))).obj M)

/-- Unfolding `ofAdicModule` recovers restriction of scalars followed by `ofModule`. -/
theorem ofAdicModule_def (I : Ideal R) (M : ModuleCat.{w} (AdicCompletion I R)) :
    ofAdicModule J I M =
      ofModule J I
        ((ModuleCat.restrictScalars (algebraMap R (AdicCompletion I R))).obj M) := sorry

end CategoryTheory.ConstantSheaf.AdicCompletion
