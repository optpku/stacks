/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.ConstantSheaf.IdealPower
public import ReasLib.CategoryTheory.Sites.LocallyConstant.DerivedTensor
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite.RestrictScalars
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ideal-power quotients and locally constant cohomology

This leaf records the successor-stage closure of finite-type locally constant cohomology under
derived tensoring with the constant ideal-power quotient sheaves.  The quotient stages are the
concrete owners from `ConstantSheaf.IdealPower`; no existential stage package is exposed.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open DerivedCategory.TStructure

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf.LocallyConstant.FiniteType.Cohomology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]

/-- The object property of locally constant sheaves of finite `Λ / I ^ n`-modules, expressed
on their underlying `Λ`-module sheaves by restriction along the quotient map. -/
@[stacks 094I "finite-type locally constant quotient coefficients"]
abbrev finiteTypeLocallyConstantIdealPowerModule (J : GrothendieckTopology C)
    (I : Ideal Λ) (n : ℕ)
    [hJ : ∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)] :
    ObjectProperty (Sheaf J (ModuleCat.{w} Λ)) :=
  finiteTypeLocallyConstantRestrictedModule (R := Λ) J
    (Ideal.Quotient.mk (I ^ n)) (hJ := hJ)

/-- Forgetting the quotient coefficient structure sends a finite-type locally constant
`Λ / I ^ n`-module sheaf to a finite-type locally constant `Λ`-module sheaf. -/
@[stacks 094I "forgetting quotient coefficients"]
theorem finiteTypeLocallyConstantIdealPowerModule_le (I : Ideal Λ) (n : ℕ) :
    finiteTypeLocallyConstantIdealPowerModule J I n ≤
      finiteTypeLocallyConstantModule J Λ := sorry

variable [IsNoetherianRing Λ]
variable [((J.W : MorphismProperty (Cᵒᵖ ⥤ ModuleCat.{w} Λ))).IsMonoidal]
variable [Abelian (Sheaf J (ModuleCat.{w} Λ))]
variable [CategoryWithHomology (Sheaf J (ModuleCat.{w} Λ))]
variable [HasDerivedCategory (Sheaf J (ModuleCat.{w} Λ))]
variable [MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))]

/-- Lemma 21.53.5 (094I): if the stage `Λ / I` has finite-type locally constant cohomology,
then every positive ideal-power quotient stage has the same property after derived tensoring with
`K`. -/
@[stacks 094I "ideal-power tensor closure of locally constant cohomology"]
theorem tensor_constantIdealPowerQuotient
    (I : Ideal Λ)
    (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))
    (hKboundedAbove : (t.minus : ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))) K)
    (hcohModI :
      DerivedCategory.cohomologyIn (finiteTypeLocallyConstantIdealPowerModule J I 1)
        (K ⊗ (DerivedCategory.singleFunctor (Sheaf J (ModuleCat.{w} Λ)) (0 : ℤ)).obj
          (constantIdealQuotientSheaf J I)))
    (n : ℕ+) :
    DerivedCategory.cohomologyIn
      (finiteTypeLocallyConstantIdealPowerModule J I (n : ℕ))
      (K ⊗ (DerivedCategory.singleFunctor (Sheaf J (ModuleCat.{w} Λ)) (0 : ℤ)).obj
        (constantIdealQuotientSheaf J (I ^ (n : ℕ)))) := sorry

/-- The natural-number successor-stage form of the ideal-power tensor closure theorem. -/
theorem tensor_constantIdealPowerQuotient_succ
    (I : Ideal Λ)
    (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))
    (hKboundedAbove : (t.minus : ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))) K)
    (hcohModI :
      DerivedCategory.cohomologyIn (finiteTypeLocallyConstantIdealPowerModule J I 1)
        (K ⊗ (DerivedCategory.singleFunctor (Sheaf J (ModuleCat.{w} Λ)) (0 : ℤ)).obj
          (constantIdealQuotientSheaf J I)))
    (n : ℕ) :
    DerivedCategory.cohomologyIn
      (finiteTypeLocallyConstantIdealPowerModule J I (n + 1))
      (K ⊗ (DerivedCategory.singleFunctor (Sheaf J (ModuleCat.{w} Λ)) (0 : ℤ)).obj
        (constantIdealQuotientSheaf J (I ^ (n + 1)))) := sorry

end CategoryTheory.Sheaf.LocallyConstant.FiniteType.Cohomology

end
