/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.Comparison

/-!
# Compatibility names for polynomial-presentation cotangent comparisons
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open HomologicalComplex
open AlgebraicTopology
open scoped Simplicial ZeroObject TensorProduct ChangeOfRings

noncomputable section

universe u

namespace CategoryTheory.CommRingCat.Under
namespace CotangentComplex

open CommRingCat.Under.FreeAlgebra

abbrev kernelModule (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) : ModuleCat.{u} A :=
  Comparison.kernelModule A B E φ

abbrev differentialsModule (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) : ModuleCat.{u} A :=
  Comparison.differentialsModule A B E φ

abbrev kernelToDifferentials (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    kernelModule A B E φ ⟶ differentialsModule A B E φ :=
  Comparison.kernelToDifferentials A B E φ

abbrev kernelDifferentialsChain (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) : ChainComplex (ModuleCat.{u} A) ℕ :=
  Comparison.kernelDifferentialsChain A B E φ

abbrev kernelDifferentialsComplex (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) : CochainComplex (ModuleCat.{u} A) ℤ :=
  Comparison.kernelDifferentialsComplex A B E φ

abbrev kernelDifferentialsComplex_X_zero (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    (kernelDifferentialsComplex A B E φ).X 0 ≅ differentialsModule A B E φ :=
  Comparison.kernelDifferentialsComplex_X_zero A B E φ

abbrev kernelDifferentialsComplex_X_negOne (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    (kernelDifferentialsComplex A B E φ).X (-1) ≅ kernelModule A B E φ :=
  Comparison.kernelDifferentialsComplex_X_negOne A B E φ

theorem kernelDifferentialsComplex_d (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    (kernelDifferentialsComplex A B E φ).d (-1) 0 =
      (kernelDifferentialsComplex_X_negOne A B E φ).hom ≫
        kernelToDifferentials A B E φ ≫
          (kernelDifferentialsComplex_X_zero A B E φ).inv :=
  Comparison.kernelDifferentialsComplex_d A B E φ

abbrev toStandard (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    (functor A).obj E ⟶ standardTerm A B (op ⦋0⦌) :=
  Comparison.toStandard A B E φ

abbrev objRestrictScalars (A : CommRingCat.{u}) (B : Under A) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  Comparison.objRestrictScalars A B

abbrev comparisonDifferentialsMap (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    CommRingCat.KaehlerDifferential ((functor A).obj E).hom ⟶
      (ModuleCat.restrictScalars (toStandard A B E φ).right.hom).obj
        (CommRingCat.KaehlerDifferential (standardTerm A B (op ⦋0⦌)).hom) :=
  Comparison.comparisonDifferentialsMap A B E φ

theorem toStandard_comp_augmentation_hom (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    φ.right.hom =
      (standardAugmentation A B (op ⦋0⦌)).hom.comp (toStandard A B E φ).right.hom :=
  Comparison.toStandard_comp_augmentation_hom A B E φ

abbrev comparison_f_zero (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    differentialsModule A B E φ ⟶
      (ModuleCat.restrictScalars B.hom.hom).obj ((simplicialModule A B).obj (op ⦋0⦌)) :=
  Comparison.comparison_f_zero A B E φ

abbrev standardKernelModule (A : CommRingCat.{u}) (B : Under A) (n : SimplexCategoryᵒᵖ) :
    ModuleCat.{u} A :=
  Comparison.standardKernelModule A B n

theorem standardKernelModule_eq (A : CommRingCat.{u}) (B : Under A) (n : SimplexCategoryᵒᵖ) :
    standardKernelModule A B n =
      (ModuleCat.restrictScalars (standardTerm A B n).hom.hom).obj
        (ModuleCat.of (standardTerm A B n).right
          (RingHom.ker (standardAugmentation A B n).hom)) :=
  Comparison.standardKernelModule_eq A B n

abbrev standardKernelMap (A : CommRingCat.{u}) (B : Under A)
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    standardKernelModule A B n ⟶ standardKernelModule A B m :=
  Comparison.standardKernelMap A B φ

abbrev kernelSimplicial (A : CommRingCat.{u}) (B : Under A) :
    SimplicialObject (ModuleCat.{u} A) :=
  Comparison.kernelSimplicial A B

theorem kernelSimplicial_obj (A : CommRingCat.{u}) (B : Under A) (n : SimplexCategoryᵒᵖ) :
    (kernelSimplicial A B).obj n = standardKernelModule A B n :=
  Comparison.kernelSimplicial_obj A B n

abbrev standardKernelToDifferentials (A : CommRingCat.{u}) (B : Under A) (n : SimplexCategoryᵒᵖ) :
    standardKernelModule A B n ⟶
      (ModuleCat.restrictScalars B.hom.hom).obj ((simplicialModule A B).obj n) :=
  Comparison.standardKernelToDifferentials A B n

abbrev kernelSimplicialToOmega (A : CommRingCat.{u}) (B : Under A) :
    kernelSimplicial A B ⟶
      simplicialModule A B ⋙ ModuleCat.restrictScalars B.hom.hom :=
  Comparison.kernelSimplicialToOmega A B

abbrev standardKernelChain (A : CommRingCat.{u}) (B : Under A) :
    ChainComplex (ModuleCat.{u} A) ℕ :=
  Comparison.standardKernelChain A B

abbrev standardKernelComplex (A : CommRingCat.{u}) (B : Under A) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  Comparison.standardKernelComplex A B

abbrev standardKernelComplex_X (A : CommRingCat.{u}) (B : Under A) (n : ℕ) :
    (standardKernelComplex A B).X (-n) ≅ standardKernelModule A B (op ⦋n⦌) :=
  Comparison.standardKernelComplex_X A B n

abbrev standardKernelToOmega_f (A : CommRingCat.{u}) (B : Under A) :
    ∀ i : ℤ, (standardKernelComplex A B).X i ⟶ (objRestrictScalars A B).X i :=
  Comparison.standardKernelToOmega_f A B

abbrev standardKernelToOmega (A : CommRingCat.{u}) (B : Under A) :
    standardKernelComplex A B ⟶ objRestrictScalars A B :=
  Comparison.standardKernelToOmega A B

theorem standardKernelToOmega_f_zero (A : CommRingCat.{u}) (B : Under A) :
    (standardKernelToOmega A B).f 0 =
      (standardKernelComplex_X A B 0).hom ≫
        standardKernelToDifferentials A B (op ⦋0⦌) ≫
          (ModuleCat.restrictScalars B.hom.hom).map (objXIso A B 0).inv :=
  Comparison.standardKernelToOmega_f_zero A B

instance hasHomotopyCofiber_standardKernelToOmega (A : CommRingCat.{u}) (B : Under A) :
    HasHomotopyCofiber (standardKernelToOmega A B) :=
  Comparison.hasHomotopyCofiber_standardKernelToOmega A B

abbrev standardEvaluationCone (A : CommRingCat.{u}) (B : Under A) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  Comparison.standardEvaluationCone A B

theorem standardEvaluationCone_eq (A : CommRingCat.{u}) (B : Under A) :
    standardEvaluationCone A B =
      CochainComplex.mappingCone (standardKernelToOmega A B) :=
  Comparison.standardEvaluationCone_eq A B

abbrev omegaInr (A : CommRingCat.{u}) (B : Under A) :
    objRestrictScalars A B ⟶ standardEvaluationCone A B :=
  Comparison.omegaInr A B

theorem omegaInr_eq (A : CommRingCat.{u}) (B : Under A) :
    omegaInr A B = CochainComplex.mappingCone.inr (standardKernelToOmega A B) :=
  Comparison.omegaInr_eq A B

abbrev kernelToStandard (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    kernelModule A B E φ ⟶ standardKernelModule A B (op ⦋0⦌) :=
  Comparison.kernelToStandard A B E φ

theorem toStandard_mem_ker (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) (j : RingHom.ker φ.right.hom) :
    (standardAugmentation A B (op ⦋0⦌)).hom ((toStandard A B E φ).right j.1) = 0 :=
  Comparison.toStandard_mem_ker A B E φ j

theorem kernelToStandard_comp_standardKernelToDifferentials
    (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    kernelToStandard A B E φ ≫ standardKernelToDifferentials A B (op ⦋0⦌) =
      kernelToDifferentials A B E φ ≫ comparison_f_zero A B E φ :=
  Comparison.kernelToStandard_comp_standardKernelToDifferentials A B E φ

theorem up_rel_negOne_zero : ComplexShape.Rel (ComplexShape.up ℤ) (-1) 0 :=
  Comparison.up_rel_negOne_zero

abbrev evaluationToMappingCone_f (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    ∀ i : ℤ,
      (kernelDifferentialsComplex A B E φ).X i ⟶ (standardEvaluationCone A B).X i :=
  Comparison.evaluationToMappingCone_f A B E φ

abbrev evaluationToMappingCone (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    kernelDifferentialsComplex A B E φ ⟶ standardEvaluationCone A B :=
  Comparison.evaluationToMappingCone A B E φ

theorem evaluationToMappingCone_f_zero (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    (evaluationToMappingCone A B E φ).f 0 =
      (kernelDifferentialsComplex_X_zero A B E φ).hom ≫
        comparison_f_zero A B E φ ≫
          (ModuleCat.restrictScalars B.hom.hom).map (objXIso A B 0).inv ≫
            (omegaInr A B).f 0 :=
  Comparison.evaluationToMappingCone_f_zero A B E φ

end CotangentComplex
end CategoryTheory.CommRingCat.Under
