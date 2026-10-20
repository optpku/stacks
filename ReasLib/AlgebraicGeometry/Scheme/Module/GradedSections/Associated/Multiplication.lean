/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.BasicOpen
public import ReasLib.AlgebraicGeometry.Scheme.Module.GradedSections.Associated

/-!
# Multiplication of associated twisted-section sheaves

The canonical multiplication from an associated twisted-section sheaf tensored with the
associated twist is specified by multiplication of homogeneous fractions on projective
standard opens.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.GradedSections

variable {X : Scheme.{u}}
variable (L : X.Modules) [Invertible L] (F : X.Modules)

/-- A degreewise multiplication from associated twisted-section sheaves whose restriction to
every positive-degree projective standard open is multiplication of homogeneous fractions. -/
structure AssociatedTwistedMultiplication where
  /-- The multiplication morphism in every integral twist degree. -/
  hom :
    ∀ n : ℤ,
      associatedTwistedSheaf L F ⊗ associatedTwistedSheaf L (L ^⊗ n) ⟶
        associatedTwistedSheaf L (F ⊗ L ^⊗ n)
  /-- On a positive-degree projective standard open, homogeneous fractions are multiplied after
  identifying the second numerator with the twist and the result with the shifted twisted-section
  module. -/
  standardOpen_formula :
    ∀ {d : ℕ} (s : RingedSpace.GradedSections.grading L d) (hd : 0 < d)
      (n : ℤ) (p q : ℕ)
      (x : RingedSpace.GradedSections.twistedDegree L F ((p • d : ℕ) : ℤ))
      (y : RingedSpace.GradedSections.twistedDegree L (L ^⊗ n) ((q • d : ℕ) : ℤ)),
      let xInternal : twistedInternalGrading L F ((p • d : ℕ) : ℤ) :=
        ⟨DirectSum.lof ℤ ℤ (RingedSpace.GradedSections.twistedDegree L F)
          ((p • d : ℕ) : ℤ) x, ⟨x, rfl⟩⟩
      let xNumerator :
          Proj.AssociatedModule.nonnegativeGrading (twistedInternalGrading L F) (p • d) :=
        xInternal
      let xFraction : Proj.AssociatedModule.away
          (RingedSpace.GradedSections.grading L) (twistedInternalGrading L F) s :=
        ⟨HomogeneousLocalization.Away.Module.powMkHomogeneous
            (RingedSpace.GradedSections.grading L)
            (Proj.AssociatedModule.nonnegativeGrading (twistedInternalGrading L F))
            s p xNumerator,
          HomogeneousLocalization.Away.Module.powMkHomogeneous_mem_degreeZeroPart
            (RingedSpace.GradedSections.grading L)
            (Proj.AssociatedModule.nonnegativeGrading (twistedInternalGrading L F))
            s xNumerator⟩
      let yInternal : twistedInternalGrading L (L ^⊗ n) ((q • d : ℕ) : ℤ) :=
        ⟨DirectSum.lof ℤ ℤ (RingedSpace.GradedSections.twistedDegree L (L ^⊗ n))
          ((q • d : ℕ) : ℤ) y, ⟨y, rfl⟩⟩
      let yNumerator : Proj.AssociatedModule.nonnegativeGrading
          (twistedInternalGrading L (L ^⊗ n)) (q • d) :=
        yInternal
      let yFraction : Proj.AssociatedModule.away
          (RingedSpace.GradedSections.grading L)
          (twistedInternalGrading L (L ^⊗ n)) s :=
        ⟨HomogeneousLocalization.Away.Module.powMkHomogeneous
            (RingedSpace.GradedSections.grading L)
            (Proj.AssociatedModule.nonnegativeGrading
              (twistedInternalGrading L (L ^⊗ n))) s q yNumerator,
          HomogeneousLocalization.Away.Module.powMkHomogeneous_mem_degreeZeroPart
            (RingedSpace.GradedSections.grading L)
            (Proj.AssociatedModule.nonnegativeGrading
              (twistedInternalGrading L (L ^⊗ n))) s yNumerator⟩
      let assoc := @MonoidalCategoryStruct.associator
        (RingedSpace.Modules X.toRingedSpace) SheafOfModules.instCategory
        (RingedSpace.modulesMonoidalCategory X.toRingedSpace).toMonoidalCategoryStruct
      let tensorIso := @MonoidalCategory.tensorIso
        (RingedSpace.Modules X.toRingedSpace) SheafOfModules.instCategory
        (RingedSpace.modulesMonoidalCategory X.toRingedSpace)
      let braid := @BraidedCategory.braiding
        (RingedSpace.Modules X.toRingedSpace) SheafOfModules.instCategory
        (RingedSpace.modulesMonoidalCategory X.toRingedSpace)
        (RingedSpace.modulesSymmetricCategory X.toRingedSpace).toBraidedCategory
      let a : ℤ := (p • d : ℕ)
      let b : ℤ := (q • d : ℕ)
      let productIso :
          (F ⊗ L ^⊗ a) ⊗ (L ^⊗ n ⊗ L ^⊗ b) ≅
            (F ⊗ L ^⊗ n) ⊗ L ^⊗ (a + b) :=
        assoc F (L ^⊗ a) (L ^⊗ n ⊗ L ^⊗ b) ≪≫
          tensorIso (Iso.refl F) (assoc (L ^⊗ a) (L ^⊗ n) (L ^⊗ b)).symm ≪≫
          tensorIso (Iso.refl F)
            (tensorIso (braid (L ^⊗ a) (L ^⊗ n)) (Iso.refl (L ^⊗ b))) ≪≫
          tensorIso (Iso.refl F) (assoc (L ^⊗ n) (L ^⊗ a) (L ^⊗ b)) ≪≫
          (assoc F (L ^⊗ n) (L ^⊗ a ⊗ L ^⊗ b)).symm ≪≫
          tensorIso (Iso.refl (F ⊗ L ^⊗ n))
            (RingedSpace.InvertiblePower.addIso L a b)
      let productSection : RingedSpace.GradedSections.twistedDegree L (F ⊗ L ^⊗ n)
          (((p + q) • d : ℕ) : ℤ) := by
        simpa only [a, b, add_nsmul, Nat.cast_add] using
          RingedSpace.sectionsEquivTop ((F ⊗ L ^⊗ n) ⊗ L ^⊗ (a + b))
            (SheafOfModules.sectionsMap productIso.hom
              (RingedSpace.tensorSection
                (RingedSpace.sectionFromTop (F ⊗ L ^⊗ a) x)
                (RingedSpace.sectionFromTop (L ^⊗ n ⊗ L ^⊗ b) y)))
      let productInternal : twistedInternalGrading L (F ⊗ L ^⊗ n)
          (((p + q) • d : ℕ) : ℤ) :=
        ⟨DirectSum.lof ℤ ℤ
          (RingedSpace.GradedSections.twistedDegree L (F ⊗ L ^⊗ n))
          (((p + q) • d : ℕ) : ℤ) productSection, ⟨productSection, rfl⟩⟩
      let productNumerator : Proj.AssociatedModule.nonnegativeGrading
          (twistedInternalGrading L (F ⊗ L ^⊗ n)) ((p + q) • d) :=
        productInternal
      let productFraction : Proj.AssociatedModule.away
          (RingedSpace.GradedSections.grading L)
          (twistedInternalGrading L (F ⊗ L ^⊗ n)) s :=
        ⟨HomogeneousLocalization.Away.Module.powMkHomogeneous
            (RingedSpace.GradedSections.grading L)
            (Proj.AssociatedModule.nonnegativeGrading
              (twistedInternalGrading L (F ⊗ L ^⊗ n)))
            s (p + q) productNumerator,
          HomogeneousLocalization.Away.Module.powMkHomogeneous_mem_degreeZeroPart
            (RingedSpace.GradedSections.grading L)
            (Proj.AssociatedModule.nonnegativeGrading
              (twistedInternalGrading L (F ⊗ L ^⊗ n))) s productNumerator⟩
      (((hom n).val.app
          (op (Proj.basicOpen (RingedSpace.GradedSections.grading L) (s : _)))).hom
        (SheafOfModules.RingedSite.tensorSection
          (Proj (RingedSpace.GradedSections.grading L)).sheaf
          (op (Proj.basicOpen (RingedSpace.GradedSections.grading L) (s : _)))
          (Proj.AssociatedModule.awaySection
            (RingedSpace.GradedSections.grading L) (twistedInternalGrading L F)
            s hd xFraction)
          (Proj.AssociatedModule.awaySection
            (RingedSpace.GradedSections.grading L)
            (twistedInternalGrading L (L ^⊗ n))
            s hd yFraction))) =
        Proj.AssociatedModule.awaySection
          (RingedSpace.GradedSections.grading L)
          (twistedInternalGrading L (F ⊗ L ^⊗ n)) s hd
          productFraction

namespace AssociatedTwistedMultiplication

/-- Construct associated twisted-section multiplication data from explicit morphisms satisfying
the standard-open homogeneous-fraction formula. -/
noncomputable def ofHom
    (hom :
      ∀ n : ℤ,
        associatedTwistedSheaf L F ⊗ associatedTwistedSheaf L (L ^⊗ n) ⟶
          associatedTwistedSheaf L (F ⊗ L ^⊗ n)) :=
  @AssociatedTwistedMultiplication.mk X L _ F hom

/-- The multiplication morphisms send standard homogeneous fractions to the fraction obtained by
tensoring their numerators, with the twist and shifted target identified canonically. -/
theorem spec
    (C : AssociatedTwistedMultiplication L F)
    {d : ℕ} (s : RingedSpace.GradedSections.grading L d) (hd : 0 < d)
    (n : ℤ) (p q : ℕ)
    (x : RingedSpace.GradedSections.twistedDegree L F ((p • d : ℕ) : ℤ))
    (y : RingedSpace.GradedSections.twistedDegree L (L ^⊗ n) ((q • d : ℕ) : ℤ)) :
    let xInternal : twistedInternalGrading L F ((p • d : ℕ) : ℤ) :=
      ⟨DirectSum.lof ℤ ℤ (RingedSpace.GradedSections.twistedDegree L F)
        ((p • d : ℕ) : ℤ) x, ⟨x, rfl⟩⟩
    let xNumerator :
        Proj.AssociatedModule.nonnegativeGrading (twistedInternalGrading L F) (p • d) :=
      xInternal
    let xFraction : Proj.AssociatedModule.away
        (RingedSpace.GradedSections.grading L) (twistedInternalGrading L F) s :=
      ⟨HomogeneousLocalization.Away.Module.powMkHomogeneous
          (RingedSpace.GradedSections.grading L)
          (Proj.AssociatedModule.nonnegativeGrading (twistedInternalGrading L F))
          s p xNumerator,
        HomogeneousLocalization.Away.Module.powMkHomogeneous_mem_degreeZeroPart
          (RingedSpace.GradedSections.grading L)
          (Proj.AssociatedModule.nonnegativeGrading (twistedInternalGrading L F))
          s xNumerator⟩
    let yInternal : twistedInternalGrading L (L ^⊗ n) ((q • d : ℕ) : ℤ) :=
      ⟨DirectSum.lof ℤ ℤ (RingedSpace.GradedSections.twistedDegree L (L ^⊗ n))
        ((q • d : ℕ) : ℤ) y, ⟨y, rfl⟩⟩
    let yNumerator : Proj.AssociatedModule.nonnegativeGrading
        (twistedInternalGrading L (L ^⊗ n)) (q • d) :=
      yInternal
    let yFraction : Proj.AssociatedModule.away
        (RingedSpace.GradedSections.grading L)
        (twistedInternalGrading L (L ^⊗ n)) s :=
      ⟨HomogeneousLocalization.Away.Module.powMkHomogeneous
          (RingedSpace.GradedSections.grading L)
          (Proj.AssociatedModule.nonnegativeGrading
            (twistedInternalGrading L (L ^⊗ n))) s q yNumerator,
        HomogeneousLocalization.Away.Module.powMkHomogeneous_mem_degreeZeroPart
          (RingedSpace.GradedSections.grading L)
          (Proj.AssociatedModule.nonnegativeGrading
            (twistedInternalGrading L (L ^⊗ n))) s yNumerator⟩
    let assoc := @MonoidalCategoryStruct.associator
      (RingedSpace.Modules X.toRingedSpace) SheafOfModules.instCategory
      (RingedSpace.modulesMonoidalCategory X.toRingedSpace).toMonoidalCategoryStruct
    let tensorIso := @MonoidalCategory.tensorIso
      (RingedSpace.Modules X.toRingedSpace) SheafOfModules.instCategory
      (RingedSpace.modulesMonoidalCategory X.toRingedSpace)
    let braid := @BraidedCategory.braiding
      (RingedSpace.Modules X.toRingedSpace) SheafOfModules.instCategory
      (RingedSpace.modulesMonoidalCategory X.toRingedSpace)
      (RingedSpace.modulesSymmetricCategory X.toRingedSpace).toBraidedCategory
    let a : ℤ := (p • d : ℕ)
    let b : ℤ := (q • d : ℕ)
    let productIso :
        (F ⊗ L ^⊗ a) ⊗ (L ^⊗ n ⊗ L ^⊗ b) ≅
          (F ⊗ L ^⊗ n) ⊗ L ^⊗ (a + b) :=
      assoc F (L ^⊗ a) (L ^⊗ n ⊗ L ^⊗ b) ≪≫
        tensorIso (Iso.refl F) (assoc (L ^⊗ a) (L ^⊗ n) (L ^⊗ b)).symm ≪≫
        tensorIso (Iso.refl F)
          (tensorIso (braid (L ^⊗ a) (L ^⊗ n)) (Iso.refl (L ^⊗ b))) ≪≫
        tensorIso (Iso.refl F) (assoc (L ^⊗ n) (L ^⊗ a) (L ^⊗ b)) ≪≫
        (assoc F (L ^⊗ n) (L ^⊗ a ⊗ L ^⊗ b)).symm ≪≫
        tensorIso (Iso.refl (F ⊗ L ^⊗ n))
          (RingedSpace.InvertiblePower.addIso L a b)
    let productSection : RingedSpace.GradedSections.twistedDegree L (F ⊗ L ^⊗ n)
        (((p + q) • d : ℕ) : ℤ) := by
      simpa only [a, b, add_nsmul, Nat.cast_add] using
        RingedSpace.sectionsEquivTop ((F ⊗ L ^⊗ n) ⊗ L ^⊗ (a + b))
          (SheafOfModules.sectionsMap productIso.hom
            (RingedSpace.tensorSection
              (RingedSpace.sectionFromTop (F ⊗ L ^⊗ a) x)
              (RingedSpace.sectionFromTop (L ^⊗ n ⊗ L ^⊗ b) y)))
    let productInternal : twistedInternalGrading L (F ⊗ L ^⊗ n)
        (((p + q) • d : ℕ) : ℤ) :=
      ⟨DirectSum.lof ℤ ℤ
        (RingedSpace.GradedSections.twistedDegree L (F ⊗ L ^⊗ n))
        (((p + q) • d : ℕ) : ℤ) productSection, ⟨productSection, rfl⟩⟩
    let productNumerator : Proj.AssociatedModule.nonnegativeGrading
        (twistedInternalGrading L (F ⊗ L ^⊗ n)) ((p + q) • d) :=
      productInternal
    let productFraction : Proj.AssociatedModule.away
        (RingedSpace.GradedSections.grading L)
        (twistedInternalGrading L (F ⊗ L ^⊗ n)) s :=
      ⟨HomogeneousLocalization.Away.Module.powMkHomogeneous
          (RingedSpace.GradedSections.grading L)
          (Proj.AssociatedModule.nonnegativeGrading
            (twistedInternalGrading L (F ⊗ L ^⊗ n)))
          s (p + q) productNumerator,
        HomogeneousLocalization.Away.Module.powMkHomogeneous_mem_degreeZeroPart
          (RingedSpace.GradedSections.grading L)
          (Proj.AssociatedModule.nonnegativeGrading
            (twistedInternalGrading L (F ⊗ L ^⊗ n))) s productNumerator⟩
    (((C.hom n).val.app
        (op (Proj.basicOpen (RingedSpace.GradedSections.grading L) (s : _)))).hom
      (SheafOfModules.RingedSite.tensorSection
        (Proj (RingedSpace.GradedSections.grading L)).sheaf
        (op (Proj.basicOpen (RingedSpace.GradedSections.grading L) (s : _)))
        (Proj.AssociatedModule.awaySection
          (RingedSpace.GradedSections.grading L) (twistedInternalGrading L F)
          s hd xFraction)
        (Proj.AssociatedModule.awaySection
          (RingedSpace.GradedSections.grading L)
          (twistedInternalGrading L (L ^⊗ n))
          s hd yFraction))) =
      Proj.AssociatedModule.awaySection
        (RingedSpace.GradedSections.grading L)
        (twistedInternalGrading L (F ⊗ L ^⊗ n)) s hd
        productFraction := sorry

end AssociatedTwistedMultiplication

end AlgebraicGeometry.Scheme.Modules.GradedSections
