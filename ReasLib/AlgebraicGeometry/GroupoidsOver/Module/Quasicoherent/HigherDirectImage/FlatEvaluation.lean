/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.HigherDirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Abelian
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector.Evaluation

/-! # Integer higher direct images and comparison at flat objects -/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open FiberedCategoryOver.Groupoids Functor.Fiber Opposite
open scoped Bicategory ZeroObject

noncomputable section
universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallAssociatedTypeSections f StandardTopology.fppf]
    [HasInjectiveResolutions (AlgebraicStack.fppfModules X)]

/-- Quasi-coherent higher direct image in integer degrees, extended by zero in negative degrees. -/
def higherDirectImageFunctorInt (i : ℤ) : QCoh X ⥤ QCoh Y :=
  match i with
  | .ofNat n => higherDirectImageFunctor f n
  | .negSucc _ => 0

/-- The integer extension agrees with quasi-coherent higher direct image in nonnegative degrees. -/
theorem higherDirectImageFunctorInt_ofNat (n : ℕ) :
    higherDirectImageFunctorInt f (Int.ofNat n) = higherDirectImageFunctor f n := rfl

/-- The integer extension of quasi-coherent higher direct image is zero in negative degrees. -/
theorem higherDirectImageFunctorInt_negSucc (n : ℕ) :
    higherDirectImageFunctorInt f (Int.negSucc n) = (0 : QCoh X ⥤ QCoh Y) := rfl

/-- Étale restriction of fppf higher direct image, extended by zero in negative degrees. -/
def higherDirectImageUnderlyingFunctorInt (i : ℤ) : QCoh X ⥤ etaleModules Y :=
  match i with
  | .ofNat n => inclusion X ⋙ AlgebraicStack.fppfHigherDirectImageFunctor f n ⋙ restriction Y
  | .negSucc _ => 0

section

omit [AlgebraicStack X] [AlgebraicStack Y]
  [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
  [HasInjectiveResolutions (AlgebraicStack.fppfModules X)]

/-- Nonnegative underlying higher images are the restricted fppf-derived images. -/
theorem higherDirectImageUnderlyingFunctorInt_ofNat (n : ℕ) :
    higherDirectImageUnderlyingFunctorInt f (Int.ofNat n) =
      inclusion X ⋙ AlgebraicStack.fppfHigherDirectImageFunctor f n ⋙ restriction Y := rfl

/-- The underlying integer higher-image functor vanishes in negative degrees. -/
theorem higherDirectImageUnderlyingFunctorInt_negSucc (n : ℕ) :
    higherDirectImageUnderlyingFunctorInt f (Int.negSucc n) =
      (0 : QCoh X ⥤ etaleModules Y) := rfl

end

/-- Evaluation of the canonical higher-image comparison, with the zero map in negative degrees. -/
def higherDirectImageCounitEval {V : Over S} (y : Y.p.Fiber V) (F : QCoh X) (i : ℤ) :
    (SheafOfModules.evaluation (etaleRingedSite Y).structureSheaf
      (op (fiberInclusion.obj y))).obj
        ((inclusion Y ⋙ restriction Y).obj ((higherDirectImageFunctorInt f i).obj F)) ⟶
    (SheafOfModules.evaluation (etaleRingedSite Y).structureSheaf
      (op (fiberInclusion.obj y))).obj ((higherDirectImageUnderlyingFunctorInt f i).obj F) :=
  match i with
  | .ofNat n => LQCohFbc.toQCohCounitEval y
      ⟨(inclusion X ⋙ AlgebraicStack.fppfHigherDirectImageFunctor f n ⋙ restriction Y).obj F,
        qCohHigherDirectImage_mem_lqcohFbc f n F⟩
  | .negSucc _ => 0

/-- In nonnegative degrees, higher-image comparison evaluates the canonical coreflection counit. -/
theorem higherDirectImageCounitEval_eq {V : Over S} (y : Y.p.Fiber V)
    (F : QCoh X) (n : ℕ) :
    higherDirectImageCounitEval f y F (Int.ofNat n) =
      LQCohFbc.toQCohCounitEval y
        ⟨(inclusion X ⋙ AlgebraicStack.fppfHigherDirectImageFunctor f n ⋙ restriction Y).obj F,
          qCohHigherDirectImage_mem_lqcohFbc f n F⟩ := rfl

/-- The higher-image comparison is the zero morphism in negative degrees. -/
theorem higherDirectImageCounitEval_negSucc {V : Over S} (y : Y.p.Fiber V)
    (F : QCoh X) (n : ℕ) :
    higherDirectImageCounitEval f y F (Int.negSucc n) = 0 := rfl

/-- Quasi-coherent and restricted fppf higher direct images have isomorphic values at flat objects
in every integer degree. -/
instance higherDirectImageCounitEval_isIso {V : Over S} (y : Y.p.Fiber V)
    [AlgebraicStack.Flat (YonedaSlice.representative y)] (F : QCoh X) (i : ℤ) :
    IsIso (higherDirectImageCounitEval f y F i) := sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
