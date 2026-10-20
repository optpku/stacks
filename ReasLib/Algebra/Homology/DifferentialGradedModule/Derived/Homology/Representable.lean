/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Regular
public import ReasLib.CategoryTheory.Shift.ShiftedHom.ModuleCat

/-!
# Homology represented by the regular derived module

For a cochain DG algebra `A`, degree-`n` homology on `D(A)` is represented by the regular
derived module with the target shifted by `n`.  Since morphisms in `D(A)` live in a larger
universe than the homology modules, the functorial statement uses `ModuleCat.uliftFunctor`.
The pointwise API removes that implementation detail by returning a cross-universe linear
equivalence.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedModule.Derived.Homology

variable {R : Type u} [CommRing R]

/-- Degree-`n` derived homology, lifted to the universe of morphisms in the derived category. -/
@[stacks 09K1 "universe-lifted derived homology functor"]
def uliftFunctor (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    Derived.Category.{u, v} A ⥤ ModuleCat.{max u (v + 1)} R :=
  Derived.homologyFunctor A n ⋙
    ModuleCat.uliftFunctor.{max u (v + 1)} R

/-- Shifted morphisms out of the regular derived module, functorial in the target. -/
@[stacks 09K1 "shifted-Hom representation functor"]
def representedFunctor (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    Derived.Category.{u, v} A ⥤ ModuleCat.{max u (v + 1)} R :=
  CategoryTheory.ShiftedHom.targetFunctor R (Derived.regularObject A) n

/-- The homotopy-category model of lifted degree-`n` homology. -/
@[stacks 09K1 "homotopy model of lifted derived homology"]
def modelFunctor (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    K R (DifferentialGradedModule.{u, v} A) ⥤ ModuleCat.{max u (v + 1)} R :=
  DifferentialGradedModule.Homotopy.homologyFunctor A n ⋙
    ModuleCat.uliftFunctor.{max u (v + 1)} R

/-- Universe-lifted derived homology is additive. -/
@[stacks 09K1 "additivity of universe-lifted derived homology"]
noncomputable instance uliftFunctorAdditive
    (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    (uliftFunctor A n).Additive := sorry

/-- Universe-lifted derived homology is `R`-linear. -/
@[stacks 09K1 "linearity of universe-lifted derived homology"]
noncomputable instance uliftFunctorLinear
    (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    Functor.Linear R (uliftFunctor A n) := sorry

/-- The shifted-Hom representation of derived homology is additive in its target. -/
noncomputable instance representedFunctorAdditive
    (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    (representedFunctor A n).Additive := sorry

/-- The shifted-Hom representation of derived homology is `R`-linear in its target. -/
noncomputable instance representedFunctorLinear
    (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    Functor.Linear R (representedFunctor A n) := sorry

/-- The homotopy-category model of lifted homology is additive. -/
noncomputable instance modelFunctorAdditive
    (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    (modelFunctor A n).Additive := sorry

/-- The homotopy-category model of lifted homology is `R`-linear. -/
noncomputable instance modelFunctorLinear
    (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    Functor.Linear R (modelFunctor A n) := sorry

/-- Reindex homology along the canonical equality `n = -(-n)`. -/
@[stacks 09K1 "double-negation reindexing for homology"]
def negNegIso {A : CochainDGAlgebra.{u, v} R}
    (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    M.homology n ≅ M.homology (- -n) :=
  eqToIso (congrArg (fun k : ℤ ↦ M.homology k) (Int.neg_neg n).symm)

/-- The canonical model-level map from lifted homology to shifted derived morphisms out of
the regular object. -/
@[stacks 09K1 "model homology-to-shifted-Hom map"]
noncomputable def modelLinearMap (A : CochainDGAlgebra.{u, v} R) (n : ℤ)
    (X : K R (DifferentialGradedModule.{u, v} A)) :
    (modelFunctor A n).obj X →ₗ[R]
      ((Derived.Q A ⋙ representedFunctor A n).obj X) where
  toFun x :=
    (ShiftedHom.sourceShiftLinearEquiv R
      (Derived.regularObject A) ((Derived.Q A).obj X) n).symm
      ((Derived.regularShiftIso A (-n)).hom ≫
        (Derived.Q A).map
          ((CochainDGAlgebra.RegularModule.homotopyLinearEquivHomology
              A X.obj (-n)).symm
            (ModuleCat.Hom.hom (negNegIso X.obj n).hom
              (ModuleCat.Hom.hom
                ((HomotopyCategory.homologyFunctorFactors
                    (ModuleCat.{v} R) (ComplexShape.up ℤ) n).hom.app
                      X.obj.toCochainComplex)
                x.down))))
  map_add' := sorry
  map_smul' := sorry

/-- The homology class of the shifted unit, regarded in the homotopy-category homology
functor. -/
@[stacks 09K1 "shifted regular unit in homotopy homology"]
noncomputable def shiftedRegularUnit (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    (DifferentialGradedModule.Homotopy.homologyFunctor A n).obj
      (CochainDGAlgebra.RegularModule.shiftK A (-n)) :=
  ModuleCat.Hom.hom
    ((HomotopyCategory.homologyFunctorFactors
      (ModuleCat.{v} R) (ComplexShape.up ℤ) n).inv.app
        (A.regularModule[(-n)]).toCochainComplex)
    (ModuleCat.Hom.hom (negNegIso (A.regularModule[(-n)]) n).inv
      (CochainDGAlgebra.RegularModule.homologyEvaluation A
        (A.regularModule[(-n)]) (-n) (𝟙 _)))

/-- The shifted unit after passage to derived homology. -/
@[stacks 09K1 "shifted regular unit in derived homology"]
noncomputable def derivedShiftedRegularUnit (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    (Derived.homologyFunctor A n).obj
      ((Derived.Q A).obj (CochainDGAlgebra.RegularModule.shiftK A (-n))) :=
  ModuleCat.Hom.hom
    ((Derived.homologyFunctorFactors A n).inv.app
      (CochainDGAlgebra.RegularModule.shiftK A (-n)))
    (shiftedRegularUnit A n)

/-- The homology factorization sends the derived shifted unit back to the homotopy shifted
unit. -/
@[simp]
theorem derivedShiftedRegularUnit_factors
    (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    ModuleCat.Hom.hom
      ((Derived.homologyFunctorFactors A n).hom.app
        (CochainDGAlgebra.RegularModule.shiftK A (-n)))
      (derivedShiftedRegularUnit A n) = shiftedRegularUnit A n := sorry

/-- Evaluate a shifted derived morphism on the localized shifted unit.  This is the explicit
inverse of `modelLinearMap`; it does not choose a preimage of a localization morphism. -/
@[stacks 09K1 "model shifted-Hom evaluation map"]
noncomputable def modelInverseLinearMap (A : CochainDGAlgebra.{u, v} R) (n : ℤ)
    (X : K R (DifferentialGradedModule.{u, v} A)) :
    ((Derived.Q A ⋙ representedFunctor A n).obj X) →ₗ[R]
      (modelFunctor A n).obj X where
  toFun f :=
    ULift.up (ModuleCat.Hom.hom
      ((Derived.homologyFunctorFactors A n).hom.app X)
      (ModuleCat.Hom.hom
        ((Derived.homologyFunctor A n).map
          ((Derived.regularShiftIso A (-n)).inv ≫
            ShiftedHom.sourceShiftLinearEquiv R
              (Derived.regularObject A) ((Derived.Q A).obj X) n f))
        (derivedShiftedRegularUnit A n)))
  map_add' := sorry
  map_smul' := sorry

/-- Evaluating `modelInverseLinearMap` applies derived homology to the source-shifted morphism
and then evaluates it on the localized shifted unit. -/
@[simp]
theorem modelInverseLinearMap_apply (A : CochainDGAlgebra.{u, v} R) (n : ℤ)
    (X : K R (DifferentialGradedModule.{u, v} A))
    (f : (Derived.Q A ⋙ representedFunctor A n).obj X) :
    modelInverseLinearMap A n X f =
      ULift.up (ModuleCat.Hom.hom
        ((Derived.homologyFunctorFactors A n).hom.app X)
        (ModuleCat.Hom.hom
          ((Derived.homologyFunctor A n).map
            ((Derived.regularShiftIso A (-n)).inv ≫
              ShiftedHom.sourceShiftLinearEquiv R
                (Derived.regularObject A) ((Derived.Q A).obj X) n f))
          (derivedShiftedRegularUnit A n))) := sorry

/-- Lifted homology of a homotopy object is linearly equivalent to shifted derived Hom from
the regular object. -/
@[stacks 09K1 "model homology-to-shifted-Hom equivalence"]
noncomputable def modelLinearEquiv (A : CochainDGAlgebra.{u, v} R) (n : ℤ)
    (X : K R (DifferentialGradedModule.{u, v} A)) :
    (modelFunctor A n).obj X ≃ₗ[R]
      ((Derived.Q A ⋙ representedFunctor A n).obj X) where
  toLinearMap := modelLinearMap A n X
  invFun := modelInverseLinearMap A n X
  left_inv := sorry
  right_inv := sorry

/-- Evaluation on the localized shifted unit is a left inverse to the canonical model map. -/
@[simp]
theorem modelInverseLinearMap_modelLinearMap
    (A : CochainDGAlgebra.{u, v} R) (n : ℤ)
    (X : K R (DifferentialGradedModule.{u, v} A))
    (x : (modelFunctor A n).obj X) :
    modelInverseLinearMap A n X (modelLinearMap A n X x) = x := sorry

/-- The canonical model map is a right inverse to evaluation on the localized shifted unit. -/
@[simp]
theorem modelLinearMap_modelInverseLinearMap
    (A : CochainDGAlgebra.{u, v} R) (n : ℤ)
    (X : K R (DifferentialGradedModule.{u, v} A))
    (f : (Derived.Q A ⋙ representedFunctor A n).obj X) :
    modelLinearMap A n X (modelInverseLinearMap A n X f) = f := sorry

/-- The model-level comparison map is bijective. -/
theorem modelLinearMap_bijective (A : CochainDGAlgebra.{u, v} R) (n : ℤ)
    (X : K R (DifferentialGradedModule.{u, v} A)) :
    Function.Bijective (modelLinearMap A n X) := sorry

/-- The forward map of `modelLinearEquiv` is the canonical comparison. -/
@[simp]
theorem modelLinearEquiv_apply (A : CochainDGAlgebra.{u, v} R) (n : ℤ)
    (X : K R (DifferentialGradedModule.{u, v} A))
    (x : (modelFunctor A n).obj X) :
    modelLinearEquiv A n X x = modelLinearMap A n X x := sorry

/-- The inverse of `modelLinearEquiv` is evaluation on the localized shifted unit. -/
@[simp]
theorem modelLinearEquiv_symm_apply (A : CochainDGAlgebra.{u, v} R) (n : ℤ)
    (X : K R (DifferentialGradedModule.{u, v} A))
    (f : (Derived.Q A ⋙ representedFunctor A n).obj X) :
    (modelLinearEquiv A n X).symm f = modelInverseLinearMap A n X f := sorry

/-- The pointwise model comparison as an isomorphism in `ModuleCat R`. -/
@[stacks 09K1 "pointwise model homology comparison"]
def modelApp (A : CochainDGAlgebra.{u, v} R) (n : ℤ)
    (X : K R (DifferentialGradedModule.{u, v} A)) :
    (modelFunctor A n).obj X ≅ ((Derived.Q A ⋙ representedFunctor A n).obj X) :=
  (modelLinearEquiv A n X).toModuleIso

/-- The model comparison is natural in the homotopy object. -/
@[reassoc, stacks 09K1 "naturality of the model homology comparison"]
theorem modelApp_naturality (A : CochainDGAlgebra.{u, v} R) (n : ℤ)
    {X Y : K R (DifferentialGradedModule.{u, v} A)} (f : X ⟶ Y) :
    (modelFunctor A n).map f ≫ (modelApp A n Y).hom =
      (modelApp A n X).hom ≫
        (Derived.Q A ⋙ representedFunctor A n).map f := sorry

/-- Evaluation on the localized shifted unit is natural in the homotopy object. -/
@[stacks 09K1 "naturality of model shifted-Hom evaluation"]
theorem modelInverseLinearMap_naturality
    (A : CochainDGAlgebra.{u, v} R) (n : ℤ)
    {X Y : K R (DifferentialGradedModule.{u, v} A)} (f : X ⟶ Y)
    (g : (Derived.Q A ⋙ representedFunctor A n).obj X) :
    modelInverseLinearMap A n Y
        (ModuleCat.Hom.hom ((Derived.Q A ⋙ representedFunctor A n).map f) g) =
      ModuleCat.Hom.hom ((modelFunctor A n).map f)
        (modelInverseLinearMap A n X g) := sorry

/-- On the homotopy category, lifted homology is naturally represented by the localized
regular object. -/
@[stacks 09K1 "homotopy-level homology representation"]
noncomputable def modelIso (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    modelFunctor A n ≅ Derived.Q A ⋙ representedFunctor A n :=
  NatIso.ofComponents (modelApp A n) (modelApp_naturality A n)

/-- The canonical derived homology functor is a localization lift of its homotopy model. -/
@[stacks 09K1 "derived homology localization factorization"]
noncomputable def sourceFactors (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    Derived.Q A ⋙ uliftFunctor A n ≅ modelFunctor A n :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Derived.homologyFunctorFactors A n)
      (ModuleCat.uliftFunctor.{max u (v + 1)} R)

/-- Lifted derived homology carries its canonical localization lifting structure. -/
@[stacks 09K1 "derived homology localization lifting"]
noncomputable instance sourceLifting (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    Localization.Lifting (Derived.Q A) (DifferentialGradedModule.quasiIso A)
      (modelFunctor A n) (uliftFunctor A n) :=
  ⟨sourceFactors A n⟩

/-- Degree-`n` homology on `D(A)` is naturally represented by shifted Hom from the regular
derived module. -/
@[stacks 09K1 "functorial representability of derived homology"]
noncomputable def representableIso (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    uliftFunctor A n ≅ representedFunctor A n :=
  Localization.liftNatIso (Derived.Q A) (DifferentialGradedModule.quasiIso A)
    (modelFunctor A n) (Derived.Q A ⋙ representedFunctor A n)
    (uliftFunctor A n) (representedFunctor A n) (modelIso A n)

/-- The ordinary degree-`n` homology module is linearly equivalent to shifted Hom from the
regular derived module; unlike the functorial statement, this API hides the universe lift. -/
noncomputable def linearEquiv (A : CochainDGAlgebra.{u, v} R)
    (X : Derived.Category.{u, v} A) (n : ℤ) :
    (Derived.homologyFunctor A n).obj X ≃ₗ[R]
      ShiftedHom (Derived.regularObject A) X n :=
  (ULift.moduleEquiv (R := R)
    (M := (Derived.homologyFunctor A n).obj X)).symm.trans
    ((representableIso A n).app X).toLinearEquiv

/-- The component of `representableIso` recovers the pointwise linear equivalence after the
canonical universe lift. -/
theorem linearEquiv_apply (A : CochainDGAlgebra.{u, v} R)
    (X : Derived.Category.{u, v} A) (n : ℤ)
    (x : (Derived.homologyFunctor A n).obj X) :
    linearEquiv A X n x =
      ModuleCat.Hom.hom ((representableIso A n).hom.app X) (ULift.up x) := sorry

variable (A : CochainDGAlgebra.{u, v} R)

#synth (uliftFunctor A 0).Additive
#synth Functor.Linear R (uliftFunctor A 0)
#synth (representedFunctor A 0).Additive
#synth Functor.Linear R (representedFunctor A 0)
#synth (modelFunctor A 0).Additive
#synth Functor.Linear R (modelFunctor A 0)

end DifferentialGradedModule.Derived.Homology
