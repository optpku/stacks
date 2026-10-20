/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.Deformation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CellReplacement.Functorial
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectTensorComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Bifunctor

/-! # Cell models for derived tensor products of étale modules -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.DerivedCategory CategoryTheory.Functor ComplexShape

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- Module sheaves inherit the symmetry of their commutative structure-ring presentation. -/
@[instance_reducible]
instance modulesSymmetricCategory (X : AlgebraicSpace S) : SymmetricCategory X.Modules :=
  DirectTensorComparison.symmetric X

/-- Native module-sheaf coproducts form the tensor product of graded objects. -/
instance modulesHasGradedTensor (X : AlgebraicSpace S)
    (G₁ G₂ : GradedObject ℤ X.Modules) : GradedObject.HasTensor G₁ G₂ := by
  intro n
  infer_instance

/-- Triple graded tensors commute with the inner coproduct in the first two factors. -/
instance modulesHasGoodTensor₁₂ (X : AlgebraicSpace S)
    (G₁ G₂ G₃ : GradedObject ℤ X.Modules) :
    GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃ := sorry

/-- Triple graded tensors commute with the inner coproduct in the last two factors. -/
instance modulesHasGoodTensor₂₃ (X : AlgebraicSpace S)
    (G₁ G₂ G₃ : GradedObject ℤ X.Modules) :
    GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃ := sorry

/-- Fourfold graded tensor products satisfy the tensor extension condition. -/
instance modulesHasTensor₄ (X : AlgebraicSpace S)
    (G₁ G₂ G₃ G₄ : GradedObject ℤ X.Modules) :
    GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄ := sorry

namespace CellTensor

variable (X : AlgebraicSpace S)

/-- The actual functorial cell replacement of a complex of module sheaves. -/
abbrev replacement := SheafOfModules.CellReplacement.functor (R := structureSheaf X)

/-- The specified augmentation from the cell complex to the original complex. -/
abbrev augmentation := SheafOfModules.CellReplacement.augmentationNatTrans (R := structureSheaf X)

/-- Ordinary tensor followed by localization in the derived category. -/
abbrev ordinary : CochainComplex X.Modules ℤ × CochainComplex X.Modules ℤ ⥤ ModuleDerived X :=
  tensor (CochainComplex X.Modules ℤ) ⋙ DerivedCategory.Q

/-- Replace both complexes, form their actual total tensor, and localize. -/
def cochain : CochainComplex X.Modules ℤ × CochainComplex X.Modules ℤ ⥤ ModuleDerived X :=
  (replacement X).prod (replacement X) ⋙ ordinary X

/-- Replace the variable complex while retaining the chosen representative of the right factor. -/
def rightCochain (E : ModuleDerived X) : CochainComplex X.Modules ℤ ⥤ ModuleDerived X :=
  replacement X ⋙ tensorRight (DerivedCategory.Q.objPreimage E) ⋙ DerivedCategory.Q

/-- The product quasi-isomorphism property on original complexes. -/
abbrev denominators :=
  (HomologicalComplex.quasiIso X.Modules (up ℤ)).prod
    (HomologicalComplex.quasiIso X.Modules (up ℤ))

/-- The product homotopy quotient of the two actual complexes. -/
abbrev quotient :=
  (HomotopyCategory.quotient X.Modules (up ℤ)).prod
    (HomotopyCategory.quotient X.Modules (up ℤ))

/-- The pair of actual cell augmentations. -/
def pairAugmentation :
    (replacement X).prod (replacement X) ⟶
      𝟭 (CochainComplex X.Modules ℤ × CochainComplex X.Modules ℤ) :=
  (augmentation X).prod (augmentation X)

/-- Quotienting both inputs and then localizing agrees with localizing them directly. -/
def localizationIso : quotient X ⋙ DerivedTensor.Bifunctor.localization ≅
    (DerivedCategory.Q (C := X.Modules)).prod DerivedCategory.Q :=
  NatIso.ofComponents
    (fun A ↦ ((DerivedCategory.quotientCompQhIso X.Modules).app A.1).prod
      ((DerivedCategory.quotientCompQhIso X.Modules).app A.2))
    (fun a ↦ by
      ext
      · exact (DerivedCategory.quotientCompQhIso X.Modules).hom.naturality a.1
      · exact (DerivedCategory.quotientCompQhIso X.Modules).hom.naturality a.2)

/-- The ordinary fixed-right source on a complex is its tensor with the specified representative. -/
def rightOrdinaryComponent (E : ModuleDerived X) (A : CochainComplex X.Modules ℤ) :
    (DerivedTensor.Right.sourceFunctor E).obj
        ((HomotopyCategory.quotient X.Modules (up ℤ)).obj A) ≅
      DerivedCategory.Q.obj (A ⊗ DerivedCategory.Q.objPreimage E) :=
  ((DerivedTensor.Right.sourceFunctorIso E).app
    ((HomotopyCategory.quotient X.Modules (up ℤ)).obj A)).symm ≪≫
  (DerivedCategory.Qh (C := X.Modules)).mapIso
    (Functor.Monoidal.μIso (HomotopyCategory.quotient X.Modules (up ℤ)) A
      (DerivedCategory.Q.objPreimage E)) ≪≫
  (DerivedCategory.quotientCompQhIso X.Modules).app
    (A ⊗ DerivedCategory.Q.objPreimage E)

/-- Cell tensor functors invert quasi-isomorphisms. The ordinary tensor source sends the
augmentation on already replaced inputs to an isomorphism, in both the product and fixed-right
models. These statements concern actual cell maps and never an unresolved variable factor. -/
theorem model_laws :
    (denominators X).IsInvertedBy (cochain X) ∧
    (∀ A, IsIso (((quotient X ⋙ DerivedTensor.Bifunctor.sourceFunctor).map
      ((pairAugmentation X).app
        (((replacement X).prod (replacement X)).obj A))))) ∧
    (∀ E : ModuleDerived X,
      (HomologicalComplex.quasiIso X.Modules (up ℤ)).IsInvertedBy (rightCochain X E)) ∧
    (∀ (E : ModuleDerived X) (A : CochainComplex X.Modules ℤ),
      IsIso ((((HomotopyCategory.quotient X.Modules (up ℤ)) ⋙
        DerivedTensor.Right.sourceFunctor E).map
        ((augmentation X).app ((replacement X).obj A))))) ∧
    (∀ {A B : CochainComplex X.Modules ℤ × CochainComplex X.Modules ℤ} (a : A ⟶ B),
      (quotient X ⋙ DerivedTensor.Bifunctor.sourceFunctor).map a ≫
          (DerivedTensor.Bifunctor.sourceFunctorObjIso B.1 B.2).hom =
        (DerivedTensor.Bifunctor.sourceFunctorObjIso A.1 A.2).hom ≫ (ordinary X).map a) ∧
    (∀ (E : ModuleDerived X) {A B : CochainComplex X.Modules ℤ} (a : A ⟶ B),
      ((HomotopyCategory.quotient X.Modules (up ℤ)) ⋙
        DerivedTensor.Right.sourceFunctor E).map a ≫ (rightOrdinaryComponent X E B).hom =
      (rightOrdinaryComponent X E A).hom ≫
        (tensorRight (DerivedCategory.Q.objPreimage E) ⋙ DerivedCategory.Q).map a) := sorry

/-- The homotopy tensor source on complexes is their ordinary totalized tensor. -/
def ordinaryIso : quotient X ⋙ DerivedTensor.Bifunctor.sourceFunctor ≅ ordinary X :=
  NatIso.ofComponents (fun A ↦ DerivedTensor.Bifunctor.sourceFunctorObjIso A.1 A.2)
    (fun a ↦ (model_laws X).2.2.2.2.1 a)

/-- Native product localization of the actual cell-tensor functor. -/
def derived : ModuleDerived X × ModuleDerived X ⥤ ModuleDerived X :=
  Localization.lift (cochain X) (model_laws X).1
    ((DerivedCategory.Q (C := X.Modules)).prod DerivedCategory.Q)

/-- The native localization computation of tensor on the displayed cell complexes. -/
def fac : (DerivedCategory.Q (C := X.Modules)).prod DerivedCategory.Q ⋙ derived X ≅ cochain X :=
  Localization.fac (cochain X) (model_laws X).1
    ((DerivedCategory.Q (C := X.Modules)).prod DerivedCategory.Q)

/-- The homotopy-presented product localization inverts exactly the product denominators. -/
instance inputLocalization :
    (quotient X ⋙ DerivedTensor.Bifunctor.localization).IsLocalization (denominators X) :=
  Functor.IsLocalization.of_iso (denominators X) (localizationIso X).symm

/-- The product computation transported to the homotopy tensor source. -/
def modelComputation :
    (quotient X ⋙ DerivedTensor.Bifunctor.localization) ⋙ derived X ≅
      (replacement X).prod (replacement X) ⋙
        (quotient X ⋙ DerivedTensor.Bifunctor.sourceFunctor) :=
  isoWhiskerRight (localizationIso X) (derived X) ≪≫ fac X ≪≫
    isoWhiskerLeft ((replacement X).prod (replacement X)) (ordinaryIso X).symm

private theorem pairAugmentation_mem (A) :
    denominators X ((pairAugmentation X).app A) :=
  ⟨SheafOfModules.CellReplacement.augmentation_quasiIso A.1,
    SheafOfModules.CellReplacement.augmentation_quasiIso A.2⟩

/-- The homotopy tensor model has the specified cochain extension maps as its universal maps. -/
def model : DerivedTensor.Bifunctor.Model (C := X.Modules) :=
  LeftDerived.Deformation.modelOnLocalizedSource
    (quotient X)
    ((HomologicalComplex.homotopyEquivalences X.Modules (up ℤ)).prod
      (HomologicalComplex.homotopyEquivalences X.Modules (up ℤ)))
    DerivedTensor.Bifunctor.localization DerivedTensor.Bifunctor.qis (denominators X)
    ((replacement X).prod (replacement X)) (pairAugmentation X)
    (by exact pairAugmentation_mem X)
    DerivedTensor.Bifunctor.sourceFunctor (derived X) (modelComputation X)
    (model_laws X).2.1

/-- The ordinary fixed-right source comparison retains its actual tensor components. -/
def rightOrdinaryIso (E : ModuleDerived X) :
    HomotopyCategory.quotient X.Modules (up ℤ) ⋙ DerivedTensor.Right.sourceFunctor E ≅
      tensorRight (DerivedCategory.Q.objPreimage E) ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (rightOrdinaryComponent X E)
    (fun a ↦ (model_laws X).2.2.2.2.2 E a)

/-- Native localization of the tensor with a fixed right representative and a replaced variable. -/
def rightDerived (E : ModuleDerived X) : ModuleDerived X ⥤ ModuleDerived X :=
  Localization.lift (rightCochain X E) ((model_laws X).2.2.1 E) DerivedCategory.Q

/-- The localization computation retains the specified fixed right representative. -/
def rightFac (E : ModuleDerived X) :
    DerivedCategory.Q ⋙ rightDerived X E ≅ rightCochain X E :=
  Localization.fac (rightCochain X E) ((model_laws X).2.2.1 E) DerivedCategory.Q

/-- The homotopy-presented unary localization has the usual cochain denominators. -/
instance rightInputLocalization :
    (HomotopyCategory.quotient X.Modules (up ℤ) ⋙ DerivedCategory.Qh).IsLocalization
      (HomologicalComplex.quasiIso X.Modules (up ℤ)) :=
  Functor.IsLocalization.of_iso _ (DerivedCategory.quotientCompQhIso X.Modules).symm

/-- The fixed-right cell computation transported to the ordinary homotopy source. -/
def rightModelComputation (E : ModuleDerived X) :
    (HomotopyCategory.quotient X.Modules (up ℤ) ⋙ DerivedCategory.Qh) ⋙
        rightDerived X E ≅
      replacement X ⋙ (HomotopyCategory.quotient X.Modules (up ℤ) ⋙
        DerivedTensor.Right.sourceFunctor E) :=
  isoWhiskerRight (DerivedCategory.quotientCompQhIso X.Modules) (rightDerived X E) ≪≫
    rightFac X E ≪≫ isoWhiskerLeft (replacement X) (rightOrdinaryIso X E).symm

/-- The fixed-right model resolves only the variable complex and carries actual extension maps. -/
def rightModel (E : ModuleDerived X) : DerivedTensor.Right.Model E :=
  LeftDerived.Deformation.modelOnLocalizedSource
    (HomotopyCategory.quotient X.Modules (up ℤ))
    (HomologicalComplex.homotopyEquivalences X.Modules (up ℤ))
    DerivedCategory.Qh (HomotopyCategory.quasiIso X.Modules (up ℤ))
    (HomologicalComplex.quasiIso X.Modules (up ℤ))
    (replacement X) (augmentation X)
    (fun A ↦ SheafOfModules.CellReplacement.augmentation_quasiIso A)
    (DerivedTensor.Right.sourceFunctor E) (rightDerived X E) (rightModelComputation X E)
    ((model_laws X).2.2.2.1 E)

end CellTensor

/-- The constructed cell tensor model supplies two-variable unbounded derived tensor. -/
instance hasDerivedTensorBifunctor (X : AlgebraicSpace S) :
    DerivedTensor.Bifunctor.Has (C := X.Modules) :=
  @Functor.HasLeftDerivedFunctor.mk' _ _ _ _ _ _
    (CellTensor.derived X) _ _ (CellTensor.model X).counit _ _
    (CellTensor.model X).isLeftDerived

namespace CellTensor

variable (X : AlgebraicSpace S)

/-- The canonical two-variable tensor is computed on the displayed pair of cell replacements. -/
def computationIso (K L : CochainComplex X.Modules ℤ) :
    (DerivedTensor.Bifunctor.functor (C := X.Modules)).obj
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj ((replacement X).obj K ⊗ (replacement X).obj L) :=
  ((DerivedTensor.Bifunctor.Right.canonicalModel (C := X.Modules)).iso (model X)).app
      (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≪≫ (fac X).app (K, L)

/-- The specified right-factor augmentation is tensored with an already replaced variable. -/
def rightAugmentation (E : ModuleDerived X) (A : CochainComplex X.Modules ℤ) :
    (replacement X).obj A ⊗ (replacement X).obj (DerivedCategory.Q.objPreimage E) ⟶
      (replacement X).obj A ⊗ DerivedCategory.Q.objPreimage E :=
  𝟙 ((replacement X).obj A) ⊗ₘ (augmentation X).app (DerivedCategory.Q.objPreimage E)

/-- Compare the two cell computations using formal localization of the specified augmentation. -/
def rightComparisonOnInput (E : ModuleDerived X)
    (h : ∀ A, QuasiIso (rightAugmentation X E A)) (A : CochainComplex X.Modules ℤ) :
    (DerivedTensor.Bifunctor.rightFunctor E).obj (DerivedCategory.Q.obj A) ≅
      (rightModel X E).functor.obj (DerivedCategory.Q.obj A) :=
  (DerivedTensor.Bifunctor.functor (C := X.Modules)).mapIso
      ((Iso.refl (DerivedCategory.Q.obj A)).prod
        (DerivedCategory.Q.objObjPreimageIso E).symm) ≪≫
    computationIso X A (DerivedCategory.Q.objPreimage E) ≪≫
    Localization.isoOfHom DerivedCategory.Q (HomologicalComplex.quasiIso X.Modules (up ℤ))
      (rightAugmentation X E A) (h A) ≪≫ ((rightFac X E).app A).symm

/-- Naturality of the specified fixed-right comparison on original complex maps. -/
abbrev RightComparisonNatural (E : ModuleDerived X)
    (h : ∀ A, QuasiIso (rightAugmentation X E A)) : Prop :=
  ∀ {A B : CochainComplex X.Modules ℤ} (a : A ⟶ B),
    (DerivedCategory.Q ⋙ DerivedTensor.Bifunctor.rightFunctor E).map a ≫
        (rightComparisonOnInput X E h B).hom =
      (rightComparisonOnInput X E h A).hom ≫
        (DerivedCategory.Q ⋙ (rightModel X E).functor).map a

/-- Both directions of the fixed-right cell comparison descend along cochain localization. -/
def rightComparisonUsing (E : ModuleDerived X)
    (h : ∀ A, QuasiIso (rightAugmentation X E A)) (hn : RightComparisonNatural X E h) :
    DerivedTensor.Bifunctor.rightFunctor E ≅ (rightModel X E).functor :=
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso X.Modules (up ℤ))
    (DerivedCategory.Q ⋙ DerivedTensor.Bifunctor.rightFunctor E)
    (DerivedCategory.Q ⋙ (rightModel X E).functor)
    (DerivedTensor.Bifunctor.rightFunctor E) (rightModel X E).functor
    (NatIso.ofComponents (rightComparisonOnInput X E h) (fun a ↦ hn a))

/-- The specified right augmentation is a quasi-isomorphism with a replaced variable, and its
localized comparison is natural and intertwines the two fixed-right counits. -/
theorem comparison_laws (E : ModuleDerived X) :
    (∀ A, QuasiIso (rightAugmentation X E A)) ∧
    (∀ h : ∀ A, QuasiIso (rightAugmentation X E A), RightComparisonNatural X E h) ∧
    (∀ (h : ∀ A, QuasiIso (rightAugmentation X E A)) (hn : RightComparisonNatural X E h),
      Functor.whiskerLeft DerivedCategory.Qh (rightComparisonUsing X E h hn).hom ≫
        (rightModel X E).counit = DerivedTensor.Bifunctor.Right.counitOf E) := sorry

/-- The augmentation-based fixed-right comparison, with its specified formal inverse. -/
def rightComparison (E : ModuleDerived X) :
    DerivedTensor.Bifunctor.rightFunctor E ≅ (rightModel X E).functor :=
  rightComparisonUsing X E (comparison_laws X E).1
    ((comparison_laws X E).2.1 (comparison_laws X E).1)

end CellTensor

/-- The two-variable tensor with one factor fixed is left derived through the specified counit. -/
instance hasDerivedTensorRightCompatible (X : AlgebraicSpace S) (E : ModuleDerived X) :
    DerivedTensor.Bifunctor.Right.Compatible E :=
  (Functor.isLeftDerivedFunctor_iff_of_iso
    (LF := DerivedTensor.Bifunctor.rightFunctor E)
    (LF' := (CellTensor.rightModel X E).functor)
    (α := DerivedTensor.Bifunctor.Right.counitOf E) (CellTensor.rightModel X E).counit
    (DerivedTensor.Right.qis (C := X.Modules)) (CellTensor.rightComparison X E)
    ((CellTensor.comparison_laws X E).2.2 (CellTensor.comparison_laws X E).1
      ((CellTensor.comparison_laws X E).2.1 (CellTensor.comparison_laws X E).1))).mpr (CellTensor.rightModel X E).isLeftDerived

end AlgebraicGeometry.AlgebraicSpace.Modules
