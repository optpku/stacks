module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Tensor

/-! # Invertibility of the derived pullback tensor comparison -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.DerivedCategory CategoryTheory.Functor ComplexShape

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

namespace CellTensorPullback

/-- Ordinary pullback preserves the cell augmentation at the tensor of two cell replacements. -/
theorem tensorPullbackAugmentation_quasiIso (f : X ⟶ Y)
    (K L : _root_.CochainComplex Y.Modules ℤ) :
    QuasiIso (((Modules.pullback f).mapHomologicalComplex (up ℤ)).map
      ((Modules.CellTensor.augmentation Y).app
        ((Modules.CellTensor.replacement Y).obj K ⊗
          (Modules.CellTensor.replacement Y).obj L))) := sorry

set_option backward.privateInPublic true in
private def cochainTensorIso (f : X ⟶ Y)
    (K L : _root_.CochainComplex Y.Modules ℤ) :
    ((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj (K ⊗ L) ≅
      ((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj K ⊗
        ((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj L :=
  (@asIso _ _ _ _
    (HomologicalComplex₂.Total.Map.Comparison.hom (Modules.pullback f)
      (Functor.Cochain.tensorBicomplex K L) (up ℤ))
    (isIso_modulesPullback_totalComparison f K L)).symm ≪≫
    HomologicalComplex₂.total.mapIso
      (HomologicalComplex.Hom.isoOfComponents
        (C₁ := Functor.Cochain.mappedTensorBicomplex (Modules.pullback f) K L)
        (C₂ := Functor.Cochain.tensorBicomplexMap (Modules.pullback f) K L)
        (fun p ↦ HomologicalComplex.Hom.isoOfComponents
          (fun q ↦ Modules.PullbackTensor.tensorIso f (K.X p) (L.X q))
          (modulesPullback_tensorBicomplex_comm₂ f K L p))
        (by
          intro p p' h
          ext q : 1
          exact modulesPullback_tensorBicomplex_comm₁ f K L p p' q h)) (up ℤ)

set_option backward.privateInPublic true in
private def tensorThenPullbackComputation (f : X ⟶ Y)
    (K L : _root_.CochainComplex Y.Modules ℤ) :
    (moduleDerivedTensorThenPullback f).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≅
      (cochain f).obj (K, L) :=
  (LeftDerived.Homotopy.functor (Modules.pullback f)).mapIso
      (Modules.CellTensor.computationIso Y K L) ≪≫
    pullbackComputation f
      ((Modules.CellTensor.replacement Y).obj K ⊗ (Modules.CellTensor.replacement Y).obj L) ≪≫
    Localization.isoOfHom DerivedCategory.Q (HomologicalComplex.quasiIso X.Modules (up ℤ))
      (((Modules.pullback f).mapHomologicalComplex (up ℤ)).map
        ((Modules.CellTensor.augmentation Y).app
          ((Modules.CellTensor.replacement Y).obj K ⊗ (Modules.CellTensor.replacement Y).obj L)))
      (tensorPullbackAugmentation_quasiIso f K L) ≪≫
    DerivedCategory.Q.mapIso (cochainTensorIso f
      ((Modules.CellTensor.replacement Y).obj K) ((Modules.CellTensor.replacement Y).obj L))

set_option backward.privateInPublic true in
private def reverseOnInput (f : X ⟶ Y)
    (K L : _root_.CochainComplex Y.Modules ℤ) :
    (moduleDerivedPullbackThenTensor f).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ⟶
      (moduleDerivedTensorThenPullback f).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :=
  (computationOnInput f (model_laws f).2.2.1 (K, L)).hom ≫
    (tensorThenPullbackComputation f K L).inv

set_option backward.privateInPublic true in
private def reverseComparison (f : X ⟶ Y) (A B : ModuleDerived Y) :
    (moduleDerivedPullbackThenTensor f).obj (A, B) ⟶
      (moduleDerivedTensorThenPullback f).obj (A, B) :=
  (moduleDerivedPullbackThenTensor f).map
      ((DerivedCategory.Q.objObjPreimageIso A).prod
        (DerivedCategory.Q.objObjPreimageIso B)).inv ≫
    reverseOnInput f (DerivedCategory.Q.objPreimage A) (DerivedCategory.Q.objPreimage B) ≫
    (moduleDerivedTensorThenPullback f).map
      ((DerivedCategory.Q.objObjPreimageIso A).prod
        (DerivedCategory.Q.objObjPreimageIso B)).hom

end CellTensorPullback

set_option backward.privateInPublic true in
/-- The reverse fixed-right tensor comparison is computed by cell replacement and localization. -/
def rightTensorComparisonInv (f : X ⟶ Y) (A B : ModuleDerived Y) :
    (DerivedTensor.Right.functor ((LeftDerived.Homotopy.functor (Modules.pullback f)).obj B)).obj
        ((LeftDerived.Homotopy.functor (Modules.pullback f)).obj A) ⟶
      (LeftDerived.Homotopy.functor (Modules.pullback f)).obj ((DerivedTensor.Right.functor B).obj A) :=
  (DerivedTensor.Bifunctor.Right.isoAppOf
      ((LeftDerived.Homotopy.functor (Modules.pullback f)).obj B)
      (Modules.hasDerivedTensorRightCompatible X _)
      ((LeftDerived.Homotopy.functor (Modules.pullback f)).obj A)).hom ≫
    CellTensorPullback.reverseComparison f A B ≫
      (LeftDerived.Homotopy.functor (Modules.pullback f)).map
        (DerivedTensor.Bifunctor.Right.isoAppOf B
          (Modules.hasDerivedTensorRightCompatible Y B) A).inv

/-- The tensor comparison followed by its cell-computed reverse is the identity. -/
theorem rightTensorComparison_hom_inv_id (f : X ⟶ Y) (A B : ModuleDerived Y) :
    rightTensorComparison f A B ≫ rightTensorComparisonInv f A B = 𝟙 _ := sorry

/-- The cell-computed reverse followed by the tensor comparison is the identity. -/
theorem rightTensorComparison_inv_hom_id (f : X ⟶ Y) (A B : ModuleDerived Y) :
    rightTensorComparisonInv f A B ≫ rightTensorComparison f A B = 𝟙 _ := sorry

/-- Derived module pullback commutes with the canonical fixed-right derived tensor. -/
def rightTensorComparisonIso (f : X ⟶ Y) (A B : ModuleDerived Y) :
    (LeftDerived.Homotopy.functor (Modules.pullback f)).obj ((DerivedTensor.Right.functor B).obj A) ≅
      (DerivedTensor.Right.functor ((LeftDerived.Homotopy.functor (Modules.pullback f)).obj B)).obj
        ((LeftDerived.Homotopy.functor (Modules.pullback f)).obj A) where
  hom := rightTensorComparison f A B
  inv := rightTensorComparisonInv f A B
  hom_inv_id := rightTensorComparison_hom_inv_id f A B
  inv_hom_id := rightTensorComparison_inv_hom_id f A B


end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
