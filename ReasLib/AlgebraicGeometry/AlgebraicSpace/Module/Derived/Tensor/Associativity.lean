/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor.Bifunctor

/-! # Associativity of derived tensor products of étale modules -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.DerivedCategory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Modules.CellTensor

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- Tensoring the cell augmentation of a tensor of two cell replacements with a third
cell replacement is a quasi-isomorphism, on either side. -/
theorem assocAugmentations_quasiIso (A B C : CochainComplex X.Modules ℤ) :
    QuasiIso (((augmentation X).app ((replacement X).obj A ⊗ (replacement X).obj B)) ⊗ₘ
      𝟙 ((replacement X).obj C)) ∧
    QuasiIso (𝟙 ((replacement X).obj A) ⊗ₘ
      ((augmentation X).app ((replacement X).obj B ⊗ (replacement X).obj C))) :=
  sorry

end Modules.CellTensor

namespace ModuleDerived

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Associativity of tensor products of derived modules is computed by cell replacements,
their augmentation maps, and the ordinary associator of complexes. -/
def derivedTensorAssocComponent (E : ModuleDerived X)
    (G : CochainComplex X.Modules ℤ) (L : ModuleDerived X) :
    (DerivedTensor.Bifunctor.leftFunctor
      (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))).obj L ≅
    (DerivedTensor.Bifunctor.leftFunctor (DerivedCategory.Q.obj G) ⋙
      DerivedTensor.Bifunctor.leftFunctor E).obj L :=
  let A : CochainComplex X.Modules ℤ := DerivedCategory.Q.objPreimage E
  let C : CochainComplex X.Modules ℤ := DerivedCategory.Q.objPreimage L
  let leftComparison :=
    (DerivedTensor.Bifunctor.functor (C := X.Modules)).mapIso
          ((Modules.CellTensor.computationIso X A G).prod
            (Iso.refl (DerivedCategory.Q.obj C))) ≪≫
        Modules.CellTensor.computationIso X
          ((Modules.CellTensor.replacement X).obj A ⊗
            (Modules.CellTensor.replacement X).obj G) C ≪≫
        Localization.isoOfHom DerivedCategory.Q (HomologicalComplex.quasiIso X.Modules (up ℤ))
          (((Modules.CellTensor.augmentation X).app
            ((Modules.CellTensor.replacement X).obj A ⊗
              (Modules.CellTensor.replacement X).obj G)) ⊗ₘ
            𝟙 ((Modules.CellTensor.replacement X).obj C))
          (Modules.CellTensor.assocAugmentations_quasiIso X A G C).1
  let rightComparison :=
    (DerivedTensor.Bifunctor.functor (C := X.Modules)).mapIso
          ((Iso.refl (DerivedCategory.Q.obj A)).prod
            (Modules.CellTensor.computationIso X G C)) ≪≫
        Modules.CellTensor.computationIso X A
          ((Modules.CellTensor.replacement X).obj G ⊗
            (Modules.CellTensor.replacement X).obj C) ≪≫
        Localization.isoOfHom DerivedCategory.Q (HomologicalComplex.quasiIso X.Modules (up ℤ))
          (𝟙 ((Modules.CellTensor.replacement X).obj A) ⊗ₘ
            ((Modules.CellTensor.augmentation X).app
              ((Modules.CellTensor.replacement X).obj G ⊗
                (Modules.CellTensor.replacement X).obj C)))
          (Modules.CellTensor.assocAugmentations_quasiIso X A G C).2
  (DerivedTensor.Bifunctor.functor (C := X.Modules)).mapIso
      (((DerivedTensor.Bifunctor.Right.isoApp (DerivedCategory.Q.obj G) E) ≪≫
        (DerivedTensor.Bifunctor.functor (C := X.Modules)).mapIso
          ((DerivedCategory.Q.objObjPreimageIso E).symm.prod
            (Iso.refl (DerivedCategory.Q.obj G)))).prod
        (DerivedCategory.Q.objObjPreimageIso L).symm) ≪≫
    leftComparison ≪≫
    DerivedCategory.Q.mapIso
      (α_ ((Modules.CellTensor.replacement X).obj (DerivedCategory.Q.objPreimage E))
        ((Modules.CellTensor.replacement X).obj G)
        ((Modules.CellTensor.replacement X).obj (DerivedCategory.Q.objPreimage L))) ≪≫
    rightComparison.symm ≪≫
    (DerivedTensor.Bifunctor.functor (C := X.Modules)).mapIso
      ((DerivedCategory.Q.objObjPreimageIso E).prod
        ((DerivedTensor.Bifunctor.leftFunctor (DerivedCategory.Q.obj G)).mapIso
          (DerivedCategory.Q.objObjPreimageIso L)))

/-- The cell-replacement associator is natural in the variable derived module. -/
theorem derivedTensorAssoc_naturality (E : ModuleDerived X)
    (G : CochainComplex X.Modules ℤ) {L L' : ModuleDerived X} (φ : L ⟶ L') :
    (DerivedTensor.Bifunctor.leftFunctor
        (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))).map φ ≫
        (derivedTensorAssocComponent E G L').hom =
      (derivedTensorAssocComponent E G L).hom ≫
        (DerivedTensor.Bifunctor.leftFunctor (DerivedCategory.Q.obj G) ⋙
          DerivedTensor.Bifunctor.leftFunctor E).map φ :=
  sorry

/-- The natural associativity isomorphism for a fixed derived module and a fixed complex. -/
def derivedTensorAssocIso (E : ModuleDerived X) (G : CochainComplex X.Modules ℤ) :
    DerivedTensor.Bifunctor.leftFunctor
        (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G)) ≅
      DerivedTensor.Bifunctor.leftFunctor (DerivedCategory.Q.obj G) ⋙
        DerivedTensor.Bifunctor.leftFunctor E :=
  NatIso.ofComponents (derivedTensorAssocComponent E G)
    (fun φ ↦ derivedTensorAssoc_naturality E G φ)

/-- The canonical associativity map from left to right iterated derived tensor. -/
def derivedTensorAssoc (E : ModuleDerived X) (G : CochainComplex X.Modules ℤ) :
    DerivedTensor.Bifunctor.leftFunctor
        (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G)) ⟶
      DerivedTensor.Bifunctor.leftFunctor (DerivedCategory.Q.obj G) ⋙
        DerivedTensor.Bifunctor.leftFunctor E :=
  (derivedTensorAssocIso E G).hom

/-- The associativity map at a derived module is the concrete cell-replacement component. -/
theorem derivedTensorAssoc_app (E : ModuleDerived X) (G : CochainComplex X.Modules ℤ)
    (L : ModuleDerived X) :
    (derivedTensorAssoc E G).app L = (derivedTensorAssocComponent E G L).hom :=
  rfl

/-- The canonical associativity transformation is an isomorphism. -/
instance isIso_derivedTensorAssoc (E : ModuleDerived X) (G : CochainComplex X.Modules ℤ) :
    IsIso (derivedTensorAssoc E G) :=
  inferInstanceAs (IsIso (derivedTensorAssocIso E G).hom)

end ModuleDerived

end AlgebraicGeometry.AlgebraicSpace
