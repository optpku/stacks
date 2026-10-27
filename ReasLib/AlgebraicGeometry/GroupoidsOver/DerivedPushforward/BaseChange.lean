/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Pushforward.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.Additive
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Right

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor ComplexShape
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.DerivedPushforward

variable {S : Scheme.{u}}
variable {X Y Y' : GroupoidsOver S} (f : X ⟶ Y) (g : Y' ⟶ Y) (τ : StandardTopology)

section Abelian

variable [HasDerivedCategory (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (Y'.associatedTopology τ) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory
    (Sheaf ((fibreProductApex f g).associatedTopology τ) AddCommGrpCat.{u + 1})]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (abelianPushforward f τ))
    (HomologicalComplex.quasiIso
      (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (abelianPushforward (fibreProductFst f g) τ))
    (HomologicalComplex.quasiIso
      (Sheaf ((fibreProductApex f g).associatedTopology τ) AddCommGrpCat.{u + 1})
      (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (abelianPushforward f τ ⋙ associatedAbelianInverseImage g τ))
    (HomologicalComplex.quasiIso
      (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (associatedAbelianInverseImage (fibreProductSnd f g) τ ⋙
        abelianPushforward (fibreProductFst f g) τ))
    (HomologicalComplex.quasiIso
      (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (up ℤ))]

/-- Derived abelian pushforward `Rf_*` on associated `τ`-sites. -/
abbrev abelian :
    DerivedCategory (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}) :=
  RightDerived.Cochain.functor (abelianPushforward f τ)

/-- `abelian f τ` is the cochain-level total right derived functor of
abelian pushforward. -/
theorem abelian_eq :
    abelian f τ = RightDerived.Cochain.functor (abelianPushforward f τ) :=
  rfl

/-- The cochain-level unit for exact postcomposition of `Rf_*` by `g⁻¹`. -/
def abelianPostcompUnit :
    RightDerived.Cochain.toDerived
        (abelianPushforward f τ ⋙ associatedAbelianInverseImage g τ) ⟶
      (DerivedCategory.Q :
          CochainComplex (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) ℤ ⥤
            DerivedCategory (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})) ⋙
        (abelian f τ ⋙
          (associatedAbelianInverseImage g τ).mapDerivedCategory) :=
  (isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (abelianPushforward f τ ⋙ associatedAbelianInverseImage g τ)) (up ℤ)).symm
      (DerivedCategory.Q :
        CochainComplex (Sheaf (Y'.associatedTopology τ) AddCommGrpCat.{u + 1}) ℤ ⥤
          DerivedCategory (Sheaf (Y'.associatedTopology τ) AddCommGrpCat.{u + 1}))).hom ≫
    (Functor.associator
        ((abelianPushforward f τ).mapHomologicalComplex (up ℤ))
        ((associatedAbelianInverseImage g τ).mapHomologicalComplex (up ℤ))
        (DerivedCategory.Q :
          CochainComplex (Sheaf (Y'.associatedTopology τ) AddCommGrpCat.{u + 1}) ℤ ⥤
            DerivedCategory (Sheaf (Y'.associatedTopology τ) AddCommGrpCat.{u + 1}))).hom ≫
    (isoWhiskerLeft ((abelianPushforward f τ).mapHomologicalComplex (up ℤ))
      (associatedAbelianInverseImage g τ).mapDerivedCategoryFactors.symm).hom ≫
    (Functor.associator
        ((abelianPushforward f τ).mapHomologicalComplex (up ℤ))
        (DerivedCategory.Q :
          CochainComplex (Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}) ℤ ⥤
            DerivedCategory (Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}))
        (associatedAbelianInverseImage g τ).mapDerivedCategory).inv ≫
    whiskerRight (RightDerived.Cochain.unit (abelianPushforward f τ))
      (associatedAbelianInverseImage g τ).mapDerivedCategory ≫
    (Functor.associator
        (DerivedCategory.Q :
          CochainComplex (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) ℤ ⥤
            DerivedCategory (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}))
        (abelian f τ)
        (associatedAbelianInverseImage g τ).mapDerivedCategory).hom

/-- The comparison from `R(f_* ⋙ g⁻¹)` to `Rf_*` followed by exact inverse image. -/
def abelianPostcomp :
    RightDerived.Cochain.functor
        (abelianPushforward f τ ⋙ associatedAbelianInverseImage g τ) ⟶
      abelian f τ ⋙
        (associatedAbelianInverseImage g τ).mapDerivedCategory :=
  (RightDerived.Cochain.functor
      (abelianPushforward f τ ⋙ associatedAbelianInverseImage g τ)).rightDerivedDesc
    (RightDerived.Cochain.unit
      (abelianPushforward f τ ⋙ associatedAbelianInverseImage g τ))
    (HomologicalComplex.quasiIso
      (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (up ℤ))
    (abelian f τ ⋙
      (associatedAbelianInverseImage g τ).mapDerivedCategory)
    (abelianPostcompUnit f g τ)

/-- Exact postcomposition of derived abelian pushforward by inverse image is an isomorphism. -/
instance abelianPostcomp_isIso
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] :
    IsIso (abelianPostcomp f g τ) :=
  sorry

/-- The cochain-level unit for exact precomposition of `Rf'_*` by `(g')⁻¹`.
This is the iterated unit of the exact inverse-image model
`(g')⁻¹.mapDerivedCategory` with the derived unit of `f'_*`. -/
def abelianPrecompUnit :
    RightDerived.Cochain.toDerived
        (associatedAbelianInverseImage (fibreProductSnd f g) τ ⋙
          abelianPushforward (fibreProductFst f g) τ) ⟶
      (DerivedCategory.Q :
          CochainComplex (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) ℤ ⥤
            DerivedCategory (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})) ⋙
        ((associatedAbelianInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
          abelian (fibreProductFst f g) τ) :=
  (isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl
          (associatedAbelianInverseImage (fibreProductSnd f g) τ ⋙
            abelianPushforward (fibreProductFst f g) τ))
        (up ℤ)).symm
      (DerivedCategory.Q :
        CochainComplex (Sheaf (Y'.associatedTopology τ) AddCommGrpCat.{u + 1}) ℤ ⥤
          DerivedCategory (Sheaf (Y'.associatedTopology τ) AddCommGrpCat.{u + 1}))).hom ≫
    (Functor.associator
        ((associatedAbelianInverseImage (fibreProductSnd f g) τ).mapHomologicalComplex (up ℤ))
        ((abelianPushforward (fibreProductFst f g) τ).mapHomologicalComplex (up ℤ))
        (DerivedCategory.Q :
          CochainComplex (Sheaf (Y'.associatedTopology τ) AddCommGrpCat.{u + 1}) ℤ ⥤
            DerivedCategory (Sheaf (Y'.associatedTopology τ) AddCommGrpCat.{u + 1}))).hom ≫
    RightDerived.Composition.iteratedUnit
      (associatedAbelianInverseImage (fibreProductSnd f g) τ).mapDerivedCategoryFactors.inv
      (RightDerived.Cochain.unit (abelianPushforward (fibreProductFst f g) τ))

/-- The comparison from `R((g')⁻¹ ⋙ f'_*)` to `Rf'_*` after exact inverse image. -/
def abelianPrecomp :
    RightDerived.Cochain.functor
        (associatedAbelianInverseImage (fibreProductSnd f g) τ ⋙
          abelianPushforward (fibreProductFst f g) τ) ⟶
      (associatedAbelianInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
        abelian (fibreProductFst f g) τ :=
  (RightDerived.Cochain.functor
      (associatedAbelianInverseImage (fibreProductSnd f g) τ ⋙
        abelianPushforward (fibreProductFst f g) τ)).rightDerivedDesc
    (RightDerived.Cochain.unit
      (associatedAbelianInverseImage (fibreProductSnd f g) τ ⋙
        abelianPushforward (fibreProductFst f g) τ))
    (HomologicalComplex.quasiIso
      (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (up ℤ))
    ((associatedAbelianInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
      abelian (fibreProductFst f g) τ)
    (abelianPrecompUnit f g τ)

/-- Derived functorial form of the underived abelian identification. -/
def abelianMapNatIso :
    RightDerived.Cochain.functor
        (abelianPushforward f τ ⋙ associatedAbelianInverseImage g τ) ≅
      RightDerived.Cochain.functor
        (associatedAbelianInverseImage (fibreProductSnd f g) τ ⋙
          abelianPushforward (fibreProductFst f g) τ) :=
  Functor.RightDerived.mapNatIso
    (DerivedCategory.Q :
      CochainComplex (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) ℤ ⥤
        DerivedCategory (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}))
    (HomologicalComplex.quasiIso
      (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (up ℤ))
    (isoWhiskerRight
      (NatIso.mapHomologicalComplex (Pushforward.abelianBaseChangeIso f g τ) (up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf (Y'.associatedTopology τ) AddCommGrpCat.{u + 1}) ℤ ⥤
          DerivedCategory (Sheaf (Y'.associatedTopology τ) AddCommGrpCat.{u + 1})))

/-- The derived base-change map is the composite of the canonical comparisons. -/
def abelianBaseChangeHom [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] :
    abelian f τ ⋙ (associatedAbelianInverseImage g τ).mapDerivedCategory ⟶
      (associatedAbelianInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
        abelian (fibreProductFst f g) τ :=
  inv (abelianPostcomp f g τ) ≫ (abelianMapNatIso f g τ).hom ≫
    abelianPrecomp f g τ

/-- The derived base-change map restricted to sheaves embedded in degree zero. -/
def abelianBaseChangeHomOnSheaves
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] :
    DerivedCategory.singleFunctor (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) 0 ⋙
        (abelian f τ ⋙ (associatedAbelianInverseImage g τ).mapDerivedCategory) ⟶
      DerivedCategory.singleFunctor (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) 0 ⋙
        ((associatedAbelianInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
          abelian (fibreProductFst f g) τ) :=
  whiskerLeft (DerivedCategory.singleFunctor (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) 0)
    (abelianBaseChangeHom f g τ)

/-- Derived base change is invertible on degree-zero sheaf inputs for algebraic stacks. -/
instance abelianBaseChangeHom_isIso
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] :
    IsIso (abelianBaseChangeHomOnSheaves f g τ) := sorry

/-- The canonical derived base-change isomorphism, natural in sheaf inputs. -/
def abelianBaseChangeIso [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] :
    DerivedCategory.singleFunctor (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) 0 ⋙
        (abelian f τ ⋙ (associatedAbelianInverseImage g τ).mapDerivedCategory) ≅
      DerivedCategory.singleFunctor (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) 0 ⋙
        ((associatedAbelianInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
          abelian (fibreProductFst f g) τ) :=
  asIso (abelianBaseChangeHomOnSheaves f g τ)

/-- The forward isomorphism is the canonical derived base-change map on sheaves. -/
theorem abelianBaseChangeIso_hom
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] :
    (abelianBaseChangeIso f g τ).hom = abelianBaseChangeHomOnSheaves f g τ := rfl

/-- The component of derived base change at a sheaf embedded in degree zero. -/
def abelianBaseChangeIso_app
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) :
    (associatedAbelianInverseImage g τ).mapDerivedCategory.obj
        ((abelian f τ).obj ((DerivedCategory.singleFunctor (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) 0).obj F)) ≅
      (abelian (fibreProductFst f g) τ).obj
        ((associatedAbelianInverseImage (fibreProductSnd f g) τ).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) 0).obj F)) :=
  (abelianBaseChangeIso f g τ).app F

end Abelian

section Modules

variable [HasSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [HasSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [HasSheafify (Y'.associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [HasSheafify ((fibreProductApex f g).associatedTopology τ) AddCommGrpCat.{u + 1}]

variable [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf X τ))]
variable [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf Y τ))]
variable [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf Y' τ))]
variable [HasDerivedCategory
    (SheafOfModules.{u + 1} (associatedStructureSheaf (fibreProductApex f g) τ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (modulePushforward f τ))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (modulePushforward (fibreProductFst f g) τ))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u + 1} (associatedStructureSheaf (fibreProductApex f g) τ))
      (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (modulePushforward f τ ⋙ associatedModuleInverseImage g τ))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (associatedModuleInverseImage (fibreProductSnd f g) τ ⋙
        modulePushforward (fibreProductFst f g) τ))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (up ℤ))]

/-- Derived module pushforward `Rf_*` on associated `τ`-sites. -/
abbrev modules :
    DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) ⥤
      DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf Y τ)) :=
  RightDerived.Cochain.functor (modulePushforward f τ)

/-- `modules f τ` is the cochain-level total right derived functor of
module pushforward. -/
theorem modules_eq :
    modules f τ = RightDerived.Cochain.functor (modulePushforward f τ) :=
  rfl

/-- The cochain-level unit for exact postcomposition of `Rf_*` by `g⁻¹`. -/
def modulePostcompUnit :
    RightDerived.Cochain.toDerived
        (modulePushforward f τ ⋙ associatedModuleInverseImage g τ) ⟶
      (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) ℤ ⥤
            DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf X τ))) ⋙
        (modules f τ ⋙
          (associatedModuleInverseImage g τ).mapDerivedCategory) :=
  (isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (modulePushforward f τ ⋙ associatedModuleInverseImage g τ)) (up ℤ)).symm
      (DerivedCategory.Q :
        CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf Y' τ)) ℤ ⥤
          DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf Y' τ)))).hom ≫
    (Functor.associator
        ((modulePushforward f τ).mapHomologicalComplex (up ℤ))
        ((associatedModuleInverseImage g τ).mapHomologicalComplex (up ℤ))
        (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf Y' τ)) ℤ ⥤
            DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf Y' τ)))).hom ≫
    (isoWhiskerLeft ((modulePushforward f τ).mapHomologicalComplex (up ℤ))
      (associatedModuleInverseImage g τ).mapDerivedCategoryFactors.symm).hom ≫
    (Functor.associator
        ((modulePushforward f τ).mapHomologicalComplex (up ℤ))
        (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf Y τ)) ℤ ⥤
            DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf Y τ)))
        (associatedModuleInverseImage g τ).mapDerivedCategory).inv ≫
    whiskerRight (RightDerived.Cochain.unit (modulePushforward f τ))
      (associatedModuleInverseImage g τ).mapDerivedCategory ≫
    (Functor.associator
        (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) ℤ ⥤
            DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)))
        (modules f τ)
        (associatedModuleInverseImage g τ).mapDerivedCategory).hom

/-- The comparison from `R(f_* ⋙ g⁻¹)` to `Rf_*` followed by exact inverse image. -/
def modulePostcomp :
    RightDerived.Cochain.functor
        (modulePushforward f τ ⋙ associatedModuleInverseImage g τ) ⟶
      modules f τ ⋙
        (associatedModuleInverseImage g τ).mapDerivedCategory :=
  (RightDerived.Cochain.functor
      (modulePushforward f τ ⋙ associatedModuleInverseImage g τ)).rightDerivedDesc
    (RightDerived.Cochain.unit
      (modulePushforward f τ ⋙ associatedModuleInverseImage g τ))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (up ℤ))
    (modules f τ ⋙
      (associatedModuleInverseImage g τ).mapDerivedCategory)
    (modulePostcompUnit f g τ)

/-- Exact postcomposition of derived module pushforward by inverse image is an isomorphism. -/
instance modulePostcomp_isIso
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] :
    IsIso (modulePostcomp f g τ) :=
  sorry

/-- The cochain-level unit for exact precomposition of `Rf'_*` by `(g')⁻¹`.
This is the iterated unit of the exact inverse-image model
`(g')⁻¹.mapDerivedCategory` with the derived unit of `f'_*`. -/
def modulePrecompUnit :
    RightDerived.Cochain.toDerived
        (associatedModuleInverseImage (fibreProductSnd f g) τ ⋙
          modulePushforward (fibreProductFst f g) τ) ⟶
      (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) ℤ ⥤
            DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf X τ))) ⋙
        ((associatedModuleInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
          modules (fibreProductFst f g) τ) :=
  (isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl
          (associatedModuleInverseImage (fibreProductSnd f g) τ ⋙
            modulePushforward (fibreProductFst f g) τ))
        (up ℤ)).symm
      (DerivedCategory.Q :
        CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf Y' τ)) ℤ ⥤
          DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf Y' τ)))).hom ≫
    (Functor.associator
        ((associatedModuleInverseImage (fibreProductSnd f g) τ).mapHomologicalComplex (up ℤ))
        ((modulePushforward (fibreProductFst f g) τ).mapHomologicalComplex (up ℤ))
        (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf Y' τ)) ℤ ⥤
            DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf Y' τ)))).hom ≫
    RightDerived.Composition.iteratedUnit
      (associatedModuleInverseImage (fibreProductSnd f g) τ).mapDerivedCategoryFactors.inv
      (RightDerived.Cochain.unit (modulePushforward (fibreProductFst f g) τ))

/-- The comparison from `R((g')⁻¹ ⋙ f'_*)` to `Rf'_*` after exact inverse image. -/
def modulePrecomp :
    RightDerived.Cochain.functor
        (associatedModuleInverseImage (fibreProductSnd f g) τ ⋙
          modulePushforward (fibreProductFst f g) τ) ⟶
      (associatedModuleInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
        modules (fibreProductFst f g) τ :=
  (RightDerived.Cochain.functor
      (associatedModuleInverseImage (fibreProductSnd f g) τ ⋙
        modulePushforward (fibreProductFst f g) τ)).rightDerivedDesc
    (RightDerived.Cochain.unit
      (associatedModuleInverseImage (fibreProductSnd f g) τ ⋙
        modulePushforward (fibreProductFst f g) τ))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (up ℤ))
    ((associatedModuleInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
      modules (fibreProductFst f g) τ)
    (modulePrecompUnit f g τ)

/-- Derived functorial form of the underived module identification. -/
def moduleMapNatIso :
    RightDerived.Cochain.functor
        (modulePushforward f τ ⋙ associatedModuleInverseImage g τ) ≅
      RightDerived.Cochain.functor
        (associatedModuleInverseImage (fibreProductSnd f g) τ ⋙
          modulePushforward (fibreProductFst f g) τ) :=
  Functor.RightDerived.mapNatIso
    (DerivedCategory.Q :
      CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) ℤ ⥤
        DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (up ℤ))
    (isoWhiskerRight
      (NatIso.mapHomologicalComplex (Pushforward.moduleBaseChangeIso f g τ) (up ℤ))
      (DerivedCategory.Q :
        CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf Y' τ)) ℤ ⥤
          DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf Y' τ))))

/-- The derived base-change map is the composite of the canonical comparisons. -/
def moduleBaseChangeHom [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] :
    modules f τ ⋙ (associatedModuleInverseImage g τ).mapDerivedCategory ⟶
      (associatedModuleInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
        modules (fibreProductFst f g) τ :=
  inv (modulePostcomp f g τ) ≫ (moduleMapNatIso f g τ).hom ≫
    modulePrecomp f g τ

/-- The derived base-change map restricted to sheaves embedded in degree zero. -/
def moduleBaseChangeHomOnSheaves
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] :
    DerivedCategory.singleFunctor (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) 0 ⋙
        (modules f τ ⋙ (associatedModuleInverseImage g τ).mapDerivedCategory) ⟶
      DerivedCategory.singleFunctor (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) 0 ⋙
        ((associatedModuleInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
          modules (fibreProductFst f g) τ) :=
  whiskerLeft (DerivedCategory.singleFunctor (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) 0)
    (moduleBaseChangeHom f g τ)

/-- Derived base change is invertible on degree-zero sheaf inputs for algebraic stacks. -/
instance moduleBaseChangeHom_isIso
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] :
    IsIso (moduleBaseChangeHomOnSheaves f g τ) := sorry

/-- The canonical derived base-change isomorphism, natural in sheaf inputs. -/
def moduleBaseChangeIso [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] :
    DerivedCategory.singleFunctor (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) 0 ⋙
        (modules f τ ⋙ (associatedModuleInverseImage g τ).mapDerivedCategory) ≅
      DerivedCategory.singleFunctor (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) 0 ⋙
        ((associatedModuleInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
          modules (fibreProductFst f g) τ) :=
  asIso (moduleBaseChangeHomOnSheaves f g τ)

/-- The forward isomorphism is the canonical derived base-change map on sheaves. -/
theorem moduleBaseChangeIso_hom
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] :
    (moduleBaseChangeIso f g τ).hom = moduleBaseChangeHomOnSheaves f g τ := rfl

/-- The component of derived base change at a sheaf embedded in degree zero. -/
def moduleBaseChangeIso_app
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) :
    (associatedModuleInverseImage g τ).mapDerivedCategory.obj
        ((modules f τ).obj ((DerivedCategory.singleFunctor (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) 0).obj F)) ≅
      (modules (fibreProductFst f g) τ).obj
        ((associatedModuleInverseImage (fibreProductSnd f g) τ).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) 0).obj F)) :=
  (moduleBaseChangeIso f g τ).app F

end Modules

end AlgebraicGeometry.GroupoidsOver.DerivedPushforward
