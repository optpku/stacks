/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Right
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Lemma_94_14_3_Pullback
public import stacks_project.Chap96.Lemma_96_21_2_HigherDirectImage
public import stacks_project.Chap96.Lemma_96_21_3_InverseImage

/-!
# Derived base change of pushforward on associated τ-sites

A 2-cartesian square of algebraic stacks supplies a canonical isomorphism
`g⁻¹ Rf_* ≅ Rf'_* (g')⁻¹` of derived-category functors, for abelian sheaves and for
sheaves of modules, obtained from the underived inverse-image 2-cell by exact
postcomposition, derived naturality, and exact precomposition.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ConcreteCategory CategoryTheory.Limits ComplexShape
open AlgebraicGeometry.GroupoidsOver
open CategoryTheory.Functor
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}
variable {X Y Y' : GroupoidsOver S} (f : X ⟶ Y) (g : Y' ⟶ Y) (τ : StandardTopology)

/-- Continuous-cocontinuous adjunction `f⁻¹ ⊣ f_*` on associated abelian `τ`-sheaves. -/
abbrev associatedAbelianInverseImage_adjunction :
    associatedAbelianInverseImage f τ ⊣ abelianPushforward f τ :=
  (toCartesianBasedFunctor f).toFunctor.sheafAdjunctionCocontinuous
    AddCommGrpCat.{u + 1} (X.associatedTopology τ) (Y.associatedTopology τ)

/-- The canonical underived comparison `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of abelian sheaves,
the mate of `abelianInverseImage_twoFibreIso`. -/
def abelianPushforwardBaseChangeHom :
    abelianPushforward f τ ⋙ associatedAbelianInverseImage g τ ⟶
      associatedAbelianInverseImage (fibreProductSnd f g) τ ⋙
        abelianPushforward (fibreProductFst f g) τ :=
  CategoryTheory.DerivedBaseChange.map
    (associatedAbelianInverseImage_adjunction f τ)
    (associatedAbelianInverseImage_adjunction (fibreProductFst f g) τ)
    (abelianInverseImage_twoFibreIso f τ g)

/-- The underived abelian comparison is invertible. -/
instance abelianPushforwardBaseChangeHom.isIso :
    IsIso (abelianPushforwardBaseChangeHom f g τ) :=
  sorry

/-- The reverse underived comparison `f'_* (g')⁻¹ ⟶ g⁻¹ f_*`. -/
def abelianPushforwardBaseChangeInv :
    associatedAbelianInverseImage (fibreProductSnd f g) τ ⋙
        abelianPushforward (fibreProductFst f g) τ ⟶
      abelianPushforward f τ ⋙ associatedAbelianInverseImage g τ :=
  inv (abelianPushforwardBaseChangeHom f g τ)

/-- The canonical underived isomorphism `g⁻¹ f_* ≅ f'_* (g')⁻¹` of abelian sheaves on
the chosen 2-fibre product. -/
def abelianPushforwardBaseChangeIso :
    abelianPushforward f τ ⋙ associatedAbelianInverseImage g τ ≅
      associatedAbelianInverseImage (fibreProductSnd f g) τ ⋙
        abelianPushforward (fibreProductFst f g) τ :=
  asIso (abelianPushforwardBaseChangeHom f g τ)

/-- `abelianPushforwardBaseChangeIso` has forward map the mate of the inverse-image 2-cell. -/
theorem abelianPushforwardBaseChangeIso_eq :
    (abelianPushforwardBaseChangeIso f g τ).hom =
      abelianPushforwardBaseChangeHom f g τ :=
  rfl

/-- Component of the underived abelian base-change isomorphism at a sheaf `F`. -/
def abelianPushforwardBaseChangeIso_app
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) :
    (associatedAbelianInverseImage g τ).obj ((abelianPushforward f τ).obj F) ≅
      (abelianPushforward (fibreProductFst f g) τ).obj
        ((associatedAbelianInverseImage (fibreProductSnd f g) τ).obj F) :=
  (abelianPushforwardBaseChangeIso f g τ).app F

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
abbrev abelianDerivedPushforward :
    DerivedCategory (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}) :=
  RightDerived.Cochain.functor (abelianPushforward f τ)

/-- `abelianDerivedPushforward f τ` is the cochain-level total right derived functor of
abelian pushforward. -/
theorem abelianDerivedPushforward_eq :
    abelianDerivedPushforward f τ = RightDerived.Cochain.functor (abelianPushforward f τ) :=
  rfl

/-- The cochain-level unit for exact postcomposition of `Rf_*` by `g⁻¹`. -/
def abelianDerivedPushforward_postcompUnit :
    RightDerived.Cochain.toDerived
        (abelianPushforward f τ ⋙ associatedAbelianInverseImage g τ) ⟶
      (DerivedCategory.Q :
          CochainComplex (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) ℤ ⥤
            DerivedCategory (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})) ⋙
        (abelianDerivedPushforward f τ ⋙
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
        (abelianDerivedPushforward f τ)
        (associatedAbelianInverseImage g τ).mapDerivedCategory).hom

/-- The comparison from `R(f_* ⋙ g⁻¹)` to `Rf_*` followed by exact inverse image. -/
def abelianDerivedPushforward_postcomp :
    RightDerived.Cochain.functor
        (abelianPushforward f τ ⋙ associatedAbelianInverseImage g τ) ⟶
      abelianDerivedPushforward f τ ⋙
        (associatedAbelianInverseImage g τ).mapDerivedCategory :=
  (RightDerived.Cochain.functor
      (abelianPushforward f τ ⋙ associatedAbelianInverseImage g τ)).rightDerivedDesc
    (RightDerived.Cochain.unit
      (abelianPushforward f τ ⋙ associatedAbelianInverseImage g τ))
    (HomologicalComplex.quasiIso
      (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (up ℤ))
    (abelianDerivedPushforward f τ ⋙
      (associatedAbelianInverseImage g τ).mapDerivedCategory)
    (abelianDerivedPushforward_postcompUnit f g τ)

/-- Exact postcomposition of derived abelian pushforward by inverse image is an isomorphism. -/
instance abelianDerivedPushforward_postcomp_isIso :
    IsIso (abelianDerivedPushforward_postcomp f g τ) :=
  sorry

/-- Exact postcomposition of `Rf_*` by `g⁻¹` is a right-derived model of the underived
composite. -/
instance abelianDerivedPushforward_postcomp_isRightDerived :
    (abelianDerivedPushforward f τ ⋙
      (associatedAbelianInverseImage g τ).mapDerivedCategory).IsRightDerivedFunctor
      (abelianDerivedPushforward_postcompUnit f g τ)
      (HomologicalComplex.quasiIso
        (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (up ℤ)) :=
  sorry

/-- The reverse comparison from exact postcomposition of `Rf_*` by `g⁻¹` to
`R(f_* ⋙ g⁻¹)`. -/
def abelianDerivedPushforward_postcompInv :
    abelianDerivedPushforward f τ ⋙
        (associatedAbelianInverseImage g τ).mapDerivedCategory ⟶
      RightDerived.Cochain.functor
        (abelianPushforward f τ ⋙ associatedAbelianInverseImage g τ) :=
  (abelianDerivedPushforward f τ ⋙
      (associatedAbelianInverseImage g τ).mapDerivedCategory).rightDerivedDesc
    (abelianDerivedPushforward_postcompUnit f g τ)
    (HomologicalComplex.quasiIso
      (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (up ℤ))
    (RightDerived.Cochain.functor
      (abelianPushforward f τ ⋙ associatedAbelianInverseImage g τ))
    (RightDerived.Cochain.unit
      (abelianPushforward f τ ⋙ associatedAbelianInverseImage g τ))

/-- The cochain-level unit for exact precomposition of `Rf'_*` by `(g')⁻¹`.
This is the iterated unit of the exact inverse-image model
`(g')⁻¹.mapDerivedCategory` with the derived unit of `f'_*`. -/
def abelianDerivedPushforward_precompUnit :
    RightDerived.Cochain.toDerived
        (associatedAbelianInverseImage (fibreProductSnd f g) τ ⋙
          abelianPushforward (fibreProductFst f g) τ) ⟶
      (DerivedCategory.Q :
          CochainComplex (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) ℤ ⥤
            DerivedCategory (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})) ⋙
        ((associatedAbelianInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
          abelianDerivedPushforward (fibreProductFst f g) τ) :=
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
def abelianDerivedPushforward_precomp :
    RightDerived.Cochain.functor
        (associatedAbelianInverseImage (fibreProductSnd f g) τ ⋙
          abelianPushforward (fibreProductFst f g) τ) ⟶
      (associatedAbelianInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
        abelianDerivedPushforward (fibreProductFst f g) τ :=
  (RightDerived.Cochain.functor
      (associatedAbelianInverseImage (fibreProductSnd f g) τ ⋙
        abelianPushforward (fibreProductFst f g) τ)).rightDerivedDesc
    (RightDerived.Cochain.unit
      (associatedAbelianInverseImage (fibreProductSnd f g) τ ⋙
        abelianPushforward (fibreProductFst f g) τ))
    (HomologicalComplex.quasiIso
      (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (up ℤ))
    ((associatedAbelianInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
      abelianDerivedPushforward (fibreProductFst f g) τ)
    (abelianDerivedPushforward_precompUnit f g τ)

/-- Exact precomposition of `Rf'_*` by `(g')⁻¹` is a right-derived model of the underived
composite, using that inverse image is exact. -/
instance abelianDerivedPushforward_precomp_isRightDerived :
    ((associatedAbelianInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
      abelianDerivedPushforward (fibreProductFst f g) τ).IsRightDerivedFunctor
      (abelianDerivedPushforward_precompUnit f g τ)
      (HomologicalComplex.quasiIso
        (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (up ℤ)) :=
  sorry

/-- The reverse comparison from exact precomposition of `Rf'_*` by `(g')⁻¹` to
`R((g')⁻¹ ⋙ f'_*)`. -/
def abelianDerivedPushforward_precompInv :
    (associatedAbelianInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
        abelianDerivedPushforward (fibreProductFst f g) τ ⟶
      RightDerived.Cochain.functor
        (associatedAbelianInverseImage (fibreProductSnd f g) τ ⋙
          abelianPushforward (fibreProductFst f g) τ) :=
  ((associatedAbelianInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
      abelianDerivedPushforward (fibreProductFst f g) τ).rightDerivedDesc
    (abelianDerivedPushforward_precompUnit f g τ)
    (HomologicalComplex.quasiIso
      (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (up ℤ))
    (RightDerived.Cochain.functor
      (associatedAbelianInverseImage (fibreProductSnd f g) τ ⋙
        abelianPushforward (fibreProductFst f g) τ))
    (RightDerived.Cochain.unit
      (associatedAbelianInverseImage (fibreProductSnd f g) τ ⋙
        abelianPushforward (fibreProductFst f g) τ))

/-- Derived functorial form of the underived abelian identification. -/
def abelianDerivedPushforward_mapNatIso :
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
      (NatIso.mapHomologicalComplex (abelianPushforwardBaseChangeIso f g τ) (up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf (Y'.associatedTopology τ) AddCommGrpCat.{u + 1}) ℤ ⥤
          DerivedCategory (Sheaf (Y'.associatedTopology τ) AddCommGrpCat.{u + 1})))

/-- The functorial derived identification `g⁻¹ Rf_* ≅ Rf'_* (g')⁻¹` on abelian sheaves,
as the composite of exact postcomposition, derived transport of the underived mate,
and exact precomposition. -/
def abelianDerivedPushforwardBaseChangeIso :
    abelianDerivedPushforward f τ ⋙
        (associatedAbelianInverseImage g τ).mapDerivedCategory ≅
      (associatedAbelianInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
        abelianDerivedPushforward (fibreProductFst f g) τ where
  hom :=
    abelianDerivedPushforward_postcompInv f g τ ≫
      (abelianDerivedPushforward_mapNatIso f g τ).hom ≫
      abelianDerivedPushforward_precomp f g τ
  inv :=
    abelianDerivedPushforward_precompInv f g τ ≫
      (abelianDerivedPushforward_mapNatIso f g τ).inv ≫
      abelianDerivedPushforward_postcomp f g τ
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Objectwise form of `abelianDerivedPushforwardBaseChangeIso`. -/
def abelianDerivedPushforwardBaseChangeIso_app
    (K : DerivedCategory (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})) :
    ((associatedAbelianInverseImage g τ).mapDerivedCategory).obj
        ((abelianDerivedPushforward f τ).obj K) ≅
      (abelianDerivedPushforward (fibreProductFst f g) τ).obj
        ((associatedAbelianInverseImage (fibreProductSnd f g) τ).mapDerivedCategory.obj K) :=
  (abelianDerivedPushforwardBaseChangeIso f g τ).app K


/-- Pointwise left Kan extensions along the opposite cartesian total functor exist on
abelian presheaves. -/
instance toCartesianBasedFunctor_op_hasLeftKanExtension_addCommGrpCat
    {X Y : GroupoidsOver S} (h : X ⟶ Y)
    (P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (toCartesianBasedFunctor h).toFunctor.op.HasLeftKanExtension P :=
  sorry

/-- Sheaves of modules on an associated `τ`-site have homology. -/
instance (priority := 2000) associatedModules_categoryWithHomology {𝒳 : GroupoidsOver S}
    {σ : StandardTopology} :
    CategoryWithHomology (SheafOfModules.{u + 1} (associatedStructureSheaf 𝒳 σ)) :=
  sorry

/-- Canonical preadditive structure on associated `τ`-module sheaves, taken from
`associatedModules_abelian` so later `Additive` and `toDerived` instances agree. -/
instance (priority := 4000) associatedModules_preadditive {𝒳 : GroupoidsOver S}
    {σ : StandardTopology} :
    Preadditive (SheafOfModules.{u + 1} (associatedStructureSheaf 𝒳 σ)) :=
  (associatedModules_abelian :
      Abelian (SheafOfModules.{u + 1} (associatedStructureSheaf 𝒳 σ))).toPreadditive

/-- Canonical zero morphisms on associated `τ`-module sheaves. -/
instance (priority := 4000) associatedModules_hasZeroMorphisms {𝒳 : GroupoidsOver S}
    {σ : StandardTopology} :
    HasZeroMorphisms (SheafOfModules.{u + 1} (associatedStructureSheaf 𝒳 σ)) :=
  Preadditive.preadditiveHasZeroMorphisms

/-- Associated module inverse image is additive. -/
instance (priority := 2000) associatedModuleInverseImage_additive {X Y : GroupoidsOver S}
    (h : X ⟶ Y) (σ : StandardTopology) :
    (associatedModuleInverseImage h σ).Additive :=
  sorry

/-- Associated module inverse image preserves homology. -/
instance associatedModuleInverseImage_preservesHomology {X Y : GroupoidsOver S}
    (h : X ⟶ Y) (σ : StandardTopology) :
    (associatedModuleInverseImage h σ).PreservesHomology :=
  sorry

/-- Associated module inverse image preserves finite limits. -/
instance associatedModuleInverseImage_preservesFiniteLimits {X Y : GroupoidsOver S}
    (h : X ⟶ Y) (σ : StandardTopology) :
    PreservesFiniteLimits (associatedModuleInverseImage h σ) :=
  sorry

/-- Associated module inverse image preserves finite colimits. -/
instance associatedModuleInverseImage_preservesFiniteColimits {X Y : GroupoidsOver S}
    (h : X ⟶ Y) (σ : StandardTopology) :
    PreservesFiniteColimits (associatedModuleInverseImage h σ) :=
  sorry

/-- Lift an abelian-sheaf morphism to a morphism of sheaves of modules with the same
underlying additive map. -/
def moduleHomOfAbelian {𝒳 : GroupoidsOver S} {σ : StandardTopology}
    {M N : SheafOfModules.{u + 1} (associatedStructureSheaf 𝒳 σ)}
    (α : (SheafOfModules.toSheaf (associatedStructureSheaf 𝒳 σ)).obj M ⟶
      (SheafOfModules.toSheaf (associatedStructureSheaf 𝒳 σ)).obj N) :
    M ⟶ N where
  val :=
    { app := fun y ↦
        ConcreteCategory.ofHom (C := ModuleCat _)
          { toFun := (α.hom.app y).hom
            map_add' := map_add (α.hom.app y).hom
            map_smul' := sorry }
      naturality := sorry }

/-- Lift an abelian-sheaf isomorphism to an isomorphism of sheaves of modules. -/
def moduleIsoOfAbelian {𝒳 : GroupoidsOver S} {σ : StandardTopology}
    {M N : SheafOfModules.{u + 1} (associatedStructureSheaf 𝒳 σ)}
    (e : (SheafOfModules.toSheaf (associatedStructureSheaf 𝒳 σ)).obj M ≅
      (SheafOfModules.toSheaf (associatedStructureSheaf 𝒳 σ)).obj N) :
    M ≅ N where
  hom := moduleHomOfAbelian e.hom
  inv := moduleHomOfAbelian e.inv
  hom_inv_id := sorry
  inv_hom_id := sorry

variable [HasSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [HasSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [HasSheafify (Y'.associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [HasSheafify ((fibreProductApex f g).associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [HasInjectiveResolutions (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})]
variable [HasInjectiveResolutions
    (Sheaf ((fibreProductApex f g).associatedTopology τ) AddCommGrpCat.{u + 1})]

section ModulePushforwardAdditive

variable {A B : GroupoidsOver S} (h : A ⟶ B) (σ : StandardTopology)
variable [HasSheafify (A.associatedTopology σ) AddCommGrpCat.{u + 1}]
variable [HasSheafify (B.associatedTopology σ) AddCommGrpCat.{u + 1}]
variable [HasInjectiveResolutions (Sheaf (A.associatedTopology σ) AddCommGrpCat.{u + 1})]

/-- Module pushforward on associated `τ`-sites is additive. -/
instance (priority := 3000) modulePushforward_isAdditive :
    (modulePushforward h σ).Additive :=
  sorry

end ModulePushforwardAdditive

/-- The composite `k⁻¹ ∘ h_*` of associated `τ`-module functors is additive. -/
instance (priority := 3000) modulePushforward_comp_inverseImage_isAdditive
    {A B C : GroupoidsOver S} (h : A ⟶ B) (k : C ⟶ B) (σ : StandardTopology)
    [HasSheafify (A.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasSheafify (B.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasSheafify (C.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions (Sheaf (A.associatedTopology σ) AddCommGrpCat.{u + 1})] :
    (modulePushforward h σ ⋙ associatedModuleInverseImage k σ).Additive :=
  sorry

/-- The composite `q_* ∘ p⁻¹` of associated `τ`-module functors is additive. -/
instance (priority := 3000) moduleInverseImage_comp_pushforward_isAdditive
    {A B C : GroupoidsOver S} (p : A ⟶ B) (q : A ⟶ C) (σ : StandardTopology)
    [HasSheafify (A.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasSheafify (B.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasSheafify (C.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions (Sheaf (A.associatedTopology σ) AddCommGrpCat.{u + 1})] :
    (associatedModuleInverseImage p σ ⋙ modulePushforward q σ).Additive :=
  sorry

/-- Forgetting module structure identifies the two underived module composites with the
abelian base-change isomorphism. -/
def modulePushforwardBaseChange_forget
    (G : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) :
    (SheafOfModules.toSheaf (associatedStructureSheaf Y' τ)).obj
      ((associatedModuleInverseImage g τ).obj ((modulePushforward f τ).obj G)) ≅
      (SheafOfModules.toSheaf (associatedStructureSheaf Y' τ)).obj
        ((modulePushforward (fibreProductFst f g) τ).obj
          ((associatedModuleInverseImage (fibreProductSnd f g) τ).obj G)) :=
  (associatedModuleInverseImage_underlyingIso g τ).app ((modulePushforward f τ).obj G) ≪≫
    (associatedAbelianInverseImage g τ).mapIso ((modulePushforward_toSheafIso f τ).app G) ≪≫
    (abelianPushforwardBaseChangeIso f g τ).app
      ((SheafOfModules.toSheaf (associatedStructureSheaf X τ)).obj G) ≪≫
    ((abelianPushforward (fibreProductFst f g) τ).mapIso
        ((associatedModuleInverseImage_underlyingIso (fibreProductSnd f g) τ).app G)).symm ≪≫
      ((modulePushforward_toSheafIso (fibreProductFst f g) τ).app
          ((associatedModuleInverseImage (fibreProductSnd f g) τ).obj G)).symm

/-- The canonical underived isomorphism `g⁻¹ f_* ≅ f'_* (g')⁻¹` of sheaves of modules. -/
def modulePushforwardBaseChangeIso :
    modulePushforward f τ ⋙ associatedModuleInverseImage g τ ≅
      associatedModuleInverseImage (fibreProductSnd f g) τ ⋙
        modulePushforward (fibreProductFst f g) τ :=
  NatIso.ofComponents (fun G ↦ moduleIsoOfAbelian (modulePushforwardBaseChange_forget f g τ G))
    sorry

/-- Component of the underived module base-change isomorphism at a sheaf of modules. -/
def modulePushforwardBaseChangeIso_app
    (G : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) :
    (associatedModuleInverseImage g τ).obj ((modulePushforward f τ).obj G) ≅
      (modulePushforward (fibreProductFst f g) τ).obj
        ((associatedModuleInverseImage (fibreProductSnd f g) τ).obj G) :=
  (modulePushforwardBaseChangeIso f g τ).app G

variable [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf X τ))]
variable [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf Y τ))]
variable [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf Y' τ))]
variable [HasDerivedCategory
    (SheafOfModules.{u + 1} (associatedStructureSheaf (fibreProductApex f g) τ))]

/-- Cochain-level localization of module pushforward. -/
abbrev modulePushforward_toDerived {A B : GroupoidsOver S} (h : A ⟶ B)
    (σ : StandardTopology)
    [HasSheafify (A.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasSheafify (B.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions (Sheaf (A.associatedTopology σ) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf A σ))]
    [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf B σ))] :
    CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf A σ)) ℤ ⥤
      DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf B σ)) :=
  RightDerived.Cochain.toDerived (modulePushforward h σ)

/-- Cochain-level localization of the underived composite `k⁻¹ ∘ h_*`. -/
abbrev modulePushforward_compInverseImage_toDerived
    {A B C : GroupoidsOver S} (h : A ⟶ B) (k : C ⟶ B) (σ : StandardTopology)
    [HasSheafify (A.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasSheafify (B.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasSheafify (C.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions (Sheaf (A.associatedTopology σ) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf A σ))]
    [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf C σ))] :
    CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf A σ)) ℤ ⥤
      DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf C σ)) :=
  RightDerived.Cochain.toDerived
    (modulePushforward h σ ⋙ associatedModuleInverseImage k σ)

/-- Cochain-level localization of the underived composite `q_* ∘ p⁻¹`. -/
abbrev moduleInverseImage_compPushforward_toDerived
    {A B C : GroupoidsOver S} (p : A ⟶ B) (q : A ⟶ C) (σ : StandardTopology)
    [HasSheafify (A.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasSheafify (B.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasSheafify (C.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions (Sheaf (A.associatedTopology σ) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf B σ))]
    [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf C σ))] :
    CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf B σ)) ℤ ⥤
      DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf C σ)) :=
  RightDerived.Cochain.toDerived
    (associatedModuleInverseImage p σ ⋙ modulePushforward q σ)

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

/-- Wrapper additivity recovers the cochain-level `toDerived` hypothesis for module
pushforward. -/
instance modulePushforward_cochain_hasRightDerivedFunctor {A B : GroupoidsOver S}
    (h : A ⟶ B) (σ : StandardTopology)
    [HasSheafify (A.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasSheafify (B.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions (Sheaf (A.associatedTopology σ) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf A σ))]
    [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf B σ))]
    [HasRightDerivedFunctor (modulePushforward_toDerived h σ)
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u + 1} (associatedStructureSheaf A σ)) (up ℤ))] :
    HasRightDerivedFunctor (RightDerived.Cochain.toDerived (modulePushforward h σ))
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u + 1} (associatedStructureSheaf A σ)) (up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor (modulePushforward_toDerived h σ)
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u + 1} (associatedStructureSheaf A σ)) (up ℤ)))

/-- Wrapper additivity recovers the cochain-level `toDerived` hypothesis for `k⁻¹ ∘ h_*`. -/
instance modulePushforward_compInverseImage_cochain_hasRightDerivedFunctor
    {A B C : GroupoidsOver S} (h : A ⟶ B) (k : C ⟶ B) (σ : StandardTopology)
    [HasSheafify (A.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasSheafify (B.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasSheafify (C.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions (Sheaf (A.associatedTopology σ) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf A σ))]
    [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf C σ))]
    [HasRightDerivedFunctor (modulePushforward_compInverseImage_toDerived h k σ)
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u + 1} (associatedStructureSheaf A σ)) (up ℤ))] :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (modulePushforward h σ ⋙ associatedModuleInverseImage k σ))
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u + 1} (associatedStructureSheaf A σ)) (up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor (modulePushforward_compInverseImage_toDerived h k σ)
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u + 1} (associatedStructureSheaf A σ)) (up ℤ)))

/-- Wrapper additivity recovers the cochain-level `toDerived` hypothesis for `q_* ∘ p⁻¹`. -/
instance moduleInverseImage_compPushforward_cochain_hasRightDerivedFunctor
    {A B C : GroupoidsOver S} (p : A ⟶ B) (q : A ⟶ C) (σ : StandardTopology)
    [HasSheafify (A.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasSheafify (B.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasSheafify (C.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions (Sheaf (A.associatedTopology σ) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf B σ))]
    [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf C σ))]
    [HasRightDerivedFunctor (moduleInverseImage_compPushforward_toDerived p q σ)
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u + 1} (associatedStructureSheaf B σ)) (up ℤ))] :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (associatedModuleInverseImage p σ ⋙ modulePushforward q σ))
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u + 1} (associatedStructureSheaf B σ)) (up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor (moduleInverseImage_compPushforward_toDerived p q σ)
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u + 1} (associatedStructureSheaf B σ)) (up ℤ)))

/-- Derived module pushforward `Rf_*` on associated `τ`-sites. -/
abbrev moduleDerivedPushforward {A B : GroupoidsOver S} (h : A ⟶ B)
    (σ : StandardTopology)
    [HasSheafify (A.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasSheafify (B.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions (Sheaf (A.associatedTopology σ) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf A σ))]
    [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf B σ))]
    [HasRightDerivedFunctor (RightDerived.Cochain.toDerived (modulePushforward h σ))
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u + 1} (associatedStructureSheaf A σ)) (up ℤ))] :
    DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf A σ)) ⥤
      DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf B σ)) :=
  RightDerived.Cochain.functor (modulePushforward h σ)

/-- `moduleDerivedPushforward h σ` is the cochain-level total right derived functor of
module pushforward. -/
theorem moduleDerivedPushforward_eq {A B : GroupoidsOver S} (h : A ⟶ B)
    (σ : StandardTopology)
    [HasSheafify (A.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasSheafify (B.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions (Sheaf (A.associatedTopology σ) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf A σ))]
    [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf B σ))]
    [HasRightDerivedFunctor (RightDerived.Cochain.toDerived (modulePushforward h σ))
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u + 1} (associatedStructureSheaf A σ)) (up ℤ))] :
    moduleDerivedPushforward h σ = RightDerived.Cochain.functor (modulePushforward h σ) :=
  rfl

/-- Total right derived functor of the underived composite `g⁻¹ ∘ f_*`. -/
abbrev moduleDerivedPushforward_compInverseImage :
    DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) ⥤
      DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf Y' τ)) :=
  RightDerived.Cochain.functor
    (modulePushforward f τ ⋙ associatedModuleInverseImage g τ)

/-- Total right derived functor of the underived composite `f'_* ∘ (g')⁻¹`. -/
abbrev moduleDerivedPushforward_inverseImageComp :
    DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) ⥤
      DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf Y' τ)) :=
  RightDerived.Cochain.functor
    (associatedModuleInverseImage (fibreProductSnd f g) τ ⋙
      modulePushforward (fibreProductFst f g) τ)

/-- The cochain-level unit of module pushforward. -/
abbrev modulePushforward_derivedUnit {A B : GroupoidsOver S} (h : A ⟶ B)
    (σ : StandardTopology)
    [HasSheafify (A.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasSheafify (B.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions (Sheaf (A.associatedTopology σ) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf A σ))]
    [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf B σ))]
    [HasRightDerivedFunctor (RightDerived.Cochain.toDerived (modulePushforward h σ))
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u + 1} (associatedStructureSheaf A σ)) (up ℤ))] :
    RightDerived.Cochain.toDerived (modulePushforward h σ) ⟶
      (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf A σ)) ℤ ⥤
            DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf A σ))) ⋙
        moduleDerivedPushforward h σ :=
  RightDerived.Cochain.unit (modulePushforward h σ)

/-- The cochain-level unit of the underived composite `g⁻¹ ∘ f_*`. -/
abbrev modulePushforward_compInverseImage_derivedUnit :
    RightDerived.Cochain.toDerived
        (modulePushforward f τ ⋙ associatedModuleInverseImage g τ) ⟶
      (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) ℤ ⥤
            DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf X τ))) ⋙
        moduleDerivedPushforward_compInverseImage f g τ :=
  RightDerived.Cochain.unit
    (modulePushforward f τ ⋙ associatedModuleInverseImage g τ)

/-- Homological-complex action of module pushforward, with additivity supplied explicitly. -/
abbrev modulePushforward_mapHomologicalComplex {A B : GroupoidsOver S} (h : A ⟶ B)
    (σ : StandardTopology)
    [HasSheafify (A.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasSheafify (B.associatedTopology σ) AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions (Sheaf (A.associatedTopology σ) AddCommGrpCat.{u + 1})] :
    CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf A σ)) ℤ ⥤
      CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf B σ)) ℤ :=
  (modulePushforward h σ).mapHomologicalComplex (up ℤ)

/-- The cochain-level unit for exact postcomposition of module `Rf_*` by `g⁻¹`. -/
def moduleDerivedPushforward_postcompUnit :
    modulePushforward_compInverseImage_toDerived f g τ ⟶
      (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) ℤ ⥤
            DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf X τ))) ⋙
        (moduleDerivedPushforward f τ ⋙
          (associatedModuleInverseImage g τ).mapDerivedCategory) :=
  (isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (modulePushforward f τ ⋙ associatedModuleInverseImage g τ)) (up ℤ)).symm
      (DerivedCategory.Q :
        CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf Y' τ)) ℤ ⥤
          DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf Y' τ)))).hom ≫
    (Functor.associator
        (modulePushforward_mapHomologicalComplex f τ)
        ((associatedModuleInverseImage g τ).mapHomologicalComplex (up ℤ))
        (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf Y' τ)) ℤ ⥤
            DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf Y' τ)))).hom ≫
    (isoWhiskerLeft (modulePushforward_mapHomologicalComplex f τ)
      (associatedModuleInverseImage g τ).mapDerivedCategoryFactors.symm).hom ≫
    (Functor.associator
        (modulePushforward_mapHomologicalComplex f τ)
        (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf Y τ)) ℤ ⥤
            DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf Y τ)))
        (associatedModuleInverseImage g τ).mapDerivedCategory).inv ≫
    whiskerRight (modulePushforward_derivedUnit f τ)
      (associatedModuleInverseImage g τ).mapDerivedCategory ≫
    (Functor.associator
        (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) ℤ ⥤
            DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)))
        (moduleDerivedPushforward f τ)
        (associatedModuleInverseImage g τ).mapDerivedCategory).hom

/-- The comparison from `R(f_* ⋙ g⁻¹)` to module `Rf_*` followed by exact inverse image. -/
def moduleDerivedPushforward_postcomp :
    moduleDerivedPushforward_compInverseImage f g τ ⟶
      moduleDerivedPushforward f τ ⋙
        (associatedModuleInverseImage g τ).mapDerivedCategory :=
  (moduleDerivedPushforward_compInverseImage f g τ).rightDerivedDesc
    (modulePushforward_compInverseImage_derivedUnit f g τ)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (up ℤ))
    (moduleDerivedPushforward f τ ⋙
      (associatedModuleInverseImage g τ).mapDerivedCategory)
    (moduleDerivedPushforward_postcompUnit f g τ)

/-- Exact postcomposition of module `Rf_*` by `g⁻¹` is a right-derived model of the underived
composite. -/
instance moduleDerivedPushforward_postcomp_isRightDerived :
    (moduleDerivedPushforward f τ ⋙
      (associatedModuleInverseImage g τ).mapDerivedCategory).IsRightDerivedFunctor
      (moduleDerivedPushforward_postcompUnit f g τ)
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (up ℤ)) :=
  sorry

/-- The reverse comparison from exact postcomposition of module `Rf_*` by `g⁻¹` to
`R(f_* ⋙ g⁻¹)`. -/
def moduleDerivedPushforward_postcompInv :
    moduleDerivedPushforward f τ ⋙
        (associatedModuleInverseImage g τ).mapDerivedCategory ⟶
      moduleDerivedPushforward_compInverseImage f g τ :=
  (moduleDerivedPushforward f τ ⋙
      (associatedModuleInverseImage g τ).mapDerivedCategory).rightDerivedDesc
    (moduleDerivedPushforward_postcompUnit f g τ)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (up ℤ))
    (moduleDerivedPushforward_compInverseImage f g τ)
    (modulePushforward_compInverseImage_derivedUnit f g τ)

/-- The cochain-level unit for exact precomposition of module `Rf'_*` by `(g')⁻¹`. -/
def moduleDerivedPushforward_precompUnit :
    RightDerived.Cochain.toDerived
        (associatedModuleInverseImage (fibreProductSnd f g) τ ⋙
          modulePushforward (fibreProductFst f g) τ) ⟶
      (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) ℤ ⥤
            DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf X τ))) ⋙
        ((associatedModuleInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
          moduleDerivedPushforward (fibreProductFst f g) τ) :=
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
        (modulePushforward_mapHomologicalComplex (fibreProductFst f g) τ)
        (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf Y' τ)) ℤ ⥤
            DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf Y' τ)))).hom ≫
    RightDerived.Composition.iteratedUnit
      (associatedModuleInverseImage (fibreProductSnd f g) τ).mapDerivedCategoryFactors.inv
      (modulePushforward_derivedUnit (fibreProductFst f g) τ)

/-- The comparison from `R((g')⁻¹ ⋙ f'_*)` to module `Rf'_*` after exact inverse image. -/
def moduleDerivedPushforward_precomp :
    moduleDerivedPushforward_inverseImageComp f g τ ⟶
      (associatedModuleInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
        moduleDerivedPushforward (fibreProductFst f g) τ :=
  (moduleDerivedPushforward_inverseImageComp f g τ).rightDerivedDesc
    (RightDerived.Cochain.unit
      (associatedModuleInverseImage (fibreProductSnd f g) τ ⋙
        modulePushforward (fibreProductFst f g) τ))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (up ℤ))
    ((associatedModuleInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
      moduleDerivedPushforward (fibreProductFst f g) τ)
    (moduleDerivedPushforward_precompUnit f g τ)

/-- Exact precomposition of module `Rf'_*` by `(g')⁻¹` is a right-derived model of the
underived composite, using that inverse image is exact. -/
instance moduleDerivedPushforward_precomp_isRightDerived :
    ((associatedModuleInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
      moduleDerivedPushforward (fibreProductFst f g) τ).IsRightDerivedFunctor
      (moduleDerivedPushforward_precompUnit f g τ)
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (up ℤ)) :=
  sorry

/-- The reverse comparison from exact precomposition of module `Rf'_*` by `(g')⁻¹` to
`R((g')⁻¹ ⋙ f'_*)`. -/
def moduleDerivedPushforward_precompInv :
    (associatedModuleInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
        moduleDerivedPushforward (fibreProductFst f g) τ ⟶
      moduleDerivedPushforward_inverseImageComp f g τ :=
  ((associatedModuleInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
      moduleDerivedPushforward (fibreProductFst f g) τ).rightDerivedDesc
    (moduleDerivedPushforward_precompUnit f g τ)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (up ℤ))
    (moduleDerivedPushforward_inverseImageComp f g τ)
    (RightDerived.Cochain.unit
      (associatedModuleInverseImage (fibreProductSnd f g) τ ⋙
        modulePushforward (fibreProductFst f g) τ))

/-- Derived functorial form of the underived module identification. -/
def moduleDerivedPushforward_mapNatIso :
    moduleDerivedPushforward_compInverseImage f g τ ≅
      moduleDerivedPushforward_inverseImageComp f g τ :=
  Functor.RightDerived.mapNatIso
    (DerivedCategory.Q :
      CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) ℤ ⥤
        DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (up ℤ))
    (isoWhiskerRight
      (NatIso.mapHomologicalComplex (modulePushforwardBaseChangeIso f g τ) (up ℤ))
      (DerivedCategory.Q :
        CochainComplex (SheafOfModules.{u + 1} (associatedStructureSheaf Y' τ)) ℤ ⥤
          DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf Y' τ))))

/-- The functorial derived identification `g⁻¹ Rf_* ≅ Rf'_* (g')⁻¹` on sheaves of modules,
as the composite of exact postcomposition, derived transport of the underived mate,
and exact precomposition. -/
def moduleDerivedPushforwardBaseChangeIso :
    moduleDerivedPushforward f τ ⋙
        (associatedModuleInverseImage g τ).mapDerivedCategory ≅
      (associatedModuleInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
        moduleDerivedPushforward (fibreProductFst f g) τ where
  hom :=
    moduleDerivedPushforward_postcompInv f g τ ≫
      (moduleDerivedPushforward_mapNatIso f g τ).hom ≫
      moduleDerivedPushforward_precomp f g τ
  inv :=
    moduleDerivedPushforward_precompInv f g τ ≫
      (moduleDerivedPushforward_mapNatIso f g τ).inv ≫
      moduleDerivedPushforward_postcomp f g τ
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Objectwise form of `moduleDerivedPushforwardBaseChangeIso`. -/
def moduleDerivedPushforwardBaseChangeIso_app
    (K : DerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf X τ))) :
    ((associatedModuleInverseImage g τ).mapDerivedCategory).obj
        ((moduleDerivedPushforward f τ).obj K) ≅
      (moduleDerivedPushforward (fibreProductFst f g) τ).obj
        ((associatedModuleInverseImage (fibreProductSnd f g) τ).mapDerivedCategory.obj K) :=
  (moduleDerivedPushforwardBaseChangeIso f g τ).app K

end AlgebraicGeometry.GroupoidsOver
