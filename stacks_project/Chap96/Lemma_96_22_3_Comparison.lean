/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Right
public import stacks_project.Chap96.Lemma_96_21_3_InverseImage
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import stacks_project.Chap96.Lemma_96_22_2_Comparison

/-!
# Derived comparison after representable base change

On a chosen 2-fibre product of algebraic stacks, if `f` is representable by
algebraic spaces and the base-changed target is represented by an algebraic
space, derived pushforward along `f` commutes with inverse image and
restriction to the small étale site, for abelian étale sheaves and for étale
modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape
open AlgebraicGeometry.GroupoidsOver
open CategoryTheory.Functor
open CategoryTheory.Sheaf.InternalModule
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Inverse image of abelian étale sheaves along a 1-morphism of categories
fibred in groupoids, as continuous sheaf pushforward of the cartesian total
functor at coefficient universe `u`. -/
abbrev etaleAbelianInverseImage {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    Sheaf Y.etaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.etaleTopology AddCommGrpCat.{u} :=
  (toCartesianBasedFunctor h).toFunctor.sheafPushforwardContinuous
    AddCommGrpCat.{u} X.etaleTopology Y.etaleTopology

/-- `etaleAbelianInverseImage h` is continuous sheaf pushforward of abelian groups
along the cartesian total functor. -/
theorem etaleAbelianInverseImage_eq {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    etaleAbelianInverseImage h =
      (toCartesianBasedFunctor h).toFunctor.sheafPushforwardContinuous
        AddCommGrpCat.{u} X.etaleTopology Y.etaleTopology :=
  rfl

/-- Inverse image of abelian étale sheaves is additive. -/
instance etaleAbelianInverseImage.instAdditive {X Y : GroupoidsOver S}
    (h : X ⟶ Y) : (etaleAbelianInverseImage h).Additive :=
  inferInstance

/-- Inverse image of abelian étale sheaves preserves homology. -/
instance etaleAbelianInverseImage.instPreservesHomology {X Y : GroupoidsOver S}
    (h : X ⟶ Y) : (etaleAbelianInverseImage h).PreservesHomology :=
  sorry

/-- Inverse image of abelian étale sheaves preserves finite limits. -/
instance etaleAbelianInverseImage.instPreservesFiniteLimits
    {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    PreservesFiniteLimits (etaleAbelianInverseImage h) :=
  sorry

/-- Inverse image of abelian étale sheaves preserves finite colimits. -/
instance etaleAbelianInverseImage.instPreservesFiniteColimits
    {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    PreservesFiniteColimits (etaleAbelianInverseImage h) :=
  sorry

/-- Continuous-cocontinuous adjunction `h⁻¹ ⊣ h_*` on abelian étale sheaves. -/
abbrev etaleAbelianInverseImage_adjunction {X Y : GroupoidsOver S} (h : X ⟶ Y)
    [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u},
      (toCartesianBasedFunctor h).toFunctor.op.HasPointwiseRightKanExtension P] :
    etaleAbelianInverseImage h ⊣ etaleAbelianPushforward h :=
  (toCartesianBasedFunctor h).toFunctor.sheafAdjunctionCocontinuous
    AddCommGrpCat.{u} X.etaleTopology Y.etaleTopology

/-- Inverse image along a composite 1-morphism identifies with the composite of
étale abelian inverse images. -/
def etaleAbelianInverseImage_compIso {X Y Z : GroupoidsOver S}
    (h : X ⟶ Y) (k : Y ⟶ Z) :
    etaleAbelianInverseImage (h ≫ k) ≅
      etaleAbelianInverseImage k ⋙ etaleAbelianInverseImage h :=
  (sheafPushforwardContinuousComp'
      (ObjectProperty.FullSubbicategory.toFunctor.compIso h k)
      AddCommGrpCat.{u} X.etaleTopology Y.etaleTopology Z.etaleTopology).symm

/-- `etaleAbelianInverseImage_compIso` is the continuous-pushforward comparison along
total-functor composition. -/
theorem etaleAbelianInverseImage_compIso_eq {X Y Z : GroupoidsOver S}
    (h : X ⟶ Y) (k : Y ⟶ Z) :
    etaleAbelianInverseImage_compIso h k =
      (sheafPushforwardContinuousComp'
          (ObjectProperty.FullSubbicategory.toFunctor.compIso h k)
          AddCommGrpCat.{u} X.etaleTopology Y.etaleTopology
          Z.etaleTopology).symm :=
  rfl

/-- The total functor of a 1-morphism is cocontinuous for associated étale
topologies. -/
instance toFunctor_isCocontinuous_etale {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    (toFunctor h).IsCocontinuous X.etaleTopology Y.etaleTopology :=
  CartesianBasedFunctor.inheritedTopology.isCocontinuous
    (toCartesianBasedFunctor h) (StandardTopology.etale.overTopology S)

variable {X Y Y' : GroupoidsOver S} (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The inverse-image 2-cell of the chosen 2-fibre product on abelian étale
sheaves: `g⁻¹ ∘ (f')⁻¹ ≅ f⁻¹ ∘ (g')⁻¹`. -/
def etaleAbelianInverseImage_twoFibreIso :
    etaleAbelianInverseImage g ⋙
        etaleAbelianInverseImage (fibreProductFst f g) ≅
      etaleAbelianInverseImage f ⋙
        etaleAbelianInverseImage (fibreProductSnd f g) :=
  (etaleAbelianInverseImage_compIso (fibreProductFst f g) g).symm ≪≫
    sheafPushforwardContinuousIso
        (toFunctorIso (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} g f))
        AddCommGrpCat.{u} (fibreProductApex f g).etaleTopology Y.etaleTopology ≪≫
      etaleAbelianInverseImage_compIso (fibreProductSnd f g) f

/-- `etaleAbelianInverseImage_twoFibreIso` is the composite of composition
comparisons with the 2-fibre-product 2-cell. -/
theorem etaleAbelianInverseImage_twoFibreIso_eq :
    etaleAbelianInverseImage_twoFibreIso f g =
      (etaleAbelianInverseImage_compIso (fibreProductFst f g) g).symm ≪≫
        sheafPushforwardContinuousIso
            (toFunctorIso
              (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} g f))
            AddCommGrpCat.{u} (fibreProductApex f g).etaleTopology
            Y.etaleTopology ≪≫
          etaleAbelianInverseImage_compIso (fibreProductSnd f g) f :=
  rfl

variable [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u},
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (fibreProductApex f g).totalᵒᵖ ⥤ AddCommGrpCat.{u},
    (toCartesianBasedFunctor (fibreProductFst f g)).toFunctor.op.HasPointwiseRightKanExtension P]

/-- The canonical underived comparison `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of abelian étale
sheaves, the mate of `etaleAbelianInverseImage_twoFibreIso`. -/
def etaleAbelianPushforwardBaseChangeHom :
    etaleAbelianPushforward f ⋙ etaleAbelianInverseImage g ⟶
      etaleAbelianInverseImage (fibreProductSnd f g) ⋙
        etaleAbelianPushforward (fibreProductFst f g) :=
  CategoryTheory.DerivedBaseChange.map
    (etaleAbelianInverseImage_adjunction f)
    (etaleAbelianInverseImage_adjunction (fibreProductFst f g))
    (etaleAbelianInverseImage_twoFibreIso f g)

/-- The underived étale abelian comparison is invertible. -/
instance etaleAbelianPushforwardBaseChangeHom.isIso :
    IsIso (etaleAbelianPushforwardBaseChangeHom f g) :=
  sorry

/-- The reverse underived comparison `f'_* (g')⁻¹ ⟶ g⁻¹ f_*`. -/
def etaleAbelianPushforwardBaseChangeInv :
    etaleAbelianInverseImage (fibreProductSnd f g) ⋙
        etaleAbelianPushforward (fibreProductFst f g) ⟶
      etaleAbelianPushforward f ⋙ etaleAbelianInverseImage g :=
  inv (etaleAbelianPushforwardBaseChangeHom f g)

/-- The canonical underived isomorphism `g⁻¹ f_* ≅ f'_* (g')⁻¹` of abelian étale
sheaves on the chosen 2-fibre product. -/
def etaleAbelianPushforwardBaseChangeIso :
    etaleAbelianPushforward f ⋙ etaleAbelianInverseImage g ≅
      etaleAbelianInverseImage (fibreProductSnd f g) ⋙
        etaleAbelianPushforward (fibreProductFst f g) :=
  asIso (etaleAbelianPushforwardBaseChangeHom f g)

/-- `etaleAbelianPushforwardBaseChangeIso` has forward map the mate of the
inverse-image 2-cell. -/
theorem etaleAbelianPushforwardBaseChangeIso_eq :
    (etaleAbelianPushforwardBaseChangeIso f g).hom =
      etaleAbelianPushforwardBaseChangeHom f g :=
  rfl

/-- Component of the underived étale abelian base-change isomorphism at a sheaf. -/
def etaleAbelianPushforwardBaseChangeIso_app
    (ℱ : Sheaf X.etaleTopology AddCommGrpCat.{u}) :
    (etaleAbelianInverseImage g).obj ((etaleAbelianPushforward f).obj ℱ) ≅
      (etaleAbelianPushforward (fibreProductFst f g)).obj
        ((etaleAbelianInverseImage (fibreProductSnd f g)).obj ℱ) :=
  (etaleAbelianPushforwardBaseChangeIso f g).app ℱ

variable [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.etaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y'.etaleTopology AddCommGrpCat.{u}]
variable [HasSheafify (fibreProductApex f g).etaleTopology AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf X.etaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf Y.etaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf Y'.etaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf (fibreProductApex f g).etaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf Y.etaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf Y'.etaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory
    (Sheaf (fibreProductApex f g).etaleTopology AddCommGrpCat.{u})]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (etaleAbelianPushforward f))
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleAbelianPushforward (fibreProductFst f g)))
    (HomologicalComplex.quasiIso
      (Sheaf (fibreProductApex f g).etaleTopology AddCommGrpCat.{u}) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleAbelianPushforward f ⋙ etaleAbelianInverseImage g))
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleAbelianInverseImage (fibreProductSnd f g) ⋙
        etaleAbelianPushforward (fibreProductFst f g)))
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))]

/-- The cochain-level unit for exact postcomposition of `Rf_*` by `g⁻¹`. -/
def etaleAbelianDerivedBaseChange_postcompUnit :
    RightDerived.Cochain.toDerived
        (etaleAbelianPushforward f ⋙ etaleAbelianInverseImage g) ⟶
      (DerivedCategory.Q :
          CochainComplex (Sheaf X.etaleTopology AddCommGrpCat.{u}) ℤ ⥤
            DerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{u})) ⋙
        (RightDerived.Cochain.functor (etaleAbelianPushforward f) ⋙
          (etaleAbelianInverseImage g).mapDerivedCategory) :=
  (isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (etaleAbelianPushforward f ⋙ etaleAbelianInverseImage g))
        (up ℤ)).symm
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y'.etaleTopology AddCommGrpCat.{u}) ℤ ⥤
          DerivedCategory (Sheaf Y'.etaleTopology AddCommGrpCat.{u}))).hom ≫
    (Functor.associator
        ((etaleAbelianPushforward f).mapHomologicalComplex (up ℤ))
        ((etaleAbelianInverseImage g).mapHomologicalComplex (up ℤ))
        (DerivedCategory.Q :
          CochainComplex (Sheaf Y'.etaleTopology AddCommGrpCat.{u}) ℤ ⥤
            DerivedCategory (Sheaf Y'.etaleTopology AddCommGrpCat.{u}))).hom ≫
    (isoWhiskerLeft ((etaleAbelianPushforward f).mapHomologicalComplex (up ℤ))
      (etaleAbelianInverseImage g).mapDerivedCategoryFactors.symm).hom ≫
    (Functor.associator
        ((etaleAbelianPushforward f).mapHomologicalComplex (up ℤ))
        (DerivedCategory.Q :
          CochainComplex (Sheaf Y.etaleTopology AddCommGrpCat.{u}) ℤ ⥤
            DerivedCategory (Sheaf Y.etaleTopology AddCommGrpCat.{u}))
        (etaleAbelianInverseImage g).mapDerivedCategory).inv ≫
    whiskerRight (RightDerived.Cochain.unit (etaleAbelianPushforward f))
      (etaleAbelianInverseImage g).mapDerivedCategory ≫
    (Functor.associator
        (DerivedCategory.Q :
          CochainComplex (Sheaf X.etaleTopology AddCommGrpCat.{u}) ℤ ⥤
            DerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{u}))
        (RightDerived.Cochain.functor (etaleAbelianPushforward f))
        (etaleAbelianInverseImage g).mapDerivedCategory).hom

/-- The comparison from `R(f_* ⋙ g⁻¹)` to `Rf_*` followed by exact inverse image. -/
def etaleAbelianDerivedBaseChange_postcomp :
    RightDerived.Cochain.functor
        (etaleAbelianPushforward f ⋙ etaleAbelianInverseImage g) ⟶
      RightDerived.Cochain.functor (etaleAbelianPushforward f) ⋙
        (etaleAbelianInverseImage g).mapDerivedCategory :=
  (RightDerived.Cochain.functor
      (etaleAbelianPushforward f ⋙ etaleAbelianInverseImage g)).rightDerivedDesc
    (RightDerived.Cochain.unit
      (etaleAbelianPushforward f ⋙ etaleAbelianInverseImage g))
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))
    (RightDerived.Cochain.functor (etaleAbelianPushforward f) ⋙
      (etaleAbelianInverseImage g).mapDerivedCategory)
    (etaleAbelianDerivedBaseChange_postcompUnit f g)

/-- Exact postcomposition of derived abelian étale pushforward by inverse image is
an isomorphism. -/
instance etaleAbelianDerivedBaseChange_postcomp_isIso :
    IsIso (etaleAbelianDerivedBaseChange_postcomp f g) :=
  sorry

/-- Exact postcomposition of `Rf_*` by `g⁻¹` is a right-derived model of the
underived composite. -/
instance etaleAbelianDerivedBaseChange_postcomp_isRightDerived :
    (RightDerived.Cochain.functor (etaleAbelianPushforward f) ⋙
      (etaleAbelianInverseImage g).mapDerivedCategory).IsRightDerivedFunctor
      (etaleAbelianDerivedBaseChange_postcompUnit f g)
      (HomologicalComplex.quasiIso
        (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ)) :=
  sorry

/-- The reverse comparison from exact postcomposition of `Rf_*` by `g⁻¹` to
`R(f_* ⋙ g⁻¹)`. -/
def etaleAbelianDerivedBaseChange_postcompInv :
    RightDerived.Cochain.functor (etaleAbelianPushforward f) ⋙
        (etaleAbelianInverseImage g).mapDerivedCategory ⟶
      RightDerived.Cochain.functor
        (etaleAbelianPushforward f ⋙ etaleAbelianInverseImage g) :=
  (RightDerived.Cochain.functor (etaleAbelianPushforward f) ⋙
      (etaleAbelianInverseImage g).mapDerivedCategory).rightDerivedDesc
    (etaleAbelianDerivedBaseChange_postcompUnit f g)
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))
    (RightDerived.Cochain.functor
      (etaleAbelianPushforward f ⋙ etaleAbelianInverseImage g))
    (RightDerived.Cochain.unit
      (etaleAbelianPushforward f ⋙ etaleAbelianInverseImage g))

/-- The cochain-level unit for exact precomposition of `Rf'_*` by `(g')⁻¹`. -/
def etaleAbelianDerivedBaseChange_precompUnit :
    RightDerived.Cochain.toDerived
        (etaleAbelianInverseImage (fibreProductSnd f g) ⋙
          etaleAbelianPushforward (fibreProductFst f g)) ⟶
      (DerivedCategory.Q :
          CochainComplex (Sheaf X.etaleTopology AddCommGrpCat.{u}) ℤ ⥤
            DerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{u})) ⋙
        ((etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory ⋙
          RightDerived.Cochain.functor
            (etaleAbelianPushforward (fibreProductFst f g))) :=
  (isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl
          (etaleAbelianInverseImage (fibreProductSnd f g) ⋙
            etaleAbelianPushforward (fibreProductFst f g)))
        (up ℤ)).symm
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y'.etaleTopology AddCommGrpCat.{u}) ℤ ⥤
          DerivedCategory (Sheaf Y'.etaleTopology AddCommGrpCat.{u}))).hom ≫
    (Functor.associator
        ((etaleAbelianInverseImage (fibreProductSnd f g)).mapHomologicalComplex
          (up ℤ))
        ((etaleAbelianPushforward (fibreProductFst f g)).mapHomologicalComplex
          (up ℤ))
        (DerivedCategory.Q :
          CochainComplex (Sheaf Y'.etaleTopology AddCommGrpCat.{u}) ℤ ⥤
            DerivedCategory (Sheaf Y'.etaleTopology AddCommGrpCat.{u}))).hom ≫
    RightDerived.Composition.iteratedUnit
      (etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategoryFactors.inv
      (RightDerived.Cochain.unit (etaleAbelianPushforward (fibreProductFst f g)))

/-- The comparison from `R((g')⁻¹ ⋙ f'_*)` to `Rf'_*` after exact inverse image. -/
def etaleAbelianDerivedBaseChange_precomp :
    RightDerived.Cochain.functor
        (etaleAbelianInverseImage (fibreProductSnd f g) ⋙
          etaleAbelianPushforward (fibreProductFst f g)) ⟶
      (etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory ⋙
        RightDerived.Cochain.functor
          (etaleAbelianPushforward (fibreProductFst f g)) :=
  (RightDerived.Cochain.functor
      (etaleAbelianInverseImage (fibreProductSnd f g) ⋙
        etaleAbelianPushforward (fibreProductFst f g))).rightDerivedDesc
    (RightDerived.Cochain.unit
      (etaleAbelianInverseImage (fibreProductSnd f g) ⋙
        etaleAbelianPushforward (fibreProductFst f g)))
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))
    ((etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory ⋙
      RightDerived.Cochain.functor
        (etaleAbelianPushforward (fibreProductFst f g)))
    (etaleAbelianDerivedBaseChange_precompUnit f g)

/-- Exact precomposition of `Rf'_*` by `(g')⁻¹` is a right-derived model of the
underived composite. -/
instance etaleAbelianDerivedBaseChange_precomp_isRightDerived :
    ((etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory ⋙
      RightDerived.Cochain.functor
        (etaleAbelianPushforward (fibreProductFst f g))).IsRightDerivedFunctor
      (etaleAbelianDerivedBaseChange_precompUnit f g)
      (HomologicalComplex.quasiIso
        (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ)) :=
  sorry

/-- The reverse comparison from exact precomposition of `Rf'_*` by `(g')⁻¹` to
`R((g')⁻¹ ⋙ f'_*)`. -/
def etaleAbelianDerivedBaseChange_precompInv :
    (etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory ⋙
        RightDerived.Cochain.functor
          (etaleAbelianPushforward (fibreProductFst f g)) ⟶
      RightDerived.Cochain.functor
        (etaleAbelianInverseImage (fibreProductSnd f g) ⋙
          etaleAbelianPushforward (fibreProductFst f g)) :=
  ((etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory ⋙
      RightDerived.Cochain.functor
        (etaleAbelianPushforward (fibreProductFst f g))).rightDerivedDesc
    (etaleAbelianDerivedBaseChange_precompUnit f g)
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))
    (RightDerived.Cochain.functor
      (etaleAbelianInverseImage (fibreProductSnd f g) ⋙
        etaleAbelianPushforward (fibreProductFst f g)))
    (RightDerived.Cochain.unit
      (etaleAbelianInverseImage (fibreProductSnd f g) ⋙
        etaleAbelianPushforward (fibreProductFst f g)))

/-- Derived functorial form of the underived étale abelian identification. -/
def etaleAbelianDerivedBaseChange_mapNatIso :
    RightDerived.Cochain.functor
        (etaleAbelianPushforward f ⋙ etaleAbelianInverseImage g) ≅
      RightDerived.Cochain.functor
        (etaleAbelianInverseImage (fibreProductSnd f g) ⋙
          etaleAbelianPushforward (fibreProductFst f g)) :=
  Functor.RightDerived.mapNatIso
    (DerivedCategory.Q :
      CochainComplex (Sheaf X.etaleTopology AddCommGrpCat.{u}) ℤ ⥤
        DerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{u}))
    (HomologicalComplex.quasiIso
      (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))
    (isoWhiskerRight
      (NatIso.mapHomologicalComplex
        (etaleAbelianPushforwardBaseChangeIso f g) (up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y'.etaleTopology AddCommGrpCat.{u}) ℤ ⥤
          DerivedCategory (Sheaf Y'.etaleTopology AddCommGrpCat.{u})))

/-- The functorial derived identification `g⁻¹ Rf_* ≅ Rf'_* (g')⁻¹` on abelian
étale sheaves. -/
def etaleAbelianDerivedBaseChangeIso :
    RightDerived.Cochain.functor (etaleAbelianPushforward f) ⋙
        (etaleAbelianInverseImage g).mapDerivedCategory ≅
      (etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory ⋙
        RightDerived.Cochain.functor
          (etaleAbelianPushforward (fibreProductFst f g)) where
  hom :=
    etaleAbelianDerivedBaseChange_postcompInv f g ≫
      (etaleAbelianDerivedBaseChange_mapNatIso f g).hom ≫
      etaleAbelianDerivedBaseChange_precomp f g
  inv :=
    etaleAbelianDerivedBaseChange_precompInv f g ≫
      (etaleAbelianDerivedBaseChange_mapNatIso f g).inv ≫
      etaleAbelianDerivedBaseChange_postcomp f g
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Objectwise form of `etaleAbelianDerivedBaseChangeIso`. -/
def etaleAbelianDerivedBaseChangeIso_app
    (K : DerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{u})) :
    ((etaleAbelianInverseImage g).mapDerivedCategory).obj
        ((RightDerived.Cochain.functor (etaleAbelianPushforward f)).obj K) ≅
      (RightDerived.Cochain.functor
          (etaleAbelianPushforward (fibreProductFst f g))).obj
        ((etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory.obj
          K) :=
  (etaleAbelianDerivedBaseChangeIso f g).app K

variable {F' G' : AlgebraicSpace S}
variable (eX' : F'.toGroupoids ≌ fibreProductApex f g)
variable (eY' : G'.toGroupoids ≌ Y')
variable (α : (fibreProductFst f g ≫ eY'.symm.hom) ≅
    (eX'.symm.hom ≫
      AlgebraicSpace.toGroupoids.map
        (inducedHom eX' eY' (fibreProductFst f g))))
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology F') AddCommGrpCat.{u}]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology G') AddCommGrpCat.{u}]
variable [HasSheafify (AlgebraicSpace.spacesEtaleTopology F') AddCommGrpCat.{u}]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology F') (Type u)]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology G') (Type u)]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F')ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F' (fibreProductApex f g) eX').op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G')ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor G' Y' eY').op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F')ᵒᵖ ⥤ RingCat.{u},
    (smallEtaleFunctor F' (fibreProductApex f g) eX').op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G')ᵒᵖ ⥤ RingCat.{u},
    (smallEtaleFunctor G' Y' eY').op.HasPointwiseRightKanExtension P]
variable [(forget RingCat.{u}).PreservesRightKanExtensions
    (smallEtaleFunctor F' (fibreProductApex f g) eX').op]
variable [(forget RingCat.{u}).PreservesRightKanExtensions
    (smallEtaleFunctor G' Y' eY').op]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F')ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F' (fibreProductApex f g) eX').op.HasLeftKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G')ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor G' Y' eY').op.HasLeftKanExtension P]
variable [∀ P : (fibreProductApex f g).totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor (fibreProductFst f g)).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : F'.toGroupoids.totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor
        (AlgebraicSpace.toGroupoids.map
          (inducedHom eX' eY' (fibreProductFst f g)))).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F')ᵒᵖ ⥤ Type u,
    (AlgebraicSpace.smallEtaleInclusion F').op.HasPointwiseRightKanExtension P]
variable [∀ P : F'.toGroupoids.totalᵒᵖ ⥤ AddCommGrpCat.{u},
    (toCartesianBasedFunctor
        (AlgebraicSpace.toGroupoids.map
          (inducedHom eX' eY' (fibreProductFst f g)))).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F')ᵒᵖ ⥤ AddCommGrpCat.{u},
    (AlgebraicSpace.smallEtaleInclusion F').op.HasPointwiseRightKanExtension P]
variable [(forget AddCommGrpCat.{u}).PreservesRightKanExtensions
    (toCartesianBasedFunctor (fibreProductFst f g)).toFunctor.op]
variable [(forget AddCommGrpCat.{u}).PreservesRightKanExtensions
    (toCartesianBasedFunctor
        (AlgebraicSpace.toGroupoids.map
          (inducedHom eX' eY' (fibreProductFst f g)))).toFunctor.op]
variable [(forget AddCommGrpCat.{u}).PreservesRightKanExtensions
    (AlgebraicSpace.smallEtaleInclusion F').op]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf (AlgebraicSpace.smallEtaleTopology F') AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf (AlgebraicSpace.smallEtaleTopology G') AddCommGrpCat.{u})]
variable [HasDerivedCategory
    (Sheaf (AlgebraicSpace.smallEtaleTopology F') AddCommGrpCat.{u})]
variable [HasDerivedCategory
    (Sheaf (AlgebraicSpace.smallEtaleTopology G') AddCommGrpCat.{u})]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (smallAbelianPushforward (inducedHom eX' eY' (fibreProductFst f g))))
    (HomologicalComplex.quasiIso
      (Sheaf (AlgebraicSpace.smallEtaleTopology F') AddCommGrpCat.{u}) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleAbelianPushforward (fibreProductFst f g) ⋙ restrictAbelian eY'))
    (HomologicalComplex.quasiIso
      (Sheaf (fibreProductApex f g).etaleTopology AddCommGrpCat.{u}) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (restrictAbelian eX' ⋙
        smallAbelianPushforward (inducedHom eX' eY' (fibreProductFst f g))))
    (HomologicalComplex.quasiIso
      (Sheaf (fibreProductApex f g).etaleTopology AddCommGrpCat.{u}) (up ℤ))]
variable [X.etaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Y.etaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Y'.etaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [(fibreProductApex f g).etaleTopology.WEqualsLocallyBijective
    AddCommGrpCat.{u}]
variable [(AlgebraicSpace.smallEtaleTopology F').WEqualsLocallyBijective
    AddCommGrpCat.{u}]
variable [(AlgebraicSpace.smallEtaleTopology G').WEqualsLocallyBijective
    AddCommGrpCat.{u}]

/-- The functorial derived identification
`g⁻¹ (Rf_* -)|_{G'_étale} ≅ Rf'_small,* (((g')⁻¹ -)|_{F'_étale})` on abelian
étale sheaves. -/
def compareRepresentableMorphismCohomologyIso :
    RightDerived.Cochain.functor (etaleAbelianPushforward f) ⋙
        (etaleAbelianInverseImage g).mapDerivedCategory ⋙
          (restrictAbelian eY').mapDerivedCategory ≅
      (etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory ⋙
        (restrictAbelian eX').mapDerivedCategory ⋙
          RightDerived.Cochain.functor
            (smallAbelianPushforward
              (inducedHom eX' eY' (fibreProductFst f g))) :=
  (Functor.associator
      (RightDerived.Cochain.functor (etaleAbelianPushforward f))
      (etaleAbelianInverseImage g).mapDerivedCategory
      (restrictAbelian eY').mapDerivedCategory) ≪≫
    isoWhiskerRight (etaleAbelianDerivedBaseChangeIso f g)
      (restrictAbelian eY').mapDerivedCategory ≪≫
    (Functor.associator
        (etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory
        (RightDerived.Cochain.functor
          (etaleAbelianPushforward (fibreProductFst f g)))
        (restrictAbelian eY').mapDerivedCategory).symm ≪≫
    isoWhiskerLeft
      (etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory
      (compareMorphismCohomologyIso eX' eY' (fibreProductFst f g) α) ≪≫
    Functor.associator
      (etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory
      (restrictAbelian eX').mapDerivedCategory
      (RightDerived.Cochain.functor
        (smallAbelianPushforward (inducedHom eX' eY' (fibreProductFst f g))))

/-- Objectwise form of `compareRepresentableMorphismCohomologyIso`. -/
def compareRepresentableMorphismCohomology_spec
    (K : DerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{u})) :
    ((restrictAbelian eY').mapDerivedCategory).obj
        ((etaleAbelianInverseImage g).mapDerivedCategory.obj
          ((RightDerived.Cochain.functor (etaleAbelianPushforward f)).obj K)) ≅
      (RightDerived.Cochain.functor
          (smallAbelianPushforward
            (inducedHom eX' eY' (fibreProductFst f g)))).obj
        ((restrictAbelian eX').mapDerivedCategory.obj
          ((etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory.obj
            K)) :=
  (compareRepresentableMorphismCohomologyIso f g eX' eY' α).app K

/-- Inverse image of étale modules along a 1-morphism, as module pullback of the
induced morphism of étale ringed topoi. -/
abbrev etaleModulePullback {A B : GroupoidsOver S} (h : A ⟶ B) :
    SheafOfModules.{u} (etaleRingedSite B).structureSheaf ⥤
      SheafOfModules.{u} (etaleRingedSite A).structureSheaf :=
  (etaleRingedToposHom h).modulePullback

/-- `etaleModulePullback h` is module pullback of `etaleRingedToposHom h`. -/
theorem etaleModulePullback_eq {A B : GroupoidsOver S} (h : A ⟶ B) :
    etaleModulePullback h = (etaleRingedToposHom h).modulePullback :=
  rfl

/-- Inverse image of étale modules is additive. -/
instance etaleModulePullback.instAdditive {A B : GroupoidsOver S} (h : A ⟶ B) :
    (etaleModulePullback h).Additive :=
  sorry

/-- Inverse image of étale modules preserves homology. -/
instance etaleModulePullback.instPreservesHomology {A B : GroupoidsOver S}
    (h : A ⟶ B) : (etaleModulePullback h).PreservesHomology :=
  sorry

/-- Inverse image of étale modules preserves finite limits. -/
instance etaleModulePullback.instPreservesFiniteLimits {A B : GroupoidsOver S}
    (h : A ⟶ B) : PreservesFiniteLimits (etaleModulePullback h) :=
  sorry

/-- Inverse image of étale modules preserves finite colimits. -/
instance etaleModulePullback.instPreservesFiniteColimits
    {A B : GroupoidsOver S} (h : A ⟶ B) :
    PreservesFiniteColimits (etaleModulePullback h) :=
  sorry

/-- The adjunction `h⁻¹ ⊣ h_*` on étale modules. -/
abbrev etaleModulePullback_adjunction {A B : GroupoidsOver S} (h : A ⟶ B) :
    etaleModulePullback h ⊣ etaleModuleDirectImage h :=
  (etaleRingedToposHom h).moduleAdjunction

variable [∀ P : X.totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : Y'.totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor g).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (fibreProductApex f g).totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor (fibreProductSnd f g)).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (fibreProductApex f g).totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor (fibreProductFst f g ≫ g)).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (fibreProductApex f g).totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor (fibreProductSnd f g ≫ f)).toFunctor.op.HasPointwiseRightKanExtension P]

/-- Forgetting module structure identifies composite étale module direct images with
composite type-valued cocontinuous pushforwards. -/
def etaleModuleDirectImage_compForget {A B C : GroupoidsOver S}
    (h : A ⟶ B) (k : B ⟶ C)
    [∀ P : A.totalᵒᵖ ⥤ Type u,
      (toCartesianBasedFunctor h).toFunctor.op.HasPointwiseRightKanExtension P]
    [∀ P : B.totalᵒᵖ ⥤ Type u,
      (toCartesianBasedFunctor k).toFunctor.op.HasPointwiseRightKanExtension P]
    [∀ P : A.totalᵒᵖ ⥤ Type u,
      (toCartesianBasedFunctor (h ≫ k)).toFunctor.op.HasPointwiseRightKanExtension P]
    (M : SheafOfModules.{u} (etaleRingedSite A).structureSheaf) :
    (ToInternal.underlying (etaleRingedSite C).structureSheaf).obj
      ((etaleModuleDirectImage k).obj ((etaleModuleDirectImage h).obj M)) ≅
      (ToInternal.underlying (etaleRingedSite C).structureSheaf).obj
        ((etaleModuleDirectImage (h ≫ k)).obj M) :=
  (RingedSite.ToposHom.ModulePushforward.forgetIso (etaleRingedToposHom k)).app
      ((etaleModuleDirectImage h).obj M) ≪≫
    (etaleRingedToposHom k).toTopos.pushforward.mapIso
      ((RingedSite.ToposHom.ModulePushforward.forgetIso
          (etaleRingedToposHom h)).app M) ≪≫
    (sheafPushforwardCocontinuousComp'
        A.etaleTopology B.etaleTopology C.etaleTopology
        (toCartesianBasedFunctor h).toFunctor
        (toCartesianBasedFunctor k).toFunctor
        (ObjectProperty.FullSubbicategory.toFunctor.compIso h k)).app
      ((ToInternal.underlying (etaleRingedSite A).structureSheaf).obj M) ≪≫
    ((RingedSite.ToposHom.ModulePushforward.forgetIso
        (etaleRingedToposHom (h ≫ k))).app M).symm

/-- Direct image of étale modules along a composite is iterated direct image. -/
def etaleModuleDirectImage_compIso {A B C : GroupoidsOver S}
    (h : A ⟶ B) (k : B ⟶ C)
    [∀ P : A.totalᵒᵖ ⥤ Type u,
      (toCartesianBasedFunctor h).toFunctor.op.HasPointwiseRightKanExtension P]
    [∀ P : B.totalᵒᵖ ⥤ Type u,
      (toCartesianBasedFunctor k).toFunctor.op.HasPointwiseRightKanExtension P]
    [∀ P : A.totalᵒᵖ ⥤ Type u,
      (toCartesianBasedFunctor (h ≫ k)).toFunctor.op.HasPointwiseRightKanExtension P] :
    etaleModuleDirectImage h ⋙ etaleModuleDirectImage k ≅
      etaleModuleDirectImage (h ≫ k) :=
  NatIso.ofComponents
    (fun M ↦
      { hom := homOfUnderlying (etaleRingedSite C).structureSheaf
          (etaleModuleDirectImage_compForget h k M).hom sorry sorry
        inv := homOfUnderlying (etaleRingedSite C).structureSheaf
          (etaleModuleDirectImage_compForget h k M).inv sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Forgetting module structure identifies étale module direct images along isomorphic
1-morphisms with the corresponding type-valued cocontinuous pushforwards. -/
def etaleModuleDirectImage_isoForget {A B : GroupoidsOver S} {h₁ h₂ : A ⟶ B}
    (e : h₁ ≅ h₂)
    [∀ P : A.totalᵒᵖ ⥤ Type u,
      (toCartesianBasedFunctor h₁).toFunctor.op.HasPointwiseRightKanExtension P]
    [∀ P : A.totalᵒᵖ ⥤ Type u,
      (toCartesianBasedFunctor h₂).toFunctor.op.HasPointwiseRightKanExtension P]
    (M : SheafOfModules.{u} (etaleRingedSite A).structureSheaf) :
    (ToInternal.underlying (etaleRingedSite B).structureSheaf).obj
      ((etaleModuleDirectImage h₁).obj M) ≅
      (ToInternal.underlying (etaleRingedSite B).structureSheaf).obj
        ((etaleModuleDirectImage h₂).obj M) :=
  (RingedSite.ToposHom.ModulePushforward.forgetIso (etaleRingedToposHom h₁)).app M ≪≫
    (sheafPushforwardCocontinuousIso
        A.etaleTopology B.etaleTopology
        (toCartesianBasedFunctor h₁).toFunctor (toFunctorIso e)).app
      ((ToInternal.underlying (etaleRingedSite A).structureSheaf).obj M) ≪≫
    ((RingedSite.ToposHom.ModulePushforward.forgetIso
        (etaleRingedToposHom h₂)).app M).symm

/-- A 2-isomorphism of 1-morphisms induces an isomorphism of étale module direct
images. -/
def etaleModuleDirectImage_iso {A B : GroupoidsOver S} {h₁ h₂ : A ⟶ B}
    (e : h₁ ≅ h₂)
    [∀ P : A.totalᵒᵖ ⥤ Type u,
      (toCartesianBasedFunctor h₁).toFunctor.op.HasPointwiseRightKanExtension P]
    [∀ P : A.totalᵒᵖ ⥤ Type u,
      (toCartesianBasedFunctor h₂).toFunctor.op.HasPointwiseRightKanExtension P] :
    etaleModuleDirectImage h₁ ≅ etaleModuleDirectImage h₂ :=
  NatIso.ofComponents
    (fun M ↦
      { hom := homOfUnderlying (etaleRingedSite B).structureSheaf
          (etaleModuleDirectImage_isoForget e M).hom sorry sorry
        inv := homOfUnderlying (etaleRingedSite B).structureSheaf
          (etaleModuleDirectImage_isoForget e M).inv sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Inverse image along a composite 1-morphism identifies with the composite of
étale module inverse images. -/
def etaleModulePullback_compIso {A B C : GroupoidsOver S}
    (h : A ⟶ B) (k : B ⟶ C)
    [∀ P : A.totalᵒᵖ ⥤ Type u,
      (toCartesianBasedFunctor h).toFunctor.op.HasPointwiseRightKanExtension P]
    [∀ P : B.totalᵒᵖ ⥤ Type u,
      (toCartesianBasedFunctor k).toFunctor.op.HasPointwiseRightKanExtension P]
    [∀ P : A.totalᵒᵖ ⥤ Type u,
      (toCartesianBasedFunctor (h ≫ k)).toFunctor.op.HasPointwiseRightKanExtension P] :
    etaleModulePullback k ⋙ etaleModulePullback h ≅
      etaleModulePullback (h ≫ k) :=
  ((etaleRingedToposHom k).moduleAdjunction.comp
      (etaleRingedToposHom h).moduleAdjunction).leftAdjointUniq
    ((etaleRingedToposHom (h ≫ k)).moduleAdjunction.ofNatIsoRight
      (etaleModuleDirectImage_compIso h k).symm)

/-- A 2-isomorphism of 1-morphisms induces an isomorphism of étale module
inverse images. -/
def etaleModulePullback_iso {A B : GroupoidsOver S} {h₁ h₂ : A ⟶ B}
    (e : h₁ ≅ h₂)
    [∀ P : A.totalᵒᵖ ⥤ Type u,
      (toCartesianBasedFunctor h₁).toFunctor.op.HasPointwiseRightKanExtension P]
    [∀ P : A.totalᵒᵖ ⥤ Type u,
      (toCartesianBasedFunctor h₂).toFunctor.op.HasPointwiseRightKanExtension P] :
    etaleModulePullback h₁ ≅ etaleModulePullback h₂ :=
  (etaleRingedToposHom h₁).moduleAdjunction.leftAdjointUniq
    ((etaleRingedToposHom h₂).moduleAdjunction.ofNatIsoRight
      (etaleModuleDirectImage_iso e).symm)

/-- The inverse-image 2-cell of the chosen 2-fibre product on étale modules:
`g⁻¹ ∘ (f')⁻¹ ≅ f⁻¹ ∘ (g')⁻¹`. -/
def etaleModulePullback_twoFibreIso :
    etaleModulePullback g ⋙ etaleModulePullback (fibreProductFst f g) ≅
      etaleModulePullback f ⋙ etaleModulePullback (fibreProductSnd f g) :=
  etaleModulePullback_compIso (fibreProductFst f g) g ≪≫
    etaleModulePullback_iso
      (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} g f) ≪≫
    (etaleModulePullback_compIso (fibreProductSnd f g) f).symm

/-- The canonical underived comparison `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of étale modules,
the mate of `etaleModulePullback_twoFibreIso`. -/
def etaleModulePushforwardBaseChangeHom :
    etaleModuleDirectImage f ⋙ etaleModulePullback g ⟶
      etaleModulePullback (fibreProductSnd f g) ⋙
        etaleModuleDirectImage (fibreProductFst f g) :=
  CategoryTheory.DerivedBaseChange.map
    (etaleModulePullback_adjunction f)
    (etaleModulePullback_adjunction (fibreProductFst f g))
    (etaleModulePullback_twoFibreIso f g)

/-- The underived étale module comparison is invertible. -/
instance etaleModulePushforwardBaseChangeHom.isIso :
    IsIso (etaleModulePushforwardBaseChangeHom f g) :=
  sorry

/-- The canonical underived isomorphism `g⁻¹ f_* ≅ f'_* (g')⁻¹` of étale modules
on the chosen 2-fibre product. -/
def etaleModulePushforwardBaseChangeIso :
    etaleModuleDirectImage f ⋙ etaleModulePullback g ≅
      etaleModulePullback (fibreProductSnd f g) ⋙
        etaleModuleDirectImage (fibreProductFst f g) :=
  asIso (etaleModulePushforwardBaseChangeHom f g)

/-- Component of the underived étale module base-change isomorphism. -/
def etaleModulePushforwardBaseChangeIso_app
    (ℳ : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    (etaleModulePullback g).obj ((etaleModuleDirectImage f).obj ℳ) ≅
      (etaleModuleDirectImage (fibreProductFst f g)).obj
        ((etaleModulePullback (fibreProductSnd f g)).obj ℳ) :=
  (etaleModulePushforwardBaseChangeIso f g).app ℳ

variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (etaleRingedSite X).structureSheaf)]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (etaleRingedSite Y).structureSheaf)]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf)]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (etaleRingedSite (fibreProductApex f g)).structureSheaf)]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (AlgebraicSpace.ringedSite F').structureSheaf)]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (AlgebraicSpace.ringedSite G').structureSheaf)]
variable [HasDerivedCategory
    (SheafOfModules.{u} (etaleRingedSite X).structureSheaf)]
variable [HasDerivedCategory
    (SheafOfModules.{u} (etaleRingedSite Y).structureSheaf)]
variable [HasDerivedCategory
    (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf)]
variable [HasDerivedCategory
    (SheafOfModules.{u} (etaleRingedSite (fibreProductApex f g)).structureSheaf)]
variable [HasDerivedCategory
    (SheafOfModules.{u} (AlgebraicSpace.ringedSite F').structureSheaf)]
variable [HasDerivedCategory
    (SheafOfModules.{u} (AlgebraicSpace.ringedSite G').structureSheaf)]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (etaleModuleDirectImage f))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleModuleDirectImage (fibreProductFst f g)))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite (fibreProductApex f g)).structureSheaf)
      (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleModuleDirectImage f ⋙ etaleModulePullback g))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleModulePullback (fibreProductSnd f g) ⋙
        etaleModuleDirectImage (fibreProductFst f g)))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (AlgebraicSpace.ringedToposHom
        (inducedHom eX' eY' (fibreProductFst f g))).modulePushforward)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (AlgebraicSpace.ringedSite F').structureSheaf) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleModuleDirectImage (fibreProductFst f g) ⋙
        (piToposHom G' Y' eY').modulePushforward))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite (fibreProductApex f g)).structureSheaf)
      (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((piToposHom F' (fibreProductApex f g) eX').modulePushforward ⋙
        (AlgebraicSpace.ringedToposHom
          (inducedHom eX' eY' (fibreProductFst f g))).modulePushforward))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite (fibreProductApex f g)).structureSheaf)
      (up ℤ))]

/-- The cochain-level unit for exact postcomposition of module `Rf_*` by `g⁻¹`. -/
def etaleModuleDerivedBaseChange_postcompUnit :
    RightDerived.Cochain.toDerived
        (etaleModuleDirectImage f ⋙ etaleModulePullback g) ⟶
      (DerivedCategory.Q :
          CochainComplex
            (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) ℤ ⥤
            DerivedCategory
              (SheafOfModules.{u} (etaleRingedSite X).structureSheaf)) ⋙
        (RightDerived.Cochain.functor (etaleModuleDirectImage f) ⋙
          (etaleModulePullback g).mapDerivedCategory) :=
  (isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (etaleModuleDirectImage f ⋙ etaleModulePullback g))
        (up ℤ)).symm
      (DerivedCategory.Q :
        CochainComplex
          (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf) ℤ ⥤
          DerivedCategory
            (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf))).hom ≫
    (Functor.associator
        ((etaleModuleDirectImage f).mapHomologicalComplex (up ℤ))
        ((etaleModulePullback g).mapHomologicalComplex (up ℤ))
        (DerivedCategory.Q :
          CochainComplex
            (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf) ℤ ⥤
            DerivedCategory
              (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf))).hom ≫
    (isoWhiskerLeft ((etaleModuleDirectImage f).mapHomologicalComplex (up ℤ))
      (etaleModulePullback g).mapDerivedCategoryFactors.symm).hom ≫
    (Functor.associator
        ((etaleModuleDirectImage f).mapHomologicalComplex (up ℤ))
        (DerivedCategory.Q :
          CochainComplex
            (SheafOfModules.{u} (etaleRingedSite Y).structureSheaf) ℤ ⥤
            DerivedCategory
              (SheafOfModules.{u} (etaleRingedSite Y).structureSheaf))
        (etaleModulePullback g).mapDerivedCategory).inv ≫
    whiskerRight (RightDerived.Cochain.unit (etaleModuleDirectImage f))
      (etaleModulePullback g).mapDerivedCategory ≫
    (Functor.associator
        (DerivedCategory.Q :
          CochainComplex
            (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) ℤ ⥤
            DerivedCategory
              (SheafOfModules.{u} (etaleRingedSite X).structureSheaf))
        (RightDerived.Cochain.functor (etaleModuleDirectImage f))
        (etaleModulePullback g).mapDerivedCategory).hom

/-- The comparison from `R(f_* ⋙ g⁻¹)` to module `Rf_*` followed by exact inverse
image. -/
def etaleModuleDerivedBaseChange_postcomp :
    RightDerived.Cochain.functor
        (etaleModuleDirectImage f ⋙ etaleModulePullback g) ⟶
      RightDerived.Cochain.functor (etaleModuleDirectImage f) ⋙
        (etaleModulePullback g).mapDerivedCategory :=
  (RightDerived.Cochain.functor
      (etaleModuleDirectImage f ⋙ etaleModulePullback g)).rightDerivedDesc
    (RightDerived.Cochain.unit
      (etaleModuleDirectImage f ⋙ etaleModulePullback g))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))
    (RightDerived.Cochain.functor (etaleModuleDirectImage f) ⋙
      (etaleModulePullback g).mapDerivedCategory)
    (etaleModuleDerivedBaseChange_postcompUnit f g)

/-- Exact postcomposition of module `Rf_*` by `g⁻¹` is a right-derived model of
the underived composite. -/
instance etaleModuleDerivedBaseChange_postcomp_isRightDerived :
    (RightDerived.Cochain.functor (etaleModuleDirectImage f) ⋙
      (etaleModulePullback g).mapDerivedCategory).IsRightDerivedFunctor
      (etaleModuleDerivedBaseChange_postcompUnit f g)
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ)) :=
  sorry

/-- The reverse comparison from exact postcomposition of module `Rf_*` by `g⁻¹`
to `R(f_* ⋙ g⁻¹)`. -/
def etaleModuleDerivedBaseChange_postcompInv :
    RightDerived.Cochain.functor (etaleModuleDirectImage f) ⋙
        (etaleModulePullback g).mapDerivedCategory ⟶
      RightDerived.Cochain.functor
        (etaleModuleDirectImage f ⋙ etaleModulePullback g) :=
  (RightDerived.Cochain.functor (etaleModuleDirectImage f) ⋙
      (etaleModulePullback g).mapDerivedCategory).rightDerivedDesc
    (etaleModuleDerivedBaseChange_postcompUnit f g)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))
    (RightDerived.Cochain.functor
      (etaleModuleDirectImage f ⋙ etaleModulePullback g))
    (RightDerived.Cochain.unit
      (etaleModuleDirectImage f ⋙ etaleModulePullback g))

/-- The cochain-level unit for exact precomposition of module `Rf'_*` by
`(g')⁻¹`. -/
def etaleModuleDerivedBaseChange_precompUnit :
    RightDerived.Cochain.toDerived
        (etaleModulePullback (fibreProductSnd f g) ⋙
          etaleModuleDirectImage (fibreProductFst f g)) ⟶
      (DerivedCategory.Q :
          CochainComplex
            (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) ℤ ⥤
            DerivedCategory
              (SheafOfModules.{u} (etaleRingedSite X).structureSheaf)) ⋙
        ((etaleModulePullback (fibreProductSnd f g)).mapDerivedCategory ⋙
          RightDerived.Cochain.functor
            (etaleModuleDirectImage (fibreProductFst f g))) :=
  (isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl
          (etaleModulePullback (fibreProductSnd f g) ⋙
            etaleModuleDirectImage (fibreProductFst f g)))
        (up ℤ)).symm
      (DerivedCategory.Q :
        CochainComplex
          (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf) ℤ ⥤
          DerivedCategory
            (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf))).hom ≫
    (Functor.associator
        ((etaleModulePullback (fibreProductSnd f g)).mapHomologicalComplex
          (up ℤ))
        ((etaleModuleDirectImage (fibreProductFst f g)).mapHomologicalComplex
          (up ℤ))
        (DerivedCategory.Q :
          CochainComplex
            (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf) ℤ ⥤
            DerivedCategory
              (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf))).hom ≫
    RightDerived.Composition.iteratedUnit
      (etaleModulePullback (fibreProductSnd f g)).mapDerivedCategoryFactors.inv
      (RightDerived.Cochain.unit
        (etaleModuleDirectImage (fibreProductFst f g)))

/-- The comparison from `R((g')⁻¹ ⋙ f'_*)` to module `Rf'_*` after exact inverse
image. -/
def etaleModuleDerivedBaseChange_precomp :
    RightDerived.Cochain.functor
        (etaleModulePullback (fibreProductSnd f g) ⋙
          etaleModuleDirectImage (fibreProductFst f g)) ⟶
      (etaleModulePullback (fibreProductSnd f g)).mapDerivedCategory ⋙
        RightDerived.Cochain.functor
          (etaleModuleDirectImage (fibreProductFst f g)) :=
  (RightDerived.Cochain.functor
      (etaleModulePullback (fibreProductSnd f g) ⋙
        etaleModuleDirectImage (fibreProductFst f g))).rightDerivedDesc
    (RightDerived.Cochain.unit
      (etaleModulePullback (fibreProductSnd f g) ⋙
        etaleModuleDirectImage (fibreProductFst f g)))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))
    ((etaleModulePullback (fibreProductSnd f g)).mapDerivedCategory ⋙
      RightDerived.Cochain.functor
        (etaleModuleDirectImage (fibreProductFst f g)))
    (etaleModuleDerivedBaseChange_precompUnit f g)

/-- Exact precomposition of module `Rf'_*` by `(g')⁻¹` is a right-derived model
of the underived composite. -/
instance etaleModuleDerivedBaseChange_precomp_isRightDerived :
    ((etaleModulePullback (fibreProductSnd f g)).mapDerivedCategory ⋙
      RightDerived.Cochain.functor
        (etaleModuleDirectImage (fibreProductFst f g))).IsRightDerivedFunctor
      (etaleModuleDerivedBaseChange_precompUnit f g)
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ)) :=
  sorry

/-- The reverse comparison from exact precomposition of module `Rf'_*` by
`(g')⁻¹` to `R((g')⁻¹ ⋙ f'_*)`. -/
def etaleModuleDerivedBaseChange_precompInv :
    (etaleModulePullback (fibreProductSnd f g)).mapDerivedCategory ⋙
        RightDerived.Cochain.functor
          (etaleModuleDirectImage (fibreProductFst f g)) ⟶
      RightDerived.Cochain.functor
        (etaleModulePullback (fibreProductSnd f g) ⋙
          etaleModuleDirectImage (fibreProductFst f g)) :=
  ((etaleModulePullback (fibreProductSnd f g)).mapDerivedCategory ⋙
      RightDerived.Cochain.functor
        (etaleModuleDirectImage (fibreProductFst f g))).rightDerivedDesc
    (etaleModuleDerivedBaseChange_precompUnit f g)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))
    (RightDerived.Cochain.functor
      (etaleModulePullback (fibreProductSnd f g) ⋙
        etaleModuleDirectImage (fibreProductFst f g)))
    (RightDerived.Cochain.unit
      (etaleModulePullback (fibreProductSnd f g) ⋙
        etaleModuleDirectImage (fibreProductFst f g)))

/-- Derived functorial form of the underived étale module identification. -/
def etaleModuleDerivedBaseChange_mapNatIso :
    RightDerived.Cochain.functor
        (etaleModuleDirectImage f ⋙ etaleModulePullback g) ≅
      RightDerived.Cochain.functor
        (etaleModulePullback (fibreProductSnd f g) ⋙
          etaleModuleDirectImage (fibreProductFst f g)) :=
  Functor.RightDerived.mapNatIso
    (DerivedCategory.Q :
      CochainComplex (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) ℤ ⥤
        DerivedCategory
          (SheafOfModules.{u} (etaleRingedSite X).structureSheaf))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))
    (isoWhiskerRight
      (NatIso.mapHomologicalComplex
        (etaleModulePushforwardBaseChangeIso f g) (up ℤ))
      (DerivedCategory.Q :
        CochainComplex
          (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf) ℤ ⥤
          DerivedCategory
            (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf)))

/-- The functorial derived identification `g⁻¹ Rf_* ≅ Rf'_* (g')⁻¹` on étale
modules. -/
def etaleModuleDerivedBaseChangeIso :
    RightDerived.Cochain.functor (etaleModuleDirectImage f) ⋙
        (etaleModulePullback g).mapDerivedCategory ≅
      (etaleModulePullback (fibreProductSnd f g)).mapDerivedCategory ⋙
        RightDerived.Cochain.functor
          (etaleModuleDirectImage (fibreProductFst f g)) where
  hom :=
    etaleModuleDerivedBaseChange_postcompInv f g ≫
      (etaleModuleDerivedBaseChange_mapNatIso f g).hom ≫
      etaleModuleDerivedBaseChange_precomp f g
  inv :=
    etaleModuleDerivedBaseChange_precompInv f g ≫
      (etaleModuleDerivedBaseChange_mapNatIso f g).inv ≫
      etaleModuleDerivedBaseChange_postcomp f g
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The functorial derived identification
`g⁻¹ (Rf_* -)|_{G'_étale} ≅ Rf'_small,* (((g')⁻¹ -)|_{F'_étale})` on étale
modules. -/
def compareRepresentableMorphismCohomology_modulesIso :
    RightDerived.Cochain.functor (etaleModuleDirectImage f) ⋙
        (etaleModulePullback g).mapDerivedCategory ⋙
          ((piToposHom G' Y' eY').modulePushforward).mapDerivedCategory ≅
      (etaleModulePullback (fibreProductSnd f g)).mapDerivedCategory ⋙
        ((piToposHom F' (fibreProductApex f g) eX').modulePushforward).mapDerivedCategory ⋙
          RightDerived.Cochain.functor
            (AlgebraicSpace.ringedToposHom
              (inducedHom eX' eY' (fibreProductFst f g))).modulePushforward :=
  (Functor.associator
      (RightDerived.Cochain.functor (etaleModuleDirectImage f))
      (etaleModulePullback g).mapDerivedCategory
      ((piToposHom G' Y' eY').modulePushforward).mapDerivedCategory) ≪≫
    isoWhiskerRight (etaleModuleDerivedBaseChangeIso f g)
      ((piToposHom G' Y' eY').modulePushforward).mapDerivedCategory ≪≫
    (Functor.associator
        (etaleModulePullback (fibreProductSnd f g)).mapDerivedCategory
        (RightDerived.Cochain.functor
          (etaleModuleDirectImage (fibreProductFst f g)))
        ((piToposHom G' Y' eY').modulePushforward).mapDerivedCategory).symm ≪≫
    isoWhiskerLeft
      (etaleModulePullback (fibreProductSnd f g)).mapDerivedCategory
      (compareMorphismCohomology_modulesIso eX' eY' (fibreProductFst f g) α) ≪≫
    Functor.associator
      (etaleModulePullback (fibreProductSnd f g)).mapDerivedCategory
      ((piToposHom F' (fibreProductApex f g) eX').modulePushforward).mapDerivedCategory
      (RightDerived.Cochain.functor
        (AlgebraicSpace.ringedToposHom
          (inducedHom eX' eY' (fibreProductFst f g))).modulePushforward)

/-- Objectwise form of `compareRepresentableMorphismCohomology_modulesIso`. -/
def compareRepresentableMorphismCohomology_modules_spec
    (K : DerivedCategory
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf)) :
    (((piToposHom G' Y' eY').modulePushforward).mapDerivedCategory).obj
        ((etaleModulePullback g).mapDerivedCategory.obj
          ((RightDerived.Cochain.functor (etaleModuleDirectImage f)).obj K)) ≅
      (RightDerived.Cochain.functor
          (AlgebraicSpace.ringedToposHom
            (inducedHom eX' eY' (fibreProductFst f g))).modulePushforward).obj
        ((((piToposHom F' (fibreProductApex f g) eX').modulePushforward).mapDerivedCategory).obj
          ((etaleModulePullback (fibreProductSnd f g)).mapDerivedCategory.obj
            K)) :=
  (compareRepresentableMorphismCohomology_modulesIso f g eX' eY' α).app K

end AlgebraicGeometry.GroupoidsOver
