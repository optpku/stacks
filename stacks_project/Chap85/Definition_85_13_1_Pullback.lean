/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Abelian
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import stacks_project.Chap85.Definition_85_12_1_Component

/-!
# Inverse image of abelian sheaves along simplex operators

Functoriality of `f_φ⁻¹` on abelian sheaves, and the induced comparisons on derived
categories `D(C_n)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Functor
open ComplexShape

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

/-- Functoriality of inverse images of abelian sheaves along a family of simplex operators:
the identifications `f_{ψ ≫ φ}⁻¹ ≅ f_ψ⁻¹ ⋙ f_φ⁻¹` and `f_id⁻¹ ≅ 𝟭`. -/
class HasAbelianInverseImageFunctoriality
    {C : SimplexCategory → Type u} [∀ n, Category.{v} (C n)]
    (J : ∀ n, GrothendieckTopology (C n))
    (fInv : ∀ {m n : SimplexCategory}, (m ⟶ n) →
      Sheaf (J m) AddCommGrpCat.{w} ⥤ Sheaf (J n) AddCommGrpCat.{w}) where
  /-- Canonical identification `f_{ψ ≫ φ}⁻¹ ≅ f_ψ⁻¹ ⋙ f_φ⁻¹`. -/
  pullbackCompIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    fInv (ψ ≫ φ) ≅ fInv ψ ⋙ fInv φ
  /-- Canonical identification `f_id⁻¹ ≅ 𝟭`. -/
  pullbackIdIso (n : SimplexCategory) :
    fInv (𝟙 n) ≅ 𝟭 (Sheaf (J n) AddCommGrpCat.{w})

variable {C : SimplexCategory → Type u} [∀ n, Category.{v} (C n)]
variable (J : ∀ n, GrothendieckTopology (C n))
variable (fInv : ∀ {m n : SimplexCategory}, (m ⟶ n) →
    Sheaf (J m) AddCommGrpCat.{w} ⥤ Sheaf (J n) AddCommGrpCat.{w})
variable [∀ n, HasSheafify (J n) AddCommGrpCat.{w}]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n), (fInv φ).Additive]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n), PreservesFiniteLimits (fInv φ)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n), PreservesFiniteColimits (fInv φ)]

/-- Inverse image `f_φ⁻¹` on derived categories of abelian sheaves. -/
abbrev derivedInverseImage {m n : SimplexCategory} (φ : m ⟶ n) :
    DerivedCategory (Sheaf (J m) AddCommGrpCat.{w}) ⥤
      DerivedCategory (Sheaf (J n) AddCommGrpCat.{w}) :=
  (fInv φ).mapDerivedCategory

/-- `derivedInverseImage φ` is `mapDerivedCategory` of the underived inverse image. -/
theorem derivedInverseImage_eq {m n : SimplexCategory} (φ : m ⟶ n) :
    derivedInverseImage J fInv φ = (fInv φ).mapDerivedCategory :=
  sorry

/-- The localization-lifting isomorphism presenting the composite of derived inverse images as a
lift of the cochain functor of `f_ψ⁻¹ ⋙ f_φ⁻¹`. -/
def derivedInverseImageCompLiftingIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    DerivedCategory.Q ⋙ (derivedInverseImage J fInv ψ ⋙ derivedInverseImage J fInv φ) ≅
      (fInv ψ ⋙ fInv φ).mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (fInv ψ).mapDerivedCategoryFactors
      (derivedInverseImage J fInv φ) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((fInv ψ).mapHomologicalComplex (up ℤ))
      (fInv φ).mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso (Iso.refl (fInv ψ ⋙ fInv φ)) (up ℤ))
      DerivedCategory.Q

/-- The composite of derived inverse images lifts the cochain functor of `f_ψ⁻¹ ⋙ f_φ⁻¹`. -/
instance derivedInverseImageComp_lifting {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    Localization.Lifting
      (DerivedCategory.Q : CochainComplex (Sheaf (J l) AddCommGrpCat.{w}) ℤ ⥤
        DerivedCategory (Sheaf (J l) AddCommGrpCat.{w}))
      (HomologicalComplex.quasiIso (Sheaf (J l) AddCommGrpCat.{w}) (up ℤ))
      ((fInv ψ ⋙ fInv φ).mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
      (derivedInverseImage J fInv ψ ⋙ derivedInverseImage J fInv φ) where
  iso := derivedInverseImageCompLiftingIso J fInv ψ φ

/-- Passage to derived categories identifies `f_ψ⁻¹ ⋙ f_φ⁻¹` with the composite of the derived
inverse images. -/
def derivedInverseImageCompFunctorIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (fInv ψ ⋙ fInv φ).mapDerivedCategory ≅
      derivedInverseImage J fInv ψ ⋙ derivedInverseImage J fInv φ :=
  Localization.liftNatIso
    (DerivedCategory.Q : CochainComplex (Sheaf (J l) AddCommGrpCat.{w}) ℤ ⥤
      DerivedCategory (Sheaf (J l) AddCommGrpCat.{w}))
    (HomologicalComplex.quasiIso (Sheaf (J l) AddCommGrpCat.{w}) (up ℤ))
    ((fInv ψ ⋙ fInv φ).mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
    ((fInv ψ ⋙ fInv φ).mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
    (fInv ψ ⋙ fInv φ).mapDerivedCategory
    (derivedInverseImage J fInv ψ ⋙ derivedInverseImage J fInv φ)
    (Iso.refl _)

/-- Component of `derivedInverseImageCompFunctorIso` on an object of `D(C_l)`. -/
theorem derivedInverseImageCompFunctorIso_app {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (K : DerivedCategory (Sheaf (J l) AddCommGrpCat.{w})) :
    (derivedInverseImageCompFunctorIso J fInv ψ φ).app K =
      (Localization.liftNatIso
        (DerivedCategory.Q : CochainComplex (Sheaf (J l) AddCommGrpCat.{w}) ℤ ⥤
          DerivedCategory (Sheaf (J l) AddCommGrpCat.{w}))
        (HomologicalComplex.quasiIso (Sheaf (J l) AddCommGrpCat.{w}) (up ℤ))
        ((fInv ψ ⋙ fInv φ).mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
        ((fInv ψ ⋙ fInv φ).mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q)
        (fInv ψ ⋙ fInv φ).mapDerivedCategory
        (derivedInverseImage J fInv ψ ⋙ derivedInverseImage J fInv φ)
        (Iso.refl _)).app K :=
  sorry

/-- Canonical comparison `f_φ⁻¹ ∘ f_ψ⁻¹ ⟶ f_{ψ ≫ φ}⁻¹` of derived inverse images, for an
underived identification `f_{ψ ≫ φ}⁻¹ ≅ f_ψ⁻¹ ⋙ f_φ⁻¹`. -/
def derivedInverseImageCompComparisonOf {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (hcomp : fInv (ψ ≫ φ) ≅ fInv ψ ⋙ fInv φ) :
    derivedInverseImage J fInv ψ ⋙ derivedInverseImage J fInv φ ⟶
      derivedInverseImage J fInv (ψ ≫ φ) :=
  (derivedInverseImageCompFunctorIso J fInv ψ φ).inv ≫
    (Functor.MapDerivedCategory.functorIso hcomp.symm).hom

/-- Component of `derivedInverseImageCompComparisonOf` on an object of `D(C_l)`. -/
theorem derivedInverseImageCompComparisonOf_app {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (hcomp : fInv (ψ ≫ φ) ≅ fInv ψ ⋙ fInv φ)
    (K : DerivedCategory (Sheaf (J l) AddCommGrpCat.{w})) :
    (derivedInverseImageCompComparisonOf J fInv ψ φ hcomp).app K =
      (derivedInverseImageCompFunctorIso J fInv ψ φ).inv.app K ≫
        (Functor.MapDerivedCategory.functorIso hcomp.symm).hom.app K :=
  sorry

/-- The composition comparison of derived inverse images is an isomorphism. -/
instance derivedInverseImageCompComparisonOf_isIso {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (hcomp : fInv (ψ ≫ φ) ≅ fInv ψ ⋙ fInv φ) :
    IsIso (derivedInverseImageCompComparisonOf J fInv ψ φ hcomp) :=
  sorry

/-- Canonical comparison `id ⟶ f_id⁻¹` of derived inverse images, for an underived identification
`f_id⁻¹ ≅ 𝟭`. -/
def derivedInverseImageIdComparisonOf {n : SimplexCategory}
    (hid : fInv (𝟙 n) ≅ 𝟭 (Sheaf (J n) AddCommGrpCat.{w})) :
    𝟭 (DerivedCategory (Sheaf (J n) AddCommGrpCat.{w})) ⟶
      derivedInverseImage J fInv (𝟙 n) :=
  (ExactFunctor.MapDerivedCategory.idFunctorIso
      (Sheaf (J n) AddCommGrpCat.{w})).inv ≫
    (Functor.MapDerivedCategory.functorIso hid).inv

/-- Component of `derivedInverseImageIdComparisonOf` on an object of `D(C_n)`. -/
theorem derivedInverseImageIdComparisonOf_app {n : SimplexCategory}
    (hid : fInv (𝟙 n) ≅ 𝟭 (Sheaf (J n) AddCommGrpCat.{w}))
    (K : DerivedCategory (Sheaf (J n) AddCommGrpCat.{w})) :
    (derivedInverseImageIdComparisonOf J fInv hid).app K =
      (ExactFunctor.MapDerivedCategory.idFunctorIso
          (Sheaf (J n) AddCommGrpCat.{w})).inv.app K ≫
        (Functor.MapDerivedCategory.functorIso hid).inv.app K :=
  sorry

/-- The identity comparison of derived inverse images is an isomorphism. -/
instance derivedInverseImageIdComparisonOf_isIso {n : SimplexCategory}
    (hid : fInv (𝟙 n) ≅ 𝟭 (Sheaf (J n) AddCommGrpCat.{w})) :
    IsIso (derivedInverseImageIdComparisonOf J fInv hid) :=
  sorry

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram.{u, v, w} C J]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

/-- Underived inverse images of abelian sheaves along simplex operators compose as
`f_{ψ ≫ φ}⁻¹ ≅ f_ψ⁻¹ ⋙ f_φ⁻¹`. -/
def abelianInverseImageCompIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    abelianInverseImage C J (ψ ≫ φ) ≅
      abelianInverseImage C J ψ ⋙ abelianInverseImage C J φ :=
  (Functor.sheafPullbackComp'
      (J l).toGrothendieck (J m).toGrothendieck (J n).toGrothendieck
      (C.map ψ).toFunctor (C.map φ).toFunctor
      (map_comp_toFunctor C ψ φ)).symm

/-- `abelianInverseImageCompIso` is the inverse of `sheafPullbackComp'` along `u_ψ` then `u_φ`. -/
theorem abelianInverseImageCompIso_eq {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    abelianInverseImageCompIso C J ψ φ =
      (Functor.sheafPullbackComp'
          (J l).toGrothendieck (J m).toGrothendieck (J n).toGrothendieck
          (C.map ψ).toFunctor (C.map φ).toFunctor
          (map_comp_toFunctor C ψ φ)).symm :=
  sorry

/-- Underived inverse image of abelian sheaves along an identity operator is the identity. -/
def abelianInverseImageIdIso (n : SimplexCategory) :
    abelianInverseImage C J (𝟙 n) ≅
      𝟭 (Sheaf (J n).toGrothendieck AddCommGrpCat.{w}) :=
  Adjunction.leftAdjointIdIso
    ((C.map (𝟙 n)).toFunctor.sheafAdjunctionContinuous AddCommGrpCat.{w}
      (J n).toGrothendieck (J n).toGrothendieck)
    (Functor.sheafPushforwardContinuousId'
      (Cat.Hom.toNatIso (eqToIso (C.map_id n)))
      AddCommGrpCat.{w} (J n).toGrothendieck)

/-- `abelianInverseImageIdIso` is left-adjoint uniqueness for the identity operator. -/
theorem abelianInverseImageIdIso_eq (n : SimplexCategory) :
    abelianInverseImageIdIso C J n =
      Adjunction.leftAdjointIdIso
        ((C.map (𝟙 n)).toFunctor.sheafAdjunctionContinuous AddCommGrpCat.{w}
          (J n).toGrothendieck (J n).toGrothendieck)
        (Functor.sheafPushforwardContinuousId'
          (Cat.Hom.toNatIso (eqToIso (C.map_id n)))
          AddCommGrpCat.{w} (J n).toGrothendieck) :=
  sorry

/-- Case A of Situation 85.3.3: inverse images `f_φ⁻¹` of abelian sheaves along simplex operators
are functorial via the canonical underived identifications. -/
instance instHasAbelianInverseImageFunctoriality_abelianInverseImage :
    HasAbelianInverseImageFunctoriality
      (fun n ↦ (J n).toGrothendieck) (fun φ ↦ abelianInverseImage C J φ) where
  pullbackCompIso := abelianInverseImageCompIso C J
  pullbackIdIso := abelianInverseImageIdIso C J

end CategoryTheory.SimplicialSites
