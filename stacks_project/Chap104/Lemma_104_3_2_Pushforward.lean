/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import stacks_project.Chap104.«104_3_2_1_Comparison»

/-!
# Unbounded derived pushforward on the 103.15.1 square

The functors `Rf_*` and `Rf'_*` on unbounded derived categories of modules and
of abelian sheaves, for the associated étale / lisse-étale and inherited fppf /
flat-fppf presentations of a 1-morphism of algebraic stacks. Each is the total
right derived functor of cocontinuous underived pushforward, right adjoint to
the exact derived inverse image of `104.3.2.1`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open CategoryTheory.ConcreteCategory CategoryTheory.Limits
open FiberedCategoryOver.Groupoids
open RingedSite.Cocontinuous
open RingedSite.Hom
open scoped Bicategory
open ComplexShape

noncomputable section

universe u z

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]
variable [UnivLE.{u + 1, z}]

/-- Pointwise right Kan extensions along `(toFunctor φ).op` exist on abelian
presheaves of universe `z`. -/
instance toFunctor.op_hasPointwiseRightKanExtension_addCommGrpCat (φ : X ⟶ Y)
    (P : X.totalᵒᵖ ⥤ AddCommGrpCat.{z}) :
    (toFunctor φ).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Pointwise right Kan extensions along `(lisseEtaleMap φ).op` exist on abelian
presheaves of universe `z`. -/
instance lisseEtaleMap.op_hasPointwiseRightKanExtension_addCommGrpCat
    (φ : X ⟶ Y) [Smooth φ] (P : (lisseEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{z}) :
    (lisseEtaleMap φ).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Pointwise right Kan extensions along `(flatFppfMap φ).op` exist on abelian
presheaves of universe `z`. -/
instance flatFppfMap.op_hasPointwiseRightKanExtension_addCommGrpCat
    (φ : X ⟶ Y) [Flat φ] (P : (flatFppfSite X)ᵒᵖ ⥤ AddCommGrpCat.{z}) :
    (flatFppfMap φ).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Pointwise right Kan extensions along `(toFunctor φ).op` exist on sheaves of
rings. -/
instance toFunctor.op_hasPointwiseRightKanExtension_ringCat (φ : X ⟶ Y)
    (P : X.totalᵒᵖ ⥤ RingCat.{u}) :
    (toFunctor φ).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Pointwise right Kan extensions along `(lisseEtaleMap φ).op` exist on sheaves
of rings. -/
instance lisseEtaleMap.op_hasPointwiseRightKanExtension_ringCat
    (φ : X ⟶ Y) [Smooth φ] (P : (lisseEtaleSite X)ᵒᵖ ⥤ RingCat.{u}) :
    (lisseEtaleMap φ).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Pointwise right Kan extensions along `(flatFppfMap φ).op` exist on sheaves of
rings. -/
instance flatFppfMap.op_hasPointwiseRightKanExtension_ringCat
    (φ : X ⟶ Y) [Flat φ] (P : (flatFppfSite X)ᵒᵖ ⥤ RingCat.{u}) :
    (flatFppfMap φ).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Cocontinuous abelian pushforward along `toFunctor φ` on associated étale
sites is additive. -/
instance toFunctor_sheafPushforwardCocontinuous_etale_additive_z (φ : X ⟶ Y) :
    ((toFunctor φ).sheafPushforwardCocontinuous AddCommGrpCat.{z}
      X.etaleTopology Y.etaleTopology).Additive :=
  sorry

/-- Cocontinuous abelian pushforward along `lisseEtaleMap φ` is additive. -/
instance lisseEtaleMap_sheafPushforwardCocontinuous_additive (φ : X ⟶ Y)
    [Smooth φ] :
    ((lisseEtaleMap φ).sheafPushforwardCocontinuous AddCommGrpCat.{z}
      (lisseEtaleTopology X) (lisseEtaleTopology Y)).Additive :=
  sorry

/-- Cocontinuous abelian pushforward along `toFunctor φ` on inherited fppf
sites is additive. -/
instance toFunctor_sheafPushforwardCocontinuous_inheritedFppf_additive_z
    (φ : X ⟶ Y) :
    ((toFunctor φ).sheafPushforwardCocontinuous AddCommGrpCat.{z}
      (inheritedFppfTopology X) (inheritedFppfTopology Y)).Additive :=
  sorry

/-- Cocontinuous abelian pushforward along `flatFppfMap φ` is additive. -/
instance flatFppfMap_sheafPushforwardCocontinuous_additive (φ : X ⟶ Y)
    [Flat φ] :
    ((flatFppfMap φ).sheafPushforwardCocontinuous AddCommGrpCat.{z}
      (flatFppfTopology X) (flatFppfTopology Y)).Additive :=
  sorry

section AbelianPushforward

variable {C' D' : Type (u + 1)} [Category.{u} C'] [Category.{u} D']
variable (J' : GrothendieckTopology C') (K' : GrothendieckTopology D')
variable (f : C' ⥤ D') [f.IsContinuous J' K'] [f.IsCocontinuous J' K']
variable [HasSheafify J' AddCommGrpCat.{z}] [HasSheafify K' AddCommGrpCat.{z}]
variable [∀ P : C'ᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasPointwiseRightKanExtension P]
variable [(f.sheafPushforwardContinuous AddCommGrpCat.{z} J' K').Additive]
variable [(f.sheafPushforwardCocontinuous AddCommGrpCat.{z} J' K').Additive]

/-- Homotopy-to-derived presentation of cocontinuous abelian pushforward. -/
abbrev abelianPushforwardToDerived :
    HomotopyCategory (Sheaf J' AddCommGrpCat.{z}) (up ℤ) ⥤
      DerivedCategory (Sheaf K' AddCommGrpCat.{z}) :=
  (f.sheafPushforwardCocontinuous AddCommGrpCat.{z} J' K').mapHomotopyCategory
      (up ℤ) ⋙
    DerivedCategory.Qh

/-- Homotopy-to-derived presentation of continuous abelian inverse image. -/
abbrev abelianInverseImageToDerived :
    HomotopyCategory (Sheaf K' AddCommGrpCat.{z}) (up ℤ) ⥤
      DerivedCategory (Sheaf J' AddCommGrpCat.{z}) :=
  (f.sheafPushforwardContinuous AddCommGrpCat.{z} J' K').mapHomotopyCategory
      (up ℤ) ⋙
    DerivedCategory.Qh

/-- Existence of the total right-derived functor of cocontinuous abelian
pushforward. -/
instance abelianPushforwardToDerived.hasRightDerived :
    Functor.HasRightDerivedFunctor (abelianPushforwardToDerived J' K' f)
      (HomotopyCategory.quasiIso (Sheaf J' AddCommGrpCat.{z}) (up ℤ)) :=
  sorry

/-- Existence of the total left-derived functor of continuous abelian inverse
image. -/
instance abelianInverseImageToDerived.hasLeftDerived :
    Functor.HasLeftDerivedFunctor (abelianInverseImageToDerived J' K' f)
      (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ)) :=
  sorry

/-- The homotopy abelian inverse-image/pushforward adjunction descends to
derived categories. -/
instance abelianDerivedPushforward.hasPair :
    CategoryTheory.Adjunction.TotalDerived.HasPair
      (G := (f.sheafPushforwardContinuous AddCommGrpCat.{z} J' K').mapHomotopyCategory
        (up ℤ))
      (F := (f.sheafPushforwardCocontinuous AddCommGrpCat.{z} J' K').mapHomotopyCategory
        (up ℤ))
      (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ))
      (HomotopyCategory.quasiIso (Sheaf J' AddCommGrpCat.{z}) (up ℤ))
      (L1 := DerivedCategory.Qh (C := Sheaf K' AddCommGrpCat.{z}))
      (L2 := DerivedCategory.Qh (C := Sheaf J' AddCommGrpCat.{z})) :=
  sorry

/-- Total right-derived abelian pushforward. -/
abbrev abelianDerivedPushforward :
    DerivedCategory (Sheaf J' AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf K' AddCommGrpCat.{z}) :=
  Functor.totalRightDerived (abelianPushforwardToDerived J' K' f)
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf J' AddCommGrpCat.{z}) (up ℤ))

/-- The total-derived abelian inverse-image/pushforward adjunction. -/
def abelianDerivedPushforward.totalAdjunction :
    Functor.totalLeftDerived (abelianInverseImageToDerived J' K' f)
        DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ)) ⊣
      abelianDerivedPushforward J' K' f :=
  CategoryTheory.Adjunction.TotalDerived.HasPair.derived
    (Adjunction.mapHomotopyCategoryAdjunction
      (f.sheafAdjunctionCocontinuous AddCommGrpCat.{z} J' K'))
    (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ))
    (HomotopyCategory.quasiIso (Sheaf J' AddCommGrpCat.{z}) (up ℤ))

/-- Exact derived abelian inverse image is a left-derived functor of its
homotopy presentation. -/
instance siteAbelianInverseImageDerived.isLeftDerived :
    (siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z} J' K' f).IsLeftDerivedFunctor
      (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z}
          J' K' f).obj.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ)) :=
  sorry

/-- The total left-derived abelian inverse image agrees with the exact derived
inverse image. -/
def abelianInverseImageTotalLeftDerivedIso :
    Functor.totalLeftDerived (abelianInverseImageToDerived J' K' f)
        DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ)) ≅
      siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z} J' K' f :=
  Functor.leftDerivedNatIso
    (Functor.totalLeftDerived (abelianInverseImageToDerived J' K' f)
      DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ)))
    (siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z} J' K' f)
    ((abelianInverseImageToDerived J' K' f).totalLeftDerivedCounit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ)))
    (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z}
        J' K' f).obj.mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ))
    (Iso.refl _)

/-- Derived abelian inverse image is left adjoint to total right-derived
pushforward. -/
def abelianDerivedPushforward.adjunction :
    siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z} J' K' f ⊣
      abelianDerivedPushforward J' K' f :=
  (abelianDerivedPushforward.totalAdjunction J' K' f).ofNatIsoLeft
    (abelianInverseImageTotalLeftDerivedIso J' K' f)

end AbelianPushforward

/-- Derived étale abelian pushforward `Rf_*`. -/
abbrev etaleAbelianDerivedPushforward (φ : X ⟶ Y) :
    DerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf Y.etaleTopology AddCommGrpCat.{z}) :=
  abelianDerivedPushforward X.etaleTopology Y.etaleTopology (toFunctor φ)

/-- `etaleAbelianDerivedPushforward` is the total right-derived functor of
cocontinuous étale abelian pushforward. -/
theorem etaleAbelianDerivedPushforward_eq (φ : X ⟶ Y) :
    etaleAbelianDerivedPushforward φ =
      abelianDerivedPushforward X.etaleTopology Y.etaleTopology (toFunctor φ) :=
  sorry

/-- Derived étale abelian inverse image is left adjoint to `Rf_*`. -/
def etaleAbelianDerivedPushforward.adjunction (φ : X ⟶ Y) :
    etaleAbelianDerivedInverseImage φ ⊣ etaleAbelianDerivedPushforward φ :=
  abelianDerivedPushforward.adjunction X.etaleTopology Y.etaleTopology
    (toFunctor φ)

/-- Derived lisse-étale abelian pushforward `Rf'_*`. -/
abbrev lisseEtaleAbelianDerivedPushforward (φ : X ⟶ Y) [Smooth φ] :
    DerivedCategory (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf (lisseEtaleTopology Y) AddCommGrpCat.{z}) :=
  abelianDerivedPushforward (lisseEtaleTopology X) (lisseEtaleTopology Y)
    (lisseEtaleMap φ)

/-- `lisseEtaleAbelianDerivedPushforward` is the total right-derived functor of
cocontinuous lisse-étale abelian pushforward. -/
theorem lisseEtaleAbelianDerivedPushforward_eq (φ : X ⟶ Y) [Smooth φ] :
    lisseEtaleAbelianDerivedPushforward φ =
      abelianDerivedPushforward (lisseEtaleTopology X) (lisseEtaleTopology Y)
        (lisseEtaleMap φ) :=
  sorry

/-- Derived lisse-étale abelian inverse image is left adjoint to `Rf'_*`. -/
def lisseEtaleAbelianDerivedPushforward.adjunction (φ : X ⟶ Y) [Smooth φ] :
    lisseEtaleAbelianDerivedInverseImage φ ⊣
      lisseEtaleAbelianDerivedPushforward φ :=
  abelianDerivedPushforward.adjunction (lisseEtaleTopology X)
    (lisseEtaleTopology Y) (lisseEtaleMap φ)

/-- Derived fppf abelian pushforward `Rf_*`. -/
abbrev fppfAbelianDerivedPushforward (φ : X ⟶ Y) :
    DerivedCategory (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf (inheritedFppfTopology Y) AddCommGrpCat.{z}) :=
  abelianDerivedPushforward (inheritedFppfTopology X) (inheritedFppfTopology Y)
    (toFunctor φ)

/-- `fppfAbelianDerivedPushforward` is the total right-derived functor of
cocontinuous inherited-fppf abelian pushforward. -/
theorem fppfAbelianDerivedPushforward_eq (φ : X ⟶ Y) :
    fppfAbelianDerivedPushforward φ =
      abelianDerivedPushforward (inheritedFppfTopology X)
        (inheritedFppfTopology Y) (toFunctor φ) :=
  sorry

/-- Derived fppf abelian inverse image is left adjoint to `Rf_*`. -/
def fppfAbelianDerivedPushforward.adjunction (φ : X ⟶ Y) :
    fppfAbelianDerivedInverseImage φ ⊣ fppfAbelianDerivedPushforward φ :=
  abelianDerivedPushforward.adjunction (inheritedFppfTopology X)
    (inheritedFppfTopology Y) (toFunctor φ)

/-- Derived flat-fppf abelian pushforward `Rf'_*`. -/
abbrev flatFppfAbelianDerivedPushforward (φ : X ⟶ Y) [Flat φ] :
    DerivedCategory (Sheaf (flatFppfTopology X) AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf (flatFppfTopology Y) AddCommGrpCat.{z}) :=
  abelianDerivedPushforward (flatFppfTopology X) (flatFppfTopology Y)
    (flatFppfMap φ)

/-- `flatFppfAbelianDerivedPushforward` is the total right-derived functor of
cocontinuous flat-fppf abelian pushforward. -/
theorem flatFppfAbelianDerivedPushforward_eq (φ : X ⟶ Y) [Flat φ] :
    flatFppfAbelianDerivedPushforward φ =
      abelianDerivedPushforward (flatFppfTopology X) (flatFppfTopology Y)
        (flatFppfMap φ) :=
  sorry

/-- Derived flat-fppf abelian inverse image is left adjoint to `Rf'_*`. -/
def flatFppfAbelianDerivedPushforward.adjunction (φ : X ⟶ Y) [Flat φ] :
    flatFppfAbelianDerivedInverseImage φ ⊣
      flatFppfAbelianDerivedPushforward φ :=
  abelianDerivedPushforward.adjunction (flatFppfTopology X)
    (flatFppfTopology Y) (flatFppfMap φ)


section ModulePushforward

variable {C' D' : Type (u + 1)} [Category.{u} C'] [Category.{u} D']
variable (J' : GrothendieckTopology C') (K' : GrothendieckTopology D')
variable (f : C' ⥤ D') [f.IsContinuous J' K'] [f.IsCocontinuous J' K']
variable (R : Sheaf J' RingCat.{u}) (S : Sheaf K' RingCat.{u})
variable (α : R ⟶ (f.sheafPushforwardContinuous RingCat.{u} J' K').obj S)
variable (α_inv : (f.sheafPushforwardContinuous RingCat.{u} J' K').obj S ⟶ R)
variable [HasSheafify J' AddCommGrpCat.{z}] [HasSheafify K' AddCommGrpCat.{z}]
variable [∀ P : C'ᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasPointwiseRightKanExtension P]
variable [(f.sheafPushforwardContinuous AddCommGrpCat.{z} J' K').Additive]
variable [(f.sheafPushforwardCocontinuous AddCommGrpCat.{z} J' K').Additive]
variable [PreservesFiniteLimits (SheafOfModules.pushforward.{z} α)]
variable [PreservesFiniteColimits (SheafOfModules.pushforward.{z} α)]

/-- Cocontinuous abelian pushforward of the underlying abelian sheaf of a module
sheaf. -/
abbrev moduleCocontinuousPushforwardAbelian (G : SheafOfModules.{z} R) :
    Sheaf K' AddCommGrpCat.{z} :=
  (f.sheafPushforwardCocontinuous AddCommGrpCat.{z} J' K').obj
    ((SheafOfModules.toSheaf R).obj G)

/-- The value of cocontinuous abelian pushforward at an object of the target
site. -/
abbrev moduleCocontinuousPushforwardObjAbelian
    (G : SheafOfModules.{z} R) (y : D'ᵒᵖ) :
    AddCommGrpCat.{z} :=
  (moduleCocontinuousPushforwardAbelian J' K' f R G).obj.obj y

/-- The ring homomorphism `S(y) ⟶ R(x)` along a comma object, using the inverse
of the coefficient isomorphism. -/
def moduleCocontinuousPushforwardRingHom (y : D'ᵒᵖ)
    (s : StructuredArrow y f.op) :
    S.obj.obj y ⟶ R.obj.obj s.right :=
  let _ := α
  S.obj.map s.hom ≫ α_inv.hom.app s.right

/-- Scalar multiplication by a section of `S` on the underlying abelian group of
`f_* G` at `y`. -/
def moduleCocontinuousPushforwardSmulHom
    (G : SheafOfModules.{z} R) (y : D'ᵒᵖ) (r : S.obj.obj y) :
    moduleCocontinuousPushforwardObjAbelian J' K' f R G y ⟶
      moduleCocontinuousPushforwardObjAbelian J' K' f R G y :=
  let L := f.op
  let P := ((SheafOfModules.toSheaf R).obj G).obj
  let e := L.ranObjObjIsoLimit P y
  let D := StructuredArrow.proj y L ⋙ P
  limit.lift D
      { pt := (L.ran.obj P).obj y
        π :=
          { app := fun s ↦
              e.hom ≫
                limit.π D s ≫
                  (G.val.obj s.right).smul
                    ((moduleCocontinuousPushforwardRingHom J' K' f R S α α_inv y s).hom r)
            naturality := sorry } } ≫
    e.inv

/-- The `S(y)`-module structure on the underlying abelian group of `f_* G` at
`y`. -/
def moduleCocontinuousPushforwardObjModule
    (G : SheafOfModules.{z} R) (y : D'ᵒᵖ) :
    Module (S.obj.obj y)
      (moduleCocontinuousPushforwardObjAbelian J' K' f R G y) where
  smul r a := (moduleCocontinuousPushforwardSmulHom J' K' f R S α α_inv G y r).hom a
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- The value of underived cocontinuous module pushforward at an object of the
target site. -/
def moduleCocontinuousPushforwardObj
    (G : SheafOfModules.{z} R) (y : D'ᵒᵖ) :
    ModuleCat.{z} (S.obj.obj y) :=
  -- Local instance justification (proof-local temporary data): the S(y)-module
  -- structure on the Kan-extension value depends on the coefficient
  -- isomorphism and is not a reusable global instance.
  letI := moduleCocontinuousPushforwardObjModule J' K' f R S α α_inv G y
  ModuleCat.of _ (moduleCocontinuousPushforwardObjAbelian J' K' f R G y)

/-- Restriction maps of underived cocontinuous module pushforward. -/
def moduleCocontinuousPushforwardMap
    (G : SheafOfModules.{z} R) {y y' : D'ᵒᵖ} (β : y ⟶ y') :
    moduleCocontinuousPushforwardObj J' K' f R S α α_inv G y ⟶
      (ModuleCat.restrictScalars (S.obj.map β).hom).obj
        (moduleCocontinuousPushforwardObj J' K' f R S α α_inv G y') :=
  ConcreteCategory.ofHom (C := ModuleCat _)
    { toFun :=
        ((moduleCocontinuousPushforwardAbelian J' K' f R G).obj.map β).hom
      map_add' :=
        map_add
          ((moduleCocontinuousPushforwardAbelian J' K' f R G).obj.map β).hom
      map_smul' := sorry }

/-- The underived cocontinuous module pushforward as a presheaf of modules. -/
def moduleCocontinuousPushforwardPresheaf (G : SheafOfModules.{z} R) :
    PresheafOfModules.{z} S.obj where
  obj y := moduleCocontinuousPushforwardObj J' K' f R S α α_inv G y
  map β := moduleCocontinuousPushforwardMap J' K' f R S α α_inv G β
  map_id := sorry
  map_comp := sorry

/-- The underived cocontinuous module pushforward `f_*` on sheaves of modules. -/
def moduleCocontinuousPushforward :
    SheafOfModules.{z} R ⥤ SheafOfModules.{z} S where
  obj G :=
    { val := moduleCocontinuousPushforwardPresheaf J' K' f R S α α_inv G
      isSheaf := sorry }
  map {G G'} φ :=
    { val :=
        { app := fun y ↦
            ConcreteCategory.ofHom (C := ModuleCat _)
              { toFun :=
                  (((f.sheafPushforwardCocontinuous AddCommGrpCat.{z} J' K').map
                        ((SheafOfModules.toSheaf R).map φ)).hom.app y).hom
                map_add' :=
                  map_add
                    (((f.sheafPushforwardCocontinuous AddCommGrpCat.{z} J' K').map
                          ((SheafOfModules.toSheaf R).map φ)).hom.app y).hom
                map_smul' := sorry }
          naturality := sorry } }
  map_id := sorry
  map_comp := sorry

/-- Cocontinuous module pushforward is additive. -/
instance moduleCocontinuousPushforward.additive :
    (moduleCocontinuousPushforward J' K' f R S α α_inv).Additive :=
  sorry

/-- Coefficient inverse image of modules is additive. -/
instance sheafOfModules_pushforward_additive :
    (SheafOfModules.pushforward.{z} α).Additive :=
  sorry

/-- Homotopy-to-derived presentation of cocontinuous module pushforward. -/
abbrev moduleCocontinuousPushforwardToDerived :
    ModuleHomotopy.{z} (RingedSite.ofRingSheaf J' R) ⥤
      ModuleDerived.{z} (RingedSite.ofRingSheaf K' S) :=
  (moduleCocontinuousPushforward J' K' f R S α α_inv).mapHomotopyCategory (up ℤ) ⋙
    moduleLocalization (RingedSite.ofRingSheaf K' S)

/-- Homotopy-to-derived presentation of coefficient module inverse image. -/
abbrev coefficientModuleInverseImageToDerived :
    ModuleHomotopy.{z} (RingedSite.ofRingSheaf K' S) ⥤
      ModuleDerived.{z} (RingedSite.ofRingSheaf J' R) :=
  (SheafOfModules.pushforward.{z} α).mapHomotopyCategory (up ℤ) ⋙
    moduleLocalization (RingedSite.ofRingSheaf J' R)

/-- Existence of the total right-derived functor of cocontinuous module
pushforward. -/
instance moduleCocontinuousPushforwardToDerived.hasRightDerived :
    Functor.HasRightDerivedFunctor
      (moduleCocontinuousPushforwardToDerived J' K' f R S α α_inv)
      (ModuleQis.{z} (RingedSite.ofRingSheaf J' R)) :=
  sorry

/-- Existence of the total left-derived functor of coefficient module inverse
image. -/
instance coefficientModuleInverseImageToDerived.hasLeftDerived :
    Functor.HasLeftDerivedFunctor
      (coefficientModuleInverseImageToDerived J' K' f R S α)
      (ModuleQis.{z} (RingedSite.ofRingSheaf K' S)) :=
  sorry

/-- The homotopy module inverse-image/pushforward adjunction descends to derived
categories. -/
instance moduleCocontinuousPushforward.hasPair :
    CategoryTheory.Adjunction.TotalDerived.HasPair
      (G := (SheafOfModules.pushforward.{z} α).mapHomotopyCategory (up ℤ))
      (F := (moduleCocontinuousPushforward J' K' f R S α α_inv).mapHomotopyCategory
        (up ℤ))
      (ModuleQis.{z} (RingedSite.ofRingSheaf K' S))
      (ModuleQis.{z} (RingedSite.ofRingSheaf J' R))
      (L1 := moduleLocalization (RingedSite.ofRingSheaf K' S))
      (L2 := moduleLocalization (RingedSite.ofRingSheaf J' R)) :=
  sorry

/-- Total right-derived module pushforward. -/
abbrev moduleCocontinuousDerivedPushforward :
    ModuleDerived.{z} (RingedSite.ofRingSheaf J' R) ⥤
      ModuleDerived.{z} (RingedSite.ofRingSheaf K' S) :=
  Functor.totalRightDerived
    (moduleCocontinuousPushforwardToDerived J' K' f R S α α_inv)
    (moduleLocalization (RingedSite.ofRingSheaf J' R))
    (ModuleQis.{z} (RingedSite.ofRingSheaf J' R))

/-- The unit of the underived module inverse-image/pushforward adjunction. -/
def moduleCocontinuousPushforward.unit :
    𝟭 (SheafOfModules.{z} S) ⟶
      SheafOfModules.pushforward.{z} α ⋙
        moduleCocontinuousPushforward J' K' f R S α α_inv where
  app N :=
    { val :=
        { app := fun y ↦
            ConcreteCategory.ofHom (C := ModuleCat _)
              { toFun :=
                  ((f.sheafAdjunctionCocontinuous AddCommGrpCat.{z} J' K').unit.app
                        ((SheafOfModules.toSheaf S).obj N)).hom.app y |>.hom
                map_add' := sorry
                map_smul' := sorry }
          naturality := sorry } }
  naturality := sorry

/-- The counit of the underived module inverse-image/pushforward adjunction. -/
def moduleCocontinuousPushforward.counit :
    moduleCocontinuousPushforward J' K' f R S α α_inv ⋙
        SheafOfModules.pushforward.{z} α ⟶
      𝟭 (SheafOfModules.{z} R) where
  app M :=
    { val :=
        { app := fun x ↦
            ConcreteCategory.ofHom (C := ModuleCat _)
              { toFun :=
                  ((f.sheafAdjunctionCocontinuous AddCommGrpCat.{z} J' K').counit.app
                        ((SheafOfModules.toSheaf R).obj M)).hom.app x |>.hom
                map_add' := sorry
                map_smul' := sorry }
          naturality := sorry } }
  naturality := sorry

/-- Coefficient module inverse image is left adjoint to cocontinuous module
pushforward. -/
def moduleCocontinuousPushforward.adjunction :
    SheafOfModules.pushforward.{z} α ⊣
      moduleCocontinuousPushforward J' K' f R S α α_inv :=
  Adjunction.mkOfUnitCounit
    { unit := moduleCocontinuousPushforward.unit J' K' f R S α α_inv
      counit := moduleCocontinuousPushforward.counit J' K' f R S α α_inv
      left_triangle := sorry
      right_triangle := sorry }

/-- The total-derived module inverse-image/pushforward adjunction. -/
def moduleCocontinuousDerivedPushforward.totalAdjunction :
    Functor.totalLeftDerived
        (coefficientModuleInverseImageToDerived J' K' f R S α)
        (moduleLocalization (RingedSite.ofRingSheaf K' S))
        (ModuleQis.{z} (RingedSite.ofRingSheaf K' S)) ⊣
      moduleCocontinuousDerivedPushforward J' K' f R S α α_inv :=
  CategoryTheory.Adjunction.TotalDerived.HasPair.derived
    (Adjunction.mapHomotopyCategoryAdjunction
      (moduleCocontinuousPushforward.adjunction J' K' f R S α α_inv))
    (ModuleQis.{z} (RingedSite.ofRingSheaf K' S))
    (ModuleQis.{z} (RingedSite.ofRingSheaf J' R))

/-- Exact derived coefficient inverse image is a left-derived functor of its
homotopy presentation. -/
instance derivedCoefficientInverseImage.isLeftDerived :
    (derivedCoefficientInverseImage J' K' f α).IsLeftDerivedFunctor
      (ExactFunctor.of (SheafOfModules.pushforward.{z} α)).obj.mapDerivedCategoryFactorsh.hom
      (ModuleQis.{z} (RingedSite.ofRingSheaf K' S)) :=
  sorry

/-- The total left-derived coefficient inverse image agrees with the exact
derived inverse image. -/
def coefficientModuleInverseImageTotalLeftDerivedIso :
    Functor.totalLeftDerived
        (coefficientModuleInverseImageToDerived J' K' f R S α)
        (moduleLocalization (RingedSite.ofRingSheaf K' S))
        (ModuleQis.{z} (RingedSite.ofRingSheaf K' S)) ≅
      derivedCoefficientInverseImage J' K' f α :=
  Functor.leftDerivedNatIso
    (Functor.totalLeftDerived
      (coefficientModuleInverseImageToDerived J' K' f R S α)
      (moduleLocalization (RingedSite.ofRingSheaf K' S))
      (ModuleQis.{z} (RingedSite.ofRingSheaf K' S)))
    (derivedCoefficientInverseImage J' K' f α)
    ((coefficientModuleInverseImageToDerived J' K' f R S α).totalLeftDerivedCounit
      (moduleLocalization (RingedSite.ofRingSheaf K' S))
      (ModuleQis.{z} (RingedSite.ofRingSheaf K' S)))
    (ExactFunctor.of (SheafOfModules.pushforward.{z} α)).obj.mapDerivedCategoryFactorsh.hom
    (ModuleQis.{z} (RingedSite.ofRingSheaf K' S))
    (Iso.refl _)

/-- Derived coefficient inverse image is left adjoint to total right-derived
module pushforward. -/
def moduleCocontinuousDerivedPushforward.adjunction :
    derivedCoefficientInverseImage J' K' f α ⊣
      moduleCocontinuousDerivedPushforward J' K' f R S α α_inv :=
  (moduleCocontinuousDerivedPushforward.totalAdjunction J' K' f R S α α_inv).ofNatIsoLeft
    (coefficientModuleInverseImageTotalLeftDerivedIso J' K' f R S α)

end ModulePushforward

/-- Derived étale module pushforward `Rf_*`. -/
abbrev etaleDerivedPushforward (φ : X ⟶ Y) :
    ModuleDerived.{z}
        (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X)) ⥤
      ModuleDerived.{z}
        (RingedSite.ofRingSheaf Y.etaleTopology (etaleStructureSheaf Y)) :=
  moduleCocontinuousDerivedPushforward X.etaleTopology Y.etaleTopology
    (toFunctor φ) (etaleStructureSheaf X) (etaleStructureSheaf Y)
    (etaleStructureSheafMap φ) (inv (etaleStructureSheafMap φ))

/-- `etaleDerivedPushforward` is the total right-derived functor of
cocontinuous étale module pushforward. -/
theorem etaleDerivedPushforward_eq (φ : X ⟶ Y) :
    etaleDerivedPushforward φ =
      moduleCocontinuousDerivedPushforward X.etaleTopology Y.etaleTopology
        (toFunctor φ) (etaleStructureSheaf X) (etaleStructureSheaf Y)
        (etaleStructureSheafMap φ) (inv (etaleStructureSheafMap φ)) :=
  sorry

/-- Derived étale module inverse image is left adjoint to `Rf_*`. -/
def etaleDerivedPushforward.adjunction (φ : X ⟶ Y) :
    etaleDerivedInverseImage φ ⊣ etaleDerivedPushforward φ :=
  moduleCocontinuousDerivedPushforward.adjunction X.etaleTopology
    Y.etaleTopology (toFunctor φ) (etaleStructureSheaf X)
    (etaleStructureSheaf Y) (etaleStructureSheafMap φ)
    (inv (etaleStructureSheafMap φ))

/-- Derived lisse-étale module pushforward `Rf'_*`. -/
abbrev lisseEtaleDerivedPushforward (φ : X ⟶ Y) [Smooth φ] :
    ModuleDerived.{z}
        (RingedSite.ofRingSheaf (lisseEtaleTopology X)
          (lisseEtaleInverseImageRingSheaf X)) ⥤
      ModuleDerived.{z}
        (RingedSite.ofRingSheaf (lisseEtaleTopology Y)
          (lisseEtaleInverseImageRingSheaf Y)) :=
  moduleCocontinuousDerivedPushforward (lisseEtaleTopology X)
    (lisseEtaleTopology Y) (lisseEtaleMap φ)
    (lisseEtaleInverseImageRingSheaf X) (lisseEtaleInverseImageRingSheaf Y)
    (lisseEtaleStructureSheafMap φ) (inv (lisseEtaleStructureSheafMap φ))

/-- `lisseEtaleDerivedPushforward` is the total right-derived functor of
cocontinuous lisse-étale module pushforward. -/
theorem lisseEtaleDerivedPushforward_eq (φ : X ⟶ Y) [Smooth φ] :
    lisseEtaleDerivedPushforward φ =
      moduleCocontinuousDerivedPushforward (lisseEtaleTopology X)
        (lisseEtaleTopology Y) (lisseEtaleMap φ)
        (lisseEtaleInverseImageRingSheaf X) (lisseEtaleInverseImageRingSheaf Y)
        (lisseEtaleStructureSheafMap φ) (inv (lisseEtaleStructureSheafMap φ)) :=
  sorry

/-- Derived lisse-étale module inverse image is left adjoint to `Rf'_*`. -/
def lisseEtaleDerivedPushforward.adjunction (φ : X ⟶ Y) [Smooth φ] :
    lisseEtaleDerivedInverseImage φ ⊣ lisseEtaleDerivedPushforward φ :=
  moduleCocontinuousDerivedPushforward.adjunction (lisseEtaleTopology X)
    (lisseEtaleTopology Y) (lisseEtaleMap φ)
    (lisseEtaleInverseImageRingSheaf X) (lisseEtaleInverseImageRingSheaf Y)
    (lisseEtaleStructureSheafMap φ) (inv (lisseEtaleStructureSheafMap φ))

/-- Derived fppf module pushforward `Rf_*`. -/
abbrev fppfDerivedPushforward (φ : X ⟶ Y) :
    ModuleDerived.{z}
        (RingedSite.ofRingSheaf (inheritedFppfTopology X) (structureSheaf X)) ⥤
      ModuleDerived.{z}
        (RingedSite.ofRingSheaf (inheritedFppfTopology Y) (structureSheaf Y)) :=
  moduleCocontinuousDerivedPushforward (inheritedFppfTopology X)
    (inheritedFppfTopology Y) (toFunctor φ) (structureSheaf X)
    (structureSheaf Y) (GroupoidsOver.structureSheafMap φ)
    (GroupoidsOver.structureSheafIso φ).hom

/-- `fppfDerivedPushforward` is the total right-derived functor of cocontinuous
inherited-fppf module pushforward. -/
theorem fppfDerivedPushforward_eq (φ : X ⟶ Y) :
    fppfDerivedPushforward φ =
      moduleCocontinuousDerivedPushforward (inheritedFppfTopology X)
        (inheritedFppfTopology Y) (toFunctor φ) (structureSheaf X)
        (structureSheaf Y) (GroupoidsOver.structureSheafMap φ)
        (GroupoidsOver.structureSheafIso φ).hom :=
  sorry

/-- Derived fppf module inverse image is left adjoint to `Rf_*`. -/
def fppfDerivedPushforward.adjunction (φ : X ⟶ Y) :
    fppfDerivedInverseImage φ ⊣ fppfDerivedPushforward φ :=
  moduleCocontinuousDerivedPushforward.adjunction (inheritedFppfTopology X)
    (inheritedFppfTopology Y) (toFunctor φ) (structureSheaf X)
    (structureSheaf Y) (GroupoidsOver.structureSheafMap φ)
    (GroupoidsOver.structureSheafIso φ).hom

/-- Derived flat-fppf module pushforward `Rf'_*`. -/
abbrev flatFppfDerivedPushforward (φ : X ⟶ Y) [Flat φ] :
    ModuleDerived.{z}
        (RingedSite.ofRingSheaf (flatFppfTopology X)
          (flatFppfInverseImageRingSheaf X)) ⥤
      ModuleDerived.{z}
        (RingedSite.ofRingSheaf (flatFppfTopology Y)
          (flatFppfInverseImageRingSheaf Y)) :=
  moduleCocontinuousDerivedPushforward (flatFppfTopology X)
    (flatFppfTopology Y) (flatFppfMap φ) (flatFppfInverseImageRingSheaf X)
    (flatFppfInverseImageRingSheaf Y) (flatFppfStructureSheafMap φ)
    (inv (flatFppfStructureSheafMap φ))

/-- `flatFppfDerivedPushforward` is the total right-derived functor of
cocontinuous flat-fppf module pushforward. -/
theorem flatFppfDerivedPushforward_eq (φ : X ⟶ Y) [Flat φ] :
    flatFppfDerivedPushforward φ =
      moduleCocontinuousDerivedPushforward (flatFppfTopology X)
        (flatFppfTopology Y) (flatFppfMap φ)
        (flatFppfInverseImageRingSheaf X) (flatFppfInverseImageRingSheaf Y)
        (flatFppfStructureSheafMap φ) (inv (flatFppfStructureSheafMap φ)) :=
  sorry

/-- Derived flat-fppf module inverse image is left adjoint to `Rf'_*`. -/
def flatFppfDerivedPushforward.adjunction (φ : X ⟶ Y) [Flat φ] :
    flatFppfDerivedInverseImage φ ⊣ flatFppfDerivedPushforward φ :=
  moduleCocontinuousDerivedPushforward.adjunction (flatFppfTopology X)
    (flatFppfTopology Y) (flatFppfMap φ) (flatFppfInverseImageRingSheaf X)
    (flatFppfInverseImageRingSheaf Y) (flatFppfStructureSheafMap φ)
    (inv (flatFppfStructureSheafMap φ))

end AlgebraicGeometry.AlgebraicStack
