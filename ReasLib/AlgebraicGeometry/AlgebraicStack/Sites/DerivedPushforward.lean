/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.CocontinuousPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.DerivedComparison

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GroupoidsOver FiberedCategoryOver.Groupoids
open RingedSite.Cocontinuous RingedSite.Hom
open scoped Bicategory

noncomputable section

universe u z

namespace AlgebraicGeometry.AlgebraicStack

/-- A bound on the successor universe also bounds the original universe. -/
private instance coefficientUniverseBound [UnivLE.{u + 1, z}] : UnivLE.{u, z} :=
  UnivLE.trans.{u, u + 1, z}

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]
variable [UnivLE.{u + 1, z}]

/-- Pointwise right Kan extensions along `(toFunctor φ).op` exist on abelian
presheaves of universe `z`. -/
instance toFunctor.op_hasPointwiseRightKanExtension_addCommGrpCat (φ : X ⟶ Y)
    (P : X.totalᵒᵖ ⥤ AddCommGrpCat.{z}) :
    (toFunctor φ).op.HasPointwiseRightKanExtension P :=
  fun y ↦
    ((hasLimitsOfSizeOfUnivLE.{z, z, u, u + 1} AddCommGrpCat.{z}).has_limits_of_shape
      _).has_limit (StructuredArrow.proj y _ ⋙ P)

/-- Pointwise right Kan extensions along `(lisseEtaleMap φ).op` exist on abelian
presheaves of universe `z`. -/
instance lisseEtaleMap.op_hasPointwiseRightKanExtension_addCommGrpCat
    (φ : X ⟶ Y) [Smooth φ] (P : (lisseEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{z}) :
    (lisseEtaleMap φ).op.HasPointwiseRightKanExtension P :=
  fun y ↦
    ((hasLimitsOfSizeOfUnivLE.{z, z, u, u + 1} AddCommGrpCat.{z}).has_limits_of_shape
      _).has_limit (StructuredArrow.proj y _ ⋙ P)

/-- Pointwise right Kan extensions along `(flatFppfMap φ).op` exist on abelian
presheaves of universe `z`. -/
instance flatFppfMap.op_hasPointwiseRightKanExtension_addCommGrpCat
    (φ : X ⟶ Y) [Flat φ] (P : (flatFppfSite X)ᵒᵖ ⥤ AddCommGrpCat.{z}) :
    (flatFppfMap φ).op.HasPointwiseRightKanExtension P :=
  fun y ↦
    ((hasLimitsOfSizeOfUnivLE.{z, z, u, u + 1} AddCommGrpCat.{z}).has_limits_of_shape
      _).has_limit (StructuredArrow.proj y _ ⋙ P)

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

/-- Derived étale abelian pushforward `Rf_*`. -/
abbrev etaleAbelianDerivedPushforward (φ : X ⟶ Y) :
    DerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf Y.etaleTopology AddCommGrpCat.{z}) :=
  CategoryTheory.Functor.AbelianPushforward.derived X.etaleTopology Y.etaleTopology (toFunctor φ)

/-- Derived étale abelian inverse image is left adjoint to `Rf_*`. -/
def etaleAbelianDerivedPushforward.adjunction (φ : X ⟶ Y) :
    etaleAbelianDerivedInverseImage φ ⊣ etaleAbelianDerivedPushforward φ :=
  CategoryTheory.Functor.AbelianPushforward.derived.adjunction X.etaleTopology Y.etaleTopology
    (toFunctor φ)

/-- Derived lisse-étale abelian pushforward `Rf'_*`. -/
abbrev lisseEtaleAbelianDerivedPushforward (φ : X ⟶ Y) [Smooth φ] :
    DerivedCategory (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf (lisseEtaleTopology Y) AddCommGrpCat.{z}) :=
  CategoryTheory.Functor.AbelianPushforward.derived (lisseEtaleTopology X) (lisseEtaleTopology Y)
    (lisseEtaleMap φ)

/-- Derived lisse-étale abelian inverse image is left adjoint to `Rf'_*`. -/
def lisseEtaleAbelianDerivedPushforward.adjunction (φ : X ⟶ Y) [Smooth φ] :
    lisseEtaleAbelianDerivedInverseImage φ ⊣
      lisseEtaleAbelianDerivedPushforward φ :=
  CategoryTheory.Functor.AbelianPushforward.derived.adjunction (lisseEtaleTopology X)
    (lisseEtaleTopology Y) (lisseEtaleMap φ)

/-- Derived fppf abelian pushforward `Rf_*`. -/
abbrev fppfAbelianDerivedPushforward (φ : X ⟶ Y) :
    DerivedCategory (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf (inheritedFppfTopology Y) AddCommGrpCat.{z}) :=
  CategoryTheory.Functor.AbelianPushforward.derived (inheritedFppfTopology X) (inheritedFppfTopology Y)
    (toFunctor φ)

/-- Derived fppf abelian inverse image is left adjoint to `Rf_*`. -/
def fppfAbelianDerivedPushforward.adjunction (φ : X ⟶ Y) :
    fppfAbelianDerivedInverseImage φ ⊣ fppfAbelianDerivedPushforward φ :=
  CategoryTheory.Functor.AbelianPushforward.derived.adjunction (inheritedFppfTopology X)
    (inheritedFppfTopology Y) (toFunctor φ)

/-- Derived flat-fppf abelian pushforward `Rf'_*`. -/
abbrev flatFppfAbelianDerivedPushforward (φ : X ⟶ Y) [Flat φ] :
    DerivedCategory (Sheaf (flatFppfTopology X) AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf (flatFppfTopology Y) AddCommGrpCat.{z}) :=
  CategoryTheory.Functor.AbelianPushforward.derived (flatFppfTopology X) (flatFppfTopology Y)
    (flatFppfMap φ)

/-- Derived flat-fppf abelian inverse image is left adjoint to `Rf'_*`. -/
def flatFppfAbelianDerivedPushforward.adjunction (φ : X ⟶ Y) [Flat φ] :
    flatFppfAbelianDerivedInverseImage φ ⊣
      flatFppfAbelianDerivedPushforward φ :=
  CategoryTheory.Functor.AbelianPushforward.derived.adjunction (flatFppfTopology X)
    (flatFppfTopology Y) (flatFppfMap φ)
/-- Derived étale module pushforward `Rf_*`. -/
abbrev etaleDerivedPushforward (φ : X ⟶ Y) :
    ModuleDerived.{z}
        (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X)) ⥤
      ModuleDerived.{z}
        (RingedSite.ofRingSheaf Y.etaleTopology (etaleStructureSheaf Y)) :=
  RingedSite.Cocontinuous.modulePushforward.derived X.etaleTopology Y.etaleTopology
    (toFunctor φ) (etaleStructureSheaf X) (etaleStructureSheaf Y)
    (etaleSiteHom_structureSheafMap φ)

/-- Derived étale module inverse image is left adjoint to `Rf_*`. -/
def etaleDerivedPushforward.adjunction (φ : X ⟶ Y) :
    etaleDerivedInverseImage φ ⊣ etaleDerivedPushforward φ :=
  RingedSite.Cocontinuous.modulePushforward.derived.adjunction X.etaleTopology
    Y.etaleTopology (toFunctor φ) (etaleStructureSheaf X)
    (etaleStructureSheaf Y) (etaleSiteHom_structureSheafMap φ)

/-- Derived lisse-étale module pushforward `Rf'_*`. -/
abbrev lisseEtaleDerivedPushforward (φ : X ⟶ Y) [Smooth φ] :
    ModuleDerived.{z}
        (RingedSite.ofRingSheaf (lisseEtaleTopology X)
          (lisseEtaleInverseImageRingSheaf X)) ⥤
      ModuleDerived.{z}
        (RingedSite.ofRingSheaf (lisseEtaleTopology Y)
          (lisseEtaleInverseImageRingSheaf Y)) :=
  RingedSite.Cocontinuous.modulePushforward.derived (lisseEtaleTopology X)
    (lisseEtaleTopology Y) (lisseEtaleMap φ)
    (lisseEtaleInverseImageRingSheaf X) (lisseEtaleInverseImageRingSheaf Y)
    (lisseEtaleStructureSheafMap φ)

/-- Derived lisse-étale module inverse image is left adjoint to `Rf'_*`. -/
def lisseEtaleDerivedPushforward.adjunction (φ : X ⟶ Y) [Smooth φ] :
    lisseEtaleDerivedInverseImage φ ⊣ lisseEtaleDerivedPushforward φ :=
  RingedSite.Cocontinuous.modulePushforward.derived.adjunction (lisseEtaleTopology X)
    (lisseEtaleTopology Y) (lisseEtaleMap φ)
    (lisseEtaleInverseImageRingSheaf X) (lisseEtaleInverseImageRingSheaf Y)
    (lisseEtaleStructureSheafMap φ)

/-- Derived fppf module pushforward `Rf_*`. -/
abbrev fppfDerivedPushforward (φ : X ⟶ Y) :
    ModuleDerived.{z}
        (RingedSite.ofRingSheaf (inheritedFppfTopology X) (structureSheaf X)) ⥤
      ModuleDerived.{z}
        (RingedSite.ofRingSheaf (inheritedFppfTopology Y) (structureSheaf Y)) :=
  RingedSite.Cocontinuous.modulePushforward.derived (inheritedFppfTopology X)
    (inheritedFppfTopology Y) (toFunctor φ) (structureSheaf X)
    (structureSheaf Y) (GroupoidsOver.structureSheafMap φ)
    (h_coeff := GroupoidsOver.structureSheafMap_isIso φ)

/-- Derived fppf module inverse image is left adjoint to `Rf_*`. -/
def fppfDerivedPushforward.adjunction (φ : X ⟶ Y) :
    fppfDerivedInverseImage φ ⊣ fppfDerivedPushforward φ :=
  RingedSite.Cocontinuous.modulePushforward.derived.adjunction (inheritedFppfTopology X)
    (inheritedFppfTopology Y) (toFunctor φ) (structureSheaf X)
    (structureSheaf Y) (GroupoidsOver.structureSheafMap φ)
    (h_coeff := GroupoidsOver.structureSheafMap_isIso φ)

/-- Derived flat-fppf module pushforward `Rf'_*`. -/
abbrev flatFppfDerivedPushforward (φ : X ⟶ Y) [Flat φ] :
    ModuleDerived.{z}
        (RingedSite.ofRingSheaf (flatFppfTopology X)
          (flatFppfInverseImageRingSheaf X)) ⥤
      ModuleDerived.{z}
        (RingedSite.ofRingSheaf (flatFppfTopology Y)
          (flatFppfInverseImageRingSheaf Y)) :=
  RingedSite.Cocontinuous.modulePushforward.derived (flatFppfTopology X)
    (flatFppfTopology Y) (flatFppfMap φ) (flatFppfInverseImageRingSheaf X)
    (flatFppfInverseImageRingSheaf Y) (flatFppfStructureSheafMap φ)

/-- Derived flat-fppf module inverse image is left adjoint to `Rf'_*`. -/
def flatFppfDerivedPushforward.adjunction (φ : X ⟶ Y) [Flat φ] :
    flatFppfDerivedInverseImage φ ⊣ flatFppfDerivedPushforward φ :=
  RingedSite.Cocontinuous.modulePushforward.derived.adjunction (flatFppfTopology X)
    (flatFppfTopology Y) (flatFppfMap φ) (flatFppfInverseImageRingSheaf X)
    (flatFppfInverseImageRingSheaf Y) (flatFppfStructureSheafMap φ)

end AlgebraicGeometry.AlgebraicStack
