/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SheafPullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Abelian
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CompactSupport

/-!
# Stalk comparison for étale lower shriek versus compactly supported fibre sections

If `f : X ⟶ Y` is separated and locally of finite type, the stalk of `f_! F`
at a geometric point `ȳ` compares with `H^0_c` of the restriction of `F` to the
geometric fibre `ȳ ×_Y X`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology.Point
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Hom
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (ybar : GeometricPoint Y)

/-- The geometric fibre `X_ȳ = ȳ ×_Y X` as a scheme over the algebraically
closed field of `ȳ`. This is `Over.mk` of `pullback.fst ȳ.hom f`, i.e. the
same chosen representative as `Hom.geometricFiber`. -/
abbrev geometricFiberOverField : SchemeOverField ybar.K :=
  { left := pullback ybar.hom f, right := ⟨⟨⟩⟩, hom := pullback.fst ybar.hom f }

/-- The structure morphism of `geometricFiberOverField` is the first projection
of `ȳ ×_Y X`. -/
theorem geometricFiberOverField_hom :
    (geometricFiberOverField f ybar).hom = pullback.fst ybar.hom f :=
  sorry

/-- The underlying scheme of `geometricFiberOverField` is the chosen pullback
`ȳ ×_Y X`. -/
theorem geometricFiberOverField_left :
    (geometricFiberOverField f ybar).left = pullback ybar.hom f :=
  sorry

-- Keep the geometric lifts private while allowing their use in the public restriction map.
set_option backward.privateInPublic true in
/-- The scheme morphism from the geometric fibre `ȳ ×_Y X` to the base change
`X_U` of an étale object `U` of `Y` along `f`, induced by a lift of `ȳ` to
`U`. -/
private def geometricFiberToBaseChange {U : Y.Etale}
    (x : (toSmallEtalePoint ybar).fiber.obj U) :
    pullback ybar.hom f ⟶ ((smallEtalePullback f).obj U).left :=
  pullback.lift (pullback.fst ybar.hom f ≫ x.left) (pullback.snd ybar.hom f) (by
    calc
      (pullback.fst ybar.hom f ≫ x.left) ≫ U.hom =
          pullback.fst ybar.hom f ≫ (x.left ≫ U.hom) := Category.assoc _ _ _
      _ = pullback.fst ybar.hom f ≫ ybar.hom :=
        congrArg (fun lift ↦ pullback.fst ybar.hom f ≫ lift) (Over.w x)
      _ = pullback.snd ybar.hom f ≫ f := pullback.condition)

set_option backward.privateInPublic true in
/-- The morphism of small-étale objects of the geometric fibre from the identity
object to the base change of `U` along the fibre inclusion `X_ȳ ⟶ X`. -/
private def geometricFiberIdentityToBaseChange {U : Y.Etale}
    (x : (toSmallEtalePoint ybar).fiber.obj U) :
    (MorphismProperty.Over.mk _ (𝟙 (pullback ybar.hom f)) inferInstance :
        (pullback ybar.hom f).Etale) ⟶
      (smallEtalePullback (pullback.snd ybar.hom f)).obj
        ((smallEtalePullback f).obj U) :=
  MorphismProperty.Over.homMk
    (pullback.lift (geometricFiberToBaseChange f ybar x) (𝟙 (pullback ybar.hom f))
      (by
        change geometricFiberToBaseChange f ybar x ≫ pullback.snd U.hom f =
          𝟙 (pullback ybar.hom f) ≫ pullback.snd ybar.hom f
        exact (pullback.lift_snd _ _ _).trans (Category.id_comp _).symm))
    (by exact pullback.lift_snd _ _ _)

variable [IsSeparated f] [LocallyOfFiniteType f]

/-- The structure morphism of the geometric fibre is separated, as a base change
of the separated morphism `f`. -/
theorem isSeparated_geometricFiberOverField_hom :
    IsSeparated (geometricFiberOverField f ybar).hom :=
  sorry

/-- The structure morphism of the geometric fibre is locally of finite type, as a
base change of `f`. -/
theorem locallyOfFiniteType_geometricFiberOverField_hom :
    LocallyOfFiniteType (geometricFiberOverField f ybar).hom :=
  sorry

-- The geometric lift remains private; only its composite defining restriction is public.
set_option backward.privateInPublic true in
/-- Component of the abelian comparison on an étale neighbourhood of `ȳ`: pull a
section of `f_* F` on `U` back to a global section of `F|_{X_ȳ}`. -/
def etaleAbelianPushforwardSectionToGeometricFiberSections
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (U : Y.Etale)
    (x : (toSmallEtalePoint ybar).fiber.obj U) :
    ((smallEtalePushforwardAb f).obj F).obj.obj (op U) ⟶
      (abelianPullbackAlong (pullback.snd ybar.hom f) F).obj.obj
        (op (globalEtale (pullback ybar.hom f))) :=
  ((((smallEtalePullback (pullback.snd ybar.hom f)).sheafAdjunctionContinuous
          AddCommGrpCat.{u} X.smallEtaleTopology
          (pullback ybar.hom f).smallEtaleTopology).unit.app F).hom.app
      (op ((smallEtalePullback f).obj U))) ≫
    ((smallEtalePullback (pullback.snd ybar.hom f)).sheafPushforwardContinuousObjObjIso
        AddCommGrpCat.{u} (abelianPullbackAlong (pullback.snd ybar.hom f) F)
        ((smallEtalePullback f).obj U)).hom ≫
    (abelianPullbackAlong (pullback.snd ybar.hom f) F).obj.map
      (op (geometricFiberIdentityToBaseChange f ybar x))

/-- Restriction to the geometric fibre commutes with morphisms of pointed
étale neighbourhoods. -/
theorem etaleAbelianPushforwardSectionToGeometricFiberSections_naturality
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {U V : Y.Etale}
    (g : U ⟶ V) (x : (toSmallEtalePoint ybar).fiber.obj U) :
    ((smallEtalePushforwardAb f).obj F).obj.map g.op ≫
        etaleAbelianPushforwardSectionToGeometricFiberSections f ybar F U x =
      etaleAbelianPushforwardSectionToGeometricFiberSections f ybar F V
        ((toSmallEtalePoint ybar).fiber.map g x) :=
  sorry

/-- Restriction of neighbourhood sections descends to a canonical morphism
from the geometric stalk of the abelian direct image to global sections on
the geometric fibre. -/
def etaleAbelianPushforwardStalkToGeometricFiberSections
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    ((toSmallEtalePoint ybar).sheafFiber : _ ⥤ AddCommGrpCat.{u}).obj ((smallEtalePushforwardAb f).obj F) ⟶
      (abelianPullbackAlong (pullback.snd ybar.hom f) F).obj.obj
        (op (globalEtale (pullback ybar.hom f))) :=
  (toSmallEtalePoint ybar).presheafFiberDesc
    (fun U x ↦
      etaleAbelianPushforwardSectionToGeometricFiberSections f ybar F U x)
    (fun {_ _} g x ↦
      etaleAbelianPushforwardSectionToGeometricFiberSections_naturality f ybar F g x)

/-- The abelian `f_*` comparison is fibre descent of restriction along
`X_ȳ ⟶ X_U` for étale neighbourhoods `U` of `ȳ`. -/
theorem etaleAbelianPushforwardStalkToGeometricFiberSections_apply
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (U : Y.Etale)
    (x : (toSmallEtalePoint ybar).fiber.obj U) :
    (toSmallEtalePoint ybar).toPresheafFiber U x
          ((smallEtalePushforwardAb f).obj F).obj ≫
        etaleAbelianPushforwardStalkToGeometricFiberSections f ybar F =
      etaleAbelianPushforwardSectionToGeometricFiberSections f ybar F U x :=
  sorry

/-- The comparison `c_ȳ` sends stalks of `f_! F` into compactly supported
global sections on the geometric fibre. -/
theorem mem_globalSectionsCompactSupport_etaleLowerShriekStalk
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (σ : ((toSmallEtalePoint ybar).sheafFiber : _ ⥤ AddCommGrpCat.{u}).obj ((etaleLowerShriek f).obj F)) :
    (etaleAbelianPushforwardStalkToGeometricFiberSections f ybar F).hom
        ((((toSmallEtalePoint ybar).sheafFiber : _ ⥤ AddCommGrpCat.{u}).map
          ((etaleLowerShriekι f).app F)).hom σ) ∈
      globalSectionsCompactSupportSubgroup (geometricFiberOverField f ybar)
        (abelianPullbackAlong (pullback.snd ybar.hom f) F) :=
  sorry

/-- Canonical comparison `(f_! F)_ȳ ⟶ H^0_c(X_ȳ, F|_{X_ȳ})`, obtained by
restricting `c_ȳ` along the inclusion `f_! ⟶ f_*`. -/
def etaleLowerShriekStalkToCompactSupport
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    ((toSmallEtalePoint ybar).sheafFiber : _ ⥤ AddCommGrpCat.{u}).obj ((etaleLowerShriek f).obj F) ⟶
      AddCommGrpCat.of
        (globalSectionsCompactSupportSubgroup (geometricFiberOverField f ybar)
          (abelianPullbackAlong (pullback.snd ybar.hom f) F)) :=
  AddCommGrpCat.ofHom
    (((etaleAbelianPushforwardStalkToGeometricFiberSections f ybar F).hom.comp
        (((toSmallEtalePoint ybar).sheafFiber : _ ⥤ AddCommGrpCat.{u}).map
          ((etaleLowerShriekι f).app F)).hom).codRestrict
      (globalSectionsCompactSupportSubgroup (geometricFiberOverField f ybar)
        (abelianPullbackAlong (pullback.snd ybar.hom f) F))
      (mem_globalSectionsCompactSupport_etaleLowerShriekStalk f ybar F))

/-- The compact-support comparison fits in a commutative square with
`etaleLowerShriekι` and the inclusion of `H^0_c` into global sections. -/
theorem etaleLowerShriekStalkToCompactSupport_comp
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleLowerShriekStalkToCompactSupport f ybar F ≫
        AddCommGrpCat.ofHom
          (globalSectionsCompactSupportSubgroup (geometricFiberOverField f ybar)
            (abelianPullbackAlong (pullback.snd ybar.hom f) F)).subtype =
      ((toSmallEtalePoint ybar).sheafFiber : _ ⥤ AddCommGrpCat.{u}).map ((etaleLowerShriekι f).app F) ≫
        etaleAbelianPushforwardStalkToGeometricFiberSections f ybar F :=
  sorry

/-- The comparison `(f_! F)_ȳ ⟶ H^0_c(X_ȳ, F|_{X_ȳ})` is an isomorphism. -/
theorem etaleLowerShriekStalkToCompactSupport_isIso
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso (etaleLowerShriekStalkToCompactSupport f ybar F) :=
  sorry

end

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
variable (ybar : GeometricPoint Y)

/-- For a separated, locally finite-type morphism, the stalk of direct image
with proper support is canonically isomorphic to compactly supported global
sections on the geometric fibre. -/
def etaleLowerShriekStalkCompactSupportIso
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    ((toSmallEtalePoint ybar).sheafFiber : _ ⥤ AddCommGrpCat.{u}).obj ((etaleLowerShriek f).obj F) ≅
      AddCommGrpCat.of
        (globalSectionsCompactSupportSubgroup (geometricFiberOverField f ybar)
          (abelianPullbackAlong (pullback.snd ybar.hom f) F)) :=
  @asIso _ _ _ _ (etaleLowerShriekStalkToCompactSupport f ybar F)
    (etaleLowerShriekStalkToCompactSupport_isIso f ybar F)

/-- The forward map of `etaleLowerShriekStalkCompactSupportIso` is the
compact-support stalk comparison. -/
theorem etaleLowerShriekStalkCompactSupportIso_hom
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleLowerShriekStalkCompactSupportIso f ybar F).hom =
      etaleLowerShriekStalkToCompactSupport f ybar F :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
