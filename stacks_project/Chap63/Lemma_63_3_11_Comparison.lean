/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import stacks_project.Chap59.Lemma_59_29_7
public import stacks_project.Chap59.Lemma_59_54_1
public import stacks_project.Chap59.Lemma_59_91_6_BaseChange
public import stacks_project.Chap63.Lemma_63_3_4_LowerShriek
public import stacks_project.Chap63.Remark_63_3_9_Open_embeddings_and_compactly_supported_sections_OpenImmersion

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

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (ybar : GeometricPoint Y)

/-- The geometric fibre `X_ȳ = ȳ ×_Y X` as a scheme over the algebraically
closed field of `ȳ`. This is `Over.mk` of `pullback.fst ȳ.hom f`, i.e. the
same chosen representative as `Hom.geometricFiber`. -/
abbrev geometricFiberOverField : SchemeOverField ybar.K :=
  Over.mk (pullback.fst ybar.hom f)

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

/-- The scheme morphism from the geometric fibre `ȳ ×_Y X` to the base change
`X_U` of an étale object `U` of `Y` along `f`, induced by a lift of `ȳ` to
`U`. -/
def geometricFiberToBaseChange {U : Y.Etale}
    (x : (toSmallEtalePoint ybar).fiber.obj U) :
    pullback ybar.hom f ⟶ ((smallEtalePullback f).obj U).left :=
  pullback.lift (pullback.fst ybar.hom f ≫ x.left) (pullback.snd ybar.hom f) sorry

/-- The morphism of small-étale objects of the geometric fibre from the identity
object to the base change of `U` along the fibre inclusion `X_ȳ ⟶ X`. -/
def geometricFiberIdentityToBaseChange {U : Y.Etale}
    (x : (toSmallEtalePoint ybar).fiber.obj U) :
    (MorphismProperty.Over.mk _ (𝟙 (pullback ybar.hom f)) inferInstance :
        (pullback ybar.hom f).Etale) ⟶
      (smallEtalePullback (pullback.snd ybar.hom f)).obj
        ((smallEtalePullback f).obj U) :=
  MorphismProperty.Over.homMk
    (pullback.lift (geometricFiberToBaseChange f ybar x) (𝟙 (pullback ybar.hom f))
      sorry)
    sorry

variable [IsSeparated f] [LocallyOfFiniteType f]

/-- The structure morphism of the geometric fibre is separated, as a base change
of the separated morphism `f`. -/
instance isSeparated_geometricFiberOverField_hom :
    IsSeparated (geometricFiberOverField f ybar).hom :=
  sorry

/-- The structure morphism of the geometric fibre is locally of finite type, as a
base change of `f`. -/
instance locallyOfFiniteType_geometricFiberOverField_hom :
    LocallyOfFiniteType (geometricFiberOverField f ybar).hom :=
  sorry

/-- Component of the abelian comparison on an étale neighbourhood of `ȳ`: pull a
section of `f_* F` on `U` back to a global section of `F|_{X_ȳ}`. -/
def etaleAbelianPushforwardSectionToGeometricFiberSections
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (U : Y.Etale)
    (x : (toSmallEtalePoint ybar).fiber.obj U) :
    ((etaleAbelianPushforward f).obj F).obj.obj (op U) ⟶
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

/-- Canonical comparison `(f_* F)_ȳ ⟶ H^0(X_ȳ, F|_{X_ȳ})` on abelian sheaves,
where `X_ȳ` is the geometric fibre `pullback ȳ.hom f`. This is the abelian
analogue of `Hom.etalePushforwardStalkToGeometricFiberSections`, in the
`Hom.geometricFiber` orientation. -/
def etaleAbelianPushforwardStalkToGeometricFiberSections
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    ((toSmallEtalePoint ybar).sheafFiber : _ ⥤ AddCommGrpCat.{u}).obj ((etaleAbelianPushforward f).obj F) ⟶
      (abelianPullbackAlong (pullback.snd ybar.hom f) F).obj.obj
        (op (globalEtale (pullback ybar.hom f))) :=
  (toSmallEtalePoint ybar).presheafFiberDesc
    (fun U x ↦
      etaleAbelianPushforwardSectionToGeometricFiberSections f ybar F U x)
    sorry

/-- The abelian `f_*` comparison is fibre descent of restriction along
`X_ȳ ⟶ X_U` for étale neighbourhoods `U` of `ȳ`. -/
theorem etaleAbelianPushforwardStalkToGeometricFiberSections_apply
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (U : Y.Etale)
    (x : (toSmallEtalePoint ybar).fiber.obj U) :
    (toSmallEtalePoint ybar).toPresheafFiber U x
          ((etaleAbelianPushforward f).obj F).obj ≫
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
instance etaleLowerShriekStalkToCompactSupport_isIso
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso (etaleLowerShriekStalkToCompactSupport f ybar F) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
