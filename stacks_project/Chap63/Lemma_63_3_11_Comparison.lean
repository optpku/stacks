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

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Stalk

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

#check (AlgebraicGeometry.Scheme.Etale.geometricFiberOverField :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (ybar : GeometricPoint Y),
    SchemeOverField ybar.K)

variable [IsSeparated f] [LocallyOfFiniteType f]

#check (AlgebraicGeometry.Scheme.Etale.etaleAbelianPushforwardSectionToGeometricFiberSections f ybar :
  ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (U : Y.Etale)
    (x : (toSmallEtalePoint ybar).fiber.obj U),
    ((etaleAbelianPushforward f).obj F).obj.obj (op U) ⟶
      (abelianPullbackAlong (pullback.snd ybar.hom f) F).obj.obj
        (op (globalEtale (pullback ybar.hom f))))

#check (AlgebraicGeometry.Scheme.Etale.etaleAbelianPushforwardStalkToGeometricFiberSections f ybar :
  ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
    ((toSmallEtalePoint ybar).sheafFiber : _ ⥤ AddCommGrpCat.{u}).obj ((etaleAbelianPushforward f).obj F) ⟶
      (abelianPullbackAlong (pullback.snd ybar.hom f) F).obj.obj
        (op (globalEtale (pullback ybar.hom f))))

#check (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekStalkToCompactSupport f ybar :
  ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
    ((toSmallEtalePoint ybar).sheafFiber : _ ⥤ AddCommGrpCat.{u}).obj ((etaleLowerShriek f).obj F) ⟶
      AddCommGrpCat.of
        (globalSectionsCompactSupportSubgroup (geometricFiberOverField f ybar)
          (abelianPullbackAlong (pullback.snd ybar.hom f) F)))

#check (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekStalkToCompactSupport_comp f ybar :
  ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
    etaleLowerShriekStalkToCompactSupport f ybar F ≫
        AddCommGrpCat.ofHom
          (globalSectionsCompactSupportSubgroup (geometricFiberOverField f ybar)
            (abelianPullbackAlong (pullback.snd ybar.hom f) F)).subtype =
      ((toSmallEtalePoint ybar).sheafFiber : _ ⥤ AddCommGrpCat.{u}).map ((etaleLowerShriekι f).app F) ≫
        etaleAbelianPushforwardStalkToGeometricFiberSections f ybar F)

#check (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekStalkToCompactSupport_isIso f ybar :
  ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
    IsIso (etaleLowerShriekStalkToCompactSupport f ybar F))

end AlgebraicGeometry.Scheme.Etale

end
