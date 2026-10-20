/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GeometricPointSections
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SectionsPullback

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) (s : GeometricPoint S)
variable [HasWeakSheafify X.smallEtaleTopology (Type u)]
variable [HasWeakSheafify S.smallEtaleTopology (Type u)]
variable [HasWeakSheafify (pullback f s.hom).smallEtaleTopology (Type u)]
variable [∀ P : X.Etaleᵒᵖ ⥤ Type u,
  (smallEtalePullback (pullback.fst f s.hom)).op.HasLeftKanExtension P]

/-- A lift of a geometric point to an étale object induces a morphism from the
geometric fibre to the base change of that étale object. -/
def geometricFiberToBaseChange {U : S.Etale}
    (x : (GeometricPoint.toSmallEtalePoint s).fiber.obj U) :
    pullback f s.hom ⟶ ((smallEtalePullback f).obj U).left :=
  pullback.lift (pullback.snd f s.hom ≫ x.left) (pullback.fst f s.hom) (by
    calc
      (pullback.snd f s.hom ≫ x.left) ≫ U.hom =
          pullback.snd f s.hom ≫ (x.left ≫ U.hom) := Category.assoc _ _ _
      _ = pullback.snd f s.hom ≫ s.hom :=
        congrArg (fun lift ↦ pullback.snd f s.hom ≫ lift) (Over.w x)
      _ = pullback.fst f s.hom ≫ f := pullback.condition.symm)

/-- A pointed étale neighbourhood induces a morphism from the identity étale
object of the geometric fibre to the pullback of that neighbourhood. -/
def geometricFiberIdentityToBaseChange {U : S.Etale}
    (x : (GeometricPoint.toSmallEtalePoint s).fiber.obj U) :
    (MorphismProperty.Over.mk _ (𝟙 (pullback f s.hom)) inferInstance :
        (pullback f s.hom).Etale) ⟶
      (smallEtalePullback (pullback.fst f s.hom)).obj ((smallEtalePullback f).obj U) :=
  MorphismProperty.Over.homMk
    (pullback.lift (geometricFiberToBaseChange f s x) (𝟙 (pullback f s.hom)) (by
      change geometricFiberToBaseChange f s x ≫ pullback.snd U.hom f =
        𝟙 (pullback f s.hom) ≫ pullback.fst f s.hom
      exact (pullback.lift_snd _ _ _).trans (Category.id_comp _).symm))
    (by exact pullback.lift_snd _ _ _)

/-- A direct-image section on a pointed étale neighbourhood restricts to a
global section of the inverse-image sheaf on the geometric fibre. -/
def etalePushforwardSectionToGeometricFiberSections
    (F : Sheaf X.smallEtaleTopology (Type u)) (U : S.Etale)
    (x : (GeometricPoint.toSmallEtalePoint s).fiber.obj U)
    (t : ((CategoryTheory.sheafToPresheaf S.smallEtaleTopology (Type u)).obj
        ((Scheme.smallEtaleDirectImage.{u, u} f).obj F)).obj (op U)) :
    etaleGlobalSections
      ((Sheaf.smallEtaleInverseImage (pullback.fst f s.hom) (Type u)).obj F) :=
  ((Sheaf.smallEtaleInverseImage (pullback.fst f s.hom) (Type u)).obj F).obj.map
    (op (geometricFiberIdentityToBaseChange f s x))
    (((smallEtalePullback (pullback.fst f s.hom)).sheafPushforwardContinuousObjObjIso
        (Type u) ((Sheaf.smallEtaleInverseImage (pullback.fst f s.hom) (Type u)).obj F)
        ((smallEtalePullback f).obj U)).hom
      ((((smallEtalePullback (pullback.fst f s.hom)).sheafAdjunctionContinuous
            (Type u) X.smallEtaleTopology
            (pullback f s.hom).smallEtaleTopology).unit.app F).hom.app
        (op ((smallEtalePullback f).obj U)) t))

/-- Restriction to the geometric fibre is natural in pointed étale neighbourhoods. -/
theorem etalePushforwardSectionToGeometricFiberSections_naturality
    (F : Sheaf X.smallEtaleTopology (Type u))
    {first second : (GeometricPoint.toSmallEtalePoint s).fiber.Elementsᵒᵖ}
    (morphism : first ⟶ second) :
    (((CategoryOfElements.π (GeometricPoint.toSmallEtalePoint s).fiber).op ⋙
      (CategoryTheory.sheafToPresheaf S.smallEtaleTopology (Type u)).obj
        ((Scheme.smallEtaleDirectImage.{u, u} f).obj F)).map morphism) ≫
        TypeCat.ofHom (etalePushforwardSectionToGeometricFiberSections f s F
          second.unop.1 second.unop.2) =
      TypeCat.ofHom (etalePushforwardSectionToGeometricFiberSections f s F
        first.unop.1 first.unop.2) ≫
          𝟙 (etaleGlobalSections
            ((Sheaf.smallEtaleInverseImage (pullback.fst f s.hom) (Type u)).obj F)) :=
  sorry

/-- The canonical comparison from the geometric stalk of a direct-image sheaf
to global sections of its inverse image on the geometric fibre. -/
def etalePushforwardStalkToGeometricFiberSections
    (F : Sheaf X.smallEtaleTopology (Type u)) :
    (stalkFunctor s).obj ((Scheme.smallEtaleDirectImage.{u, u} f).obj F) →
      etaleGlobalSections
        ((Sheaf.smallEtaleInverseImage (pullback.fst f s.hom) (Type u)).obj F) :=
  colimit.desc
    ((CategoryOfElements.π (GeometricPoint.toSmallEtalePoint s).fiber).op ⋙
      (CategoryTheory.sheafToPresheaf S.smallEtaleTopology (Type u)).obj
        ((Scheme.smallEtaleDirectImage.{u, u} f).obj F))
    { pt := etaleGlobalSections
        ((Sheaf.smallEtaleInverseImage (pullback.fst f s.hom) (Type u)).obj F)
      ι :=
        { app := fun x ↦
            TypeCat.ofHom
              (etalePushforwardSectionToGeometricFiberSections f s F x.unop.1 x.unop.2)
          naturality := fun _ _ morphism ↦
            etalePushforwardSectionToGeometricFiberSections_naturality f s F morphism } }

/-- On a neighbourhood germ, the stalk comparison is restriction along the
induced morphism from the geometric fibre to the base-changed neighbourhood. -/
theorem etalePushforwardStalkToGeometricFiberSections_apply
    (F : Sheaf X.smallEtaleTopology (Type u))
    (U : S.Etale) (x : (GeometricPoint.toSmallEtalePoint s).fiber.obj U)
    (t : ((CategoryTheory.sheafToPresheaf S.smallEtaleTopology (Type u)).obj
        ((Scheme.smallEtaleDirectImage.{u, u} f).obj F)).obj (op U)) :
    etalePushforwardStalkToGeometricFiberSections f s F
        ((GeometricPoint.toSmallEtalePoint s).toPresheafFiber U x
          ((CategoryTheory.sheafToPresheaf S.smallEtaleTopology (Type u)).obj
            ((Scheme.smallEtaleDirectImage.{u, u} f).obj F)) t) =
      ((Sheaf.smallEtaleInverseImage (pullback.fst f s.hom) (Type u)).obj F).obj.map
        (op (geometricFiberIdentityToBaseChange f s x))
        (((smallEtalePullback (pullback.fst f s.hom)).sheafPushforwardContinuousObjObjIso
            (Type u) ((Sheaf.smallEtaleInverseImage (pullback.fst f s.hom) (Type u)).obj F)
            ((smallEtalePullback f).obj U)).hom
          ((((smallEtalePullback (pullback.fst f s.hom)).sheafAdjunctionContinuous
                (Type u) X.smallEtaleTopology
                (pullback f s.hom).smallEtaleTopology).unit.app F).hom.app
            (op ((smallEtalePullback f).obj U)) t)) :=
  sorry

/-- For a proper morphism of schemes, the canonical comparison from a geometric
stalk of direct image to sections on the geometric fibre is bijective. -/
theorem etalePushforwardStalk_bijective_of_isProper
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (s : GeometricPoint S)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasWeakSheafify S.smallEtaleTopology (Type u)]
    [HasWeakSheafify (pullback f s.hom).smallEtaleTopology (Type u)]
    [∀ P : X.Etaleᵒᵖ ⥤ Type u,
      (smallEtalePullback (pullback.fst f s.hom)).op.HasLeftKanExtension P]
    (F : Sheaf X.smallEtaleTopology (Type u)) :
    Function.Bijective (etalePushforwardStalkToGeometricFiberSections f s F) := sorry

end AlgebraicGeometry.Scheme.Hom

end
