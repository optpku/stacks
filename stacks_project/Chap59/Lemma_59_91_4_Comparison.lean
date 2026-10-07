module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import stacks_project.Chap59.Lemma_59_82_2
public import stacks_project.Chap59.Proposition_59_47_1
public import stacks_project.Chap59.Remark_59_56_6_StalkFunctor
public import stacks_project.Chap59.Remark_59_75_1_Alternative_description_of_sp_Pullback

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

/-- The scheme morphism from the geometric fibre `X ×_S Spec κ(s̄)` to the
base change of an étale object `U` of `S` along `f`, induced by a lift of `s̄`
to `U`. -/
def geometricFiberToBaseChange {U : S.Etale}
    (x : (GeometricPoint.toSmallEtalePoint s).fiber.obj U) :
    pullback f s.hom ⟶ ((smallEtalePullback f).obj U).left :=
  pullback.lift (pullback.snd f s.hom ≫ x.left) (pullback.fst f s.hom) sorry

/-- The morphism of small-étale objects of the geometric fibre from the identity
object to the base change of `U` along the fibre inclusion. -/
def geometricFiberIdentityToBaseChange {U : S.Etale}
    (x : (GeometricPoint.toSmallEtalePoint s).fiber.obj U) :
    (MorphismProperty.Over.mk _ (𝟙 (pullback f s.hom)) inferInstance :
        (pullback f s.hom).Etale) ⟶
      (smallEtalePullback (pullback.fst f s.hom)).obj ((smallEtalePullback f).obj U) :=
  MorphismProperty.Over.homMk
    (pullback.lift (geometricFiberToBaseChange f s x) (𝟙 (pullback f s.hom)) sorry)
    sorry

/-- Component of the comparison on an étale neighbourhood of `s̄`. -/
def etalePushforwardSectionToGeometricFiberSections
    (F : Sheaf X.smallEtaleTopology (Type u)) (U : S.Etale)
    (x : (GeometricPoint.toSmallEtalePoint s).fiber.obj U)
    (t : ((CategoryTheory.sheafToPresheaf S.smallEtaleTopology (Type u)).obj
        ((smallEtalePushforwardType f).obj F)).obj (op U)) :
    etaleGlobalSections (smallEtaleSheafPullback (pullback.fst f s.hom) F) :=
  (smallEtaleSheafPullback (pullback.fst f s.hom) F).obj.map
    (op (geometricFiberIdentityToBaseChange f s x))
    (((smallEtalePullback (pullback.fst f s.hom)).sheafPushforwardContinuousObjObjIso
        (Type u) (smallEtaleSheafPullback (pullback.fst f s.hom) F)
        ((smallEtalePullback f).obj U)).hom
      ((((smallEtalePullback (pullback.fst f s.hom)).sheafAdjunctionContinuous
            (Type u) X.smallEtaleTopology
            (pullback f s.hom).smallEtaleTopology).unit.app F).hom.app
        (op ((smallEtalePullback f).obj U)) t))

/-- Canonical comparison `(f_* F)_{s̄} ⟶ Γ(X_{s̄}, F|_{X_{s̄}})` on sheaves of sets,
where `X_{s̄}` is the geometric fibre `pullback f s.hom`. -/
def etalePushforwardStalkToGeometricFiberSections
    (F : Sheaf X.smallEtaleTopology (Type u)) :
    (stalkFunctor s).obj ((smallEtalePushforwardType f).obj F) →
      etaleGlobalSections
        (smallEtaleSheafPullback (pullback.fst f s.hom) F) :=
  colimit.desc
    ((CategoryOfElements.π (GeometricPoint.toSmallEtalePoint s).fiber).op ⋙
      (CategoryTheory.sheafToPresheaf S.smallEtaleTopology (Type u)).obj
        ((smallEtalePushforwardType f).obj F))
    { pt := etaleGlobalSections (smallEtaleSheafPullback (pullback.fst f s.hom) F)
      ι :=
        { app := fun x ↦
            TypeCat.ofHom
              (etalePushforwardSectionToGeometricFiberSections f s F x.unop.1 x.unop.2)
          naturality := sorry } }

/-- The comparison is the site-point fibre descent of restriction along
`X_{s̄} ⟶ X ×_S U` for étale neighbourhoods `U` of `s̄`. -/
theorem etalePushforwardStalkToGeometricFiberSections_apply
    (F : Sheaf X.smallEtaleTopology (Type u))
    (U : S.Etale) (x : (GeometricPoint.toSmallEtalePoint s).fiber.obj U)
    (t : ((CategoryTheory.sheafToPresheaf S.smallEtaleTopology (Type u)).obj
        ((smallEtalePushforwardType f).obj F)).obj (op U)) :
    etalePushforwardStalkToGeometricFiberSections f s F
        ((GeometricPoint.toSmallEtalePoint s).toPresheafFiber U x
          ((CategoryTheory.sheafToPresheaf S.smallEtaleTopology (Type u)).obj ((smallEtalePushforwardType f).obj F)) t) =
      (smallEtaleSheafPullback (pullback.fst f s.hom) F).obj.map
        (op (geometricFiberIdentityToBaseChange f s x))
        (((smallEtalePullback (pullback.fst f s.hom)).sheafPushforwardContinuousObjObjIso
            (Type u) (smallEtaleSheafPullback (pullback.fst f s.hom) F)
            ((smallEtalePullback f).obj U)).hom
          ((((smallEtalePullback (pullback.fst f s.hom)).sheafAdjunctionContinuous
                (Type u) X.smallEtaleTopology
                (pullback f s.hom).smallEtaleTopology).unit.app F).hom.app
            (op ((smallEtalePullback f).obj U)) t)) :=
  sorry

end AlgebraicGeometry.Scheme.Hom

end
