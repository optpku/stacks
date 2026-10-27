/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module.Restriction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Associated
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Sheafification.Sites
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AtlasCharts
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # Module inverse image from a representing small étale site -/

@[expose] public section

set_option backward.privateInPublic true

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
  CategoryTheory.Limits Opposite
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.PiModulePullback

variable {S : Scheme.{u}} {F : AlgebraicSpace S} {X : GroupoidsOver S}

private instance etaleWeakSheafify (X : GroupoidsOver S) :
    HasWeakSheafify X.etaleTopology AddCommGrpCat.{u} :=
  Sheafification.Etale.stackHasWeakSheafify X

private instance identityLocallyInjective (X : GroupoidsOver S) :
    Presheaf.IsLocallyInjective X.etaleTopology (𝟙 (etaleStructureSheaf X).obj) :=
  Presheaf.isLocallyInjective_of_injective _ _ (fun _ => Function.injective_id)

private instance identityLocallySurjective (X : GroupoidsOver S) :
    Presheaf.IsLocallySurjective X.etaleTopology (𝟙 (etaleStructureSheaf X).obj) :=
  Presheaf.isLocallySurjective_of_surjective _ _ (fun _ => Function.surjective_id)

private def chartRing (F : AlgebraicSpace S) :
    Sheaf (AlgebraicSpace.SmallEtale.AtlasCharts.topology F) RingCat.{u} :=
  ((AlgebraicSpace.SmallEtale.AtlasCharts.inclusion F).sheafPushforwardContinuous
    RingCat.{u} (AlgebraicSpace.SmallEtale.AtlasCharts.topology F)
      (AlgebraicSpace.smallEtaleTopology F)).obj (AlgebraicSpace.structureSheaf F)

private def chartRestriction (F : AlgebraicSpace S) :
    SheafOfModules.{u} (AlgebraicSpace.structureSheaf F) ⥤
      SheafOfModules.{u} (chartRing F) :=
  SheafOfModules.pushforward (F := AlgebraicSpace.SmallEtale.AtlasCharts.inclusion F)
    (𝟙 (chartRing F))

private def chartPreimageUnderlying
    {M N : SheafOfModules.{u} (AlgebraicSpace.structureSheaf F)}
    (f : (chartRestriction F).obj M ⟶ (chartRestriction F).obj N) :
    M.val.presheaf ⟶ N.val.presheaf :=
  Functor.IsCoverDense.sheafHom (G := AlgebraicSpace.SmallEtale.AtlasCharts.inclusion F)
    (ℱ' := ⟨N.val.presheaf, N.isSheaf⟩)
    ((PresheafOfModules.toPresheaf _).map f.val)

/-- Extension of an additive module morphism from the small affine chart family
commutes with multiplication by sections of the structure sheaf. -/
theorem left_laws
    {M N : SheafOfModules.{u} (AlgebraicSpace.structureSheaf F)}
    (f : (chartRestriction F).obj M ⟶ (chartRestriction F).obj N)
    (U : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ)
    (r : (AlgebraicSpace.structureSheaf F).obj.obj U) (m : M.val.obj U) :
    (chartPreimageUnderlying f).app U (r • m) =
      r • (chartPreimageUnderlying f).app U m := by
  sorry

private def chartPreimage
    {M N : SheafOfModules.{u} (AlgebraicSpace.structureSheaf F)}
    (f : (chartRestriction F).obj M ⟶ (chartRestriction F).obj N) : M ⟶ N where
  val := PresheafOfModules.homMk (chartPreimageUnderlying f) (left_laws f)

/-- Restriction and extension of module morphisms on a dense affine chart family
are inverse operations. -/
theorem adjunction_laws :
    (∀ {M N : SheafOfModules.{u} (AlgebraicSpace.structureSheaf F)}
      (f : (chartRestriction F).obj M ⟶ (chartRestriction F).obj N),
      (chartRestriction F).map (chartPreimage f) = f) ∧
    (∀ {M N : SheafOfModules.{u} (AlgebraicSpace.structureSheaf F)} (f : M ⟶ N),
      chartPreimage ((chartRestriction F).map f) = f) := by
  sorry

private def chartFullyFaithful (F : AlgebraicSpace S) :
    (chartRestriction F).FullyFaithful where
  preimage f := chartPreimage f
  map_preimage f := adjunction_laws.1 f
  preimage_map f := adjunction_laws.2 f

private def chartFunctor (e : F.toGroupoids ≌ X) :
    AlgebraicSpace.SmallEtale.AtlasCharts.Site F ⥤ X.total :=
  AlgebraicSpace.SmallEtale.AtlasCharts.inclusion F ⋙ smallEtaleFunctor F X e

private instance chartFunctor_continuous (e : F.toGroupoids ≌ X) :
    (chartFunctor e).IsContinuous
      (AlgebraicSpace.SmallEtale.AtlasCharts.topology F) X.etaleTopology :=
  Functor.isContinuous_comp (AlgebraicSpace.SmallEtale.AtlasCharts.inclusion F)
    (smallEtaleFunctor F X e) (AlgebraicSpace.SmallEtale.AtlasCharts.topology F)
    (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology

private def chartCoefficient (e : F.toGroupoids ≌ X) :
    chartRing F ⟶ ((chartFunctor e).sheafPushforwardContinuous RingCat.{u}
      (AlgebraicSpace.SmallEtale.AtlasCharts.topology F) X.etaleTopology).obj
        (etaleStructureSheaf X) :=
  ⟨whiskerLeft (AlgebraicSpace.SmallEtale.AtlasCharts.inclusion F).op
    (pi F X e).structureSheafMap.hom⟩

private def freeChartCorepresentable (e : F.toGroupoids ≌ X)
    (U : AlgebraicSpace.SmallEtale.AtlasCharts.Site F) :
    (PresheafOfModules.pushforward (chartCoefficient e).hom ⋙
      coyoneda.obj (op ((PresheafOfModules.free (chartRing F).obj).obj (yoneda.obj U)))).CorepresentableBy
        ((PresheafOfModules.free (etaleStructureSheaf X).obj).obj
          (yoneda.obj ((chartFunctor e).obj U))) where
  homEquiv := PresheafOfModules.freeYonedaEquiv.trans
    (PresheafOfModules.freeYonedaEquiv
      (M := (PresheafOfModules.pushforward (chartCoefficient e).hom).obj _)).symm
  homEquiv_comp g f := PresheafOfModules.freeYonedaEquiv.injective (by
    dsimp
    erw [Equiv.apply_symm_apply, PresheafOfModules.freeYonedaEquiv_comp]
    conv_rhs => erw [PresheafOfModules.freeYonedaEquiv_comp]
    erw [Equiv.apply_symm_apply]
    rfl)

private theorem chartPresheafPullback_exists (e : F.toGroupoids ≌ X) :
    PresheafOfModules.pullbackObjIsDefined.{u} (chartCoefficient e).hom = ⊤ := by
  ext M
  simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
  apply leftAdjointObjIsDefined_of_isColimit
    M.isColimitFreeYonedaCoproductsCokernelCofork
  rintro (_ | _)
  all_goals
    apply leftAdjointObjIsDefined_colimit
      (F := PresheafOfModules.pushforward.{u} (chartCoefficient e).hom) _
    intro U
    exact (freeChartCorepresentable e U.as.1.unop).isCorepresentable

private instance chartPresheafPushforward_rightAdjoint (e : F.toGroupoids ≌ X) :
    (PresheafOfModules.pushforward.{u} (chartCoefficient e).hom).IsRightAdjoint :=
  isRightAdjoint_of_leftAdjointObjIsDefined_eq_top (chartPresheafPullback_exists e)

private def chartLeft (e : F.toGroupoids ≌ X) :
    SheafOfModules.{u} (chartRing F) ⥤ etaleModules X :=
  SheafOfModules.forget (chartRing F) ⋙
    PresheafOfModules.pullback.{u} (chartCoefficient e).hom ⋙
      @PresheafOfModules.sheafification.{u} _ _ X.etaleTopology
        (etaleStructureSheaf X).obj (etaleStructureSheaf X)
        (𝟙 (etaleStructureSheaf X).obj)
        (identityLocallyInjective X) (identityLocallySurjective X)
        inferInstance (etaleWeakSheafify X)

private def chartAdjunction (e : F.toGroupoids ≌ X) :
    chartLeft e ⊣ SheafOfModules.pushforward (chartCoefficient e) :=
  SheafOfModules.PullbackConstruction.adjunction.{u} (chartCoefficient e)

/-- The module inverse image is restriction to the actual small affine charts,
module-presheaf inverse image, and sheafification on the associated étale site. -/
def left (e : F.toGroupoids ≌ X) :
    SheafOfModules.{u} (AlgebraicSpace.structureSheaf F) ⥤ etaleModules X :=
  chartRestriction F ⋙ chartLeft e

/-- The concrete small-chart inverse image is left adjoint to restriction to
the representing space's small étale site. -/
def adjunction (e : F.toGroupoids ≌ X) : left e ⊣ restrictModules e :=
  (chartAdjunction e).restrictFullyFaithful
    (chartFullyFaithful F) (Functor.FullyFaithful.id _)
    (Functor.rightUnitor (left e)).symm
    (Functor.leftUnitor _ ≪≫
      (SheafOfModules.pushforwardComp
        (F := AlgebraicSpace.SmallEtale.AtlasCharts.inclusion F)
        (G := smallEtaleFunctor F X e) (𝟙 (chartRing F))
        (pi F X e).structureSheafMap).symm)

/-- The canonical restriction functor is a right adjoint, with its displayed
small-chart module inverse image as left adjoint. -/
instance restrictModules_isRightAdjoint (e : F.toGroupoids ≌ X) :
    (restrictModules e).IsRightAdjoint :=
  (adjunction e).isRightAdjoint

end AlgebraicGeometry.GroupoidsOver.PiModulePullback
