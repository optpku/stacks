/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Simplicial
public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Exactness
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.Small

/-!
# Modules on the total localization of a simplicial family

The canonical augmentation and fiber morphisms are flat. Coefficient transport
identifies the fiber module restriction and its left adjoint, which is exact.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w z

namespace RingedSite.Localization.AtSimplicialSR

open SemiRepresentableFamily (OverSite overTopology overSiteDiagram overSiteTotalTopology totalForget overMap)

variable {X : RingedSite.{u, v, w}}
variable (K : SimplicialObject (FormalCoproduct.{ι} X.carrier))

/-- The total augmentation of a simplicial localization is flat. -/
theorem toAmbient_isFlat
    [UnivLE.{max ι u v, w}]
    [HasSheafify (overSiteTotalTopology X.siteTopology K) (Type w)]
    [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ Type w,
      (totalForget K).op.HasPointwiseRightKanExtension P]
    [(overSiteTotalTopology X.siteTopology K).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})] :
    ToposHom.IsFlat (toAmbient K) := by
  have h_iso := toAmbient_structureMap_isIso K
  sorry

/-- Each degree augmentation of a simplicial localization is flat. -/
theorem stageToAmbient_isFlat (n : SimplexCategory)
    [UnivLE.{max ι u v, w}]
    [HasSheafify (overTopology X.siteTopology (K.obj (op n))) (Type w)]
    [∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type w,
      (SemiRepresentableFamily.forget (K.obj (op n))).op.HasPointwiseRightKanExtension P]
    [(overTopology X.siteTopology (K.obj (op n))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})] :
    ToposHom.IsFlat (stageToAmbient K n) := by
  have h_iso := AtSR.toAmbient_structureMap_isIso (K.obj (op n))
  sorry

/-- The morphism of ringed topoi induced by a simplex operator is flat. -/
theorem stageMap_isFlat {m n : SimplexCategory} (φ : m ⟶ n)
    [UnivLE.{max ι u v, w}]
    [HasSheafify (overTopology X.siteTopology (K.obj (op n))) (Type w)]
    [∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type w,
      (overMap (K.map φ.op)).op.HasPointwiseRightKanExtension P]
    [(overTopology X.siteTopology (K.obj (op n))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [(overTopology X.siteTopology (K.obj (op m))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})] :
    ToposHom.IsFlat (stageMap K φ) := by
  have h_iso := AtSR.map_structureMap_isIso (K.map φ.op)
  sorry

/-- The ringed inclusion of each fiber in the total localization is flat. -/
theorem stageIncl_isFlat (n : SimplexCategory)
    [UnivLE.{max ι u v, w}]
    [HasSheafify (overTopology X.siteTopology (K.obj (op n))) (Type w)]
    [∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type w,
      (Grothendieck.ι (overSiteDiagram K) (op n)).op.HasPointwiseRightKanExtension P]
    [(overTopology X.siteTopology (K.obj (op n))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [(overSiteTotalTopology X.siteTopology K).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [h_ι_cont : (Grothendieck.ι (overSiteDiagram K) (op n)).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) (overSiteTotalTopology X.siteTopology K)] :
    ToposHom.IsFlat (stageIncl K n) := by
  have h_iso := stageIncl_structureMap_isIso K n
  sorry

/-- Module pullback along the total augmentation is exact. -/
theorem toAmbient_modulePullback_exact
    [UnivLE.{max ι u v, w}]
    [HasSheafify (overSiteTotalTopology X.siteTopology K) (Type w)]
    [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ Type w,
      (totalForget K).op.HasPointwiseRightKanExtension P]
    [(overSiteTotalTopology X.siteTopology K).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [(SheafOfModules.restrictScalars.{w} (toAmbient K).structureMap).IsRightAdjoint] :
    exactFunctor
      (SheafOfModules.{w} X.structureSheaf)
      (SheafOfModules.{w} (site K).structureSheaf)
      (toAmbient K).modulePullback :=
  @ToposHom.IsFlat.pullback_exact _ _ _ _ (toAmbient K) inferInstance
    (toAmbient_isFlat K)

/-- Module pullback along a simplex-operator morphism is exact. -/
theorem stageMap_modulePullback_exact {m n : SimplexCategory} (φ : m ⟶ n)
    [UnivLE.{max ι u v, w}]
    [HasSheafify (overTopology X.siteTopology (K.obj (op n))) (Type w)]
    [∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type w,
      (overMap (K.map φ.op)).op.HasPointwiseRightKanExtension P]
    [(overTopology X.siteTopology (K.obj (op n))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [(overTopology X.siteTopology (K.obj (op m))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [(SheafOfModules.restrictScalars.{w} (stageMap K φ).structureMap).IsRightAdjoint] :
    exactFunctor
      (SheafOfModules.{w} (AtSR.site (K.obj (op m))).structureSheaf)
      (SheafOfModules.{w} (AtSR.site (K.obj (op n))).structureSheaf)
      (stageMap K φ).modulePullback :=
  @ToposHom.IsFlat.pullback_exact _ _ _ _ (stageMap K φ) inferInstance
    (stageMap_isFlat K φ)

/-- Module pullback along a fiber inclusion is exact. -/
theorem stageIncl_modulePullback_exact (n : SimplexCategory)
    [UnivLE.{max ι u v, w}]
    [HasSheafify (overTopology X.siteTopology (K.obj (op n))) (Type w)]
    [∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type w,
      (Grothendieck.ι (overSiteDiagram K) (op n)).op.HasPointwiseRightKanExtension P]
    [(overTopology X.siteTopology (K.obj (op n))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [(overSiteTotalTopology X.siteTopology K).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [h_ι_cont : (Grothendieck.ι (overSiteDiagram K) (op n)).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) (overSiteTotalTopology X.siteTopology K)]
    [(SheafOfModules.restrictScalars.{w} (stageIncl K n).structureMap).IsRightAdjoint] :
    exactFunctor
      (SheafOfModules.{w} (site K).structureSheaf)
      (SheafOfModules.{w} (AtSR.site (K.obj (op n))).structureSheaf)
      (stageIncl K n).modulePullback :=
  @ToposHom.IsFlat.pullback_exact _ _ _ _ (stageIncl K n) inferInstance
    (stageIncl_isFlat K n)

/-- Change of coefficients along `O_n ≅ g_n⁻¹ O`, as modules on `C / K_n`. -/
def stageInclRingSheafModulesIso (n : SimplexCategory)
    [h_ι : (Grothendieck.ι (overSiteDiagram K) (op n)).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) (overSiteTotalTopology X.siteTopology K)]
    [h_stage : (SemiRepresentableFamily.forget (K.obj (op n))).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) X.siteTopology] :
    SheafOfModules.{z} (AtSR.ringSheaf (K.obj (op n))) ⥤
      SheafOfModules.{z}
        (@Cocontinuous.inverseImageRingSheaf _ _ _ _
          (overTopology X.siteTopology (K.obj (op n)))
          (overSiteTotalTopology X.siteTopology K)
          (Grothendieck.ι (overSiteDiagram K) (op n)) h_ι (ringSheaf K)) :=
  SheafOfModules.pushforward (F := 𝟭 _)
    ((stageRingIso K n).inv ≫
      (Functor.sheafPushforwardContinuousId RingCat.{w}
        (overTopology X.siteTopology (K.obj (op n)))).inv.app
        (AtSR.ringSheaf (K.obj (op n))))

/-- The functor `g_{n!} : Mod(O_n) ⥤ Mod(O)`, obtained by transporting module lower shriek
along `ι` across `stageRingIso`. -/
def stageInclModuleLowerShriek (n : SimplexCategory)
    [h_ι : (Grothendieck.ι (overSiteDiagram K) (op n)).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) (overSiteTotalTopology X.siteTopology K)]
    [h_ι' : (Grothendieck.ι (overSiteDiagram K) (op n)).IsCocontinuous
      (overTopology X.siteTopology (K.obj (op n))) (overSiteTotalTopology X.siteTopology K)]
    [h_stage : (SemiRepresentableFamily.forget (K.obj (op n))).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) X.siteTopology] :
    SheafOfModules.{z} (AtSR.ringSheaf (K.obj (op n))) ⥤ SheafOfModules.{z} (ringSheaf K) :=
  stageInclRingSheafModulesIso K n ⋙
    @Cocontinuous.moduleLowerShriek _ _ _ _
      (overTopology X.siteTopology (K.obj (op n)))
      (overSiteTotalTopology X.siteTopology K)
      (Grothendieck.ι (overSiteDiagram K) (op n)) h_ι h_ι' (ringSheaf K)

/-- Inverse image of modules along `g_n`, as a functor `Mod(O) ⥤ Mod(O_n)`. -/
def stageInclModuleInverseImage (n : SimplexCategory)
    [h_ι : (Grothendieck.ι (overSiteDiagram K) (op n)).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) (overSiteTotalTopology X.siteTopology K)]
    [h_stage : (SemiRepresentableFamily.forget (K.obj (op n))).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) X.siteTopology] :
    SheafOfModules.{z} (ringSheaf K) ⥤ SheafOfModules.{z} (AtSR.ringSheaf (K.obj (op n))) :=
  @Cocontinuous.moduleInverseImage _ _ _ _
      (overTopology X.siteTopology (K.obj (op n)))
      (overSiteTotalTopology X.siteTopology K)
      (Grothendieck.ι (overSiteDiagram K) (op n)) h_ι (ringSheaf K) ⋙
    SheafOfModules.pushforward (F := 𝟭 _)
      ((stageRingIso K n).hom ≫
        (Functor.sheafPushforwardContinuousId RingCat.{w}
          (overTopology X.siteTopology (K.obj (op n)))).inv.app
          (@Cocontinuous.inverseImageRingSheaf _ _ _ _
            (overTopology X.siteTopology (K.obj (op n)))
            (overSiteTotalTopology X.siteTopology K)
            (Grothendieck.ι (overSiteDiagram K) (op n)) h_ι (ringSheaf K)))

-- Local declaration justification (metaprogramming implementation): Export this
-- private proof law for the Prop-valued fields of an exposed construction.
set_option backward.privateInPublic true in
/-- The inverse coefficient maps satisfy the counit compatibility for identity-site restriction. -/
private theorem stageInclCoefficient_counit (n : SimplexCategory)
    [h_ι : (Grothendieck.ι (overSiteDiagram K) (op n)).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) (overSiteTotalTopology X.siteTopology K)]
    [h_stage : (SemiRepresentableFamily.forget (K.obj (op n))).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) X.siteTopology] :
    let φ := ((stageRingIso K n).inv ≫
        (Functor.sheafPushforwardContinuousId RingCat.{w}
          (overTopology X.siteTopology (K.obj (op n)))).inv.app
          (AtSR.ringSheaf (K.obj (op n))))
    let ψ := ((stageRingIso K n).hom ≫
        (Functor.sheafPushforwardContinuousId RingCat.{w}
          (overTopology X.siteTopology (K.obj (op n)))).inv.app
          (@Cocontinuous.inverseImageRingSheaf _ _ _ _
            (overTopology X.siteTopology (K.obj (op n)))
            (overSiteTotalTopology X.siteTopology K)
            (Grothendieck.ι (overSiteDiagram K) (op n)) h_ι (ringSheaf K)))
    Functor.whiskerRight
      (NatTrans.op (Adjunction.id (C := OverSite (K.obj (op n)))).counit)
      (AtSR.ringSheaf (K.obj (op n))).obj =
      ψ.hom ≫ (𝟭 (OverSite (K.obj (op n)))).op.whiskerLeft φ.hom := sorry

-- Local declaration justification (metaprogramming implementation): Export this
-- private proof law for the Prop-valued fields of an exposed construction.
set_option backward.privateInPublic true in
/-- The inverse coefficient maps satisfy the unit compatibility for identity-site restriction. -/
private theorem stageInclCoefficient_unit (n : SimplexCategory)
    [h_ι : (Grothendieck.ι (overSiteDiagram K) (op n)).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) (overSiteTotalTopology X.siteTopology K)]
    [h_stage : (SemiRepresentableFamily.forget (K.obj (op n))).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) X.siteTopology] :
    let φ := ((stageRingIso K n).inv ≫
        (Functor.sheafPushforwardContinuousId RingCat.{w}
          (overTopology X.siteTopology (K.obj (op n)))).inv.app
          (AtSR.ringSheaf (K.obj (op n))))
    let ψ := ((stageRingIso K n).hom ≫
        (Functor.sheafPushforwardContinuousId RingCat.{w}
          (overTopology X.siteTopology (K.obj (op n)))).inv.app
          (@Cocontinuous.inverseImageRingSheaf _ _ _ _
            (overTopology X.siteTopology (K.obj (op n)))
            (overSiteTotalTopology X.siteTopology K)
            (Grothendieck.ι (overSiteDiagram K) (op n)) h_ι (ringSheaf K)))
    φ.hom ≫ (𝟭 (OverSite (K.obj (op n)))).op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight
        (NatTrans.op (Adjunction.id (C := OverSite (K.obj (op n)))).unit)
        (@Cocontinuous.inverseImageRingSheaf _ _ _ _
        (overTopology X.siteTopology (K.obj (op n)))
        (overSiteTotalTopology X.siteTopology K)
        (Grothendieck.ι (overSiteDiagram K) (op n)) h_ι (ringSheaf K)).obj = 𝟙 (@Cocontinuous.inverseImageRingSheaf _ _ _ _
        (overTopology X.siteTopology (K.obj (op n)))
        (overSiteTotalTopology X.siteTopology K)
        (Grothendieck.ι (overSiteDiagram K) (op n)) h_ι (ringSheaf K)).obj := sorry

-- Local declaration justification (metaprogramming implementation): The exposed
-- composite adjunction uses private coefficient laws only as proof arguments.
set_option backward.privateInPublic true in
/-- The functor `g_{n!}` is left adjoint to `g_n^*`, using `stageRingIso` as `O_n ≅ g_n⁻¹ O`. -/
def stageInclModuleLowerShriek_adjunction (n : SimplexCategory)
    [h_ι : (Grothendieck.ι (overSiteDiagram K) (op n)).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) (overSiteTotalTopology X.siteTopology K)]
    [h_ι' : (Grothendieck.ι (overSiteDiagram K) (op n)).IsCocontinuous
      (overTopology X.siteTopology (K.obj (op n))) (overSiteTotalTopology X.siteTopology K)]
    [h_stage : (SemiRepresentableFamily.forget (K.obj (op n))).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) X.siteTopology] :
    stageInclModuleLowerShriek K n ⊣ stageInclModuleInverseImage K n :=
  (SheafOfModules.pushforwardPushforwardAdj Adjunction.id
      ((stageRingIso K n).inv ≫
        (Functor.sheafPushforwardContinuousId RingCat.{w}
          (overTopology X.siteTopology (K.obj (op n)))).inv.app
          (AtSR.ringSheaf (K.obj (op n))))
      ((stageRingIso K n).hom ≫
        (Functor.sheafPushforwardContinuousId RingCat.{w}
          (overTopology X.siteTopology (K.obj (op n)))).inv.app
          (@Cocontinuous.inverseImageRingSheaf _ _ _ _
            (overTopology X.siteTopology (K.obj (op n)))
            (overSiteTotalTopology X.siteTopology K)
            (Grothendieck.ι (overSiteDiagram K) (op n)) h_ι (ringSheaf K)))
      (stageInclCoefficient_counit K n) (stageInclCoefficient_unit K n)).comp
    (@Cocontinuous.moduleLowerShriek.adjunction _ _ _ _
      (overTopology X.siteTopology (K.obj (op n)))
      (overSiteTotalTopology X.siteTopology K)
      (Grothendieck.ι (overSiteDiagram K) (op n)) h_ι h_ι' (ringSheaf K))

/-- Module lower shriek from a fiber to the total localization is exact before
transport of coefficients. -/
private theorem stageIncl_fiberModuleLowerShriek_exact (n : SimplexCategory)
    [UnivLE.{max ι u v, w}]
    [UnivLE.{max ι v, z}]
    [HasWeakSheafify (overSiteTotalTopology X.siteTopology K) AddCommGrpCat.{z}]
    [(overSiteTotalTopology X.siteTopology K).WEqualsLocallyBijective AddCommGrpCat.{z}]
    [∀ m, HasSheafify (overTopology X.siteTopology (K.obj (op m))) (Type w)]
    [∀ {m : SimplexCategory} (φ : n ⟶ m) (P : (OverSite (K.obj (op m)))ᵒᵖ ⥤ Type w),
      (overMap (K.map φ.op)).op.HasPointwiseRightKanExtension P]
    [∀ m, (overTopology X.siteTopology (K.obj (op m))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [∀ {m : SimplexCategory} (φ : n ⟶ m),
      (overMap (K.map φ.op)).IsCocontinuous
        (overTopology X.siteTopology (K.obj (op m)))
        (overTopology X.siteTopology (K.obj (op n)))]
    [h_ι : (Grothendieck.ι (overSiteDiagram K) (op n)).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) (overSiteTotalTopology X.siteTopology K)]
    [h_ι' : (Grothendieck.ι (overSiteDiagram K) (op n)).IsCocontinuous
      (overTopology X.siteTopology (K.obj (op n))) (overSiteTotalTopology X.siteTopology K)] :
    exactFunctor
      (SheafOfModules.{z}
        (@Cocontinuous.inverseImageRingSheaf _ _ _ _
          (overTopology X.siteTopology (K.obj (op n)))
          (overSiteTotalTopology X.siteTopology K)
          (Grothendieck.ι (overSiteDiagram K) (op n)) h_ι (ringSheaf K)))
      (SheafOfModules.{z} (ringSheaf K))
      (@Cocontinuous.moduleLowerShriek _ _ _ _
        (overTopology X.siteTopology (K.obj (op n)))
        (overSiteTotalTopology X.siteTopology K)
        (Grothendieck.ι (overSiteDiagram K) (op n)) h_ι h_ι' (ringSheaf K)) := by
  have h_flat : ∀ {m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (stageMap K φ) := fun φ ↦ stageMap_isFlat K φ
  sorry

/-- The coefficient-transported module lower shriek from a fiber to the total
localization is exact. -/
theorem stageIncl_moduleLowerShriek_exact (n : SimplexCategory)
    [UnivLE.{max ι u v, w}]
    [UnivLE.{max ι v, z}]
    [HasWeakSheafify (overSiteTotalTopology X.siteTopology K) AddCommGrpCat.{z}]
    [(overSiteTotalTopology X.siteTopology K).WEqualsLocallyBijective AddCommGrpCat.{z}]
    [∀ m, HasSheafify (overTopology X.siteTopology (K.obj (op m))) (Type w)]
    [∀ {m : SimplexCategory} (φ : n ⟶ m) (P : (OverSite (K.obj (op m)))ᵒᵖ ⥤ Type w),
      (overMap (K.map φ.op)).op.HasPointwiseRightKanExtension P]
    [∀ m, (overTopology X.siteTopology (K.obj (op m))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [∀ {m : SimplexCategory} (φ : n ⟶ m),
      (overMap (K.map φ.op)).IsCocontinuous
        (overTopology X.siteTopology (K.obj (op m)))
        (overTopology X.siteTopology (K.obj (op n)))]
    [h_ι : (Grothendieck.ι (overSiteDiagram K) (op n)).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) (overSiteTotalTopology X.siteTopology K)]
    [h_ι' : (Grothendieck.ι (overSiteDiagram K) (op n)).IsCocontinuous
      (overTopology X.siteTopology (K.obj (op n))) (overSiteTotalTopology X.siteTopology K)]
    [h_stage : (SemiRepresentableFamily.forget (K.obj (op n))).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) X.siteTopology] :
    exactFunctor
      (SheafOfModules.{z} (AtSR.ringSheaf (K.obj (op n))))
      (SheafOfModules.{z} (ringSheaf K))
      (stageInclModuleLowerShriek K n) := by
  have h_exact :
    exactFunctor
      (SheafOfModules.{z}
        (@Cocontinuous.inverseImageRingSheaf _ _ _ _
          (overTopology X.siteTopology (K.obj (op n)))
          (overSiteTotalTopology X.siteTopology K)
          (Grothendieck.ι (overSiteDiagram K) (op n)) h_ι (ringSheaf K)))
      (SheafOfModules.{z} (ringSheaf K))
      (@Cocontinuous.moduleLowerShriek _ _ _ _
        (overTopology X.siteTopology (K.obj (op n)))
        (overSiteTotalTopology X.siteTopology K)
        (Grothendieck.ι (overSiteDiagram K) (op n)) h_ι h_ι' (ringSheaf K)) :=
    stageIncl_fiberModuleLowerShriek_exact K n
  sorry

end RingedSite.Localization.AtSimplicialSR
