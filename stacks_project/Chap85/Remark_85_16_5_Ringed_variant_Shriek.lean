module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import stacks_project.Chap85.Lemma_85_11_1_Flat
public import stacks_project.Chap85.Lemma_85_6_3
public import stacks_project.Chap85.Remark_85_16_5_Ringed_variant_Ringed

/-!
# Module lower shriek and flatness for simplicial SR total localization

The functor `a_!` is module lower shriek along `totalForget` (Modules on Sites,
Lemma 18.41.1). It is left adjoint to `a^*` but not generally exact. Stage functors
`a_{n!}` and `f_{φ!}` are exact by Remark 85.15.6, so `a`, `a_n`, and `f_φ` are flat;
exactness of `g_{n!}` is then Lemma 85.6.3.
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

/-- The functor `a_! : Mod(O) ⥤ Mod(O_C)`, module lower shriek along `totalForget`.
It exists by Modules on Sites, Lemma 18.41.1 because `O = a⁻¹ O_C`, but in general
is not exact. -/
abbrev moduleLowerShriek :
    SheafOfModules.{z} (ringSheaf K) ⥤ SheafOfModules.{z} X.structureSheaf :=
  Cocontinuous.moduleLowerShriek (totalForget K) X.structureSheaf

/-- The adjunction `a_! ⊣ a^*` of module lower shriek along `totalForget` with module
inverse image. -/
def moduleLowerShriek_adjunction :
    moduleLowerShriek K ⊣ Cocontinuous.moduleInverseImage (totalForget K) X.structureSheaf :=
  Cocontinuous.moduleLowerShriek.adjunction (totalForget K) X.structureSheaf

/-- The morphism `a` is a flat morphism of ringed topoi. -/
instance toAmbient_isFlat
    [UnivLE.{max ι u v, w}]
    [HasSheafify (overSiteTotalTopology X.siteTopology K) (Type w)]
    [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ Type w,
      (totalForget K).op.HasPointwiseRightKanExtension P]
    [(overSiteTotalTopology X.siteTopology K).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [(SheafOfModules.restrictScalars.{w} (toAmbient K).structureMap).IsRightAdjoint] :
    ToposHom.IsFlat (toAmbient K) := sorry

/-- The morphism `a_n` is a flat morphism of ringed topoi. -/
instance stageToAmbient_isFlat (n : SimplexCategory)
    [UnivLE.{max ι u v, w}]
    [HasSheafify (overTopology X.siteTopology (K.obj (op n))) (Type w)]
    [∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type w,
      (SemiRepresentableFamily.forget (K.obj (op n))).op.HasPointwiseRightKanExtension P]
    [(overTopology X.siteTopology (K.obj (op n))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [(SheafOfModules.restrictScalars.{w} (stageToAmbient K n).structureMap).IsRightAdjoint] :
    ToposHom.IsFlat (stageToAmbient K n) := sorry

/-- The morphism `f_φ` is a flat morphism of ringed topoi. -/
instance stageMap_isFlat {m n : SimplexCategory} (φ : m ⟶ n)
    [UnivLE.{max ι u v, w}]
    [HasSheafify (overTopology X.siteTopology (K.obj (op n))) (Type w)]
    [∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type w,
      (overMap (K.map φ.op)).op.HasPointwiseRightKanExtension P]
    [(overTopology X.siteTopology (K.obj (op n))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [(overTopology X.siteTopology (K.obj (op m))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [(SheafOfModules.restrictScalars.{w} (stageMap K φ).structureMap).IsRightAdjoint] :
    ToposHom.IsFlat (stageMap K φ) := sorry

/-- The functor `f_{φ!} : Mod(O_n) ⥤ Mod(O_m)` is exact. -/
theorem stageMap_moduleLowerShriek_exact {m n : SimplexCategory} (φ : m ⟶ n) :
    exactFunctor
      (SheafOfModules.{z} (AtSR.ringSheaf (K.obj (op n))))
      (SheafOfModules.{z} (AtSR.ringSheaf (K.obj (op m))))
      (AtSR.mapModuleLowerShriek (K.map φ.op)) := sorry

/-- The morphism `g_n` is a flat morphism of ringed topoi. -/
instance stageIncl_isFlat (n : SimplexCategory)
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
    ToposHom.IsFlat (stageIncl K n) := sorry

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
      sorry sorry).comp
    (@Cocontinuous.moduleLowerShriek.adjunction _ _ _ _
      (overTopology X.siteTopology (K.obj (op n)))
      (overSiteTotalTopology X.siteTopology K)
      (Grothendieck.ι (overSiteDiagram K) (op n)) h_ι h_ι' (ringSheaf K))

/-- Exactness of untransported module lower shriek along `ι` on `Mod(ι⁻¹ O)`, the
Lemma 85.6.3 helper before transporting across `stageRingIso`. -/
theorem stageIncl_fiberModuleLowerShriek_exact (n : SimplexCategory)
    [UnivLE.{max ι u v, w}]
    [∀ m, HasSheafify (overTopology X.siteTopology (K.obj (op m))) (Type w)]
    [∀ {m : SimplexCategory} (φ : n ⟶ m) (P : (OverSite (K.obj (op m)))ᵒᵖ ⥤ Type w),
      (overMap (K.map φ.op)).op.HasPointwiseRightKanExtension P]
    [∀ m, (overTopology X.siteTopology (K.obj (op m))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [∀ {m : SimplexCategory} (φ : n ⟶ m),
      (overMap (K.map φ.op)).IsCocontinuous
        (overTopology X.siteTopology (K.obj (op m)))
        (overTopology X.siteTopology (K.obj (op n)))]
    [∀ {m : SimplexCategory} (φ : n ⟶ m),
      (SheafOfModules.restrictScalars.{w} (stageMap K φ).structureMap).IsRightAdjoint]
    [h_ι : (Grothendieck.ι (overSiteDiagram K) (op n)).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) (overSiteTotalTopology X.siteTopology K)]
    [h_ι' : (Grothendieck.ι (overSiteDiagram K) (op n)).IsCocontinuous
      (overTopology X.siteTopology (K.obj (op n))) (overSiteTotalTopology X.siteTopology K)]
    (h_flat : ∀ {m : SimplexCategory} (φ : n ⟶ m), ToposHom.IsFlat (stageMap K φ)) :
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
        (Grothendieck.ι (overSiteDiagram K) (op n)) h_ι h_ι' (ringSheaf K)) := sorry

/-- The functor `g_{n!} : Mod(O_n) ⥤ Mod(O)` left adjoint to `g_n^*` is exact, by
Lemma 85.6.3, once every `f_φ` is flat. -/
theorem stageIncl_moduleLowerShriek_exact (n : SimplexCategory)
    [UnivLE.{max ι u v, w}]
    [∀ m, HasSheafify (overTopology X.siteTopology (K.obj (op m))) (Type w)]
    [∀ {m : SimplexCategory} (φ : n ⟶ m) (P : (OverSite (K.obj (op m)))ᵒᵖ ⥤ Type w),
      (overMap (K.map φ.op)).op.HasPointwiseRightKanExtension P]
    [∀ m, (overTopology X.siteTopology (K.obj (op m))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
    [∀ {m : SimplexCategory} (φ : n ⟶ m),
      (overMap (K.map φ.op)).IsCocontinuous
        (overTopology X.siteTopology (K.obj (op m)))
        (overTopology X.siteTopology (K.obj (op n)))]
    [∀ {m : SimplexCategory} (φ : n ⟶ m),
      (SheafOfModules.restrictScalars.{w} (stageMap K φ).structureMap).IsRightAdjoint]
    [h_ι : (Grothendieck.ι (overSiteDiagram K) (op n)).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) (overSiteTotalTopology X.siteTopology K)]
    [h_ι' : (Grothendieck.ι (overSiteDiagram K) (op n)).IsCocontinuous
      (overTopology X.siteTopology (K.obj (op n))) (overSiteTotalTopology X.siteTopology K)]
    [h_stage : (SemiRepresentableFamily.forget (K.obj (op n))).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) X.siteTopology]
    (h_flat : ∀ {m : SimplexCategory} (φ : n ⟶ m), ToposHom.IsFlat (stageMap K φ)) :
    exactFunctor
      (SheafOfModules.{z} (AtSR.ringSheaf (K.obj (op n))))
      (SheafOfModules.{z} (ringSheaf K))
      (stageInclModuleLowerShriek K n) := sorry

end RingedSite.Localization.AtSimplicialSR
