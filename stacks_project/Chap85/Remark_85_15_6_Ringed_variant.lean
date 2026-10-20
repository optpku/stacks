module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Family
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SemiRepresentableFamily

universe ι u v w z

variable {X : RingedSite.{u, v, w}} (K L : FormalCoproduct.{ι} X.carrier) (φ : K ⟶ L)

/- Remark 85.15.6 (Ringed variant) (1): the family localization has the
restricted structure sheaf. -/
@[stacks 0D9U] #check (RingedSite.Localization.AtSR.site K :
  RingedSite.{max ι u v, max ι u v, w})
#check (RingedSite.Localization.AtSR.structureSheaf_spec K :
  (RingedSite.Localization.AtSR.site K).structureSheaf =
    RingedSite.Localization.AtSR.ringSheaf K)

/- Remark 85.15.6 (Ringed variant) (2): module sheaves decompose as the
product of the module categories of the component slices. -/
@[stacks 0D9U] #check (RingedSite.Localization.AtSR.modulesEquiv K :
  SheafOfModules.{z} (RingedSite.Localization.AtSR.ringSheaf K) ≌
    ∀ i : K.I, SheafOfModules.{z} (X.structureSheaf.over (K.obj i)))

section AmbientTopos

variable [UnivLE.{max ι u v, w}]
  [HasSheafify (overTopology X.siteTopology K) (Type w)]
  [∀ P : (OverSite K)ᵒᵖ ⥤ Type w,
    (CategoryTheory.SemiRepresentableFamily.forget K).op.HasPointwiseRightKanExtension P]
  [(overTopology X.siteTopology K).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]

/- Remark 85.15.6 (Ringed variant) (3): the ambient localization is a
morphism of ringed topoi. -/
@[stacks 0D9U] #check (RingedSite.Localization.AtSR.toAmbient K :
  RingedSite.ToposHom (RingedSite.Localization.AtSR.site K) X)
#check (RingedSite.Localization.AtSR.toAmbient_structureMap_isIso K :
  IsIso (RingedSite.Localization.AtSR.toAmbient K).structureMap)

end AmbientTopos

section RelocalizationTopos

variable [UnivLE.{max ι u v, w}]
  [HasSheafify (overTopology X.siteTopology K) (Type w)]
  [∀ P : (OverSite K)ᵒᵖ ⥤ Type w, (overMap φ).op.HasPointwiseRightKanExtension P]
  [(overTopology X.siteTopology K).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [(overTopology X.siteTopology L).HasSheafCompose (CategoryTheory.forget RingCat.{w})]

/- Remark 85.15.6 (Ringed variant) (4): a family morphism induces a
morphism of the corresponding ringed topoi. -/
@[stacks 0D9U] #check (RingedSite.Localization.AtSR.map φ :
  RingedSite.ToposHom (RingedSite.Localization.AtSR.site K)
    (RingedSite.Localization.AtSR.site L))
#check (RingedSite.Localization.AtSR.map_structureMap_isIso φ :
  IsIso (RingedSite.Localization.AtSR.map φ).structureMap)

end RelocalizationTopos

section AmbientExtension

variable [UnivLE.{max ι v, z}] [UnivLE.{v, z}]
  [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
  [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}]
  (F : ∀ i : K.I, SheafOfModules.{z} (X.structureSheaf.over (K.obj i)))
  [HasCoproduct fun i : K.I ↦
    (SheafOfModules.Localization.lowerShriekDirectSum X.structureSheaf (K.obj i)).obj (F i)]

/- Remark 85.15.6 (Ringed variant) (5): ambient restriction has an
exact left adjoint, with extension computed by the sum of the slice extensions. -/
@[stacks 0D9U] #check (RingedSite.Localization.AtSR.moduleLowerShriekAdjunction K :
  (RingedSite.Localization.AtSR.moduleLowerShriek K :
    SheafOfModules.{z} (RingedSite.Localization.AtSR.ringSheaf K) ⥤
      SheafOfModules.{z} X.structureSheaf) ⊣
    (RingedSite.Cocontinuous.moduleInverseImage
      (CategoryTheory.SemiRepresentableFamily.forget K) X.structureSheaf :
      SheafOfModules.{z} X.structureSheaf ⥤
        SheafOfModules.{z} (RingedSite.Localization.AtSR.ringSheaf K)))
#check (RingedSite.Localization.AtSR.moduleLowerShriek_exact K :
  CategoryTheory.exactFunctor
    (SheafOfModules.{z} (RingedSite.Localization.AtSR.ringSheaf K))
    (SheafOfModules.{z} X.structureSheaf)
    (RingedSite.Localization.AtSR.moduleLowerShriek K))
#check (RingedSite.Localization.AtSR.moduleLowerShriekCoprod_isIso K F :
  IsIso (RingedSite.Localization.AtSR.moduleLowerShriekCoprod K F))

end AmbientExtension

section RelocalizationExtension

variable [UnivLE.{max ι v, z}]
  [HasWeakSheafify (overTopology X.siteTopology L) AddCommGrpCat.{z}]
  [(overTopology X.siteTopology L).WEqualsLocallyBijective AddCommGrpCat.{z}]

/- Remark 85.15.6 (Ringed variant) (6): relocalization restriction has
an exact left adjoint. -/
@[stacks 0D9U] #check (RingedSite.Localization.AtSR.mapModuleLowerShriek_adjunction φ :
  (RingedSite.Localization.AtSR.mapModuleLowerShriek φ :
    SheafOfModules.{z} (RingedSite.Localization.AtSR.ringSheaf K) ⥤
      SheafOfModules.{z} (RingedSite.Localization.AtSR.ringSheaf L)) ⊣
    (RingedSite.Localization.AtSR.mapModulePullback φ :
      SheafOfModules.{z} (RingedSite.Localization.AtSR.ringSheaf L) ⥤
        SheafOfModules.{z} (RingedSite.Localization.AtSR.ringSheaf K)))
#check (RingedSite.Localization.AtSR.map_moduleLowerShriek_exact φ :
  CategoryTheory.exactFunctor
    (SheafOfModules.{z} (RingedSite.Localization.AtSR.ringSheaf K))
    (SheafOfModules.{z} (RingedSite.Localization.AtSR.ringSheaf L))
    (RingedSite.Localization.AtSR.mapModuleLowerShriek φ))

end RelocalizationExtension

/- Remark 85.15.6 (Ringed variant) (7): ambient and relocalization
restriction are exact, so both ringed-topos morphisms are flat. -/
@[stacks 0D9U] #check (RingedSite.Localization.AtSR.toAmbient_modulePullback_exact K :
  CategoryTheory.exactFunctor
    (SheafOfModules.{z} X.structureSheaf)
    (SheafOfModules.{z} (RingedSite.Localization.AtSR.ringSheaf K))
    (RingedSite.Cocontinuous.moduleInverseImage
      (CategoryTheory.SemiRepresentableFamily.forget K) X.structureSheaf))
#check (RingedSite.Localization.AtSR.map_modulePullback_exact φ :
  CategoryTheory.exactFunctor
    (SheafOfModules.{z} (RingedSite.Localization.AtSR.ringSheaf L))
    (SheafOfModules.{z} (RingedSite.Localization.AtSR.ringSheaf K))
    (RingedSite.Localization.AtSR.mapModulePullback φ))
