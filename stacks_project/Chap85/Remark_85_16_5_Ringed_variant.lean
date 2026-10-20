/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Simplicial
public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Simplicial.Module
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits Opposite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w z

open SemiRepresentableFamily
  (OverSite overTopology overSiteDiagram overSiteTotalTopology totalForget overMap)
open RingedSite.Localization

variable {X : RingedSite.{u, v, w}}
variable (K : SimplicialObject (FormalCoproduct.{ι} X.carrier))

/- Remark 85.16.5 (Ringed variant) (1): the total ringed site with structure sheaf
`O = a⁻¹ O_C`. -/
@[stacks 0D9W] #check (RingedSite.Localization.AtSimplicialSR.site K :
  RingedSite.{max ι u v, max ι u v, w})

#check (RingedSite.Localization.AtSimplicialSR.structureSheaf_spec K :
  (AtSimplicialSR.site K).structureSheaf =
    RingedSite.Cocontinuous.inverseImageRingSheaf
      (J := overSiteTotalTopology X.siteTopology K) (totalForget K) X.structureSheaf)

section RingedMorphisms

variable [UnivLE.{max ι u v, w}]
variable [HasSheafify (overSiteTotalTopology X.siteTopology K) (Type w)]
variable [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ Type w,
  (totalForget K).op.HasPointwiseRightKanExtension P]
variable [(overSiteTotalTopology X.siteTopology K).HasSheafCompose
  (CategoryTheory.forget RingCat.{w})]
variable [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, HasSheafify (overTopology X.siteTopology (K.obj (op n))) (Type w)]
variable [∀ n, (overTopology X.siteTopology (K.obj (op n))).HasSheafCompose
  (CategoryTheory.forget RingCat.{w})]
variable [∀ n (P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type w),
  (SemiRepresentableFamily.forget (K.obj (op n))).op.HasPointwiseRightKanExtension P]
variable [∀ n (P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type w),
  (Grothendieck.ι (overSiteDiagram K) (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n) (P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type w),
  (overMap (K.map φ.op)).op.HasPointwiseRightKanExtension P]
variable (n : SimplexCategory) {m : SimplexCategory} (φ : m ⟶ n)

/- Remark 85.16.5 (Ringed variant) (2): the total augmentation to the ambient
ringed topos. -/
@[stacks 0D9W] #check (RingedSite.Localization.AtSimplicialSR.toAmbient K :
  RingedSite.ToposHom (AtSimplicialSR.site K) X)

/- Remark 85.16.5 (Ringed variant) (3): the degree augmentations to the ambient
ringed topos. -/
@[stacks 0D9W] #check (RingedSite.Localization.AtSimplicialSR.stageToAmbient K n :
  RingedSite.ToposHom (AtSR.site (K.obj (op n))) X)

/- Remark 85.16.5 (Ringed variant) (6): the total and degree augmentations are flat. -/
@[stacks 0D9W] #check (RingedSite.Localization.AtSimplicialSR.toAmbient_isFlat K :
  RingedSite.ToposHom.IsFlat (AtSimplicialSR.toAmbient K))

#check (RingedSite.Localization.AtSimplicialSR.stageToAmbient_isFlat K n :
  RingedSite.ToposHom.IsFlat (AtSimplicialSR.stageToAmbient K n))

/- Remark 85.16.5 (Ringed variant) (7): the morphism induced by a simplex operator
is flat. Its exact module adjunction is checked below. -/
@[stacks 0D9W] #check (RingedSite.Localization.AtSimplicialSR.stageMap_isFlat K φ :
  RingedSite.ToposHom.IsFlat (AtSimplicialSR.stageMap K φ))

/- Remark 85.16.5 (Ringed variant) (8): the fiber inclusion is flat. Its exact
module adjunction is checked below. -/
@[stacks 0D9W] #check (RingedSite.Localization.AtSimplicialSR.stageIncl_isFlat K n :
  RingedSite.ToposHom.IsFlat (AtSimplicialSR.stageIncl K n))

end RingedMorphisms

/- Remark 85.16.5 (Ringed variant) (4): total module lower shriek is left adjoint
to inverse image. It is not asserted exact. -/
@[stacks 0D9W] #check (RingedSite.Cocontinuous.moduleLowerShriek.adjunction
  (totalForget K) X.structureSheaf :
  (RingedSite.Cocontinuous.moduleLowerShriek (totalForget K) X.structureSheaf :
    SheafOfModules.{z} (AtSimplicialSR.ringSheaf K) ⥤ SheafOfModules.{z} X.structureSheaf) ⊣
    RingedSite.Cocontinuous.moduleInverseImage (totalForget K) X.structureSheaf)

section DegreeModules

variable [UnivLE.{max ι v, z}]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}]
variable (n : SimplexCategory)

/- Remark 85.16.5 (Ringed variant) (5): the degree lower-shriek functor is exact
and left adjoint to degree inverse image. -/
@[stacks 0D9W] #check (RingedSite.Localization.AtSR.moduleLowerShriek_exact
  (K.obj (op n)) :
  exactFunctor (SheafOfModules.{z} (AtSR.ringSheaf (K.obj (op n))))
    (SheafOfModules.{z} X.structureSheaf) (AtSR.moduleLowerShriek (K.obj (op n))))

#check (RingedSite.Localization.AtSR.moduleLowerShriekAdjunction (K.obj (op n)) :
  (AtSR.moduleLowerShriek (K.obj (op n)) :
    SheafOfModules.{z} (AtSR.ringSheaf (K.obj (op n))) ⥤ SheafOfModules.{z} X.structureSheaf) ⊣
    RingedSite.Cocontinuous.moduleInverseImage
      (SemiRepresentableFamily.forget (K.obj (op n))) X.structureSheaf)

end DegreeModules

section OperatorModules

variable [UnivLE.{max ι v, z}]
variable {m n : SimplexCategory} (φ : m ⟶ n)
variable [HasWeakSheafify (overTopology X.siteTopology (K.obj (op m))) AddCommGrpCat.{z}]
variable [(overTopology X.siteTopology (K.obj (op m))).WEqualsLocallyBijective
  AddCommGrpCat.{z}]

#check (RingedSite.Localization.AtSR.map_moduleLowerShriek_exact (K.map φ.op) :
  exactFunctor (SheafOfModules.{z} (AtSR.ringSheaf (K.obj (op n))))
    (SheafOfModules.{z} (AtSR.ringSheaf (K.obj (op m))))
    (AtSR.mapModuleLowerShriek (K.map φ.op)))

#check (RingedSite.Localization.AtSR.mapModuleLowerShriek_adjunction (K.map φ.op) :
  (AtSR.mapModuleLowerShriek (K.map φ.op) :
    SheafOfModules.{z} (AtSR.ringSheaf (K.obj (op n))) ⥤
      SheafOfModules.{z} (AtSR.ringSheaf (K.obj (op m)))) ⊣
    AtSR.mapModulePullback (K.map φ.op))

end OperatorModules

section FiberModules

variable (n : SimplexCategory)

#check (RingedSite.Localization.AtSimplicialSR.stageInclModuleLowerShriek_adjunction K n :
  (AtSimplicialSR.stageInclModuleLowerShriek K n :
    SheafOfModules.{z} (AtSR.ringSheaf (K.obj (op n))) ⥤
      SheafOfModules.{z} (AtSimplicialSR.ringSheaf K)) ⊣
    AtSimplicialSR.stageInclModuleInverseImage K n)

variable [UnivLE.{max ι u v, w}] [UnivLE.{max ι v, z}]
variable [HasWeakSheafify (overSiteTotalTopology X.siteTopology K) AddCommGrpCat.{z}]
variable [(overSiteTotalTopology X.siteTopology K).WEqualsLocallyBijective AddCommGrpCat.{z}]
variable [∀ m, HasSheafify (overTopology X.siteTopology (K.obj (op m))) (Type w)]
variable [∀ m, (overTopology X.siteTopology (K.obj (op m))).HasSheafCompose
  (CategoryTheory.forget RingCat.{w})]
variable [∀ {m : SimplexCategory} (φ : n ⟶ m) (P : (OverSite (K.obj (op m)))ᵒᵖ ⥤ Type w),
  (overMap (K.map φ.op)).op.HasPointwiseRightKanExtension P]

#check (RingedSite.Localization.AtSimplicialSR.stageIncl_moduleLowerShriek_exact K n :
  exactFunctor (SheafOfModules.{z} (AtSR.ringSheaf (K.obj (op n))))
    (SheafOfModules.{z} (AtSimplicialSR.ringSheaf K))
    (AtSimplicialSR.stageInclModuleLowerShriek K n))

end FiberModules
