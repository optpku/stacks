/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Simplicial.Cartesian

/-!
# Cartesian modules on a ringed total localization

An `O`-module on `((C / K)_total, O)` is cartesian when every simplex-operator comparison
`f_φ^* F_m ⟶ F_n` is an isomorphism. Inverse and direct image of modules along the ringed
augmentation `a` are `toAmbient.modulePullback` and `toAmbient.modulePushforward`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Functor Grothendieck
open RingedSite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace RingedSite.Localization.AtSimplicialSR

open SemiRepresentableFamily
  (OverSite overTopology overSiteDiagram overSiteTotalTopology totalForget
    overSite_ι_isContinuous overSite_ι_isCocontinuous overMap overSitePrecoverage)

variable {X : RingedSite.{u, v, w}}
variable (K : SimplicialObject (FormalCoproduct.{ι} X.carrier))
variable [UnivLE.{max ι u v, w}]
variable [HasSheafify (overSiteTotalTopology X.siteTopology K) (Type w)]
variable [HasWeakSheafify (overSiteTotalTopology X.siteTopology K) (Type w)]
variable [∀ n : SimplexCategory,
    HasSheafify (overTopology X.siteTopology (K.obj (op n))) (Type w)]
variable [∀ n : SimplexCategory,
    HasWeakSheafify (overTopology X.siteTopology (K.obj (op n))) (Type w)]
variable [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ Type w,
    (totalForget K).op.HasPointwiseRightKanExtension P]
variable [∀ n : SimplexCategory, ∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type w,
    (Grothendieck.ι (overSiteDiagram K) (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type w,
      (overMap (K.map φ.op)).op.HasPointwiseRightKanExtension P]
variable [(overSiteTotalTopology X.siteTopology K).HasSheafCompose
    (CategoryTheory.forget RingCat.{w})]
variable [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n : SimplexCategory,
    (overTopology X.siteTopology (K.obj (op n))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
variable [(SheafOfModules.restrictScalars.{w} (toAmbient K).structureMap).IsRightAdjoint]
variable [∀ n : SimplexCategory,
    (SheafOfModules.restrictScalars.{w} (stageIncl K n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (stageMap K φ).structureMap).IsRightAdjoint]

/- Cartesian modules on a simplicial ringed localization. -/
#check (RingedSite.Localization.AtSimplicialSR.IsCartesian K :
  SheafOfModules.{w} (ringSheaf K) → Prop)

#check (RingedSite.Localization.AtSimplicialSR.moduleTransition K :
  ∀ {m n : SimplexCategory} (φ : m ⟶ n) (F : SheafOfModules.{w} (ringSheaf K)),
    (stageMap K φ).modulePullback.obj ((moduleComponent K m).obj F) ⟶
      (moduleComponent K n).obj F)

#check (RingedSite.Localization.AtSimplicialSR.isCartesian_iff_underlying K :
  ∀ F : SheafOfModules.{w} (ringSheaf K), IsCartesian K F ↔
    Grothendieck.Sheaf.IsCartesian (overSiteDiagram K)
      (overSitePrecoverage X.siteTopology K) (Type w)
      ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K)).obj F))

end RingedSite.Localization.AtSimplicialSR
