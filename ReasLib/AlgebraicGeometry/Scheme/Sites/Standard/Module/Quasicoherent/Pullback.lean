module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Pullback.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Standard
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Pullback.Module
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Small.Ringed
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

/-!
# Pullback of quasi-coherent modules on standard scheme sites

This module restricts the canonical module pullback functors to the full
subcategories of quasi-coherent module sheaves on standard big sites and on
the selected small Zariski or étale site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.StandardTopology.Big.QCoh

variable {S T : Scheme.{u}}

/-- Pullback along a scheme morphism preserves quasi-coherence on its standard big site. -/
theorem modulePullback_isQuasicoherent (τ : StandardTopology) (f : T ⟶ S)
    (F : SheafOfModules (Scheme.AssociatedModule.bigStructureSheaf τ S))
    [F.IsQuasicoherent] :
    ((@RingedSite.Hom.modulePullback _ _ (pullbackRingedHom τ f)
      (pullbackRingedHom_modulePushforward_isRightAdjoint τ f)).obj F).IsQuasicoherent := sorry

/-- Pullback of quasi-coherent module sheaves on the standard big `τ`-site. -/
noncomputable def pullback (τ : StandardTopology) (f : T ⟶ S) :
    (SheafOfModules.isQuasicoherent
        (Scheme.AssociatedModule.bigStructureSheaf τ S)).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent
        (Scheme.AssociatedModule.bigStructureSheaf τ T)).FullSubcategory :=
  FullSubcategory.restrict
    (@RingedSite.Hom.modulePullback _ _ (pullbackRingedHom τ f)
      (pullbackRingedHom_modulePushforward_isRightAdjoint τ f))
    (fun F hF ↦ @modulePullback_isQuasicoherent S T τ f F hF)

namespace pullback

/-- Forgetting quasi-coherence after big-site pullback recovers the ambient
module pullback. -/
noncomputable def inclusionIso (τ : StandardTopology) (f : T ⟶ S) :
    pullback τ f ⋙
        (SheafOfModules.isQuasicoherent
          (Scheme.AssociatedModule.bigStructureSheaf τ T)).ι ≅
      (SheafOfModules.isQuasicoherent
          (Scheme.AssociatedModule.bigStructureSheaf τ S)).ι ⋙
        (@RingedSite.Hom.modulePullback _ _ (pullbackRingedHom τ f)
          (pullbackRingedHom_modulePushforward_isRightAdjoint τ f)) :=
  FullSubcategory.restrict.compιIso
    (@RingedSite.Hom.modulePullback _ _ (pullbackRingedHom τ f)
      (pullbackRingedHom_modulePushforward_isRightAdjoint τ f))
    (fun F hF ↦ @modulePullback_isQuasicoherent S T τ f F hF)

/-- The underlying module sheaf of big-site quasi-coherent pullback is ambient pullback. -/
theorem obj_obj (τ : StandardTopology) (f : T ⟶ S)
    (F : (SheafOfModules.isQuasicoherent
      (Scheme.AssociatedModule.bigStructureSheaf τ S)).FullSubcategory) :
    ((pullback τ f).obj F).obj =
      (@RingedSite.Hom.modulePullback _ _ (pullbackRingedHom τ f)
        (pullbackRingedHom_modulePushforward_isRightAdjoint τ f)).obj F.obj := sorry

end pullback

end AlgebraicGeometry.StandardTopology.Big.QCoh

namespace AlgebraicGeometry.SmallStandardTopology.QCoh

variable {S T : Scheme.{u}}

/-- The ambient module pullback on the selected small standard site, expressed
branchwise so that its structure sheaves agree definitionally with the
associated-module structure sheaves. -/
noncomputable def ambientPullback (σ : SmallStandardTopology) (f : T ⟶ S) :
    SheafOfModules (Scheme.AssociatedModule.smallStructureSheaf σ S) ⥤
      SheafOfModules (Scheme.AssociatedModule.smallStructureSheaf σ T) :=
  match σ with
  | .zariski =>
      @RingedSite.Hom.modulePullback _ _
        (SmallStandardTopology.ringedHom .zariski f)
        (SmallStandardTopology.ringedHom_modulePushforward_isRightAdjoint .zariski f)
  | .etale =>
      @RingedSite.Hom.modulePullback _ _
        (SmallStandardTopology.ringedHom .etale f)
        (SmallStandardTopology.ringedHom_modulePushforward_isRightAdjoint .etale f)

/-- On the Zariski branch, `ambientPullback` is the canonical ringed-site
module pullback. -/
theorem ambientPullback_zariski (f : T ⟶ S) :
    ambientPullback .zariski f =
      @RingedSite.Hom.modulePullback _ _
        (SmallStandardTopology.ringedHom .zariski f)
        (SmallStandardTopology.ringedHom_modulePushforward_isRightAdjoint .zariski f) := sorry

/-- On the étale branch, `ambientPullback` is the canonical ringed-site
module pullback. -/
theorem ambientPullback_etale (f : T ⟶ S) :
    ambientPullback .etale f =
      @RingedSite.Hom.modulePullback _ _
        (SmallStandardTopology.ringedHom .etale f)
        (SmallStandardTopology.ringedHom_modulePushforward_isRightAdjoint .etale f) := sorry

/-- Pullback along a scheme morphism preserves quasi-coherence on the selected small site. -/
theorem modulePullback_isQuasicoherent (σ : SmallStandardTopology) (f : T ⟶ S)
    (F : SheafOfModules (Scheme.AssociatedModule.smallStructureSheaf σ S))
    [F.IsQuasicoherent] :
    ((ambientPullback σ f).obj F).IsQuasicoherent := sorry

/-- Pullback of quasi-coherent module sheaves on the selected small standard site. -/
noncomputable def pullback (σ : SmallStandardTopology) (f : T ⟶ S) :
    (SheafOfModules.isQuasicoherent
        (Scheme.AssociatedModule.smallStructureSheaf σ S)).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent
        (Scheme.AssociatedModule.smallStructureSheaf σ T)).FullSubcategory :=
  FullSubcategory.restrict (ambientPullback σ f)
    (fun F hF ↦ @modulePullback_isQuasicoherent S T σ f F hF)

namespace pullback

/-- Forgetting quasi-coherence after small-site pullback recovers the ambient
module pullback. -/
noncomputable def inclusionIso (σ : SmallStandardTopology) (f : T ⟶ S) :
    pullback σ f ⋙
        (SheafOfModules.isQuasicoherent
          (Scheme.AssociatedModule.smallStructureSheaf σ T)).ι ≅
      (SheafOfModules.isQuasicoherent
          (Scheme.AssociatedModule.smallStructureSheaf σ S)).ι ⋙
        ambientPullback σ f :=
  FullSubcategory.restrict.compιIso (ambientPullback σ f)
    (fun F hF ↦ @modulePullback_isQuasicoherent S T σ f F hF)

/-- The underlying module sheaf of small-site quasi-coherent pullback is ambient pullback. -/
theorem obj_obj (σ : SmallStandardTopology) (f : T ⟶ S)
    (F : (SheafOfModules.isQuasicoherent
      (Scheme.AssociatedModule.smallStructureSheaf σ S)).FullSubcategory) :
    ((pullback σ f).obj F).obj = (ambientPullback σ f).obj F.obj := sorry

end pullback

end AlgebraicGeometry.SmallStandardTopology.QCoh
