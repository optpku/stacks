/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Standard
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Small.Ringed
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

/-!
# Pushforward of quasi-coherent modules on small standard scheme sites

This module restricts module pushforward along a qcqs scheme morphism to the
full subcategories of quasi-coherent module sheaves on the selected small
Zariski or étale site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.SmallStandardTopology.QCoh

variable {S T : Scheme.{u}}

/-- The ambient module pushforward on the selected small standard site,
expressed branchwise so that its structure sheaves agree definitionally with
the associated-module structure sheaves. -/
noncomputable def ambientPushforward (σ : SmallStandardTopology) (f : T ⟶ S) :
    SheafOfModules (Scheme.AssociatedModule.smallStructureSheaf σ T) ⥤
      SheafOfModules (Scheme.AssociatedModule.smallStructureSheaf σ S) :=
  match σ with
  | .zariski => (SmallStandardTopology.ringedHom .zariski f).modulePushforward.{u}
  | .etale => (SmallStandardTopology.ringedHom .etale f).modulePushforward.{u}

/-- On the Zariski branch, `ambientPushforward` is the canonical ringed-site
module pushforward. -/
theorem ambientPushforward_zariski (f : T ⟶ S) :
    ambientPushforward .zariski f =
      (SmallStandardTopology.ringedHom .zariski f).modulePushforward.{u} := sorry

/-- On the étale branch, `ambientPushforward` is the canonical ringed-site
module pushforward. -/
theorem ambientPushforward_etale (f : T ⟶ S) :
    ambientPushforward .etale f =
      (SmallStandardTopology.ringedHom .etale f).modulePushforward.{u} := sorry

/-- Small-site pushforward along a qcqs scheme morphism preserves quasi-coherence. -/
theorem modulePushforward_isQuasicoherent (σ : SmallStandardTopology)
    (f : T ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (F : SheafOfModules (Scheme.AssociatedModule.smallStructureSheaf σ T))
    [F.IsQuasicoherent] :
    ((ambientPushforward σ f).obj F).IsQuasicoherent := sorry

/-- Pushforward of quasi-coherent module sheaves along a qcqs morphism on the
selected small standard site. -/
noncomputable def pushforward (σ : SmallStandardTopology)
    (f : T ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    (SheafOfModules.isQuasicoherent
        (Scheme.AssociatedModule.smallStructureSheaf σ T)).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent
        (Scheme.AssociatedModule.smallStructureSheaf σ S)).FullSubcategory :=
  FullSubcategory.restrict (ambientPushforward σ f)
    (fun F hF ↦ @modulePushforward_isQuasicoherent S T σ f _ _ F hF)

namespace pushforward

/-- Forgetting quasi-coherence after small-site pushforward recovers the
ambient module pushforward. -/
noncomputable def inclusionIso (σ : SmallStandardTopology)
    (f : T ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    pushforward σ f ⋙
        (SheafOfModules.isQuasicoherent
          (Scheme.AssociatedModule.smallStructureSheaf σ S)).ι ≅
      (SheafOfModules.isQuasicoherent
          (Scheme.AssociatedModule.smallStructureSheaf σ T)).ι ⋙
        ambientPushforward σ f :=
  FullSubcategory.restrict.compιIso (ambientPushforward σ f)
    (fun F hF ↦ @modulePushforward_isQuasicoherent S T σ f _ _ F hF)

/-- The underlying module sheaf of small-site quasi-coherent pushforward is
ambient pushforward. -/
theorem obj_obj (σ : SmallStandardTopology)
    (f : T ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (F : (SheafOfModules.isQuasicoherent
      (Scheme.AssociatedModule.smallStructureSheaf σ T)).FullSubcategory) :
    ((pushforward σ f).obj F).obj =
      (ambientPushforward σ f).obj F.obj := sorry

end pushforward

end AlgebraicGeometry.SmallStandardTopology.QCoh
