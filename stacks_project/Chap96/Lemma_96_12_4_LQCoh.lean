module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.LocallyQuasiCoherent

/-!
# Locally quasi-coherent étale module presentations

Compatibility checks for the canonical small-étale definition and its
comparison with the underlying module-presheaf presentation.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver
open SheafOfModules.RingedSite (ringedSiteModuleCategory)

universe u

variable {S : Scheme.{u}}

#check (AlgebraicGeometry.GroupoidsOver.isLocallyQuasiCoherent_iff :
  ∀ {X : GroupoidsOver S} (F : etaleModules X),
    IsLocallyQuasiCoherent F ↔
      ∀ x : X.total, ((restrictModulesToSmallEtale X x).obj F).IsQuasicoherent)

#check (AlgebraicGeometry.GroupoidsOver.isLocallyQuasiCoherent_iff_isLocallyQuasicoherent :
  ∀ {X : GroupoidsOver S} (F : etaleModules X),
    IsLocallyQuasiCoherent F ↔ IsLocallyQuasicoherent (etaleModulePresheaf F))

#check (AlgebraicGeometry.GroupoidsOver.isLocallyQuasiCoherentLift_iff :
  ∀ {X : GroupoidsOver S}
    (F : ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
      X.etaleTopology (commEtaleStructureSheafLift X)),
    IsLocallyQuasiCoherentLift F ↔
      ∀ x : X.total, ((restrictToSmallEtaleLift X x).obj F).IsQuasicoherent)
