module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.CommRing

/-!
# Commutative structure sheaves for associated modules

This source bridge checks the reusable commutative-ring-valued associated-module API.
-/

@[expose] public section

open CategoryTheory

universe u v w

#check (CommRingCat.universeLift :
  CommRingCat.{u} ⥤ CommRingCat.{max u w})

namespace AlgebraicGeometry.Scheme

variable {C : Type w} [Category.{v} C] {S : Scheme.{u}}

#check (Over.commStructurePresheaf :
  (p : C ⥤ Over S) → Cᵒᵖ ⥤ CommRingCat.{u + 1})

#check (Modules.commPullbackSectionsObj :
  (p : C ⥤ Over S) → (F : S.Modules) → (U : Cᵒᵖ) →
    ModuleCat.{u + 1} ((Over.commStructurePresheaf p).obj U))

#check (Modules.commPullbackSectionsMap :
  (p : C ⥤ Over S) → (F : S.Modules) → {U V : Cᵒᵖ} → (f : U ⟶ V) →
    Modules.commPullbackSectionsObj p F U ⟶
      Modules.commPullbackSectionsTarget p F f)

#check (Modules.commPullbackSectionsPresheaf :
  (p : C ⥤ Over S) → (F : S.Modules) →
    _root_.PresheafOfModules.{u + 1}
      (CategoryTheory.Presheaf.ringPresheafOfComm
        (Over.commStructurePresheaf p)))

namespace AssociatedModule

#check (bigComm :
  (τ : StandardTopology) → (S : Scheme.{u}) →
    (F : S.Modules) → [F.IsQuasicoherent] →
      SheafOfModules.RingedSite.ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
        (τ.overTopology S) (bigCommStructureSheaf τ S))

#check (smallComm :
  (σ : SmallStandardTopology) → (S : Scheme.{u}) →
    (F : S.Modules) → [F.IsQuasicoherent] →
      SheafOfModules.RingedSite.ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
        (σ.topology S) (smallCommStructureSheaf σ S))

#check (StandardSmall.comm :
  (τ : StandardTopology) → (S : Scheme.{u}) →
    (F : S.Modules) → [F.IsQuasicoherent] →
      SheafOfModules.RingedSite.ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
        (StandardTopology.Small.topology τ S)
        (StandardSmall.commStructureSheaf τ S))

end AssociatedModule

end AlgebraicGeometry.Scheme
