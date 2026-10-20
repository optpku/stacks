module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.LocallyQuasicoherent
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module

/-!
# Locally quasi-coherent modules on a category fibred in groupoids

An étale `𝒪_X`-module is locally quasi-coherent when its restriction to the small étale
site of the scheme underlying every object of `X` is quasi-coherent. The full subcategory
of such modules is `LQCoh 𝒪_X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
  CategoryTheory.ObjectProperty Opposite
open AlgebraicGeometry
open SheafOfModules.RingedSite (ringedSiteModuleCategory)
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Reassociation `p.op ⋙ (Γ ⋙ forget₂) ≅ (p.op ⋙ Γ) ⋙ forget₂` relating the fppf
and étale presentations of `𝒪_X`. -/
def fppfToEtaleStructurePresheafIso (X : GroupoidsOver S) :
    (structureSheaf X).obj ≅ (etaleStructureSheaf X).obj :=
  (X.p.sheafPushforwardContinuousCompSheafToPresheafIso RingCat.{u}
      (fppfTopology X) (Scheme.fppfTopology.over S)).app
    (StandardTopology.Big.structureSheaf .fppf S) ≪≫
    isoWhiskerLeft X.p.op
      (associator (Over.forget S).op Scheme.Γ
        (forget₂ CommRingCat.{u} RingCat.{u})).symm ≪≫
    (associator X.p.op ((Over.forget S).op ⋙ Scheme.Γ)
      (forget₂ CommRingCat.{u} RingCat.{u})).symm ≪≫
    (isoWhiskerRight
      ((X.p.sheafPushforwardContinuousCompSheafToPresheafIso CommRingCat.{u}
          X.etaleTopology (StandardTopology.etale.overTopology S)).app
        bigEtaleCommStructureSheaf)
      (forget₂ CommRingCat.{u} RingCat.{u})).symm

/-- Γ-comparison from the fppf structure presheaf of `X` to the étale structure
presheaf of `X`, via the functor associator between `p.op ⋙ (Γ ⋙ forget₂)` and
`(p.op ⋙ Γ) ⋙ forget₂`. -/
def fppfToEtaleStructurePresheaf (X : GroupoidsOver S) :
    (structureSheaf X).obj ⟶ (etaleStructureSheaf X).obj :=
  (fppfToEtaleStructurePresheafIso X).hom

/-- Components of `fppfToEtaleStructurePresheaf` are identities of global sections. -/
theorem fppfToEtaleStructurePresheaf_app (X : GroupoidsOver S) (x : X.total) :
    (fppfToEtaleStructurePresheaf X).app (op x) = 𝟙 _ := sorry

/-- The underlying module presheaf of an étale `𝒪_X`-module, as a presheaf of modules over
the fppf structure sheaf of `X`. -/
noncomputable def etaleModulePresheaf {X : GroupoidsOver S} (F : etaleModules X) :
    PresheafOfModules.{u} (structureSheaf X).obj :=
  (PresheafOfModules.restrictScalars (fppfToEtaleStructurePresheaf X)).obj F.val

/-- An étale `𝒪_X`-module is a sheaf for the associated étale topology. -/
theorem etaleModulePresheaf_isEtaleSheaf {X : GroupoidsOver S} (F : etaleModules X) :
    Presheaf.IsSheaf X.etaleTopology (etaleModulePresheaf F).presheaf := sorry

/-- An étale `𝒪_X`-module is locally quasi-coherent if for every object `x` of `X` lying
over a scheme `U`, the restriction to `U_étale` is a quasi-coherent `𝒪_U`-module. -/
class IsLocallyQuasiCoherent {X : GroupoidsOver S} (F : etaleModules X) : Prop where
  /-- Restriction to the small étale site of the scheme underlying `x` is quasi-coherent. -/
  restrict_isQuasicoherent (x : X.total) :
    ((restrictModulesToSmallEtale X x).obj F).IsQuasicoherent

/-- Local quasi-coherence is pointwise quasi-coherence of small-étale restrictions. -/
theorem isLocallyQuasiCoherent_iff {X : GroupoidsOver S} (F : etaleModules X) :
    IsLocallyQuasiCoherent F ↔
      ∀ x : X.total, ((restrictModulesToSmallEtale X x).obj F).IsQuasicoherent := sorry

/-- Local quasi-coherence on étale modules agrees with `IsLocallyQuasicoherent` after
transport to a presheaf of modules over the fppf structure sheaf. -/
theorem isLocallyQuasiCoherent_iff_isLocallyQuasicoherent
    {X : GroupoidsOver S} (F : etaleModules X) :
    IsLocallyQuasiCoherent F ↔ IsLocallyQuasicoherent (etaleModulePresheaf F) := sorry

/-- The étale structure sheaf `𝒪_X` is locally quasi-coherent. -/
instance isLocallyQuasiCoherent_unit (X : GroupoidsOver S) :
    IsLocallyQuasiCoherent (SheafOfModules.unit (etaleStructureSheaf X) : etaleModules X) :=
  sorry

/-- The object property of locally quasi-coherent étale `𝒪_X`-modules. -/
abbrev locallyQuasiCoherent (X : GroupoidsOver S) : ObjectProperty (etaleModules X) :=
  IsLocallyQuasiCoherent

/-- Tensor product of étale `𝒪_X`-modules in the commutative ringed-site presentation. -/
noncomputable abbrev moduleTensorEtale {X : GroupoidsOver S} (F G : etaleModules X) :
    etaleModules X :=
  SheafOfModules.RingedSite.moduleTensor.{u + 1, u, u} F G

/-- The category of locally quasi-coherent étale `𝒪_X`-modules. -/
abbrev LQCoh (X : GroupoidsOver S) :=
  (locallyQuasiCoherent X).FullSubcategory

namespace LQCoh

/-- The inclusion of locally quasi-coherent modules into all étale `𝒪_X`-modules. -/
abbrev inclusion (X : GroupoidsOver S) : LQCoh X ⥤ etaleModules X :=
  (locallyQuasiCoherent X).ι

end LQCoh

/-- A locally quasi-coherent module on the universe-lifted étale ringed site of `X`. -/
class IsLocallyQuasiCoherentLift {X : GroupoidsOver S}
    (F : ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
      X.etaleTopology (commEtaleStructureSheafLift X)) : Prop where
  /-- Restriction to the lifted small étale site of the scheme underlying `x` is
  quasi-coherent. -/
  restrict_isQuasicoherent (x : X.total) :
    ((restrictToSmallEtaleLift X x).obj F).IsQuasicoherent

/-- The universe-lifted étale structure sheaf is locally quasi-coherent. -/
instance isLocallyQuasiCoherentLift_unit (X : GroupoidsOver S) :
    IsLocallyQuasiCoherentLift
      (SheafOfModules.unit
        (Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (commEtaleStructureSheafLift X))) := sorry

/-- Lifted local quasi-coherence is pointwise quasi-coherence of lifted small-étale
restrictions. -/
theorem isLocallyQuasiCoherentLift_iff {X : GroupoidsOver S}
    (F : ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
      X.etaleTopology (commEtaleStructureSheafLift X)) :
    IsLocallyQuasiCoherentLift F ↔
      ∀ x : X.total, ((restrictToSmallEtaleLift X x).obj F).IsQuasicoherent := sorry

end AlgebraicGeometry.GroupoidsOver
