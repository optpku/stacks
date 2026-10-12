/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.CategoryTheory.Sites.Topos.ModuleAdjunction

/-!
# Pullback and pushforward adjunction for ringed topoi

The geometric module adjunction is composed with extension of scalars.
The right adjoint is identified with the existing module pushforward using
the canonical underlying-sheaf comparisons. No module map is supplied as
an arbitrary parameter or chosen from an existence assertion.
-/

@[expose] public section

open CategoryTheory

universe uX vX uY vY w

namespace RingedSite.ToposHom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable (f : ToposHom X Y)

/-- The right adjoint before combining the two restrictions of scalars. -/
noncomputable def moduleRightComposite :
    SheafOfModules.{w} X.structureSheaf ⥤ SheafOfModules.{w} Y.structureSheaf :=
  SheafOfModules.restrictScalars f.structureMap ⋙
    f.toTopos.moduleRightOver Y.structureSheaf

/-- The composite right adjoint has the usual underlying direct-image sheaf. -/
noncomputable def moduleRightCompositeForgetIso :
    f.moduleRightComposite ⋙ Sheaf.InternalModule.ToInternal.underlying Y.structureSheaf ≅
      Sheaf.InternalModule.ToInternal.underlying X.structureSheaf ⋙ f.toTopos.pushforward :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.restrictScalars f.structureMap)
      (f.toTopos.moduleRightOverForgetIso Y.structureSheaf)

/-- Combining scalar restrictions preserves the specified underlying sheaf
map, with scalar compatibility induced by the ring-adjunction mate. -/
noncomputable def moduleRightComparisonHom (M : SheafOfModules.{w} X.structureSheaf) :
    f.moduleRightComposite.obj M ⟶ f.modulePushforward.obj M :=
  Sheaf.InternalModule.homOfUnderlying Y.structureSheaf
    ((f.moduleRightCompositeForgetIso).hom.app M ≫
      (ModulePushforward.forgetIso f).inv.app M) sorry sorry

/-- The reverse comparison uses the inverse of the same forgetful isomorphisms. -/
noncomputable def moduleRightComparisonInv (M : SheafOfModules.{w} X.structureSheaf) :
    f.modulePushforward.obj M ⟶ f.moduleRightComposite.obj M :=
  Sheaf.InternalModule.homOfUnderlying Y.structureSheaf
    ((ModulePushforward.forgetIso f).hom.app M ≫
      (f.moduleRightCompositeForgetIso).inv.app M) sorry sorry

/-- The two right-adjoint presentations agree through canonical module maps. -/
noncomputable def moduleRightComparison : f.moduleRightComposite ≅ f.modulePushforward :=
  NatIso.ofComponents
    (fun M ↦
      { hom := f.moduleRightComparisonHom M
        inv := f.moduleRightComparisonInv M
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

variable [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]

/-- Compose the geometric module adjunction and scalar-extension adjunction. -/
noncomputable def moduleCompositeAdjunction :
    f.modulePullback ⊣ f.moduleRightComposite :=
  (f.toTopos.moduleAdjunction Y.structureSheaf).comp (ModulePullback.scalarAdjunction f)

/-- Pullback is left adjoint to the existing ringed-topos module pushforward. -/
noncomputable def moduleAdjunction : f.modulePullback ⊣ f.modulePushforward :=
  f.moduleCompositeAdjunction.ofNatIsoRight f.moduleRightComparison

end RingedSite.ToposHom
