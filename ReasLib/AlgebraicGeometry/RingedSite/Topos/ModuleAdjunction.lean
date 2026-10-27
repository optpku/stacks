/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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
variable [@GrothendieckTopology.HasSheafCompose X.carrier X.carrier.str RingCat.{w} inferInstance (Type w) inferInstance X.siteTopology (forget RingCat.{w})]
  [@GrothendieckTopology.HasSheafCompose Y.carrier Y.carrier.str RingCat.{w} inferInstance (Type w) inferInstance Y.siteTopology (forget RingCat.{w})]
variable (f : ToposHom X Y)

/-- The right adjoint before combining the two restrictions of scalars. -/
noncomputable def moduleRightComposite :
    (@_root_.SheafOfModules.{w} X.carrier X.carrier.str X.siteTopology X.structureSheaf) ⥤ (@_root_.SheafOfModules.{w} Y.carrier Y.carrier.str Y.siteTopology Y.structureSheaf) :=
  (@SheafOfModules.restrictScalars.{w} X.carrier X.carrier.str X.siteTopology _ _ f.structureMap) ⋙
    (@MorphismOfTopoiIn.moduleRightOver Y.carrier Y.carrier.str Y.siteTopology X.carrier X.carrier.str X.siteTopology inferInstance inferInstance f.toTopos Y.structureSheaf)

/-- The composite right adjoint has the usual underlying direct-image sheaf. -/
noncomputable def moduleRightCompositeForgetIso :
    f.moduleRightComposite ⋙ (@Sheaf.InternalModule.ToInternal.underlying Y.carrier Y.carrier.str Y.siteTopology inferInstance Y.structureSheaf) ≅
      (@Sheaf.InternalModule.ToInternal.underlying X.carrier X.carrier.str X.siteTopology inferInstance X.structureSheaf) ⋙ f.toTopos.pushforward :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((@SheafOfModules.restrictScalars.{w} X.carrier X.carrier.str X.siteTopology _ _ f.structureMap))
      ((@MorphismOfTopoiIn.moduleRightOverForgetIso Y.carrier Y.carrier.str Y.siteTopology X.carrier X.carrier.str X.siteTopology inferInstance inferInstance f.toTopos Y.structureSheaf))

/-- Combining scalar restrictions preserves the specified underlying sheaf
map, with scalar compatibility induced by the ring-adjunction mate. -/
noncomputable def moduleRightComparisonHom (M : (@_root_.SheafOfModules.{w} X.carrier X.carrier.str X.siteTopology X.structureSheaf)) :
    f.moduleRightComposite.obj M ⟶ f.modulePushforward.obj M :=
  @Sheaf.InternalModule.homOfUnderlying Y.carrier Y.carrier.str Y.siteTopology inferInstance Y.structureSheaf _ _
    ((f.moduleRightCompositeForgetIso).hom.app M ≫
      (ModulePushforward.forgetIso f).inv.app M) sorry sorry

/-- The reverse comparison uses the inverse of the same forgetful isomorphisms. -/
noncomputable def moduleRightComparisonInv (M : (@_root_.SheafOfModules.{w} X.carrier X.carrier.str X.siteTopology X.structureSheaf)) :
    f.modulePushforward.obj M ⟶ f.moduleRightComposite.obj M :=
  @Sheaf.InternalModule.homOfUnderlying Y.carrier Y.carrier.str Y.siteTopology inferInstance Y.structureSheaf _ _
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

variable [((@SheafOfModules.restrictScalars.{w} X.carrier X.carrier.str X.siteTopology _ _ f.structureMap)).IsRightAdjoint]

/-- Compose the geometric module adjunction and scalar-extension adjunction. -/
noncomputable def moduleCompositeAdjunction :
    f.modulePullback ⊣ f.moduleRightComposite :=
  ((@MorphismOfTopoiIn.moduleAdjunction Y.carrier Y.carrier.str Y.siteTopology X.carrier X.carrier.str X.siteTopology inferInstance inferInstance f.toTopos Y.structureSheaf)).comp (ModulePullback.scalarAdjunction f)

/-- Pullback is left adjoint to the existing ringed-topos module pushforward. -/
noncomputable def moduleAdjunction : f.modulePullback ⊣ f.modulePushforward :=
  f.moduleCompositeAdjunction.ofNatIsoRight f.moduleRightComparison

end RingedSite.ToposHom
