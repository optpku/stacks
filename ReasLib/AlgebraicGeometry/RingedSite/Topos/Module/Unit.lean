/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.Comparison
public import ReasLib.CategoryTheory.Sites.Topos.Sections

/-! # Inverse image of the structure module -/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf.InternalModule

noncomputable section

universe uX vX uY vY w

namespace RingedSite.ToposHom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [X.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable (f : ToposHom X Y)
variable [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]

/-- Maps from the inverse image of the structure module are the global sections of
an arbitrary module on the source topos. -/
def modulePullbackUnitHomEquiv (N : SheafOfModules.{w} X.structureSheaf) :
    (f.modulePullback.obj (SheafOfModules.unit Y.structureSheaf) ⟶ N) ≃
      (SheafOfModules.unit X.structureSheaf ⟶ N) :=
  (f.moduleAdjunction.homEquiv _ _).trans
    ((f.modulePushforward.obj N).unitHomEquiv.trans
      ((ToInternal.sectionsEquiv Y.structureSheaf (f.modulePushforward.obj N)).symm.trans
        (((Functor.sectionsFunctor _).mapIso
          ((sheafToPresheaf _ _).mapIso ((ModulePushforward.forgetIso f).app N))).toEquiv.trans
          ((f.toTopos.pushforwardSectionsEquiv _).trans
            ((ToInternal.sectionsEquiv X.structureSheaf N).trans N.unitHomEquiv.symm)))))

/-- The canonical inverse image of the structure module is isomorphic to the
structure module of the source topos. -/
def modulePullbackUnitIso :
    f.modulePullback.obj (SheafOfModules.unit Y.structureSheaf) ≅
      SheafOfModules.unit X.structureSheaf := by
  let forward := modulePullbackObjUnitToUnit f
  let backward := modulePullbackUnitHomEquiv f _ (𝟙 _)
  have laws : forward ≫ backward = 𝟙 _ ∧ backward ≫ forward = 𝟙 _ := by
    sorry
  exact ⟨forward, backward, laws.1, laws.2⟩

/-- The forward structure-module isomorphism is the canonical adjunction comparison. -/
theorem modulePullbackUnitIso_hom :
    (modulePullbackUnitIso f).hom = modulePullbackObjUnitToUnit f := rfl

end RingedSite.ToposHom
