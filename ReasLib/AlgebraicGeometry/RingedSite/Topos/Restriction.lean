/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Flat
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek

/-!
# Canonical restrictions of ringed topoi

Continuous and cocontinuous site functors induce ringed-topos morphisms with the
restricted structure sheaf. An object-surjective family of these restrictions
detects flatness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v uX vX uY vY uI w

namespace RingedSite.Cocontinuous

variable (X : RingedSite.{uX, vX, w})
variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) (inclusion : C ⥤ X.carrier)
variable [inclusion.IsContinuous J X.siteTopology]

/-- The ringed site whose structure sheaf is the restriction of the given structure
sheaf along a continuous site functor. -/
abbrev restrictionRingedSite : RingedSite.{u, v, w} :=
  ofRingSheaf J (inverseImageRingSheaf inclusion X.structureSheaf)

variable [inclusion.IsCocontinuous J X.siteTopology]
variable [HasSheafify J (Type w)]
variable [∀ P : Cᵒᵖ ⥤ Type w, inclusion.op.HasPointwiseRightKanExtension P]
variable [J.HasSheafCompose (forget RingCat.{w})]
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]

/-- The ringed-topos morphism induced by a continuous and cocontinuous site functor,
using the identity comparison on the restricted structure sheaf. -/
def restrictionMorphism : ToposHom (restrictionRingedSite X J inclusion) X :=
  toRingedTopos inclusion (𝟙 (inclusion.op ⋙ X.structureSheaf.obj))

/-- The canonical morphism from a site with the restricted structure sheaf is flat. -/
theorem restrictionMorphism_isFlat
    [(SheafOfModules.restrictScalars.{w}
      (restrictionMorphism X J inclusion).structureMap).IsRightAdjoint] :
    ToposHom.IsFlat (restrictionMorphism X J inclusion) :=
  sorry

end RingedSite.Cocontinuous

namespace RingedSite.ToposHom

/-- Flatness of a ringed-topos morphism is detected by canonical restrictions along
an object-surjective family of continuous and cocontinuous site functors. -/
theorem isFlat_iff_restrictions
    (X : RingedSite.{uX, vX, w}) {Y : RingedSite.{uY, vY, w}}
    {I : Type uI} (C : I → Type u) [∀ index, Category.{v} (C index)]
    (J : ∀ index, GrothendieckTopology (C index))
    (inclusion : ∀ index, C index ⥤ X.carrier)
    [∀ index, (inclusion index).IsContinuous (J index) X.siteTopology]
    [∀ index, (inclusion index).IsCocontinuous (J index) X.siteTopology]
    [∀ index, HasSheafify (J index) (Type w)]
    [∀ index, ∀ P : (C index)ᵒᵖ ⥤ Type w,
      (inclusion index).op.HasPointwiseRightKanExtension P]
    [∀ index, (J index).HasSheafCompose (forget RingCat.{w})]
    [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
    (objectSurjective : ∀ totalObject : X.carrier, ∃ index, ∃ stageObject : C index,
      (inclusion index).obj stageObject = totalObject)
    (a : ToposHom X Y)
    [(SheafOfModules.restrictScalars.{w} a.structureMap).IsRightAdjoint]
    [∀ index : I, Functor.IsRightAdjoint (SheafOfModules.restrictScalars.{w}
      ((Cocontinuous.restrictionMorphism X (J index) (inclusion index)).comp a).structureMap)] :
    IsFlat a ↔ ∀ index,
      IsFlat ((Cocontinuous.restrictionMorphism X (J index) (inclusion index)).comp a) :=
  sorry

end RingedSite.ToposHom
