/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.Equivalence
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module

/-!
# Flat morphisms of ringed topoi

A morphism of site-presented ringed topoi is flat when its
inverse-image structure map is flat: `O_X` is flat as a sheaf of `f⁻¹ O_Y`-modules.
This is exactness of extension of scalars along `f.structureMap`, not exactness of the
geometric module pullback `f.modulePullback`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe uX vX uY vY uZ vZ w

namespace RingedSite.ToposHom

section

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]

/-- A morphism of ringed topoi is flat when `f.structureMap : f⁻¹ O_Y ⟶ O_X` is
flat, i.e. `O_X` is flat as an `f⁻¹ O_Y`-module, encoded as exactness of `SheafOfModules.ChangeOfRings.extendScalars f.structureMap`. -/
class IsFlat.{u₁, v₁, u₂, v₂, wFlat}
    {X : RingedSite.{u₁, v₁, wFlat}} {Y : RingedSite.{u₂, v₂, wFlat}}
    [X.siteTopology.HasSheafCompose (forget RingCat.{wFlat})]
    [Y.siteTopology.HasSheafCompose (forget RingCat.{wFlat})]
    (f : ToposHom X Y)
    [(SheafOfModules.restrictScalars.{wFlat} f.structureMap).IsRightAdjoint] : Prop where
  /-- Extension of scalars along `f.structureMap : f⁻¹ O_Y ⟶ O_X` is exact. -/
  exact_extendScalars :
    exactFunctor
      (SheafOfModules.{wFlat} (f.toTopos.ringInverseImage.obj Y.structureSheaf))
      (SheafOfModules.{wFlat} X.structureSheaf)
      (SheafOfModules.ChangeOfRings.extendScalars f.structureMap)

/-- Bundled exact extension of scalars along the inverse-image structure map of a
flat morphism of ringed topoi. -/
def IsFlat.exactExtendScalars (f : ToposHom X Y)
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint] [IsFlat f] :
    SheafOfModules.{w} (f.toTopos.ringInverseImage.obj Y.structureSheaf) ⥤ₑ
      SheafOfModules.{w} X.structureSheaf :=
  ⟨SheafOfModules.ChangeOfRings.extendScalars f.structureMap,
    (inferInstance : IsFlat f).exact_extendScalars⟩

/-- Extension of scalars along the inverse-image structure map of a flat morphism is
exact. -/
theorem IsFlat.extendScalars_exact (f : ToposHom X Y)
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint] [IsFlat f] :
    exactFunctor
      (SheafOfModules.{w} (f.toTopos.ringInverseImage.obj Y.structureSheaf))
      (SheafOfModules.{w} X.structureSheaf)
      (SheafOfModules.ChangeOfRings.extendScalars f.structureMap) :=
  (inferInstance : IsFlat f).exact_extendScalars

/-- Flatness of a morphism of ringed topoi is exactness of extension of scalars along
`f.structureMap`. -/
theorem isFlat_iff_extendScalars_exact (f : ToposHom X Y)
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint] :
    IsFlat f ↔
      exactFunctor
        (SheafOfModules.{w} (f.toTopos.ringInverseImage.obj Y.structureSheaf))
        (SheafOfModules.{w} X.structureSheaf)
        (SheafOfModules.ChangeOfRings.extendScalars f.structureMap) :=
  ⟨fun h ↦ h.exact_extendScalars, fun h ↦ ⟨h⟩⟩

/-- Extension of scalars along the inverse-image structure map of a flat morphism
preserves finite limits. -/
theorem IsFlat.preservesFiniteLimits (f : ToposHom X Y)
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint] [IsFlat f] :
    PreservesFiniteLimits
      (SheafOfModules.ChangeOfRings.extendScalars f.structureMap) :=
  (IsFlat.extendScalars_exact f).1

/-- Extension of scalars along the inverse-image structure map of a flat morphism
preserves finite colimits. -/
theorem IsFlat.preservesFiniteColimits (f : ToposHom X Y)
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint] [IsFlat f] :
    PreservesFiniteColimits
      (SheafOfModules.ChangeOfRings.extendScalars f.structureMap) :=
  (IsFlat.extendScalars_exact f).2

/-- A flat morphism of ringed topoi has exact module pullback. -/
theorem IsFlat.pullback_exact (f : ToposHom X Y)
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint] [IsFlat f] :
    exactFunctor
      (SheafOfModules.{w} Y.structureSheaf)
      (SheafOfModules.{w} X.structureSheaf)
      f.modulePullback :=
  sorry

/-- The module pullback of a flat morphism, bundled with its exactness certificate. -/
def IsFlat.exactPullback (f : ToposHom X Y)
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint] [IsFlat f] :
    SheafOfModules.{w} Y.structureSheaf ⥤ₑ SheafOfModules.{w} X.structureSheaf :=
  ⟨f.modulePullback, IsFlat.pullback_exact f⟩

end

/-- The identity morphism of a site-presented ringed topos is flat. -/
theorem IsFlat.id (X : RingedSite.{uX, vX, w})
    [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [(SheafOfModules.restrictScalars.{w} (ToposHom.id X).structureMap).IsRightAdjoint] :
    IsFlat (ToposHom.id X) := by
  let e := (MorphismOfTopoiIn.ringInverseImageIdIso
    (J₀ := X.siteTopology)).app X.structureSheaf
  letI : (SheafOfModules.restrictScalars.{w}
      (ToposHom.id X).structureMap).IsEquivalence :=
    (SheafOfModules.ChangeOfRings.restrictScalarsEquivalence e).isEquivalence_inverse
  letI := (SheafOfModules.ChangeOfRings.extendRestrictAdjunction
    (ToposHom.id X).structureMap).isEquivalence_left_of_isEquivalence_right
  exact ⟨(exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩⟩

/-- The composite of flat morphisms of ringed topoi is flat. -/
theorem IsFlat.comp {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    {Z : RingedSite.{uZ, vZ, w}}
    [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [Z.siteTopology.HasSheafCompose (forget RingCat.{w})]
    (f : ToposHom X Y) (g : ToposHom Y Z)
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} g.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} (f.comp g).structureMap).IsRightAdjoint]
    [IsFlat f] [IsFlat g] : IsFlat (f.comp g) :=
  sorry

end RingedSite.ToposHom
