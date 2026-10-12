/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Square
public import stacks_project.Chap91.Situation_91_9_1_Thickening

/-!
# Comparison maps along a morphism of thickenings of ringed topoi

A morphism of thickenings is a commutative square of ringed topoi whose horizontals are
thickenings.  After identifying inverse images along the thickening equivalences, `(f')^♯`
induces an `𝒪'`-module map `(f')^* 𝒥 ⟶ ℐ`.  In the first-order case this becomes
`f^* 𝒥 ⟶ ℐ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Sheaf.InternalModule
open SheafOfModules.ChangeOfRings

noncomputable section

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ uZ vZ w

namespace RingedSite.ToposHom

variable {X : RingedSite.{u₀, v₀, w}} {Y : RingedSite.{u₁, v₁, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [X.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

/-- The inverse-image mate of an isomorphism of direct-image functors. -/
noncomputable def inverseImageIsoOfPushforwardIso (f g : ToposHom X Y)
    (e : f.toTopos.pushforward ≅ g.toTopos.pushforward) :
    f.toTopos.inverseImage ≅ g.toTopos.inverseImage :=
  (f.toTopos.adjunction.ofNatIsoRight e).leftAdjointUniq g.toTopos.adjunction

/-- If `i_*` is an equivalence, then `i^{-1}` is canonically the inverse functor of `i_*`. -/
noncomputable def inverseImageIsoPushforwardInv (f : ToposHom X Y)
    [Functor.IsEquivalence f.toTopos.pushforward] :
    f.toTopos.inverseImage ≅ f.toTopos.pushforward.inv :=
  f.toTopos.adjunction.leftAdjointUniq f.toTopos.pushforward.asEquivalence.symm.toAdjunction

/-- Direct image of modules along morphisms related by an invertible `2`-cell. -/
noncomputable def modulePushforwardIsoOfTwoIso {f g : ToposHom X Y} (e : TwoIso f g) :
    f.modulePushforward ≅ g.modulePushforward :=
  NatIso.ofComponents
    (fun M ↦
      { hom := homOfUnderlying Y.structureSheaf
          ((ModulePushforward.forgetIso f).hom.app M ≫
            e.homIso.hom.app ((ToInternal.underlying X.structureSheaf).obj M) ≫
              (ModulePushforward.forgetIso g).inv.app M)
          sorry sorry
        inv := homOfUnderlying Y.structureSheaf
          ((ModulePushforward.forgetIso g).hom.app M ≫
            e.homIso.inv.app ((ToInternal.underlying X.structureSheaf).obj M) ≫
              (ModulePushforward.forgetIso f).inv.app M)
          sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Inverse image of modules along morphisms related by an invertible `2`-cell. -/
noncomputable def modulePullbackIsoOfTwoIso {f g : ToposHom X Y} (e : TwoIso f g)
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} g.structureMap).IsRightAdjoint] :
    f.modulePullback ≅ g.modulePullback :=
  f.moduleAdjunction.leftAdjointUniq
    (g.moduleAdjunction.ofNatIsoRight (modulePushforwardIsoOfTwoIso e).symm)

variable {Z : RingedSite.{u₂, v₂, w}}
variable [Z.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Z.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

/-- Direct image of modules along a composite is iterated direct image. -/
noncomputable def modulePushforwardCompIso (f : ToposHom X Y) (g : ToposHom Y Z) :
    f.modulePushforward ⋙ g.modulePushforward ≅ (comp f g).modulePushforward :=
  NatIso.ofComponents
    (fun M ↦
      { hom := homOfUnderlying Z.structureSheaf
          ((ModulePushforward.forgetIso g).hom.app (f.modulePushforward.obj M) ≫
            g.toTopos.pushforward.map ((ModulePushforward.forgetIso f).hom.app M) ≫
              (ModulePushforward.forgetIso (comp f g)).inv.app M)
          sorry sorry
        inv := homOfUnderlying Z.structureSheaf
          ((ModulePushforward.forgetIso (comp f g)).hom.app M ≫
            g.toTopos.pushforward.map ((ModulePushforward.forgetIso f).inv.app M) ≫
              (ModulePushforward.forgetIso g).inv.app (f.modulePushforward.obj M))
          sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Inverse image of modules along a composite is iterated inverse image. -/
noncomputable def modulePullbackCompIso (f : ToposHom X Y) (g : ToposHom Y Z)
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} g.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} (comp f g).structureMap).IsRightAdjoint] :
    (comp f g).modulePullback ≅ g.modulePullback ⋙ f.modulePullback :=
  (comp f g).moduleAdjunction.leftAdjointUniq
    ((g.moduleAdjunction.comp f.moduleAdjunction).ofNatIsoRight
      (modulePushforwardCompIso f g))

/-- The unit `𝒪`-module has the same underlying type-valued sheaf as the structure sheaf. -/
noncomputable def unitCarrierIso (Z : RingedSite.{uZ, vZ, w})
    [Z.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [Z.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})] :
    Hom.underlyingStructureSheaf Z ≅
      (ToInternal.underlying Z.structureSheaf).obj (SheafOfModules.unit Z.structureSheaf) where
  hom := ⟨{ app := fun U ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry }⟩
  inv := ⟨{ app := fun U ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry }⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The canonical map `(f')^* 𝒪_Y ⟶ 𝒪_X` on unit modules. -/
noncomputable def modulePullbackObjUnitToUnit (f : ToposHom X Y)
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint] :
    f.modulePullback.obj (SheafOfModules.unit Y.structureSheaf) ⟶
      SheafOfModules.unit X.structureSheaf :=
  (f.moduleAdjunction.homEquiv _ _).symm
    (homOfUnderlying Y.structureSheaf
      ((unitCarrierIso Y).inv ≫
        f.underlyingDirectImageMap ≫
          f.toTopos.pushforward.map (unitCarrierIso X).hom ≫
            (ModulePushforward.forgetIso f).inv.app (SheafOfModules.unit X.structureSheaf))
      sorry sorry)

end RingedSite.ToposHom

namespace RingedSite.ToposHom.Thickening

variable {A : RingedSite.{u₀, v₀, w}} {B : RingedSite.{u₁, v₁, w}}
variable {C : RingedSite.{u₂, v₂, w}} {D : RingedSite.{u₃, v₃, w}}
variable [A.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [B.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [C.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [D.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [A.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [B.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [C.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [D.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasSheafify B.siteTopology AddCommGrpCat.{w}]
variable [HasSheafify D.siteTopology AddCommGrpCat.{w}]
variable [B.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [D.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Assemble a morphism of thickenings of ringed topoi from the four edges and the invertible
`2`-cell, with thickening hypotheses on the horizontal arrows. -/
def homMk (i : ToposHom A B) (f : ToposHom A C) (f' : ToposHom B D) (t : ToposHom C D)
    [IsThickening i] [IsThickening t]
    (cell : TwoIso (comp i f') (comp f t)) : CommSquare A B C D where
  upper := i
  left := f
  right := f'
  lower := t
  cell := cell

/-- The upper edge of `homMk` is the source thickening. -/
theorem homMk_upper (i : ToposHom A B) (f : ToposHom A C) (f' : ToposHom B D)
    (t : ToposHom C D) [IsThickening i] [IsThickening t]
    (cell : TwoIso (comp i f') (comp f t)) :
    (homMk i f f' t cell).upper = i := sorry

/-- The left edge of `homMk` is the closed-space map. -/
theorem homMk_left (i : ToposHom A B) (f : ToposHom A C) (f' : ToposHom B D)
    (t : ToposHom C D) [IsThickening i] [IsThickening t]
    (cell : TwoIso (comp i f') (comp f t)) :
    (homMk i f f' t cell).left = f := sorry

/-- The right edge of `homMk` is the ambient map. -/
theorem homMk_right (i : ToposHom A B) (f : ToposHom A C) (f' : ToposHom B D)
    (t : ToposHom C D) [IsThickening i] [IsThickening t]
    (cell : TwoIso (comp i f') (comp f t)) :
    (homMk i f f' t cell).right = f' := sorry

/-- The lower edge of `homMk` is the target thickening. -/
theorem homMk_lower (i : ToposHom A B) (f : ToposHom A C) (f' : ToposHom B D)
    (t : ToposHom C D) [IsThickening i] [IsThickening t]
    (cell : TwoIso (comp i f') (comp f t)) :
    (homMk i f f' t cell).lower = t := sorry

/-- Identification of inverse images of the two composites of a commutative square of
ringed topoi. -/
noncomputable def pullbackIso (sq : CommSquare A B C D) :
    (comp sq.upper sq.right).toTopos.inverseImage ≅
      (comp sq.left sq.lower).toTopos.inverseImage :=
  inverseImageIsoOfPushforwardIso (comp sq.upper sq.right) (comp sq.left sq.lower)
    sq.cell.homIso

section IdealMap

variable (sq : CommSquare A B C D)
variable [IsThickening sq.upper] [IsThickening sq.lower]
variable [(SheafOfModules.restrictScalars.{w} sq.right.structureMap).IsRightAdjoint]

/-- The comparison `(f')^* 𝒥 ⟶ 𝒪'` induced by `(f')^♯` on the target kernel. -/
noncomputable def idealMap_toUnit :
    sq.right.modulePullback.obj (ker sq.lower) ⟶
      SheafOfModules.unit B.structureSheaf :=
  sq.right.modulePullback.map (kernelIdeal_ι sq.lower) ≫
    modulePullbackObjUnitToUnit sq.right

/-- The comparison `(f')^* 𝒥 ⟶ 𝒪'` factors through `ℐ = Ker(i^♯)`. -/
theorem idealMap_toUnit_comp_kernelMap :
    idealMap_toUnit sq ≫ kernelMap sq.upper = 0 := sorry

/-- The `𝒪'`-module comparison `(f')^* 𝒥 ⟶ ℐ` induced by `(f')^♯`. -/
noncomputable def idealMap :
    sq.right.modulePullback.obj (ker sq.lower) ⟶ ker sq.upper :=
  kernel.lift (kernelMap sq.upper) (idealMap_toUnit sq) (idealMap_toUnit_comp_kernelMap sq)

/-- The comparison `(f')^* 𝒥 ⟶ ℐ` followed by the inclusion of `ℐ` recovers
`(f')^* 𝒥 ⟶ 𝒪'`. -/
theorem idealMap_spec :
    idealMap sq ≫ kernelIdeal_ι sq.upper = idealMap_toUnit sq := sorry

end IdealMap

section SourceIdealMap

variable (sq : CommSquare A B C D)
variable [IsFirstOrderThickening sq.upper] [IsFirstOrderThickening sq.lower]
variable [(SheafOfModules.restrictScalars.{w} sq.left.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} sq.right.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} sq.upper.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} sq.lower.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} (comp sq.left sq.lower).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} (comp sq.upper sq.right).structureMap).IsRightAdjoint]

/-- The first-order comparison `f^* 𝒥 ⟶ ℐ` of kernel ideals as `𝒪`-modules. -/
noncomputable def sourceIdealMap :
    sq.left.modulePullback.obj (idealModule sq.lower) ⟶ idealModule sq.upper :=
  (modulePullbackCompIso sq.left sq.lower).inv.app (kernelIdeal sq.lower) ≫
    (modulePullbackIsoOfTwoIso sq.cell).inv.app (kernelIdeal sq.lower) ≫
      (modulePullbackCompIso sq.upper sq.right).hom.app (kernelIdeal sq.lower) ≫
        sq.upper.modulePullback.map (idealMap sq)

/-- `sourceIdealMap` is the composite of `modulePullbackCompIso`, the identification along
the square cell, and inverse image of `idealMap`. -/
theorem sourceIdealMap_spec :
    sourceIdealMap sq =
      (modulePullbackCompIso sq.left sq.lower).inv.app (kernelIdeal sq.lower) ≫
        (modulePullbackIsoOfTwoIso sq.cell).inv.app (kernelIdeal sq.lower) ≫
          (modulePullbackCompIso sq.upper sq.right).hom.app (kernelIdeal sq.lower) ≫
            sq.upper.modulePullback.map (idealMap sq) := sorry

end SourceIdealMap

end RingedSite.ToposHom.Thickening
