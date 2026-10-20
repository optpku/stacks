/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.Strict
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.FlatOver
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Finite presentation across strict first-order thickenings

Relative flatness over the thickened base makes finite presentation invariant under
pullback along the source thickening of a strict morphism of first-order thickenings.
-/

@[expose] public section

namespace RingedSite.ToposHom.Thickening

open CategoryTheory

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ w

variable {C₀ : Type u₀} [Category.{v₀} C₀] {C₁ : Type u₁} [Category.{v₁} C₁]
variable {C₂ : Type u₂} [Category.{v₂} C₂] {C₃ : Type u₃} [Category.{v₃} C₃]
variable {J₀ : GrothendieckTopology C₀} {J₁ : GrothendieckTopology C₁}
variable {J₂ : GrothendieckTopology C₂} {J₃ : GrothendieckTopology C₃}
variable [J₀.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J₁.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J₂.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J₃.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J₀.HasSheafCompose (forget RingCat.{w})]
variable [J₁.HasSheafCompose (forget RingCat.{w})]
variable [J₂.HasSheafCompose (forget RingCat.{w})]
variable [J₃.HasSheafCompose (forget RingCat.{w})]
variable [J₀.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [J₁.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [J₂.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [J₃.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasSheafify J₁ AddCommGrpCat.{w}] [HasSheafify J₃ AddCommGrpCat.{w}]
variable [J₁.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [J₃.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : C₀, HasWeakSheafify (J₀.over U) AddCommGrpCat.{w}]
variable [∀ U : C₀, (J₀.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : C₁, HasWeakSheafify (J₁.over U) AddCommGrpCat.{w}]
variable [∀ U : C₁, (J₁.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O₀ : Sheaf J₀ CommRingCat.{w}} {O₁ : Sheaf J₁ CommRingCat.{w}}
variable {O₂ : Sheaf J₂ CommRingCat.{w}} {O₃ : Sheaf J₃ CommRingCat.{w}}

/-- For a strict morphism of first-order thickenings of commutative ringed topoi, a module
on the thickened source that is flat over the thickened base is finitely presented if and
only if its pullback to the unthickened source is finitely presented. -/
@[stacks 08VU]
theorem isFinitePresentation_iff
    (sq : CommSquare (ofCommRingSheaf J₀ O₀) (ofCommRingSheaf J₁ O₁)
      (ofCommRingSheaf J₂ O₂) (ofCommRingSheaf J₃ O₃))
    [IsFirstOrderThickening sq.upper] [IsFirstOrderThickening sq.lower]
    [(SheafOfModules.restrictScalars.{w} sq.upper.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} sq.right.structureMap).IsRightAdjoint]
    (F' : SheafOfModules.RingedSite.ringedSiteModuleCategory.{u₁, v₁, w, w} J₁ O₁)
    (hflat : IsFlatOver sq.right F') (hstrict : IsStrict sq) :
    F'.IsFinitePresentation ↔ (sq.upper.modulePullback.obj F').IsFinitePresentation := sorry

end RingedSite.ToposHom.Thickening
