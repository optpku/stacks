module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.FinitePresentation
import StacksCheckRecall

@[expose] public section

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

/- Lemma 91.11.3. For a strict morphism of first-order thickenings, a module flat over
the thickened base is finitely presented exactly when its canonical pullback is. -/
@[stacks 08VU] #check (RingedSite.ToposHom.Thickening.isFinitePresentation_iff :
  ∀ (sq : RingedSite.ToposHom.CommSquare
      (RingedSite.ofCommRingSheaf J₀ O₀) (RingedSite.ofCommRingSheaf J₁ O₁)
      (RingedSite.ofCommRingSheaf J₂ O₂) (RingedSite.ofCommRingSheaf J₃ O₃))
    [RingedSite.ToposHom.IsFirstOrderThickening sq.upper]
    [RingedSite.ToposHom.IsFirstOrderThickening sq.lower]
    [(SheafOfModules.restrictScalars.{w} sq.upper.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} sq.right.structureMap).IsRightAdjoint]
    (F' : SheafOfModules.RingedSite.ringedSiteModuleCategory.{u₁, v₁, w, w} J₁ O₁),
    RingedSite.ToposHom.IsFlatOver sq.right F' →
    RingedSite.ToposHom.Thickening.IsStrict sq →
    (F'.IsFinitePresentation ↔ (sq.upper.modulePullback.obj F').IsFinitePresentation))
